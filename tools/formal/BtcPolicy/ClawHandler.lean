import BtcPolicy.FedSilence
/-! The claw-back handler's acceptance log inside the SILENCE walk (`SPN-50`, `SPN-51`, `DUR-1`, `DUR-36`).

`BtcPolicy.FedSilence.walk` covers a claw-back's post-check registration, `Kernel.Event.clawback`, and
answers it as `Silence.respond` does from `ClawbackIngress.verdict`. `SPN-50` puts an idempotent replay
before that registration: "After the preceding admission and post-preflight checks pass, a retained
acceptance key MUST return the claw-back commitment's first `Accepted` on this node verbatim and re-relay
the request, without signing again, registering again, reopening a window or resetting any resident
lifecycle state." This module adds that step to the walk.

**The request and its key.** `ClawHandler.Request` is a ClawbackRequest that passed the checks before
the replay lookup: its coordinator nonce, its exact decoded PSBT bytes, and the candidate
`Ingress.checkClawback` hands the kernel. `SPN-50`: "the acceptance key MUST be the request role
`clawback`, its commitment id, and its exact base64-decoded PSBT bytes, excluding the coordinator nonce
and coordinator signature" (`ClawHandler.Request.key`, `ClawHandler.key_nonce`).

**The log.** Each node keeps a list of `ClawHandler.Entry`, a key beside the response that node gave
the request, kept in structured form (`Silence.Resp`). `ClawHandler.lookup` and `ClawHandler.retain`
are `ClawbackIngress.lookup` and `ClawbackIngress.retain` over that form: for every encoder of a
response into bytes, encoding the log commutes with both (`ClawHandler.lookup_encode`,
`ClawHandler.retain_encode`), so the bytes a retained acceptance returns are the bytes the encoder gave
the stored response. No serializer is modelled, and nothing here says that a real one, a nonce
generator or a signer produces equal wire traffic.

**Three transitions.** A request at node `i` takes one of three cases (`ClawHandler.caseOf`), in
`SPN-50`'s order: Lockdown first; then the retained key (`replay`), which changes no state and answers
the stored response; otherwise fresh evaluation, which is the existing composed step on
`Kernel.Event.clawback` (`FedSilence.lapply`) and answers `Silence.respond`'s registration response,
either a refusal by code and check (`refusal`, `SPN-51`: it "MUST NOT be cached as an evaluation
refusal") or `Accepted` (`fresh`), whose key the log retains with the commitment's first `Accepted`.

**The walk.** `ClawHandler.hwalk` is `FedSilence.walk` with these request steps added to the schedule
alphabet (`ClawHandler.HStep`). A request step is admitted and stops the walk exactly where its fresh
evaluation would: the same `Federation.admits`, `Silence.preHorizon` and `Silence.wfEvent` guard
(`FedSilence.inside`). A replay observation has the shape of a fresh evaluation's
(`ClawHandler.replayObs`): the response, `/pending`, `locked_down`, no marker, no effect, no work and
no message; on a node where the claw-back is resident it differs from the observation fresh evaluation
would emit at most in the response's content (`ClawHandler.replay_indistinct`). No replay tag is
observed.

**What is outside.** The checks before the lookup (Lockdown at admission, authentication, nonce
length, freshness and nonce admission, propagatability, prevout fetch, expiry predicates, decode),
retention ending at commitment expiry, cacheable evaluation refusals, and the relay of the request on
fresh evaluation and its re-relay on replay. No entry here expires: the log keeps every key it
retained, and a result about a replay holds only while the real log would still hold that key. A nonce is admitted before the lookup
and is not consumed here; `SPN-50` says "A fresh nonce alone establishes no commitment replay hit;
nonce admission still precedes this lookup." These results concern the handler after those checks;
they are not a proof of the whole HTTP handler.

**Premises.** `ClawHandler.hfed_silence` takes `FedSilence.fed_silence`'s premises and equal logs
(`ClawHandler.HCoupled`); `ClawHandler.hfed_silence_fresh` and
`ClawHandler.hfed_silence_adaptive_fresh` take `FedSilence.fed_silence_fresh`'s and any log, one for
both runs. The responses the logs hold are never assumed equal: each fresh response is equal by the
coupling (`Silence.respond_clawback_pub`), and the logs stay equal because only such a response is
retained. On schedules without request steps the walk is `FedSilence.walk` and the adaptive walk is
`FedSilence.awalk` (`ClawHandler.hwalk_steps`, `ClawHandler.hawalk_lift`). -/
namespace BtcPolicy.ClawHandler
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence

/-! ## The request, its key and the structured log -/

/-- A ClawbackRequest after the checks before the replay lookup: the coordinator nonce, the exact
decoded PSBT bytes, and the candidate the checks hand the kernel. -/
structure Request where
  nonce : Nat
  psbt : Encode.Bytes
  cand : Cand
  deriving DecidableEq, Repr

/-- `SPN-50`: "the request role `clawback`, its commitment id, and its exact base64-decoded PSBT
bytes, excluding the coordinator nonce and coordinator signature". -/
@[req "SPN-50"]
def Request.key (q : Request) : ClawbackIngress.Key := ⟨.clawback, q.cand.id, q.psbt⟩

/-- Another coordinator nonce is the same key. -/
@[req "SPN-50"]
theorem key_nonce (q : Request) (m : Nat) : ({ q with nonce := m } : Request).key = q.key := rfl

/-- Other PSBT bytes are another key, whatever the commitment. -/
@[req "SPN-50"]
theorem key_bytes (q : Request) (p : Encode.Bytes) (h : p ≠ q.psbt) :
    ({ q with psbt := p } : Request).key ≠ q.key :=
  ClawbackIngress.bytes_separate _ _ h

/-- A retained key beside the response its first acceptance on this node gave, in structured form. -/
structure Entry where
  key : ClawbackIngress.Key
  resp : Resp
  deriving DecidableEq, Repr

/-- `ClawbackIngress.lookup`'s own matching rule, read entry by entry, so that the structured log
matches a key exactly when the byte log does. -/
@[req "SPN-50"]
def keyMatch (e : Entry) (key : ClawbackIngress.Key) : Bool :=
  (ClawbackIngress.lookup [⟨e.key, []⟩] key).isSome

/-- `ClawbackIngress.lookup` over the structured log: only the retained matching key answers. -/
@[req "SPN-50"]
def lookup (log : List Entry) (key : ClawbackIngress.Key) : Option Resp :=
  (log.find? (keyMatch · key)).map (·.resp)

/-- The rule matches the exact key. -/
@[req "SPN-50"]
theorem keyMatch_iff (e : Entry) (key : ClawbackIngress.Key) : keyMatch e key = decide (e.key = key) := by
  by_cases h : e.key = key <;> simp [keyMatch, ClawbackIngress.lookup, h]

/-- `ClawbackIngress.retain` over the structured log: a new key is added beside the commitment's
first acceptance for this role; existing entries are never replaced. -/
@[req "SPN-50"]
def retain (log : List Entry) (key : ClawbackIngress.Key) (resp : Resp) : List Entry :=
  if (lookup log key).isSome then log
  else
    let first := (log.find? fun e => e.key.role == key.role && e.key.id == key.id).map (·.resp)
    log ++ [⟨key, first.getD resp⟩]

/-- The byte log an encoder makes of the structured one. -/
def encode (enc : Resp → Encode.Bytes) (log : List Entry) : List ClawbackIngress.Entry :=
  log.map fun e => ⟨e.key, enc e.resp⟩

/-- **The lookup is `ClawbackIngress.lookup`, under every encoder.** -/
@[req "SPN-50"]
theorem lookup_encode (enc : Resp → Encode.Bytes) (log : List Entry) (key : ClawbackIngress.Key) :
    ClawbackIngress.lookup (encode enc log) key = (lookup log key).map enc := by
  have hk : (keyMatch · key) = fun e => decide (e.key = key) := funext fun e => keyMatch_iff e key
  simp only [ClawbackIngress.lookup, lookup, encode, List.find?_map, Option.map_map, hk]
  rfl

/-- **The retention is `ClawbackIngress.retain`, under every encoder.** -/
@[req "SPN-50"]
theorem retain_encode (enc : Resp → Encode.Bytes) (log : List Entry) (key : ClawbackIngress.Key)
    (resp : Resp) :
    encode enc (retain log key resp) = ClawbackIngress.retain (encode enc log) key (enc resp) := by
  unfold retain ClawbackIngress.retain
  rw [lookup_encode, Option.isSome_map]
  split
  · rfl
  · simp only [encode, List.map_append, List.map_cons, List.map_nil, List.find?_map, Option.map_map,
      Function.comp_def]
    congr 2
    generalize List.find? (fun e => e.key.role == key.role && e.key.id == key.id) log = o
    cases o <;> rfl

theorem lookup_none_iff (log : List Entry) (key : ClawbackIngress.Key) :
    lookup log key = none ↔ ∀ e ∈ log, e.key ≠ key := by
  simp [lookup, List.find?_eq_none, keyMatch_iff]

/-! ## The handler's transitions -/

/-- A federation whose nodes carry their Hot ledgers (`FedSilence.LFed`) and their acceptance logs. -/
structure HFed where
  L : LFed
  logs : Nat → List Entry

/-- One schedule step: a step of `FedSilence.PStep`, or a ClawbackRequest at node `i`. -/
inductive HStep
  | step (p : PStep)
  | claw (i : Nat) (env : Env) (q : Request)
  deriving DecidableEq, Repr

/-- The composed step a request's fresh evaluation takes: its post-check registration. -/
def freshStep (i : Nat) (env : Env) (q : Request) : Federation.Step :=
  .process i env (.clawback q.cand)

/-- The federation step a schedule step is guarded by, under one enrolment family. -/
def HStep.fed (tbls : Nat → Enrolment) : HStep → Federation.Step
  | .step p => p.step tbls
  | .claw i env q => freshStep i env q

/-- The three cases a request at a node takes. -/
inductive Case
  /-- A retained key: the stored response. -/
  | replay (resp : Resp)
  /-- Fresh evaluation refused at registration (`ClawbackIngress.verdict`). -/
  | refusal
  /-- Fresh evaluation accepted. -/
  | fresh
  deriving DecidableEq, Repr

/-- `SPN-50`'s order: Lockdown, then "idempotent replay", then registration. A latched node is
never answered from the log. -/
@[req "SPN-50"]
def hit (F : HFed) (i : Nat) (q : Request) : Option Resp :=
  if (F.L.fed.worlds i).node.lockedDown then none else lookup (F.logs i) q.key

@[req "SPN-51"]
def caseOf (F : HFed) (i : Nat) (q : Request) : Case :=
  match hit F i q with
  | some resp => .replay resp
  | none => if (ClawbackIngress.verdict (F.L.fed.worlds i).node q.cand).isSome then .refusal else .fresh

/-- The response fresh evaluation gives: `Silence.respond` on the post-check registration. -/
def freshResp (cfg : Config) (r : Rules) (F : HFed) (i : Nat) (env : Env) (q : Request) : Resp :=
  respond r cfg env (F.L.sys i) (.clawback q.cand)

/-- One log changed. -/
def setLog (logs : Nat → List Entry) (i : Nat) (log : List Entry) : Nat → List Entry :=
  fun j => if j = i then log else logs j

/-- The step. A replay changes nothing. A refusal is the composed step on the registration, which
leaves the node as it was (`ClawbackIngress.register_projection`), and no entry. An acceptance is the
composed step, and its key is retained with the response. -/
@[req "SPN-50"]
def happly (g : Guards) (cfg : Config) (r : Rules) (tbls : Nat → Enrolment) (F : HFed) :
    HStep → HFed
  | .step p => { F with L := lapply g cfg r F.L (p.step tbls) }
  | .claw i env q =>
    match caseOf F i q with
    | .replay _ => F
    | .refusal => { F with L := lapply g cfg r F.L (freshStep i env q) }
    | .fresh =>
      { L := lapply g cfg r F.L (freshStep i env q),
        logs := setLog F.logs i (retain (F.logs i) q.key (freshResp cfg r F i env q)) }

/-- A replay's observation at its node: the stored response, `/pending` and `locked_down` as the
node stands, and no marker, effect or work, the shape a fresh evaluation's has. -/
@[req "API-12"]
def replayObs (r : Rules) (env : Env) (n : Node) (resp : Resp) : Obs :=
  { resp := resp, pending := pending r env n, lockedDown := n.lockedDown, marker := false,
    effects := [], ops := [] }

/-- One step's observation. A replay addresses no message and moves no inventory. -/
@[req "DUR-1"]
def hobs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (F : HFed) : HStep → FObs
  | .step p => fobs mk g cfg r peers F.L (p.step tbls)
  | .claw i env q =>
    match caseOf F i q with
    | .replay resp =>
      { node := some (i, replayObs r env (F.L.fed.worlds i).node resp), sent := [], recv := none,
        net := F.L.fed.net, parts := F.L.fed.parts, extracted := F.L.fed.extracted }
    | _ => fobs mk g cfg r peers F.L (freshStep i env q)

/-- The two runs walked together. The guard is `FedSilence.walk`'s, on the step's federation form:
a request step is admitted and inside exactly where its fresh evaluation is. -/
def hwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : HFed → HFed → List HStep → List (FObs × FObs)
  | _, _, [] => []
  | A, B, s :: rest =>
    if Federation.admits honest A.L.fed (s.fed tbls₀) && inside r A.L (s.fed tbls₀) &&
        inside r B.L (s.fed tbls₁) then
      (hobs mk g cfg r peers tbls₀ A s, hobs mk g cfg r peers tbls₁ B s) ::
        hwalk mk g cfg r honest peers tbls₀ tbls₁ (happly g cfg r tbls₀ A s)
          (happly g cfg r tbls₁ B s) rest
    else []

/-! ## The three cases, one at a time -/

/-- **A retained acceptance, verbatim.** On a hit the handler changes no node, ledger, inventory or
log, and answers the stored response; under every encoder the byte log answers that response's bytes,
which is `ClawbackIngress.lookup`'s answer. A candidate pruned after the first acceptance is not
recreated and no window is reopened or re-timed: nothing moves. -/
@[req "SPN-50"]
theorem replay_unchanged (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (enc : Resp → Encode.Bytes) (F : HFed) (i : Nat) (env : Env)
    (q : Request) (resp : Resp) (h : hit F i q = some resp) :
    happly g cfg r tbls F (.claw i env q) = F ∧
      (hobs mk g cfg r peers tbls F (.claw i env q)).node =
        some (i, replayObs r env (F.L.fed.worlds i).node resp) ∧
      (hobs mk g cfg r peers tbls F (.claw i env q)).sent = [] ∧
      ClawbackIngress.lookup (encode enc (F.logs i)) q.key = some (enc resp) := by
  have hc : caseOf F i q = .replay resp := by simp [caseOf, h]
  refine ⟨by simp [happly, hc], by simp [hobs, hc], by simp [hobs, hc], ?_⟩
  rw [lookup_encode]
  unfold hit at h
  split at h
  · cases h
  · rw [h]; rfl

/-- **Fresh evaluation is the existing step.** Without a hit, a request's state change is
`FedSilence.lapply` on its post-check registration and its observation is `FedSilence.fobs`'s; only
an acceptance adds to the log, under `ClawHandler.retain`. -/
@[req "SPN-50"]
theorem fresh_projection (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (F : HFed) (i : Nat) (env : Env) (q : Request) (h : hit F i q = none) :
    (happly g cfg r tbls F (.claw i env q)).L = lapply g cfg r F.L (freshStep i env q) ∧
      hobs mk g cfg r peers tbls F (.claw i env q) = fobs mk g cfg r peers F.L (freshStep i env q) ∧
      ((happly g cfg r tbls F (.claw i env q)).logs =
        if (ClawbackIngress.verdict (F.L.fed.worlds i).node q.cand).isSome then F.logs
        else setLog F.logs i (retain (F.logs i) q.key (freshResp cfg r F i env q))) := by
  by_cases hv : (ClawbackIngress.verdict (F.L.fed.worlds i).node q.cand).isSome
  · have hc : caseOf F i q = .refusal := by simp [caseOf, h, hv]
    simp [happly, hobs, hc, hv]
  · have hc : caseOf F i q = .fresh := by simp [caseOf, h, hv]
    simp [happly, hobs, hc, hv]

/-- **Lockdown precedes the replay.** A latched node answers every request `FRAUD_SUSPECTED` /
`lockdown`, a retained key included, and retains nothing. -/
@[req "SPN-50"]
theorem lockdown_precedes_replay (mk : Marker) (g : Guards) (cfg : Config) (r : Rules)
    (peers : List Nat) (tbls : Nat → Enrolment) (F : HFed) (i : Nat) (env : Env) (q : Request)
    (hl : (F.L.fed.worlds i).node.lockedDown = true) :
    caseOf F i q = .refusal ∧ (happly g cfg r tbls F (.claw i env q)).logs = F.logs ∧
      (hobs mk g cfg r peers tbls F (.claw i env q)).node.map (·.2.resp) =
        some (.refusal .FRAUD_SUSPECTED "lockdown") := by
  have hh : hit F i q = none := by simp [hit, hl]
  have hv : ClawbackIngress.verdict (F.L.fed.worlds i).node q.cand =
      some ⟨.FRAUD_SUSPECTED, "lockdown"⟩ := by simp [ClawbackIngress.verdict, hl]
  have hc : caseOf F i q = .refusal := by simp [caseOf, hh, hv]
  refine ⟨hc, by simp [happly, hc], ?_⟩
  simp only [hobs, hc, fobs, localObs, freshStep, Federation.actor, Option.map_some, obsOf, respond,
    LFed.sys]
  rw [hv]

/-- **The nonce is not read.** A request with another coordinator nonce takes the same case, the same
step and the same observation. -/
@[req "SPN-50"]
theorem nonce_independent (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (F : HFed) (i : Nat) (env : Env) (q : Request) (m : Nat) :
    caseOf F i { q with nonce := m } = caseOf F i q ∧
      happly g cfg r tbls F (.claw i env { q with nonce := m }) = happly g cfg r tbls F (.claw i env q) ∧
      hobs mk g cfg r peers tbls F (.claw i env { q with nonce := m }) =
        hobs mk g cfg r peers tbls F (.claw i env q) :=
  ⟨rfl, rfl, rfl⟩

/-- **No replay tag.** At a node where a candidate under the request's id is resident, a replay's
observation is the one fresh evaluation would emit there, but for the response it carries: the same
`/pending`, `locked_down`, marker, effects, work, messages and inventories. Which response each gives
is a separate fact (the stored one, and `Silence.respond`'s); no other field tells them apart. -/
@[req "DUR-1"]
theorem replay_indistinct (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (F : HFed) (i : Nat) (env : Env) (q : Request) (resp : Resp)
    (h : hit F i q = some resp)
    (hres : (F.L.fed.worlds i).node.cands.any (·.id == q.cand.id) = true) :
    hobs mk g cfg r peers tbls F (.claw i env q) =
      let y := fobs mk g cfg r peers F.L (freshStep i env q)
      { y with node := y.node.map fun p => (p.1, { p.2 with resp := resp }) } := by
  have hc : caseOf F i q = .replay resp := by simp [caseOf, h]
  have hn : clawback env (F.L.fed.worlds i).node q.cand = (F.L.fed.worlds i).node := by
    simp [Kernel.clawback, hres]
  simp only [hobs, hc, fobs, localObs, freshStep, Federation.actor, Option.map_some, obsOf,
    replayObs, sent, received, lapply, LFed.advance, sysStep, LFed.sys, refusedByBudget, step, hn,
    markerOf, work, Federation.fanout, Federation.outbox, List.filterMap_nil, List.flatMap_nil,
    List.map_nil, List.append_nil, addressed, Bool.false_eq_true, if_false]
  simp

/-! ## The coupling -/

/-- Two handler states: the federations coupled as `FedSilence.FCoupled` has it, and equal logs. -/
structure HCoupled (r : Rules) (honest : List Nat) (A B : HFed) : Prop where
  fc : FCoupled r honest A.L B.L
  logs : A.logs = B.logs

theorem hcoupled_refl (r : Rules) (honest : List Nat) (A : HFed) : HCoupled r honest A A :=
  ⟨fcoupled_refl r honest A.L, rfl⟩

theorem node_pub {r : Rules} {honest : List Nat} {A B : HFed} (hc : HCoupled r honest A B) {i : Nat}
    (hi : i ∈ honest) : pubNode r (A.L.fed.worlds i).node = pubNode r (B.L.fed.worlds i).node :=
  (hc.fc.node i hi).node

/-- **The case reads no arm state.** Coupled states take the same case at an honest node: the hit
reads the Lockdown latch and the log, and the verdict the latch and pair membership. -/
@[req "DUR-36"]
theorem caseOf_pub {r : Rules} {honest : List Nat} {A B : HFed} (hc : HCoupled r honest A B)
    {i : Nat} (hi : i ∈ honest) (q : Request) : caseOf A i q = caseOf B i q := by
  have hn := node_pub hc hi
  have hv : ClawbackIngress.verdict (A.L.fed.worlds i).node q.cand =
      ClawbackIngress.verdict (B.L.fed.worlds i).node q.cand := by
    have := register_refusal_pub (env := Env.mk (Wall.sample 0) (HighWater.sample 0) (Mono.sample 0)
      ⟨Mtp.sample 0, []⟩ [] []) hn q.cand
    rwa [ClawbackIngress.register_verdict, ClawbackIngress.register_verdict] at this
  simp only [caseOf, hit, pub_lockedDown hn, hc.logs, hv]

theorem actor_mem {honest : List Nat} {f : Federation.Fed} {i : Nat} {env : Env} {q : Request}
    (h : Federation.admits honest f (freshStep i env q) = true) : i ∈ honest := by
  simp only [freshStep, Federation.admits, Bool.and_eq_true] at h
  exact List.contains_iff_mem.mp h.1

/-- One schedule step, in both runs: the coupling, the invariant in each run and the observation.
The responses a fresh step retains are equal by the coupling, never by a premise. -/
theorem hstep_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers : List Nat}
    {A B : HFed} (hc : HCoupled r honest A B) (hia : FInv r honest A.L) (hib : FInv r honest B.L)
    (s : HStep) (tbls₀ tbls₁ : Nat → Enrolment)
    (ha : Federation.admits honest A.L.fed (s.fed tbls₀) = true)
    (hpa : inside r A.L (s.fed tbls₀) = true) (hpb : inside r B.L (s.fed tbls₁) = true) :
    HCoupled r honest (happly g cfg r tbls₀ A s) (happly g cfg r tbls₁ B s) ∧
    FInv r honest (happly g cfg r tbls₀ A s).L ∧ FInv r honest (happly g cfg r tbls₁ B s).L ∧
    hobs mk g cfg r peers tbls₀ A s = hobs mk g cfg r peers tbls₁ B s := by
  cases s with
  | step p =>
    obtain ⟨h1, h2, h3, h4⟩ := pstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr
      hc.fc hia hib p tbls₀ tbls₁ ha hpa hpb
    exact ⟨⟨h1, hc.logs⟩, h2, h3, h4⟩
  | claw i env q =>
    have hi : i ∈ honest := actor_mem ha
    obtain ⟨h1, h2, h3, h4⟩ := pstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr
      hc.fc hia hib (.net (freshStep i env q)) tbls₀ tbls₁ ha hpa hpb
    have hcase := caseOf_pub hc hi q
    have hn := node_pub hc hi
    have hresp : freshResp cfg r A i env q = freshResp cfg r B i env q :=
      respond_clawback_pub hn q.cand
    cases hA : caseOf A i q with
    | replay resp =>
      have hB : caseOf B i q = .replay resp := hcase ▸ hA
      refine ⟨by simp only [happly, hA, hB]; exact hc, by simp only [happly, hA]; exact hia,
        by simp only [happly, hB]; exact hib, ?_⟩
      simp only [hobs, hA, hB, replayObs, pending_pub hn, pub_lockedDown hn, hc.fc.net, hc.fc.parts,
        hc.fc.extracted]
    | refusal =>
      have hB : caseOf B i q = .refusal := hcase ▸ hA
      simp only [happly, hobs, hA, hB]
      exact ⟨⟨h1, hc.logs⟩, h2, h3, h4⟩
    | fresh =>
      have hB : caseOf B i q = .fresh := hcase ▸ hA
      simp only [happly, hobs, hA, hB]
      exact ⟨⟨h1, by rw [hc.logs, hresp]⟩, h2, h3, h4⟩

/-! ## The relation -/

/-- **SILENCE through the handler, under one fixed exogenous schedule.** `DUR-1`: "Every observable
a node emits MUST be identical between a normal-PIN and a duress-PIN request".

`FedSilence.fed_silence` with ClawbackRequests in the schedule: fresh registration, retained replay
and refusal. The premises are `fed_silence`'s and equal logs at the start. -/
@[req "DUR-1"]
theorem hfed_silence {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List HStep) (A B : HFed), HCoupled r honest A B → FInv r honest A.L →
      FInv r honest B.L → ∀ y ∈ hwalk mk g cfg r honest peers tbls₀ tbls₁ A B sched, y.1 = y.2 := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons s rest ih =>
    intro A B hc hia hib y hy
    simp only [hwalk] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', hobs'⟩ :=
        hstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr hc hia hib s tbls₀ tbls₁
          ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hobs'
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-! ## The initial boundary -/

/-- Two handler states equal but for each node's `unarmedT`. -/
def HUEq (A A' : HFed) : Prop := UEq A.L A'.L ∧ A.logs = A'.logs

theorem node_u {A A' : HFed} (h : HUEq A A') (i : Nat) :
    ∃ u, (A.L.fed.worlds i).node = { (A'.L.fed.worlds i).node with unarmedT := u } := by
  obtain ⟨u, hu⟩ := world_u h.1 i
  exact ⟨u, by rw [hu]; rfl⟩

theorem caseOf_u {A A' : HFed} (h : HUEq A A') (i : Nat) (q : Request) :
    caseOf A i q = caseOf A' i q := by
  obtain ⟨u, hu⟩ := node_u h i
  simp only [caseOf, hit, hu, h.2]
  rfl

theorem freshResp_u {cfg : Config} {r : Rules} {A A' : HFed} (h : HUEq A A') (i : Nat) (env : Env)
    (q : Request) : freshResp cfg r A i env q = freshResp cfg r A' i env q := by
  obtain ⟨u, hu⟩ := h.1.2.2.2 i
  simp only [freshResp, hu]
  rfl

theorem happly_u {mk : Marker} {g : Guards} {cfg : Config} {r : Rules} {honest peers : List Nat}
    {A A' : HFed} (h : HUEq A A') (tbls : Nat → Enrolment) (s : HStep) :
    HUEq (happly g cfg r tbls A s) (happly g cfg r tbls A' s) ∧
    Federation.admits honest A.L.fed (s.fed tbls) = Federation.admits honest A'.L.fed (s.fed tbls) ∧
    inside r A.L (s.fed tbls) = inside r A'.L (s.fed tbls) ∧
    hobs mk g cfg r peers tbls A s = hobs mk g cfg r peers tbls A' s := by
  obtain ⟨u1, u2, u3, u4⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
    (peers := peers) h.1 (s.fed tbls)
  cases s with
  | step p => exact ⟨⟨u1, h.2⟩, u2, u3, u4⟩
  | claw i env q =>
    refine ⟨?_, u2, u3, ?_⟩
    · have hc := caseOf_u h i q
      cases hA : caseOf A i q with
      | replay resp =>
        have hA' : caseOf A' i q = .replay resp := hc ▸ hA
        simp only [happly, hA, hA']; exact h
      | refusal =>
        have hA' : caseOf A' i q = .refusal := hc ▸ hA
        simp only [happly, hA, hA']; exact ⟨u1, h.2⟩
      | fresh =>
        have hA' : caseOf A' i q = .fresh := hc ▸ hA
        simp only [happly, hA, hA']
        exact ⟨u1, by rw [h.2, freshResp_u h i env q]⟩
    · have hc := caseOf_u h i q
      cases hA : caseOf A i q with
      | replay resp =>
        have hA' : caseOf A' i q = .replay resp := hc ▸ hA
        obtain ⟨u, hu⟩ := node_u h i
        simp only [hobs, hA, hA', hu, h.1.1, h.1.2.1, h.1.2.2.1]
        rfl
      | refusal =>
        have hA' : caseOf A' i q = .refusal := hc ▸ hA
        simp only [hobs, hA, hA']; exact u4
      | fresh =>
        have hA' : caseOf A' i q = .fresh := hc ▸ hA
        simp only [hobs, hA, hA']; exact u4

theorem hwalk_u (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List HStep) (A B A' B' : HFed), HUEq A A' → HUEq B B' →
      hwalk mk g cfg r honest peers tbls₀ tbls₁ A B sched =
        hwalk mk g cfg r honest peers tbls₀ tbls₁ A' B' sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons s rest ih =>
    intro A B A' B' ha hb
    obtain ⟨ua, adA, inA, obA⟩ := happly_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) ha tbls₀ s
    obtain ⟨ub, _, inB, obB⟩ := happly_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) hb tbls₁ s
    simp only [hwalk, adA, inA, inB, obA, obB, ih _ _ _ _ ua ub]

/-- **`hfed_silence` at every initial state the federation admits with its sweep flags clear**, as
`FedSilence.fed_silence_fresh` states it, with any acceptance logs, one for both runs. -/
@[req "DUR-1"]
theorem hfed_silence_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : HFed) (hf : Federation.Fresh honest F.L.fed)
    (hs : ∀ i ∈ honest, (F.L.fed.worlds i).node.sweepActive = false) :
    ∀ (sched : List HStep), ∀ y ∈ hwalk mk g cfg r honest peers tbls₀ tbls₁ F F sched, y.1 = y.2 := by
  intro sched y hy
  let F' : HFed := { F with L := withU F.L (fun i => (F.L.fed.worlds i).node.T) }
  have hu : HUEq F F' :=
    ⟨⟨rfl, rfl, rfl, fun i => ⟨(F.L.fed.worlds i).node.unarmedT, rfl⟩⟩, rfl⟩
  rw [hwalk_u mk g cfg r honest peers tbls₀ tbls₁ sched F F F' F' hu hu] at hy
  have hinv : FInv r honest F'.L := by
    intro i hi
    obtain ⟨_, _, ha, hc, _, _⟩ := hf.2.2 i hi
    exact nodeInv_initial (F'.L.fed.worlds i).node _ hc ha (hs i hi) rfl
  exact hfed_silence hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ sched F' F' (hcoupled_refl r honest F')
    hinv hinv y hy

/-! ## An adaptive observer -/

/-- An adaptive observer whose next step may be a ClawbackRequest: a function of the observations
its own run emitted, and of nothing else. -/
structure HObserver where
  next : List FObs → Option HStep

/-- A scheduler that may also read the state; the adaptive theorems take only an `HObserver`. -/
abbrev HScheduler := HFed → List FObs → Option HStep

def HObserver.sched (σ : HObserver) : HScheduler := fun _ h => σ.next h

/-- `FedSilence.awalk` over handler steps: each run is scheduled from its own state and history. -/
def hawalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (c : HScheduler) :
    Nat → HFed → HFed → List FObs → List FObs → List (FObs × FObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match c A hA, c B hB with
    | some p, some q =>
      if Federation.admits honest A.L.fed (p.fed tbls₀) && inside r A.L (p.fed tbls₀) &&
          inside r B.L (q.fed tbls₁) then
        (hobs mk g cfg r peers tbls₀ A p, hobs mk g cfg r peers tbls₁ B q) ::
          hawalk mk g cfg r honest peers tbls₀ tbls₁ c n (happly g cfg r tbls₀ A p)
            (happly g cfg r tbls₁ B q) (hA ++ [hobs mk g cfg r peers tbls₀ A p])
            (hB ++ [hobs mk g cfg r peers tbls₁ B q])
      else []
    | _, _ => []

/-- The schedule an observer selects in one run, at most `n` steps. -/
def hplay (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (σ : HObserver) : Nat → HFed → List FObs → List HStep
  | 0, _, _ => []
  | n + 1, F, h =>
    match σ.next h with
    | none => []
    | some p => p :: hplay mk g cfg r peers tbls σ n (happly g cfg r tbls F p)
        (h ++ [hobs mk g cfg r peers tbls F p])

/-- **Equal histories, the same step**, as `FedSilence.awalk_walk`. -/
theorem hawalk_hwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : HObserver) :
    ∀ (n : Nat) (A B : HFed) (h : List FObs),
      (∀ y ∈ hwalk mk g cfg r honest peers tbls₀ tbls₁ A B (hplay mk g cfg r peers tbls₀ σ n A h),
        y.1 = y.2) →
      hawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
        hwalk mk g cfg r honest peers tbls₀ tbls₁ A B (hplay mk g cfg r peers tbls₀ σ n A h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B h heq
    cases hσ : σ.next h with
    | none => simp only [hawalk, HObserver.sched, hplay, hσ, hwalk]
    | some p =>
      simp only [hplay, hσ] at heq ⊢
      simp only [hawalk, HObserver.sched, hσ]
      simp only [hwalk] at heq ⊢
      split
      · rename_i hguard
        simp only [hguard, if_true, List.mem_cons, forall_eq_or_imp] at heq
        obtain ⟨hhead, htail⟩ := heq
        rw [← hhead, ih _ _ _ htail]
      · rfl

/-- **SILENCE through the handler against an adaptive observer.** `DUR-1`: "Every observable a node
emits MUST be identical between a normal-PIN and a duress-PIN request". Under `hfed_silence`'s
premises, each run scheduled by one `HObserver` reading only its own run's observations emits equal
`FedSilence.FObs` at every step, and the adaptive walk is `hwalk` over the schedule the observer
selects. No premise is taken on the observer. -/
@[req "DUR-1"]
theorem hfed_silence_adaptive {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (σ : HObserver) :
    ∀ (n : Nat) (A B : HFed) (h : List FObs), HCoupled r honest A B → FInv r honest A.L →
      FInv r honest B.L →
      hawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
          hwalk mk g cfg r honest peers tbls₀ tbls₁ A B (hplay mk g cfg r peers tbls₀ σ n A h) ∧
        ∀ y ∈ hawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h, y.1 = y.2 := by
  intro n A B h hc hia hib
  have hw := hfed_silence (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁
    (hplay mk g cfg r peers tbls₀ σ n A h) A B hc hia hib
  have he := hawalk_hwalk mk g cfg r honest peers tbls₀ tbls₁ σ n A B h hw
  exact ⟨he, he ▸ hw⟩

/-- **The headline: SILENCE through the handler, adaptive, from the initial boundary.** Every
`Federation.Fresh` state with the honest nodes' sweep flags clear, any acceptance logs one for both
runs, and an observer that has seen nothing: the two runs emit equal observations at every step of
the adaptive walk, whose schedule may hold fresh claw-back registrations, retained replays and
refusals, and the walk stops where `FedSilence.walk`'s guard stops it. -/
@[req "DUR-1"]
theorem hfed_silence_adaptive_fresh {mk : Marker} (hg : mk = .committed) {g : Guards}
    {cfg : Config} {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : HFed) (hf : Federation.Fresh honest F.L.fed)
    (hs : ∀ i ∈ honest, (F.L.fed.worlds i).node.sweepActive = false) (σ : HObserver) :
    ∀ n : Nat,
      hawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [] =
          hwalk mk g cfg r honest peers tbls₀ tbls₁ F F (hplay mk g cfg r peers tbls₀ σ n F []) ∧
        ∀ y ∈ hawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [], y.1 = y.2 := by
  intro n
  have hw := hfed_silence_fresh (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ F
    hf hs (hplay mk g cfg r peers tbls₀ σ n F [])
  have he := hawalk_hwalk mk g cfg r honest peers tbls₀ tbls₁ σ n F F [] hw
  exact ⟨he, he ▸ hw⟩

/-! ## The earlier domain: restriction -/

/-- **The walk without requests is `FedSilence.walk`.** On a schedule of `FedSilence.PStep`s, with any
logs, the handler walk is the walk, step for step; so every conclusion of `FedSilence.fed_silence`
and its corollaries is unchanged on its domain. -/
@[req "DUR-1"]
theorem hwalk_steps (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed) (la lb : Nat → List Entry),
      hwalk mk g cfg r honest peers tbls₀ tbls₁ ⟨A, la⟩ ⟨B, lb⟩ (sched.map .step) =
        walk mk g cfg r honest peers tbls₀ tbls₁ A B sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons p rest ih =>
    intro A B la lb
    simp only [List.map_cons, hwalk, walk, HStep.fed, hobs, happly]
    split <;> simp only [ih]

/-- A scheduler over `FedSilence.PStep`s, as a handler scheduler. -/
def lift (c : Scheduler) : HScheduler := fun F h => (c F.L h).map .step

/-- **The adaptive walk without requests is `FedSilence.awalk`.** -/
@[req "DUR-1"]
theorem hawalk_lift (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (c : Scheduler) :
    ∀ (n : Nat) (A B : LFed) (la lb : Nat → List Entry) (hA hB : List FObs),
      hawalk mk g cfg r honest peers tbls₀ tbls₁ (lift c) n ⟨A, la⟩ ⟨B, lb⟩ hA hB =
        awalk mk g cfg r honest peers tbls₀ tbls₁ c n A B hA hB := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B la lb hA hB
    simp only [hawalk, awalk, lift]
    cases c A hA with
    | none => rfl
    | some p =>
      cases c B hB with
      | none => rfl
      | some q =>
        simp only [Option.map_some, HStep.fed, hobs, happly]
        split <;> simp only [ih]

end BtcPolicy.ClawHandler
