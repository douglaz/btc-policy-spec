import BtcPolicy.Federation
import BtcPolicy.Silence
import BtcPolicy.Envelope
/-! SILENCE over a composed federation, under one fixed exogenous schedule (`DUR-1`, with the
scope `SEC-10` holds). `BtcPolicy.Silence` proves the two-run relation for one node, whose peers'
relays are inputs held equal across the two runs. Here honest nodes run the composition of
`BtcPolicy.Federation`, each with its Hot ledger (`Ledger.sysStep`), and the inventories a node
receives from are assumed equal only at the initial states and stay equal by the run. From a
`Federation.Fresh` start, where both are empty (`FedSilence.fed_silence_fresh`), a relay or a partial
a node receives is one an honest node emitted or queued in the same run, or one a schedule step
injected or forged in both runs.

**The experiment is unchanged.** Both runs take one schedule of `FedSilence.PStep`: the same
requests and PIN bytes, the same relays emitted, deliveries, key copies and forged partials, and the
same samples, in the same order. Only the enrolment tables differ, one table per node, and each node
classifies the PIN its own input presented by its own table. Two different public PINs are a
different experiment and not this one. In `FedSilence.fed_silence` the schedule is fixed in
advance: no step is chosen by looking at what either run emitted.

**An adaptive observer.** `FedSilence.fed_silence_adaptive` lets each run's next step be chosen by
one `FedSilence.Observer` from the observations that run has emitted so far. The observer's type is
a function of that history alone, so it cannot read a world, a ledger, an enrolment table or the
arm bit. In `FedSilence.awalk` each run's observer reads its own run's history, and the two pick the
same step because the histories are equal (`FedSilence.awalk_walk`); the adaptive walk is then
`FedSilence.walk` over the schedule the observer selects, with the same stop. The observer chooses
public inputs only: a request's PIN bytes are part of the step it picks, the same in both runs.

**The step.** `FedSilence.lapply` is `Federation.apply` with each kernel event taken through
`Ledger.sysStep`, so a hot spend the budget check refuses is staged and registers nothing, as on one
node. `FedSilence.lrun_execution`: forgetting the ledgers of a legal run leaves a
`Federation.Execution` whose process steps carry the kernel events `Ledger.sysStep` took
(`FedSilence.kernelEvent`), so every result stated over that composition applies to these runs.

**What is compared.** `FedSilence.FObs`: the acting node and its `Silence.Obs`, if a node acts; the
messages the step addresses, one `FedSilence.Frame` per destination, and the message it delivers
with its destination; and the relay inventory, the partial inventory and the extracted set as the
step leaves them. What `Silence.Obs` omits is omitted here too; the docstring of `BtcPolicy.Silence`
names it. A step addresses each partial it queues and each relay it emits to every peer on one
manifest list but itself, peer by peer (`FedSilence.sent`), so a peer outside the honest list, which
runs nothing here, is a destination too. The inventories carry no destination: a delivery hands a
relay or a partial to any honest node, and which one, and when, is a step both runs share.

**Shape, size, bytes.** A frame is compared by sender, destination and body, and a body by what this
model carries of it: a relay by its Carrier's identity, a partial by its row. That is shape
equality. `FedSilence.frame_preimage_length` adds size: the frame's `NCH-11` envelope preimage, built
with `WIR-18`'s moves (`BtcPolicy.Envelope`), is a fixed width plus the payload's length, whatever
its type, ids, nonce and timestamp, so equal frames have preimages of one length exactly when their
payloads do. No result here gives equal bytes: the payload's JSON and base64, and the JSON envelope
on the wire with its padding, have no encoder; the nonce is a fresh random draw per attempt and a
partial's payload carries an ECDSA signature, and neither draw has a model or a coupling here
(`Exhibits.FedSilence.equal_frames_unequal_bytes`). Transport attempts, retries and their timing are
not modelled.

**The horizon.** `FedSilence.walk` stops at the first step of the schedule that is not admitted, or
whose acting node, in either run, is outside its own horizon (`Silence.preHorizon`) at that step's
own sample or receives a request shape `Silence.wfEvent` refuses. That is the first execution event
at which a participating run crosses a local horizon. No minimum over the nodes' clock samples is
taken: samples are per node and unordered across nodes, as in `Federation.Execution`. Once the walk
stops nothing reopens it, a backward sample included, because the walk quantifies over a prefix. A
step no node takes (a relay emitted or injected, a key copied, a partial forged) reads no clock and
never ends the walk. A claw-back's post-check registration (`Kernel.Event.clawback`) is in the
alphabet and inside the boundary as the entry target stands (`Silence.wfEvent_clawback_escapeRole`):
it ends the walk only at admission or at the horizon, like any node step. The walks that stopped at
every claw-back are `FedSilence.walkPre` and `FedSilence.awalkPre`, and `FedSilence.fed_silence_pre`
and `FedSilence.fed_silence_adaptive_pre` keep the relation on them. The handler's retained-replay
log (`ClawbackIngress.lookup`, `ClawbackIngress.retain`) and the relay of a claw-back request are not
modelled here.

**Threat profile.** It is not the safety theorems'. `Federation.Step.extract` and
`Federation.Step.forge` are in the alphabet because they are inputs the schedule fixes and both runs
take: a copied signing key yields partials and reads no PIN, enrolment table or digest, and a forged
partial is the same row in both runs. That is not tolerance of a compromised node. `SEC-10` says "a
compromised node sees the PIN in plaintext", and no step here lets the adversary read a node's PIN,
table or digest. A node outside the honest list has no world and no table here. Applying the relation
as SILENCE needs every node that receives either PIN on the honest list, and `SEC-10`'s
"release-history premise" and "digest premise", which these proofs do not establish; so is the
absence of any record of either PIN from any source (`DUR-1`).

**Premises.** `FedSilence.fed_silence` takes the six rule and marker premises `Silence.silence` takes,
two federation states related by `FedSilence.FCoupled` (equal inventories, every honest node coupled
by `Silence.Coupled`), and `Silence.NodeInv` at every honest node of each, at its own time ratchet.
`FedSilence.fed_silence_fresh` discharges the last two at every state `Federation.Fresh` admits with
the honest nodes' sweep flags clear, with any ledgers and any extracted set.
`FedSilence.fed_silence_adaptive` and `FedSilence.fed_silence_adaptive_fresh` take the same
premises respectively, with the threat profile and horizon above, and none on the observer. Each
takes the peer list as an argument, the same in both runs, and no premise on it. -/

namespace BtcPolicy.FedSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence

/-! ## A federation whose nodes carry their Hot ledgers -/

/-- A federation state with each node's Hot ledger beside its world. -/
structure LFed where
  fed : Federation.Fed
  leds : Nat → Ledger

/-- Node `i` as `Ledger.sysStep` takes it. -/
def LFed.sys (F : LFed) (i : Nat) : Sys := { world := F.fed.worlds i, led := F.leds i }

/-- Node `i` takes one event through `Ledger.sysStep`; no other node and no inventory moves. -/
def LFed.advance (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env)
    (e : Event) : LFed :=
  { fed := { F.fed with worlds := fun j =>
      if j = i then (sysStep g cfg r env (F.sys i) e).1.world else F.fed.worlds j },
    leds := fun j => if j = i then (sysStep g cfg r env (F.sys i) e).1.led else F.leds j }

/-- `Federation.apply` with each kernel event taken through `Ledger.sysStep`. -/
def lapply (g : Guards) (cfg : Config) (r : Rules) (F : LFed) : Federation.Step → LFed
  | .process i env e =>
    { F.advance g cfg r i env e with
      fed := { (F.advance g cfg r i env e).fed with
        parts := F.fed.parts ++
          Federation.fanout (F.fed.worlds i) (sysStep g cfg r env (F.sys i) e).2 } }
  | .deliver i env m => F.advance g cfg r i env (.receipt m.cid m.sender)
  | .deliverPartial i env x =>
    F.advance g cfg r i env (.receivePartial x.msg x.input x.signer x.cid)
  | .unstaged i cid => { F with fed := Federation.apply r F.fed (.unstaged i cid) }
  | .emit i cid => { F with fed := Federation.apply r F.fed (.emit i cid) }
  | .inject m => { F with fed := Federation.apply r F.fed (.inject m) }
  | .extract j => { F with fed := Federation.apply r F.fed (.extract j) }
  | .forge x => { F with fed := Federation.apply r F.fed (.forge x) }

theorem sys_advance_self (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env)
    (e : Event) : (F.advance g cfg r i env e).sys i = (sysStep g cfg r env (F.sys i) e).1 := by
  simp [LFed.advance, LFed.sys]

theorem sys_advance_other (g : Guards) (cfg : Config) (r : Rules) (F : LFed) {i j : Nat}
    (env : Env) (e : Event) (h : j ≠ i) : (F.advance g cfg r i env e).sys j = F.sys j := by
  simp [LFed.advance, LFed.sys, h]

/-! ## The bridge: forgetting the ledgers leaves a `Federation.Execution` -/

/-- The kernel event `Ledger.sysStep` takes for an event: a hot spend the budget check refuses is
`Ledger.budgetRefusal`'s staged refusal, and every other event is itself. -/
def kernelEvent (g : Guards) (cfg : Config) (env : Env) (l : Ledger) : Event → Event
  | .accept cid d E sp es =>
    if refusedByBudget cfg (checked g.release env cfg.window l (.accept cid d E sp es))
        (.accept cid d E sp es) then
      .refuse cid d E (some (sp.id, es.id)) .HOT_VELOCITY_EXCEEDED
    else .accept cid d E sp es
  | .receipt cid s => .receipt cid s
  | .refuse cid d E pair code => .refuse cid d E pair code
  | .firePass => .firePass
  | .packageAccepted c => .packageAccepted c
  | .send c => .send c
  | .settle tx => .settle tx
  | .prune => .prune
  | .tick => .tick
  | .panic => .panic
  | .adversaryExposes m i s c => .adversaryExposes m i s c
  | .receivePartial m i s c => .receivePartial m i s c
  | .clawback c => .clawback c

/-- The world and the effects of `Ledger.sysStep` are `Kernel.step`'s on `kernelEvent`. -/
theorem sysStep_kernel (g : Guards) (cfg : Config) (r : Rules) (env : Env) (sys : Sys)
    (e : Event) :
    (sysStep g cfg r env sys e).1.world = (step r env sys.world (kernelEvent g cfg env sys.led e)).1 ∧
      (sysStep g cfg r env sys e).2 = (step r env sys.world (kernelEvent g cfg env sys.led e)).2 := by
  cases e with
  | accept cid d E sp es =>
    simp only [sysStep, kernelEvent]
    split <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem ownEvent_kernelEvent (g : Guards) (cfg : Config) (env : Env) (l : Ledger) (e : Event) :
    Federation.ownEvent (kernelEvent g cfg env l e) = Federation.ownEvent e := by
  cases e with
  | accept cid d E sp es => simp only [kernelEvent]; split <;> rfl
  | _ => rfl

/-- The `Federation.Step` a ledgered step is, once the ledger is forgotten. -/
def kernelStep (g : Guards) (cfg : Config) (F : LFed) : Federation.Step → Federation.Step
  | .process i env e => .process i env (kernelEvent g cfg env (F.leds i) e)
  | s => s

theorem advance_fed (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env)
    (e : Event) (he : kernelEvent g cfg env (F.leds i) e = e) :
    (F.advance g cfg r i env e).fed = Federation.advance r F.fed i env e := by
  have h := (sysStep_kernel g cfg r env (F.sys i) e).1
  simp only [LFed.sys] at h
  simp only [LFed.advance, Federation.advance, LFed.sys, h, he]

/-- Forgetting the ledgers commutes with the step: a ledgered step moves the federation as
`Federation.apply` moves it on `kernelStep`. -/
theorem lapply_fed (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (s : Federation.Step) :
    (lapply g cfg r F s).fed = Federation.apply r F.fed (kernelStep g cfg F s) := by
  have h := fun i env e => sysStep_kernel g cfg r env (F.sys i) e
  cases s with
  | process i env e =>
    obtain ⟨h1, h2⟩ := h i env e
    simp only [LFed.sys] at h1 h2
    simp only [lapply, kernelStep, Federation.apply, LFed.advance, Federation.advance, LFed.sys,
      h1, h2]
  | deliver i env m => exact advance_fed g cfg r F i env _ rfl
  | deliverPartial i env x => exact advance_fed g cfg r F i env _ rfl
  | _ => rfl

theorem admits_kernelStep (honest : List Nat) (g : Guards) (cfg : Config) (F : LFed)
    (s : Federation.Step) :
    Federation.admits honest F.fed (kernelStep g cfg F s) = Federation.admits honest F.fed s := by
  cases s with
  | process i env e => simp only [kernelStep, Federation.admits, ownEvent_kernelEvent]
  | _ => rfl

/-- A schedule run through the ledgered step. -/
def lrun (g : Guards) (cfg : Config) (r : Rules) : LFed → List Federation.Step → LFed
  | F, [] => F
  | F, s :: ss => lrun g cfg r (lapply g cfg r F s) ss

/-- Every step of the schedule admitted where it is taken. -/
def llegal (g : Guards) (cfg : Config) (r : Rules) (honest : List Nat) :
    LFed → List Federation.Step → Bool
  | _, [] => true
  | F, s :: ss => Federation.admits honest F.fed s && llegal g cfg r honest (lapply g cfg r F s) ss

/-- The composed trace the forgotten run leaves, newest first. -/
def ltrace (g : Guards) (cfg : Config) (r : Rules) :
    Federation.Trace → LFed → List Federation.Step → Federation.Trace
  | t, _, [] => t
  | t, F, s :: ss => ltrace g cfg r ((F.fed, kernelStep g cfg F s) :: t) (lapply g cfg r F s) ss

/-- **The ledgered run is a federation execution.** Forgetting the Hot ledgers of a legal
ledgered run leaves a `Federation.Execution` over the same honest list, whose process steps carry
the kernel events `Ledger.sysStep` took. Every result stated over `Federation.Execution` applies to
it. -/
theorem lrun_execution {g : Guards} {cfg : Config} {r : Rules} {honest : List Nat}
    {t : Federation.Trace} {F : LFed} (hx : Federation.Execution r honest t F.fed) :
    ∀ ss, llegal g cfg r honest F ss = true →
      Federation.Execution r honest (ltrace g cfg r t F ss) (lrun g cfg r F ss).fed := by
  intro ss
  induction ss generalizing t F with
  | nil => intro _; exact hx
  | cons s ss ih =>
    intro hl
    simp only [llegal, Bool.and_eq_true] at hl
    have ha : Federation.admits honest F.fed (kernelStep g cfg F s) = true := by
      rw [admits_kernelStep]; exact hl.1
    have hx' := Federation.Execution.next (kernelStep g cfg F s) ha hx
    rw [← lapply_fed] at hx'
    exact ih hx' hl.2

/-! ## One exogenous schedule, two enrolment families -/

/-- One step of the schedule, as the environment presents it. `input` is a kernel input at a
node, which carries the PIN it presented if it is a request or a staged refusal; `net` is any
federation step, taken as it is in both runs. -/
inductive PStep
  | input (i : Nat) (env : Env) (x : Silence.Input)
  | net (s : Federation.Step)
  deriving DecidableEq, Repr

/-- The federation step one enrolment family makes of a schedule step: node `i`'s own table
classifies the PIN its input presented. -/
def PStep.step (tbls : Nat → Enrolment) : PStep → Federation.Step
  | .input i env x => .process i env (x.event (tbls i))
  | .net s => s

/-- The acting node is inside its own horizon at the step's own sample, and the request shape is
the one `Silence.wfEvent` admits. A step no node takes is inside. -/
def inside (r : Rules) (F : LFed) (s : Federation.Step) : Bool :=
  match Federation.actor s with
  | some (i, env, e) => preHorizon r env (F.fed.worlds i).node && wfEvent r (F.fed.worlds i).node e
  | none => true

/-- `inside` with the request-shape boundary as it stood before claw-back ingress was admitted
(`Silence.wfEventPre`). -/
def insidePre (r : Rules) (F : LFed) (s : Federation.Step) : Bool :=
  match Federation.actor s with
  | some (i, env, e) => preHorizon r env (F.fed.worlds i).node && wfEventPre (F.fed.worlds i).node e
  | none => true

theorem insidePre_le (r : Rules) (F : LFed) (s : Federation.Step) (h : insidePre r F s = true) :
    inside r F s = true := by
  unfold insidePre at h; unfold inside
  cases hs : Federation.actor s with
  | none => rfl
  | some x =>
    obtain ⟨i, env, e⟩ := x
    rw [hs] at h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, wfEventPre_le r _ _ h.2⟩

/-! ## Per-destination messages -/

/-- A message's body, by what this model carries of it: `NCH-20`'s two types, a `request` by the
identity of the Carrier it relays and a `partial` by its row (`Body.part`). -/
inductive Body
  | request (cid : Nat)
  | part (x : Exp)
  deriving DecidableEq, Repr

/-- One message on one channel: its sender, the node it is addressed to, and its body. -/
structure Frame where
  src : Nat
  dst : Nat
  body : Body
  deriving DecidableEq, Repr

/-- Node `i`'s bodies addressed to every peer on the list but itself, peer by peer, and to each
peer in the order given: `NCH-9`'s "one sending task per peer, with messages to one peer sent in
order". -/
@[req "NCH-9"]
def addressed (peers : List Nat) (i : Nat) (bodies : List Body) : List Frame :=
  (peers.filter (· != i)).flatMap fun j => bodies.map fun b => ⟨i, j, b⟩

/-- The messages a step addresses. A process step addresses every partial it queues
(`Federation.fanout`) to every peer, as `NCH-23` has it: "one message per released rung per signed
input to every peer". A relay, emitted from a staged Carrier or at gate 10, goes to every peer
(`SPN-35`, `SPN-9`). An injected relay and a forged partial are the adversary's, addressed as it
chooses, and a delivery addresses nothing. `peers` is the manifest's node list, one list for both
runs. -/
@[req "NCH-23"]
def sent (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat) (F : LFed) :
    Federation.Step → List Frame
  | .process i env e =>
    addressed peers i
      ((Federation.fanout (F.fed.worlds i) (sysStep g cfg r env (F.sys i) e).2).map .part)
  | .unstaged i cid | .emit i cid => addressed peers i [.request cid]
  | _ => []

/-- The message a delivery hands to its node: a relay under the sender it names, or a partial under
its signer, which `NCH-24` checks equals the sender. -/
def received : Federation.Step → Option Frame
  | .deliver i _ m => some ⟨m.sender, i, .request m.cid⟩
  | .deliverPartial i _ x => some ⟨x.signer, i, .part x⟩
  | _ => none

/-- One step's observation: the acting node and its `Silence.Obs`, if a node acts; the messages the
step addresses, one per destination, and the message it delivers, with its destination; and the
three inventories as the step leaves them. -/
structure FObs where
  node : Option (Nat × Obs)
  sent : List Frame
  recv : Option Frame
  net : List Federation.Relay
  parts : List Exp
  extracted : List Nat
  deriving DecidableEq, Repr

def localObs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (F : LFed)
    (s : Federation.Step) : Option (Nat × Obs) :=
  match Federation.actor s with
  | some (i, env, e) =>
    some (i, obsOf mk cfg r env (F.sys i) (sysStep g cfg r env (F.sys i) e).1
      (sysStep g cfg r env (F.sys i) e).2 e)
  | none => none

def fobs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat) (F : LFed)
    (s : Federation.Step) : FObs :=
  { node := localObs mk g cfg r F s, sent := sent g cfg r peers F s, recv := received s,
    net := (lapply g cfg r F s).fed.net,
    parts := (lapply g cfg r F s).fed.parts, extracted := (lapply g cfg r F s).fed.extracted }

/-- The two runs walked together over one schedule. The walk ends at the first step that is not
admitted, or whose acting node, in either run, is outside its horizon at that step's sample or
receives a request shape `Silence.wfEvent` refuses. -/
def walk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : LFed → LFed → List PStep → List (FObs × FObs)
  | _, _, [] => []
  | A, B, p :: rest =>
    if Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
        inside r B (p.step tbls₁) then
      (fobs mk g cfg r peers A (p.step tbls₀), fobs mk g cfg r peers B (p.step tbls₁)) ::
        walk mk g cfg r honest peers tbls₀ tbls₁ (lapply g cfg r A (p.step tbls₀))
          (lapply g cfg r B (p.step tbls₁)) rest
    else []

/-! ## The coupling, node by node -/

/-- Two federation states with equal inventories and every honest node coupled by
`Silence.Coupled`. -/
structure FCoupled (r : Rules) (honest : List Nat) (A B : LFed) : Prop where
  net : A.fed.net = B.fed.net
  parts : A.fed.parts = B.fed.parts
  extracted : A.fed.extracted = B.fed.extracted
  node : ∀ i ∈ honest, Coupled r (A.sys i) (B.sys i)

/-- `Silence.NodeInv` at every honest node, at its own time ratchet. -/
def FInv (r : Rules) (honest : List Nat) (A : LFed) : Prop :=
  ∀ i ∈ honest, NodeInv r (A.fed.worlds i).node (A.fed.worlds i).node.ratchet

theorem fcoupled_refl (r : Rules) (honest : List Nat) (A : LFed) : FCoupled r honest A A :=
  ⟨rfl, rfl, rfl, fun _ _ => coupled_refl _⟩

theorem consumed_pub {r : Rules} {x y : Node} (h : pubNode r x = pubNode r y) (cid : Nat) :
    Federation.consumed x cid = Federation.consumed y cid := by
  simp only [Federation.consumed, carriers_any_pub h (fun k => k.cid == cid) (fun _ => rfl),
    tombstones_any_pub h (fun k => k.cid == cid) (fun _ => rfl)]

theorem ownEvent_pin (x : Silence.Input) (tbl₀ tbl₁ : Enrolment) :
    Federation.ownEvent (x.event tbl₀) = Federation.ownEvent (x.event tbl₁) := by
  cases x <;> rfl

/-- The two runs admit the same steps. -/
theorem admits_pub {r : Rules} {honest : List Nat} {A B : LFed} (hc : FCoupled r honest A B)
    (p : PStep) (tbls₀ tbls₁ : Nat → Enrolment) :
    Federation.admits honest A.fed (p.step tbls₀) = Federation.admits honest B.fed (p.step tbls₁) := by
  cases p with
  | input i env x => simp only [PStep.step, Federation.admits, ownEvent_pin x (tbls₀ i) (tbls₁ i)]
  | net s =>
    cases s with
    | unstaged i cid =>
      by_cases hi : i ∈ honest
      · have hn : pubNode r (A.fed.worlds i).node = pubNode r (B.fed.worlds i).node :=
          (hc.node i hi).node
        simp only [PStep.step, Federation.admits, consumed_pub hn cid]
      · have hf : honest.contains i = false := by simpa using hi
        simp only [PStep.step, Federation.admits, hf, Bool.false_and]
    | emit i cid =>
      by_cases hi : i ∈ honest
      · have hn : pubNode r (A.fed.worlds i).node = pubNode r (B.fed.worlds i).node :=
          (hc.node i hi).node
        simp only [PStep.step, Federation.admits, consumed_pub hn cid]
      · have hf : honest.contains i = false := by simpa using hi
        simp only [PStep.step, Federation.admits, hf, Bool.false_and]
    | deliver i env m => simp only [PStep.step, Federation.admits, hc.net]
    | deliverPartial i env x => simp only [PStep.step, Federation.admits, hc.parts]
    | forge x => simp only [PStep.step, Federation.admits, hc.extracted]
    | _ => rfl

/-- The partials a step sends are the same in both runs: `Federation.fanout` reads the node's id
and, for the other inputs, a candidate's id and transaction, which the projection keeps. -/
theorem others_pub {r : Rules} {wa wb : World} (h : pubNode r wa.node = pubNode r wb.node)
    (x : Exp) : Federation.others wa x = Federation.others wb x := by
  let P : Cand → Bool := fun c => c.id == x.cid && sighash c.tx 0 == x.msg
  have hf : (wa.node.cands.find? P).map (pubCand r (selIds wa.node)) =
      (wb.node.cands.find? P).map (pubCand r (selIds wb.node)) := by
    rw [find?_comm (pubCand r (selIds wa.node)) P wa.node.cands P
          (fun c _ => by simp [P, pubCand_id, pubCand_tx]),
        find?_comm (pubCand r (selIds wb.node)) P wb.node.cands P
          (fun c _ => by simp [P, pubCand_id, pubCand_tx]), pub_cands h]
  unfold Federation.others
  change (match wa.node.cands.find? P with
      | some c => ((List.range c.tx.inputs.length).drop 1).map fun k =>
          { x with msg := sighash c.tx k, input := k }
      | none => []) =
    (match wb.node.cands.find? P with
      | some c => ((List.range c.tx.inputs.length).drop 1).map fun k =>
          { x with msg := sighash c.tx k, input := k }
      | none => [])
  cases ha : wa.node.cands.find? P <;> cases hb : wb.node.cands.find? P <;>
    rw [ha, hb] at hf <;> simp only [Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hf
  all_goals first
    | rfl
    | (have ht := congrArg Cand.tx hf
       simp only [pubCand_tx] at ht
       dsimp only
       rw [ht])

theorem fanout_pub {r : Rules} {wa wb : World} (h : pubNode r wa.node = pubNode r wb.node)
    (effs : List Effect) : Federation.fanout wa effs = Federation.fanout wb effs := by
  have ho : Federation.outbox wa effs = Federation.outbox wb effs := by
    simp only [Federation.outbox, pub_id h]
  simp only [Federation.fanout, ho, others_pub h]

/-- One node's step, in both runs: the coupling of every honest node, the effects, the invariant
in each run, and the node's observation. -/
theorem advance_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest : List Nat}
    {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A) (hib : FInv r honest B)
    {i : Nat} (hi : i ∈ honest) (env : Env) (x : Silence.Input) (tbl₀ tbl₁ : Enrolment)
    (hpa : preHorizon r env (A.fed.worlds i).node = true)
    (hpb : preHorizon r env (B.fed.worlds i).node = true)
    (hwf : wfEvent r (A.fed.worlds i).node (x.event tbl₀) = true) :
    (∀ j ∈ honest, Coupled r ((A.advance g cfg r i env (x.event tbl₀)).sys j)
      ((B.advance g cfg r i env (x.event tbl₁)).sys j)) ∧
    (sysStep g cfg r env (A.sys i) (x.event tbl₀)).2 = (sysStep g cfg r env (B.sys i) (x.event tbl₁)).2 ∧
    FInv r honest (A.advance g cfg r i env (x.event tbl₀)) ∧
    FInv r honest (B.advance g cfg r i env (x.event tbl₁)) ∧
    obsOf mk cfg r env (A.sys i) (sysStep g cfg r env (A.sys i) (x.event tbl₀)).1
        (sysStep g cfg r env (A.sys i) (x.event tbl₀)).2 (x.event tbl₀) =
      obsOf mk cfg r env (B.sys i) (sysStep g cfg r env (B.sys i) (x.event tbl₁)).1
        (sysStep g cfg r env (B.sys i) (x.event tbl₁)).2 (x.event tbl₁) := by
  have hci := hc.node i hi
  have hiai := hia i hi
  have hibi := hib i hi
  obtain ⟨hc', heff⟩ := sysStep_coupled (g := g) (cfg := cfg) ht hcl hdr hci hiai hibi hpa hpb x tbl₀ tbl₁
  have hwfb : wfEvent r (B.fed.worlds i).node (x.event tbl₁) = true := by
    have hw' := wfEvent_pub hci.node x tbl₀ tbl₁
    simp only [LFed.sys] at hw'
    rw [← hw']; exact hwf
  have inv (F : LFed) (hF : FInv r honest F) (tbl : Enrolment)
      (hp : preHorizon r env (F.fed.worlds i).node = true)
      (hw : wfEvent r (F.fed.worlds i).node (x.event tbl) = true) :
      FInv r honest (F.advance g cfg r i env (x.event tbl)) := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      have := inv_sysStep (g := g) (cfg := cfg) (env := env) (sys := F.sys j) ht hd hr (hF j hj) (x.event tbl) hw
        (fun ha => (Effective.deadlineReached_latest (preHorizon_below hdr hp ha)).2)
      simpa [LFed.advance, LFed.sys] using this
    · have := hF j hj
      simpa [LFed.advance, hji] using this
  refine ⟨?_, heff, inv A hia tbl₀ hpa hwf, inv B hib tbl₁ hpb hwfb,
    obsOf_eq hg ht hcl hdr hci hiai hibi hpa hpb x tbl₀ tbl₁⟩
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [sys_advance_self, sys_advance_self]
    exact hc'
  · rw [sys_advance_other _ _ _ _ _ _ hji, sys_advance_other _ _ _ _ _ _ hji]
    exact hc.node j hj

/-- The acting node of an admitted step is on the honest list. -/
theorem actor_honest {honest : List Nat} {f : Federation.Fed} {s : Federation.Step} {i : Nat}
    {env : Env} {e : Event} (ha : Federation.admits honest f s = true)
    (hs : Federation.actor s = some (i, env, e)) : i ∈ honest := by
  cases s <;> simp only [Federation.actor, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hs <;>
    obtain ⟨rfl, rfl, rfl⟩ := hs <;>
    simp only [Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at ha <;>
    first | exact ha.1 | exact ha

/-- A process step at an honest node, in both runs. -/
theorem process_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers : List Nat}
    {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A) (hib : FInv r honest B)
    {i : Nat} (hi : i ∈ honest) (env : Env) (x : Silence.Input) (tbl₀ tbl₁ : Enrolment)
    (hpa : preHorizon r env (A.fed.worlds i).node = true)
    (hpb : preHorizon r env (B.fed.worlds i).node = true)
    (hwf : wfEvent r (A.fed.worlds i).node (x.event tbl₀) = true) :
    FCoupled r honest (lapply g cfg r A (.process i env (x.event tbl₀)))
      (lapply g cfg r B (.process i env (x.event tbl₁))) ∧
    FInv r honest (lapply g cfg r A (.process i env (x.event tbl₀))) ∧
    FInv r honest (lapply g cfg r B (.process i env (x.event tbl₁))) ∧
    fobs mk g cfg r peers A (.process i env (x.event tbl₀)) = fobs mk g cfg r peers B (.process i env (x.event tbl₁)) := by
  obtain ⟨hn, heff, hia', hib', hobs⟩ :=
    advance_pub (g := g) (cfg := cfg) hg ht hd hr hcl hdr hc hia hib hi env x tbl₀ tbl₁ hpa hpb hwf
  have hfan : Federation.fanout (A.fed.worlds i) (sysStep g cfg r env (A.sys i) (x.event tbl₀)).2 =
      Federation.fanout (B.fed.worlds i) (sysStep g cfg r env (B.sys i) (x.event tbl₁)).2 := by
    have hni : pubNode r (A.fed.worlds i).node = pubNode r (B.fed.worlds i).node :=
      (hc.node i hi).node
    rw [heff, fanout_pub hni]
  have hparts : A.fed.parts ++ Federation.fanout (A.fed.worlds i) (sysStep g cfg r env (A.sys i) (x.event tbl₀)).2 =
      B.fed.parts ++ Federation.fanout (B.fed.worlds i) (sysStep g cfg r env (B.sys i) (x.event tbl₁)).2 := by
    rw [hc.parts, hfan]
  refine ⟨⟨hc.net, hparts, hc.extracted, hn⟩, hia', hib', ?_⟩
  simp only [fobs, localObs, sent, received, Federation.actor, lapply, LFed.advance, hobs, hfan,
    hc.net, hc.parts, hc.extracted]

/-- A delivery at an honest node, a relay's or a partial's, in both runs. -/
theorem advance_fcoupled {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {honest : List Nat}
    {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A) (hib : FInv r honest B)
    {i : Nat} (hi : i ∈ honest) (env : Env) (e : Event)
    (hpa : preHorizon r env (A.fed.worlds i).node = true)
    (hpb : preHorizon r env (B.fed.worlds i).node = true)
    (hwf : wfEvent r (A.fed.worlds i).node e = true) :
    FCoupled r honest (A.advance g cfg r i env e) (B.advance g cfg r i env e) ∧
    FInv r honest (A.advance g cfg r i env e) ∧ FInv r honest (B.advance g cfg r i env e) ∧
    obsOf mk cfg r env (A.sys i) (sysStep g cfg r env (A.sys i) e).1 (sysStep g cfg r env (A.sys i) e).2 e =
      obsOf mk cfg r env (B.sys i) (sysStep g cfg r env (B.sys i) e).1
        (sysStep g cfg r env (B.sys i) e).2 e := by
  obtain ⟨hn, _, hia', hib', hobs⟩ :=
    advance_pub (g := g) (cfg := cfg) hg ht hd hr hcl hdr hc hia hib hi env (.pinless e)
      (fun _ => false) (fun _ => false) hpa hpb hwf
  exact ⟨⟨hc.net, hc.parts, hc.extracted, hn⟩, hia', hib', hobs⟩

/-- One schedule step, in both runs: the coupling, the invariant in each run and the observation. -/
theorem pstep_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers : List Nat}
    {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A) (hib : FInv r honest B)
    (p : PStep) (tbls₀ tbls₁ : Nat → Enrolment)
    (ha : Federation.admits honest A.fed (p.step tbls₀) = true)
    (hpa : inside r A (p.step tbls₀) = true) (hpb : inside r B (p.step tbls₁) = true) :
    FCoupled r honest (lapply g cfg r A (p.step tbls₀)) (lapply g cfg r B (p.step tbls₁)) ∧
    FInv r honest (lapply g cfg r A (p.step tbls₀)) ∧
    FInv r honest (lapply g cfg r B (p.step tbls₁)) ∧
    fobs mk g cfg r peers A (p.step tbls₀) = fobs mk g cfg r peers B (p.step tbls₁) := by
  have frame : ∀ s : Federation.Step, Federation.actor s = none →
      (∀ F : LFed, lapply g cfg r F s = { F with fed := Federation.apply r F.fed s }) →
      (∀ F G : LFed, F.fed.net = G.fed.net → F.fed.parts = G.fed.parts →
        F.fed.extracted = G.fed.extracted →
        (Federation.apply r F.fed s).net = (Federation.apply r G.fed s).net ∧
        (Federation.apply r F.fed s).parts = (Federation.apply r G.fed s).parts ∧
        (Federation.apply r F.fed s).extracted = (Federation.apply r G.fed s).extracted) →
      (∀ F G : LFed, sent g cfg r peers F s = sent g cfg r peers G s) →
      FCoupled r honest (lapply g cfg r A s) (lapply g cfg r B s) ∧
      FInv r honest (lapply g cfg r A s) ∧ FInv r honest (lapply g cfg r B s) ∧
      fobs mk g cfg r peers A s = fobs mk g cfg r peers B s := by
    intro s hs hl hinvs hsent
    have hw : ∀ F : LFed, ∀ j, (lapply g cfg r F s).sys j = F.sys j := by
      intro F j
      rw [hl F]
      simp only [LFed.sys, Federation.apply_no_actor r F.fed s hs j]
    have hinv : ∀ F, FInv r honest F → FInv r honest (lapply g cfg r F s) := by
      intro F hF j hj
      have := hw F j
      simp only [LFed.sys, Sys.mk.injEq] at this
      rw [this.1]
      exact hF j hj
    have hfc : FCoupled r honest (lapply g cfg r A s) (lapply g cfg r B s) := by
      rw [hl A, hl B]
      obtain ⟨h1, h2, h3⟩ := hinvs A B hc.net hc.parts hc.extracted
      refine ⟨h1, h2, h3, fun j hj => ?_⟩
      · have h := hc.node j hj
        simp only [LFed.sys, Federation.apply_no_actor r _ s hs j]
        exact h
    refine ⟨hfc, hinv A hia, hinv B hib, ?_⟩
    simp only [fobs, localObs, hs, hsent A B, hfc.net, hfc.parts, hfc.extracted]
  cases p with
  | input i env x =>
    simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb ⊢
    exact process_pub hg ht hd hr hcl hdr hc hia hib (actor_honest ha rfl) env x (tbls₀ i) (tbls₁ i)
      hpa.1 hpb.1 hpa.2
  | net s =>
    cases s with
    | process i env e =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb ⊢
      exact process_pub (g := g) (cfg := cfg) hg ht hd hr hcl hdr hc hia hib (actor_honest ha rfl) env
        (.pinless e) (fun _ => false) (fun _ => false) hpa.1 hpb.1 hpa.2
    | deliver i env m =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb ⊢
      obtain ⟨h1, h2, h3, h4⟩ := advance_fcoupled (g := g) (cfg := cfg) hg ht hd hr hcl hdr hc hia
        hib (actor_honest ha rfl) env _ hpa.1 hpb.1 hpa.2
      refine ⟨h1, h2, h3, ?_⟩
      simp only [fobs, localObs, sent, received, Federation.actor, lapply, h4, h1.net, h1.parts,
        h1.extracted]
    | deliverPartial i env x =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb ⊢
      obtain ⟨h1, h2, h3, h4⟩ := advance_fcoupled (g := g) (cfg := cfg) hg ht hd hr hcl hdr hc hia
        hib (actor_honest ha rfl) env _ hpa.1 hpb.1 hpa.2
      refine ⟨h1, h2, h3, ?_⟩
      simp only [fobs, localObs, sent, received, Federation.actor, lapply, h4, h1.net, h1.parts,
        h1.extracted]
    | unstaged i cid =>
      exact frame (.unstaged i cid) rfl (fun _ => rfl)
        (fun _ _ h1 h2 h3 => by simp [Federation.apply, h1, h2, h3]) (fun _ _ => rfl)
    | emit i cid =>
      exact frame (.emit i cid) rfl (fun _ => rfl)
        (fun _ _ h1 h2 h3 => by simp [Federation.apply, h1, h2, h3]) (fun _ _ => rfl)
    | inject m =>
      exact frame (.inject m) rfl (fun _ => rfl)
        (fun _ _ h1 h2 h3 => by simp [Federation.apply, h1, h2, h3]) (fun _ _ => rfl)
    | extract j =>
      exact frame (.extract j) rfl (fun _ => rfl)
        (fun _ _ h1 h2 h3 => by simp [Federation.apply, h1, h2, h3]) (fun _ _ => rfl)
    | forge x =>
      exact frame (.forge x) rfl (fun _ => rfl)
        (fun _ _ h1 h2 h3 => by simp [Federation.apply, h1, h2, h3]) (fun _ _ => rfl)

/-! ## The relation -/

/-- **SILENCE over a federation, under one fixed exogenous schedule.** `DUR-1`: "Every observable
a node emits MUST be identical between a normal-PIN and a duress-PIN request".

One schedule, two enrolment families, two coupled federation states: the two runs emit equal
`FedSilence.FObs` at every step of `FedSilence.walk`. The relay and partial inventories are assumed
equal at the initial states (`FedSilence.FCoupled`) and not after: they stay equal because every
honest node's step does (`FedSilence.pstep_pub`). Only from a `Federation.Fresh` start, where both
are empty, is every relay or partial an honest node receives one an honest node emitted or queued in
the same run, or one a schedule step both runs take injected or forged. The rule and marker premises are
`Silence.silence`'s. The coupling and the invariant are assumed of the initial states;
`FedSilence.fed_silence_fresh` discharges them at the federation's initial boundary. No premise is
taken on the schedule's samples. -/
@[req "DUR-1"]
theorem fed_silence {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed), FCoupled r honest A B → FInv r honest A →
      FInv r honest B → ∀ y ∈ walk mk g cfg r honest peers tbls₀ tbls₁ A B sched, y.1 = y.2 := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons p rest ih =>
    intro A B hc hia hib y hy
    simp only [walk] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', hobs⟩ :=
        pstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr hc hia hib p tbls₀ tbls₁ ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hobs
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-! ## The initial boundary: `unarmedT` is ghost state here too -/

/-- Every node's `Node.unarmedT` replaced. -/
def withU (F : LFed) (u : Nat → Wall) : LFed :=
  { F with fed := { F.fed with worlds := fun i => (withUnarmedT (F.sys i) (u i)).world } }

/-- Two ledgered federations equal but for each node's `unarmedT`. -/
def UEq (A A' : LFed) : Prop :=
  A.fed.net = A'.fed.net ∧ A.fed.parts = A'.fed.parts ∧ A.fed.extracted = A'.fed.extracted ∧
    ∀ i, ∃ u, A.sys i = withUnarmedT (A'.sys i) u

theorem withUnarmedT_self (s : Sys) : withUnarmedT s s.world.node.unarmedT = s := rfl

theorem sys_advance (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env)
    (e : Event) (j : Nat) :
    (F.advance g cfg r i env e).sys j = if j = i then (sysStep g cfg r env (F.sys i) e).1 else F.sys j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl, sys_advance_self]
  · rw [if_neg h, sys_advance_other _ _ _ _ _ _ h]

theorem sysStep_u (g : Guards) (cfg : Config) (r : Rules) (env : Env) {s s' : Sys} {u : Wall}
    (h : s = withUnarmedT s' u) (e : Event) :
    (∃ v, (sysStep g cfg r env s e).1 = withUnarmedT (sysStep g cfg r env s' e).1 v) ∧
      (sysStep g cfg r env s e).2 = (sysStep g cfg r env s' e).2 := by
  subst h
  obtain ⟨h1, h2⟩ := sysStep_unarmedT g cfg r env s' u
    (sysStep g cfg r env (withUnarmedT s' u) e).1.world.node.unarmedT e
  rw [withUnarmedT_self] at h1
  exact ⟨⟨_, h1⟩, h2⟩

theorem advance_u {g : Guards} {cfg : Config} {r : Rules} {A A' : LFed} (h : UEq A A') (i : Nat)
    (env : Env) (e : Event) : UEq (A.advance g cfg r i env e) (A'.advance g cfg r i env e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun j => ?_⟩
  rw [sys_advance, sys_advance]
  split
  · obtain ⟨u, hu⟩ := h4 i
    exact (sysStep_u g cfg r env hu e).1
  · exact h4 j

theorem world_u {A A' : LFed} (h : UEq A A') (i : Nat) :
    ∃ u, A.fed.worlds i = (withUnarmedT (A'.sys i) u).world := by
  obtain ⟨u, hu⟩ := h.2.2.2 i
  exact ⟨u, congrArg Sys.world hu⟩

/-- One step from two states equal but for `unarmedT`: the same admission, horizon and
observation, and two states equal but for `unarmedT`. -/
theorem lapply_u {mk : Marker} {g : Guards} {cfg : Config} {r : Rules} {honest peers : List Nat}
    {A A' : LFed} (h : UEq A A') (s : Federation.Step) :
    UEq (lapply g cfg r A s) (lapply g cfg r A' s) ∧
    Federation.admits honest A.fed s = Federation.admits honest A'.fed s ∧
    inside r A s = inside r A' s ∧ fobs mk g cfg r peers A s = fobs mk g cfg r peers A' s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hobs : ∀ i env e, obsOf mk cfg r env (A.sys i) (sysStep g cfg r env (A.sys i) e).1
      (sysStep g cfg r env (A.sys i) e).2 e = obsOf mk cfg r env (A'.sys i)
      (sysStep g cfg r env (A'.sys i) e).1 (sysStep g cfg r env (A'.sys i) e).2 e := by
    intro i env e
    obtain ⟨u, hu⟩ := h4 i
    obtain ⟨⟨v, hv⟩, he⟩ := sysStep_u g cfg r env hu e
    rw [hv, he, hu, obsOf_unarmedT]
  have hin : ∀ i env e, (preHorizon r env (A.fed.worlds i).node && wfEvent r (A.fed.worlds i).node e) =
      (preHorizon r env (A'.fed.worlds i).node && wfEvent r (A'.fed.worlds i).node e) := by
    intro i env e
    obtain ⟨u, hu⟩ := world_u ⟨h1, h2, h3, h4⟩ i
    rw [hu]; rfl
  have hcons : ∀ i cid, Federation.consumed (A.fed.worlds i).node cid =
      Federation.consumed (A'.fed.worlds i).node cid := by
    intro i cid
    obtain ⟨u, hu⟩ := world_u ⟨h1, h2, h3, h4⟩ i
    rw [hu]; rfl
  have hfan : ∀ i effs, Federation.fanout (A.fed.worlds i) effs =
      Federation.fanout (A'.fed.worlds i) effs := by
    intro i effs
    obtain ⟨u, hu⟩ := world_u ⟨h1, h2, h3, h4⟩ i
    rw [hu]; rfl
  have hadv := fun i env e => advance_u (g := g) (cfg := cfg) (r := r) ⟨h1, h2, h3, h4⟩ i env e
  cases s with
  | process i env e =>
    obtain ⟨⟨v, hv⟩, he⟩ := sysStep_u g cfg r env (h4 i).choose_spec e
    obtain ⟨a1, a2, a3, a4⟩ := hadv i env e
    have hp : A.fed.parts ++ Federation.fanout (A.fed.worlds i) (sysStep g cfg r env (A.sys i) e).2 =
        A'.fed.parts ++ Federation.fanout (A'.fed.worlds i) (sysStep g cfg r env (A'.sys i) e).2 := by
      rw [h2, he, hfan]
    refine ⟨⟨a1, hp, a3, a4⟩, by simp only [Federation.admits], by simp only [inside, Federation.actor, hin], ?_⟩
    have hsent : sent g cfg r peers A (.process i env e) = sent g cfg r peers A' (.process i env e) := by
      simp only [sent, he, hfan]
    simp only [fobs, localObs, received, Federation.actor, lapply, LFed.advance, hobs, hp, hsent, h1,
      h3]
  | deliver i env m =>
    refine ⟨hadv i env _, by simp only [Federation.admits, h1], by simp only [inside, Federation.actor, hin], ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, LFed.advance, hobs, h1, h2, h3]
  | deliverPartial i env x =>
    refine ⟨hadv i env _, by simp only [Federation.admits, h2], by simp only [inside, Federation.actor, hin], ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, LFed.advance, hobs, h1, h2, h3]
  | unstaged i cid =>
    refine ⟨⟨by simp [lapply, Federation.apply, h1], h2, h3, fun j => h4 j⟩,
      by simp only [Federation.admits, hcons], rfl, ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, Federation.apply, h1, h2, h3]
  | emit i cid =>
    refine ⟨⟨by simp [lapply, Federation.apply, h1], h2, h3, fun j => h4 j⟩,
      by simp only [Federation.admits, hcons], rfl, ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, Federation.apply, h1, h2, h3]
  | inject m =>
    refine ⟨⟨by simp [lapply, Federation.apply, h1], h2, h3, fun j => h4 j⟩, rfl, rfl, ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, Federation.apply, h1, h2, h3]
  | extract j =>
    refine ⟨⟨h1, h2, by simp [lapply, Federation.apply, h3], fun j => h4 j⟩, rfl, rfl, ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, Federation.apply, h1, h2, h3]
  | forge x =>
    refine ⟨⟨h1, by simp [lapply, Federation.apply, h2], h3, fun j => h4 j⟩,
      by simp only [Federation.admits, h3], rfl, ?_⟩
    simp only [fobs, localObs, sent, received, Federation.actor, lapply, Federation.apply, h1, h2, h3]

/-- The two runs walked together emit the same observations, and stop at the same step, whatever
`unarmedT` any node starts from. -/
theorem walk_u (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B A' B' : LFed), UEq A A' → UEq B B' →
      walk mk g cfg r honest peers tbls₀ tbls₁ A B sched = walk mk g cfg r honest peers tbls₀ tbls₁ A' B' sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons p rest ih =>
    intro A B A' B' ha hb
    obtain ⟨ua, adA, inA, obA⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest) (peers := peers) ha (p.step tbls₀)
    obtain ⟨ub, _, inB, obB⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest) (peers := peers) hb (p.step tbls₁)
    simp only [walk, adA, inA, inB, obA, obB, ih _ _ _ _ ua ub]

/-- **`fed_silence` at every initial state the federation admits with its sweep flags clear.**
`Federation.Fresh` admits each honest node unarmed, with no candidate, no Carrier and no tombstone,
and both inventories empty. Taken with every honest node's sweep flag clear (`hs`), any ledgers and
any extracted set, and run under both enrolment families, it emits equal observations at every step
of the walk. As in `Silence.silence_initial`, no observation reads a node's `Node.unarmedT`
(`FedSilence.walk_u`), so each node is given its `T` there. -/
@[req "DUR-1"]
theorem fed_silence_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) :
    ∀ (sched : List PStep), ∀ y ∈ walk mk g cfg r honest peers tbls₀ tbls₁ F F sched, y.1 = y.2 := by
  intro sched y hy
  let F' := withU F (fun i => (F.fed.worlds i).node.T)
  have hu : UEq F F' :=
    ⟨rfl, rfl, rfl, fun i => ⟨(F.fed.worlds i).node.unarmedT, rfl⟩⟩
  rw [walk_u mk g cfg r honest peers tbls₀ tbls₁ sched F F F' F' hu hu] at hy
  have hinv : FInv r honest F' := by
    intro i hi
    obtain ⟨_, _, ha, hc, _, _⟩ := hf.2.2 i hi
    exact nodeInv_initial (F'.fed.worlds i).node _ hc ha (hs i hi) rfl
  exact fed_silence hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ sched F' F' (fcoupled_refl r honest F')
    hinv hinv y hy

/-! ## An adaptive observer over the public history -/

/-- **An adaptive observer.** Its next schedule step is a function of the observations its own run
has emitted so far, oldest first, and of nothing else: the type gives it no argument that holds a
world, a ledger, an enrolment table or an arm bit. `none` ends the schedule. -/
structure Observer where
  next : List FObs → Option PStep

/-- A scheduler that may also read the state it is about to step. The adaptive theorems take only
an `Observer`, read through `Observer.sched`; a scheduler that reads the state is the control. -/
abbrev Scheduler := LFed → List FObs → Option PStep

/-- An observer as a scheduler: the state is not read. -/
def Observer.sched (σ : Observer) : Scheduler := fun _ h => σ.next h

/-- The two runs walked together, each scheduled by `c` from its own state and its own history:
run `A` takes the step `c` picks from `A` and `hA`, and run `B` the step `c` picks from `B` and
`hB`, each turned into a federation step by its own enrolment family. At most `n` steps. The stop
is `FedSilence.walk`'s, admission read in run `A` as there, and the walk also ends when `c` ends
either schedule. -/
def awalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (c : Scheduler) :
    Nat → LFed → LFed → List FObs → List FObs → List (FObs × FObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match c A hA, c B hB with
    | some p, some q =>
      if Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
          inside r B (q.step tbls₁) then
        (fobs mk g cfg r peers A (p.step tbls₀), fobs mk g cfg r peers B (q.step tbls₁)) ::
          awalk mk g cfg r honest peers tbls₀ tbls₁ c n (lapply g cfg r A (p.step tbls₀))
            (lapply g cfg r B (q.step tbls₁)) (hA ++ [fobs mk g cfg r peers A (p.step tbls₀)])
            (hB ++ [fobs mk g cfg r peers B (q.step tbls₁)])
      else []
    | _, _ => []

/-- The schedule an observer selects in one run, at most `n` steps: each step is picked from the
observations the run has emitted so far. -/
def play (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment)
    (σ : Observer) : Nat → LFed → List FObs → List PStep
  | 0, _, _ => []
  | n + 1, F, h =>
    match σ.next h with
    | none => []
    | some p => p :: play mk g cfg r peers tbls σ n (lapply g cfg r F (p.step tbls))
        (h ++ [fobs mk g cfg r peers F (p.step tbls)])

/-- **Equal histories, the same step.** Whenever `FedSilence.walk` over the schedule run `A`'s
observer selects emits equal observations, the adaptive walk is that walk: run `B`'s observer,
reading `B`'s history, picks at every step, the stopping one included, the step run `A`'s picked.
No rule premise is taken. -/
theorem awalk_walk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : Observer) :
    ∀ (n : Nat) (A B : LFed) (h : List FObs),
      (∀ y ∈ walk mk g cfg r honest peers tbls₀ tbls₁ A B (play mk g cfg r peers tbls₀ σ n A h), y.1 = y.2) →
      awalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
        walk mk g cfg r honest peers tbls₀ tbls₁ A B (play mk g cfg r peers tbls₀ σ n A h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B h heq
    cases hσ : σ.next h with
    | none => simp only [awalk, Observer.sched, play, hσ, walk]
    | some p =>
      simp only [play, hσ] at heq ⊢
      simp only [awalk, Observer.sched, hσ]
      simp only [walk] at heq ⊢
      split
      · rename_i hguard
        simp only [hguard, if_true, List.mem_cons, forall_eq_or_imp] at heq
        obtain ⟨hhead, htail⟩ := heq
        rw [← hhead, ih _ _ _ htail]
      · rfl

/-- **SILENCE against an adaptive observer.** `DUR-1`: "Every observable a node emits MUST be
identical between a normal-PIN and a duress-PIN request".

Each run is scheduled by one `FedSilence.Observer` reading only the observations its own run has
emitted, from one prior history `h` both share. Under `FedSilence.fed_silence`'s premises the two
runs emit equal `FedSilence.FObs` at every step of `FedSilence.awalk`, and the adaptive walk is
`FedSilence.walk` over the schedule the observer selects (`FedSilence.awalk_walk`), so it stops at
the same horizon. The premises are `fed_silence`'s; the observer is restricted by its type, and no
premise is taken on it. -/
@[req "DUR-1"]
theorem fed_silence_adaptive {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (σ : Observer) :
    ∀ (n : Nat) (A B : LFed) (h : List FObs), FCoupled r honest A B → FInv r honest A →
      FInv r honest B →
      awalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
          walk mk g cfg r honest peers tbls₀ tbls₁ A B (play mk g cfg r peers tbls₀ σ n A h) ∧
        ∀ y ∈ awalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h, y.1 = y.2 := by
  intro n A B h hc hia hib
  have hw := fed_silence (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁
    (play mk g cfg r peers tbls₀ σ n A h) A B hc hia hib
  have he := awalk_walk mk g cfg r honest peers tbls₀ tbls₁ σ n A B h hw
  exact ⟨he, he ▸ hw⟩

/-- **`fed_silence_adaptive` at every initial state the federation admits with its sweep flags
clear**, as `FedSilence.fed_silence_fresh` states it, with an observer that has seen nothing. -/
@[req "DUR-1"]
theorem fed_silence_adaptive_fresh {mk : Marker} (hg : mk = .committed) {g : Guards}
    {cfg : Config} {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) (σ : Observer) :
    ∀ n : Nat,
      awalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [] =
          walk mk g cfg r honest peers tbls₀ tbls₁ F F (play mk g cfg r peers tbls₀ σ n F []) ∧
        ∀ y ∈ awalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [], y.1 = y.2 := by
  intro n
  have hw := fed_silence_fresh (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ F hf hs
    (play mk g cfg r peers tbls₀ σ n F [])
  have he := awalk_walk mk g cfg r honest peers tbls₀ tbls₁ σ n F F [] hw
  exact ⟨he, he ▸ hw⟩

/-! ## The earlier domain: restriction

Before claw-back ingress was admitted, the walk stopped at every claw-back (`FedSilence.insidePre`,
`Silence.wfEventPre`). `walkPre` and `awalkPre` are those walks. Each is a prefix of the expanded
walk on every schedule and pair of states (`walkPre_prefix`, `awalkPre_prefix`), so every
conclusion of `fed_silence`, `fed_silence_fresh`, `fed_silence_adaptive` and
`fed_silence_adaptive_fresh` holds of the earlier walks under the same premises
(`fed_silence_pre`, `fed_silence_adaptive_pre`). -/

/-- `FedSilence.walk` with the earlier boundary. -/
def walkPre (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : LFed → LFed → List PStep → List (FObs × FObs)
  | _, _, [] => []
  | A, B, p :: rest =>
    if Federation.admits honest A.fed (p.step tbls₀) && insidePre r A (p.step tbls₀) &&
        insidePre r B (p.step tbls₁) then
      (fobs mk g cfg r peers A (p.step tbls₀), fobs mk g cfg r peers B (p.step tbls₁)) ::
        walkPre mk g cfg r honest peers tbls₀ tbls₁ (lapply g cfg r A (p.step tbls₀))
          (lapply g cfg r B (p.step tbls₁)) rest
    else []

theorem walkPre_prefix (mk : Marker) (g : Guards) (cfg : Config) (r : Rules)
    (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed),
      walkPre mk g cfg r honest peers tbls₀ tbls₁ A B sched <+:
        walk mk g cfg r honest peers tbls₀ tbls₁ A B sched := by
  intro sched
  induction sched with
  | nil => intro _ _; exact List.prefix_refl _
  | cons p rest ih =>
    intro A B
    simp only [walkPre, walk]
    by_cases hg : (Federation.admits honest A.fed (p.step tbls₀) && insidePre r A (p.step tbls₀) &&
        insidePre r B (p.step tbls₁)) = true
    · have hg' : (Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
          inside r B (p.step tbls₁)) = true := by
        simp only [Bool.and_eq_true] at hg ⊢
        exact ⟨⟨hg.1.1, insidePre_le r _ _ hg.1.2⟩, insidePre_le r _ _ hg.2⟩
      rw [if_pos hg, if_pos hg']
      exact List.cons_prefix_cons.2 ⟨rfl, ih _ _⟩
    · rw [if_neg hg]; exact List.nil_prefix

/-- **`fed_silence` on the earlier domain**, under its premises. -/
@[req "DUR-1"]
theorem fed_silence_pre {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed), FCoupled r honest A B → FInv r honest A →
      FInv r honest B → ∀ y ∈ walkPre mk g cfg r honest peers tbls₀ tbls₁ A B sched, y.1 = y.2 :=
  fun sched A B hc hia hib y hy =>
    fed_silence hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ sched A B hc hia hib y
      ((walkPre_prefix mk g cfg r honest peers tbls₀ tbls₁ sched A B).subset hy)

/-- `FedSilence.awalk` with the earlier boundary. -/
def awalkPre (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (c : Scheduler) :
    Nat → LFed → LFed → List FObs → List FObs → List (FObs × FObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match c A hA, c B hB with
    | some p, some q =>
      if Federation.admits honest A.fed (p.step tbls₀) && insidePre r A (p.step tbls₀) &&
          insidePre r B (q.step tbls₁) then
        (fobs mk g cfg r peers A (p.step tbls₀), fobs mk g cfg r peers B (q.step tbls₁)) ::
          awalkPre mk g cfg r honest peers tbls₀ tbls₁ c n (lapply g cfg r A (p.step tbls₀))
            (lapply g cfg r B (q.step tbls₁)) (hA ++ [fobs mk g cfg r peers A (p.step tbls₀)])
            (hB ++ [fobs mk g cfg r peers B (q.step tbls₁)])
      else []
    | _, _ => []

theorem awalkPre_prefix (mk : Marker) (g : Guards) (cfg : Config) (r : Rules)
    (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) (c : Scheduler) :
    ∀ (n : Nat) (A B : LFed) (hA hB : List FObs),
      awalkPre mk g cfg r honest peers tbls₀ tbls₁ c n A B hA hB <+:
        awalk mk g cfg r honest peers tbls₀ tbls₁ c n A B hA hB := by
  intro n
  induction n with
  | zero => intros; exact List.prefix_refl _
  | succ n ih =>
    intro A B hA hB
    simp only [awalkPre, awalk]
    cases c A hA with
    | none => exact List.prefix_refl _
    | some p =>
      cases c B hB with
      | none => exact List.prefix_refl _
      | some q =>
        dsimp only
        by_cases hg : (Federation.admits honest A.fed (p.step tbls₀) && insidePre r A (p.step tbls₀) &&
            insidePre r B (q.step tbls₁)) = true
        · have hg' : (Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
              inside r B (q.step tbls₁)) = true := by
            simp only [Bool.and_eq_true] at hg ⊢
            exact ⟨⟨hg.1.1, insidePre_le r _ _ hg.1.2⟩, insidePre_le r _ _ hg.2⟩
          rw [if_pos hg, if_pos hg']
          exact List.cons_prefix_cons.2 ⟨rfl, ih _ _ _ _⟩
        · rw [if_neg hg]; exact List.nil_prefix

/-- **`fed_silence_adaptive` on the earlier domain**, under its premises: against every observer,
equal observations at every step of the adaptive walk that stops at every claw-back. -/
@[req "DUR-1"]
theorem fed_silence_adaptive_pre {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (σ : Observer) :
    ∀ (n : Nat) (A B : LFed) (h : List FObs), FCoupled r honest A B → FInv r honest A →
      FInv r honest B →
      ∀ y ∈ awalkPre mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h, y.1 = y.2 :=
  fun n A B h hc hia hib y hy =>
    (fed_silence_adaptive hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ σ n A B h hc hia hib).2 y
      ((awalkPre_prefix mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h).subset hy)

/-! ## The envelope a message travels in -/

/-- `NCH-20`'s `msg_type` of a body. -/
def Body.msgType : Body → Encode.Bytes
  | .request _ => Envelope.requestType
  | .part _ => Envelope.partialType

/-- The `NCH-11` envelope of a frame: its type, sender and recipient from the frame, and
`protocol_version` 4. What this model does not carry is an argument: the wallet id and manifest
hash, the base64 payload, the nonce and the timestamp. -/
def Frame.envelope (f : Frame) (walletId manifestHash payload nonce : Encode.Bytes) (ts : Nat) :
    Envelope.Envelope :=
  { msgType := f.body.msgType, version := 4, walletId, manifestHash, sender := f.src,
    recipient := f.dst, payload, nonce, timestamp := ts }

/-- **Size, and not bytes.** A frame's envelope preimage is 115 bytes plus its payload's length,
whatever the frame (relay or partial, any sender, any recipient), the nonce's sixteen bytes and the
timestamp. So where `FedSilence.fed_silence` gives the two runs the same frames, their preimages have
one length exactly when their payloads do, whatever nonces and timestamps the two runs draw. Nothing
here derives a payload's length or bytes, and equal lengths are not equal bytes: the nonce is a
random draw, and no theorem here couples it across the runs. -/
@[req "NCH-11"]
theorem frame_preimage_length (f : Frame) (walletId manifestHash payload nonce : Encode.Bytes)
    (ts : Nat) (hw : walletId.length = 32) (hm : manifestHash.length = 32)
    (hn : nonce.length = 16) :
    (Envelope.preimage (f.envelope walletId manifestHash payload nonce ts)).length =
      115 + payload.length := by
  rw [Envelope.preimage_length _ hw hm hn]
  have h : f.body.msgType.length = 7 := by
    cases f.body <;> simp only [Body.msgType, Envelope.msgType_length]
  simp only [Frame.envelope, h]

end BtcPolicy.FedSilence
