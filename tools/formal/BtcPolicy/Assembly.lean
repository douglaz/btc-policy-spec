import BtcPolicy.Ladder
/-! The assembly and the send for each candidate class the formal model admits: a Hot spend, a selected paired
Escape, and a singleton claw-back. `SPN-39` asks of every due candidate, whatever its class, that the node
"finalize on a clone at the highest rung at or below the latch that carries at least `t` distinct valid partials
on every input, walking downward; assemble the package (`WTC-24`); test it for mempool acceptance; re-check the
slot, the freeze and the window under the store lock as the linearization point between arming and sending; then
broadcast." `BtcPolicy.Sweep` puts a backend check on the assembly of a candidate in the Escape role only
(`Sweep.assemblyOk`); this module puts the check each class owes on every assembly, and changes nothing else.
There is no second release machine: the state, the steps and the step function are `BtcPolicy.Sweep`'s, the fire
passes carry `PreRelease`'s verdict, and only the assembly's admission is refined.

**The class.** `Assembly.classOf` reads the registration-owned role (`Kernel.Cand.isEscape`, from the pair
`SPN-32` records) and the recorded class (`SPN-28`'s `hot`): the Escape of a pair is `escape`, an unpaired
candidate that is not hot is `clawback`, and every other candidate is `spend`. A claw-back gets its own class from
what its registration writes (`Assembly.clawbackBorn_class`), never the Escape role: `SPN-51` registers it with "no
Escape", and the check it gets is not the Escape's (`Assembly.checkAt_clawback`).

**What every class's assembly reads.** From the node's latest observation (`Sweep.State.obs`) and its own history,
all at the assembly's state: `DUR-28`'s "`≥ t` distinct valid partials on every input" over the node's possession
(`Sweep.possessed`, `Federation.held`); `WTC-24`'s ancestry with `WTC-25`'s replacement (`Assembly.ancestry`, which
is `Package.validate` over the snapshot, one membership read and the authorized set, as a replacement of the
resident `Assembly.target` derives, if any); and `WTC-26`'s package acceptance (`Assembly.packageOk`) over the
package `WTC-23` makes of the candidate, its transaction alone. The selected Escape owes two more, `DUR-28`'s "The
finalized transaction MUST pass `DUR-23` and `DUR-24` again at its exact vsize": coverage at the assembly's own
pass (`Sweep.covered`) and the fee floor at the exact finalized vsize (`Assembly.exactVsize`). With no
observation, no class assembles: `DUR-32`'s "no preflight context".

**Replacement.** `WTC-25` names three permitted replacements: "a higher rung over a resident lower rung, a refresh
over a resident refresh of the same coins, or a claw-back over a resident claw-back of the same coins". Refresh is
outside this module. For a claw-back, `Assembly.target` is the first resident transaction, other than its own,
that spends one of its inputs and is a claw-back this node registered, now or earlier in its history
(`Assembly.clawTxs`); `Package.validate` then asks it to be resident and in the authorized set, and the candidate
to spend exactly its ordered outpoints. A resident the node never registered as a claw-back is no target, and its
spending of the inputs reads them as spent (`Assembly.target_registered`). A Hot spend and a base Escape replace
nothing. A higher rung's replacement of a resident lower rung is `Assembly.rungCheck`'s, over the ladder of
`BtcPolicy.Ladder`.

**The exact finalized size.** `DUR-25`: "after finalization it MUST be re-evaluated on the exact finalized
transaction at its exact vsize". The model has no finalized transaction bytes, so the weight of each input's
finalized witness is supplied per txid (`Assembly.Cfg.witnesses`), and `Assembly.exactVsize` is
`Witness.finalizedVsize` over the transaction's legacy length and those weights. Its relation to the candidate is
the explicit assumption `Assembly.Fits`: one witness per input, each at most `CHN-34`'s `W_N` at the node's
threshold and the federation's key count. Under it the exact vsize is at most the maximum the release checked
(`Assembly.exact_le_max`), and a fee that met the floor at the maximum meets it at the exact size
(`Assembly.exact_fee_of_max`). Without it a supplied size bears no relation to the candidate
(`Exhibits.Assembly.unrelated_size`).

**The package verdict.** `WTC-26`: "Package acceptance MUST require every entry allowed, tolerating exactly one
rejection reason — `txn-already-in-mempool`". The backend's answer is a named external input,
`Assembly.Cfg.test`, one `Assembly.Entry` per member of the tested package; `Assembly.accepts` is the node's
reading of it, and nothing here says the backend answers correctly.

**The refined run and the old abstraction.** `Assembly.Execution` is `PreRelease.Execution` with one more conjunct
on an assembly: every resident under the commitment passes `Assembly.checkOf` at that state and history
(`Assembly.guardOk`). `Assembly.to_prerelease` is the restriction, so every result about `PreRelease`, `Sweep`,
`Federation` and the kernel applies, and `Assembly.execution_iff` says the refinement is exactly that conjunct. On
the Escape the new check implies the old (`Assembly.checkOf_escape`, `Assembly.guardOk_sweep`), so for a selected
Escape this refines `Sweep.check`; for a Hot spend or a claw-back the old run assembled without any backend read,
and the new one refuses some of those assemblies, which the old abstraction allowed and the rule does not
(`Exhibits.Assembly.hot_old_broader`). Nothing but an assembly is constrained: a history with no assembly is a
refined run whenever it is a `PreRelease` one (`Assembly.of_unassembled`), so arming, freezing, every release,
claw-back ingress, Lockdown, extraction and forgery wait on no assembly check (`Assembly.lift_safety`).

**The send.** No step but an assembly reads the backend here (`Assembly.guardOk_of_none`), so the send's
admission is `PreRelease`'s (`Assembly.send_admits`): `DUR-29`'s re-authorization reads what that point reads,
"this Escape still in `selected_escapes` with `sweep_active` AND its own duress bit set, not frozen, window open",
which is `Kernel.send`'s `due` and `releaseAuthorized`, and no second backend check. `Assembly.submitted_in_order`:
every submission, of any class, is of a resident whose package test was earned at an earlier assembly passing that
class's check at that assembly's own reads (`Assembly.Assembled`), and which the send's own state re-authorizes. An
earlier assembly grants no lasting authority: the send reads the current state, so a holder decision between them
that freezes a Hot spend stops its send (`Exhibits.Assembly.frozen_after_assembly`), and a backend that moves
after the assembly is the current specified boundary, which the send does not re-read
(`Exhibits.Assembly.backend_moves_after_assembly`). The class-specific treatment of an in-flight candidate through
Lockdown is the kernel's: `Kernel.lockdown_preserves_in_flight`. What the backend does with a submission, and
whether anything confirms, is not here.

**Not modelled.** Refresh. A resident txid outside the ladder in the batched read. The binding of the ladder's
per-pass reads, and of `Assembly.rungCheck`'s rung, to the composed run and its kernel, which assembles one rung
per candidate. The finalized transaction's bytes, its signatures' actual lengths and `WTC-27`'s local
deserialization. `CHN-16`'s relations between rungs. Freshness of the observation. -/

namespace BtcPolicy.Assembly
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Coverage (Coin Outpoint)
open BtcPolicy.Sweep (Backend)

/-! ## The class -/

/-- The candidate classes an assembly distinguishes. -/
inductive Cls
  | spend | escape | clawback
  deriving DecidableEq, Repr

/-- The Escape of a pair is `escape`; an unpaired candidate that is not hot, which is how `SPN-51` registers a
claw-back ("one candidate, not hot, not duress, born open, … no Escape"), is `clawback`; every other candidate is
`spend`. It reads the pair, the candidate's own id and the hot bit, all written at registration. -/
@[req "SPN-39"]
def classOf (c : Cand) : Cls :=
  if c.isEscape then .escape else if c.pair.isNone && !c.hot then .clawback else .spend

/-- A registered claw-back is in its own class and never in the Escape role, whatever request it came from. -/
@[req "SPN-51"]
theorem clawbackBorn_class (self : Nat) (slack : Secs) (env : Env) (c : Cand) :
    classOf (clawbackBorn self slack env c) = .clawback ∧ (clawbackBorn self slack env c).isEscape = false := by
  simp [classOf, clawbackBorn, born, Cand.isEscape]

/-! ## The backend's package verdict (`WTC-26`) -/

/-- The backend's answer on one entry of the tested package: allowed, `txn-already-in-mempool`, or another
rejection. -/
inductive Entry
  | allowed
  | alreadyInMempool
  | rejected (reason : Nat)
  deriving DecidableEq, Repr

/-- "every entry allowed, tolerating exactly one rejection reason — `txn-already-in-mempool`". -/
@[req "WTC-26"]
def Entry.tolerated : Entry → Bool
  | .allowed => true
  | .alreadyInMempool => true
  | .rejected _ => false

/-- The node's reading of the backend's answer on a package: one entry per member, each tolerated. -/
@[req "WTC-26"]
def accepts (pkg : List Nat) (es : List Entry) : Bool := es.length == pkg.length && es.all Entry.tolerated

/-- The answer is accepted exactly when it has one entry per member and each is allowed or
`txn-already-in-mempool`; "Any other rejection is a verdict the sweep treats as inadmissible for this pass". -/
@[req "WTC-26"]
theorem accepts_iff (pkg : List Nat) (es : List Entry) :
    accepts pkg es = true ↔ es.length = pkg.length ∧ ∀ e ∈ es, e = .allowed ∨ e = .alreadyInMempool := by
  simp only [accepts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine and_congr_right fun _ => forall₂_congr fun e _ => ?_
  cases e <;> simp [Entry.tolerated]

/-- Another rejection on any entry refuses the package. -/
@[req "WTC-26"]
theorem rejected_refuses (pkg : List Nat) (es : List Entry) (k : Nat) (h : Entry.rejected k ∈ es) :
    accepts pkg es = false := by
  cases hb : accepts pkg es
  · rfl
  · rcases ((accepts_iff pkg es).1 hb).2 _ h with h | h <;> cases h

/-! ## The configuration -/

/-- The pre-release check's parameters, the weight of each input's finalized witness by txid, and the backend's
package verdict at an instant, one entry per member of the package tested. -/
structure Cfg where
  pre : PreRelease.Cfg
  witnesses : Nat → List Nat
  test : Backend → List Nat → List Entry

/-! ## The exact finalized size (`DUR-25`) -/

/-- The exact finalized vsize: `Witness.finalizedVsize` over the transaction's legacy length and the supplied
weight of each input's finalized witness. -/
@[req "DUR-25"]
def exactVsize (cfg : Cfg) (tx : Tx) : Nat :=
  Witness.finalizedVsize (cfg.pre.legacyLen tx.id) (cfg.witnesses tx.id)

/-- The consistency assumption that relates the supplied witnesses to the candidate: one per input, each at most
`CHN-34`'s `W_N` at threshold `t` and the federation's key count. -/
@[req "DUR-25"]
def Fits (cfg : Cfg) (t : Nat) (tx : Tx) : Prop :=
  (cfg.witnesses tx.id).length = tx.inputs.length ∧
    ∀ w ∈ cfg.witnesses tx.id, w ≤ Witness.W t cfg.pre.sweep.keys.length

/-- `DUR-25`'s "evaluated at each rung's **maximum** finalized vsize, so it still holds once the missing
signatures land": under `Fits` the exact size is at most the maximum the release read. -/
@[req "DUR-25"]
theorem exact_le_max (cfg : Cfg) (t : Nat) (tx : Tx) (h : Fits cfg t tx) :
    exactVsize cfg tx ≤ PreRelease.maxVsize cfg.pre t tx := by
  unfold exactVsize PreRelease.maxVsize
  rw [← h.1]
  exact Witness.finalized_le_max _ _ _ _ h.2

/-- `DUR-23`'s floor holds at a smaller size whenever it holds at a larger one. -/
@[req "DUR-23"]
theorem feeOk_mono (cfg : PreRelease.Cfg) {vs vs' : Nat} (tx : Tx) (h : vs ≤ vs')
    (hf : PreRelease.feeOk cfg vs' tx = true) : PreRelease.feeOk cfg vs tx = true := by
  simp only [PreRelease.feeOk, Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
  exact ⟨hf.1, Nat.le_trans (Nat.mul_le_mul_left _ h) hf.2⟩

/-- Under `Fits`, a fee that met the floor at the maximum finalized vsize meets it at the exact one. -/
@[req "DUR-25"]
theorem exact_fee_of_max (cfg : Cfg) (t : Nat) (tx : Tx) (h : Fits cfg t tx)
    (hf : PreRelease.feeOk cfg.pre (PreRelease.maxVsize cfg.pre t tx) tx = true) :
    PreRelease.feeOk cfg.pre (exactVsize cfg tx) tx = true :=
  feeOk_mono cfg.pre tx (exact_le_max cfg t tx h) hf

/-! ## Replacement (`WTC-25`) -/

/-- The txids of the claw-backs this node registered, now and before each step of its history. -/
@[req "WTC-25"]
def clawTxs (h : History) (n : Node) : List Nat :=
  ((n.cands.filter fun c => classOf c == .clawback).map (·.tx.id)) ++
    h.flatMap fun a => (a.1.node.cands.filter fun c => classOf c == .clawback).map (·.tx.id)

/-- The resident a candidate replaces: for a claw-back, the first resident transaction other than its own that
spends one of its inputs and is a claw-back this node registered (`C`); for every other class, none. -/
@[req "WTC-25"]
def target (C : List Nat) (b : Backend) (c : Cand) : Option Nat :=
  match classOf c with
  | .clawback =>
    (b.mempool.find? fun m => m.1 != c.tx.id && C.contains m.1 && m.2.any (c.tx.inputs.contains ·)).map (·.1)
  | _ => none

/-- A target is a resident, a registered claw-back, and spends one of the candidate's inputs; only a claw-back
has one. -/
@[req "WTC-25"]
theorem target_registered {C : List Nat} {b : Backend} {c : Cand} {r : Nat} (h : target C b c = some r) :
    classOf c = .clawback ∧ r ∈ C ∧ r ≠ c.tx.id ∧ ∃ ins, (r, ins) ∈ b.mempool ∧ ∃ o ∈ ins, o ∈ c.tx.inputs := by
  unfold target at h
  split at h
  · rename_i hc
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    have hmem := List.mem_of_find?_eq_some hm
    have hp := List.find?_some hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem, List.any_eq_true] at hp
    obtain ⟨⟨h1, h2⟩, o, ho, ho'⟩ := hp
    exact ⟨hc, h2, h1, m.2, hmem, o, ho, ho'⟩
  · cases h

/-- `WTC-24` with `WTC-25` on this candidate at that instant, its membership read and the authorized set. -/
@[req "WTC-24"]
def ancestry (cfg : Sweep.Cfg) (A C : List Nat) (b : Backend) (c : Cand) : Package.Verdict :=
  Package.validate cfg.ancestry cfg.creator (Sweep.snapshot A b) b.mempool A (Sweep.candidateOf c.tx)
    (target C b c)

/-- With no target the ancestry is `Sweep.ancestryOk`'s. -/
theorem ancestry_none {cfg : Sweep.Cfg} {A C : List Nat} {b : Backend} {c : Cand} (h : target C b c = none) :
    (ancestry cfg A C b c).isAdmitted = Sweep.ancestryOk cfg A b c := by
  simp [ancestry, Sweep.ancestryOk, h]

/-! ## The check, class by class -/

/-- `WTC-26` on the package `WTC-23` makes of a transaction: the transaction alone. -/
@[req "WTC-26"]
def packageOk (cfg : Cfg) (b : Backend) (tx : Tx) : Bool := accepts [tx.id] (cfg.test b [tx.id])

/-- The Escape's re-evaluation at its exact vsize, `DUR-28`'s "pass `DUR-23` and `DUR-24` again at its exact
vsize", read at the assembly's own pass; no other class owes it. -/
@[req "DUR-28"]
def exactOk (cfg : Cfg) (A : List Nat) (n : Node) (b : Backend) (c : Cand) : Bool :=
  match classOf c with
  | .escape => Sweep.covered cfg.pre.sweep A n b c && PreRelease.feeOk cfg.pre (exactVsize cfg c.tx) c.tx
  | _ => true

/-- `SPN-39`'s assembly of one candidate at instant `b`, authorized set `A`, registered claw-backs `C`, registry
`n` and possession `R`, in its order: `t` distinct signers on every input, the Escape's exact re-evaluation,
the package's ancestry, and the backend's acceptance. -/
@[req "SPN-39"]
def checkAt (cfg : Cfg) (A C : List Nat) (n : Node) (R : List Authority.Sig) (b : Backend) (c : Cand) : Bool :=
  Sweep.possessed cfg.pre.sweep n.t R c && exactOk cfg A n b c &&
    (ancestry cfg.pre.sweep A C b c).isAdmitted && packageOk cfg b c.tx

/-- A Hot spend's assembly reads possession, ancestry and the backend's verdict, and no coverage or fee floor. -/
@[req "SPN-39"]
theorem checkAt_spend (cfg : Cfg) (A C : List Nat) (n : Node) (R : List Authority.Sig) (b : Backend) (c : Cand)
    (h : classOf c = .spend) :
    checkAt cfg A C n R b c = (Sweep.possessed cfg.pre.sweep n.t R c &&
      Sweep.ancestryOk cfg.pre.sweep A b c && packageOk cfg b c.tx) := by
  have ht : target C b c = none := by simp [target, h]
  simp [checkAt, exactOk, h, ancestry_none ht]

/-- A claw-back's assembly reads possession, its ancestry as a replacement of a resident claw-back it derives,
and the backend's verdict, and not the Escape's coverage or fee floor: it gets its check from its own class. -/
@[req "SPN-51"]
theorem checkAt_clawback (cfg : Cfg) (A C : List Nat) (n : Node) (R : List Authority.Sig) (b : Backend) (c : Cand)
    (h : classOf c = .clawback) :
    checkAt cfg A C n R b c = (Sweep.possessed cfg.pre.sweep n.t R c &&
      (ancestry cfg.pre.sweep A C b c).isAdmitted && packageOk cfg b c.tx) := by
  simp [checkAt, exactOk, h]

/-- What an admitted assembly established, class by class: `t` distinct signers on every input in the node's
possession; `WTC-24`'s admitted verdict, with every input shown by the snapshot or the resident's own, every
unconfirmed ancestor authorized and at most `Package.ancestorLimit` of them, and for a replacement the resident
resolved under `WTC-25`; the backend's verdict with one tolerated entry for the transaction; and, for the Escape,
coverage at the assembly's pass and the floor at the exact finalized vsize. -/
@[req "SPN-39"]
theorem checkAt_iff (cfg : Cfg) (A C : List Nat) (n : Node) (R : List Authority.Sig) (b : Backend) (c : Cand) :
    checkAt cfg A C n R b c = true ↔
      Authority.quorum cfg.pre.sweep.keys n.t c.tx R = true ∧
      (classOf c = .escape → Sweep.covered cfg.pre.sweep A n b c = true ∧
        PreRelease.feeOk cfg.pre (exactVsize cfg c.tx) c.tx = true) ∧
      (∃ anc, ancestry cfg.pre.sweep A C b c = .admitted anc) ∧
      (cfg.test b [c.tx.id]).length = 1 ∧
      ∀ e ∈ cfg.test b [c.tx.id], e = .allowed ∨ e = .alreadyInMempool := by
  constructor
  · intro h
    simp only [checkAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, he⟩, ha⟩, hk⟩ := h
    obtain ⟨hl, hk⟩ := (accepts_iff _ _).1 hk
    refine ⟨hp, fun hc => ?_, ?_, by simpa using hl, hk⟩
    · simp only [exactOk, hc, Bool.and_eq_true] at he
      exact he
    · cases hv : ancestry cfg.pre.sweep A C b c with
      | admitted anc => exact ⟨anc, rfl⟩
      | refused _ => rw [hv] at ha; cases ha
  · rintro ⟨hp, he, ⟨anc, ha⟩, hl, hk⟩
    have hk' : packageOk cfg b c.tx = true := (accepts_iff _ _).2 ⟨by simpa using hl, hk⟩
    have he' : exactOk cfg A n b c = true := by
      cases hcl : classOf c with
      | escape =>
        obtain ⟨h1, h2⟩ := he hcl
        simp [exactOk, hcl, h1, h2]
      | spend => simp [exactOk, hcl]
      | clawback => simp [exactOk, hcl]
    simp only [checkAt, Bool.and_eq_true]
    exact ⟨⟨⟨hp, he'⟩, by rw [ha]; rfl⟩, hk'⟩

/-! ## The composed check -/

/-- The claw-backs node `i` registered, read in state `st` after history `T`. -/
def clawTxsAt (st : Sweep.State) (T : Sweep.Trace) (i : Nat) : List Nat :=
  clawTxs (Federation.project i (Sweep.fedTrace T)) (st.fed.worlds i).node

/-- The check on one candidate at node `i`, in state `st` after history `T`, from this node's latest observation,
its own history and its possession. No observation, no assembly. -/
@[req "SPN-39"]
def checkOf (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (c : Cand) : Bool :=
  match st.obs i with
  | none => false
  | some b =>
    checkAt cfg (Sweep.authorizedAt st T i) (clawTxsAt st T i) (st.fed.worlds i).node
      (Federation.held i (Sweep.fedTrace T) st.fed) b c

/-- On the Escape the check implies `Sweep.check`: coverage, ancestry with no resident named, and possession. -/
@[req "DUR-29"]
theorem checkOf_escape {cfg : Cfg} {st : Sweep.State} {T : Sweep.Trace} {i : Nat} {c : Cand}
    (hc : c.isEscape = true) (h : checkOf cfg st T i c = true) : Sweep.check cfg.pre.sweep st T i c = true := by
  have hcls : classOf c = .escape := by simp [classOf, hc]
  unfold checkOf at h
  unfold Sweep.check
  split at h
  · cases h
  · rename_i b hb
    rw [hb]
    have ht : target (clawTxsAt st T i) b c = none := by simp [target, hcls]
    simp only [checkAt, exactOk, hcls, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hcv, -⟩, ha⟩, -⟩ := h
    rw [ancestry_none ht] at ha
    simp [hp, hcv, ha]

/-- An assembly of a commitment needs the check on every resident under that id, whatever its class. Every other
step passes. -/
@[req "SPN-39"]
def guardOk (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) : Federation.Step → Bool
  | .process i _ (.packageAccepted cid) =>
    (st.fed.worlds i).node.cands.all fun c => !(c.id == cid) || checkOf cfg st T i c
  | _ => true

/-- The new guard refines the old one: an assembly it admits, `Sweep.assemblyOk` admits. -/
@[req "DUR-29"]
theorem guardOk_sweep {cfg : Cfg} {st : Sweep.State} {T : Sweep.Trace} {s : Federation.Step}
    (h : guardOk cfg st T s = true) : Sweep.assemblyOk cfg.pre.sweep st T s = true := by
  cases s with
  | process i env e =>
    cases e with
    | packageAccepted cid =>
      simp only [guardOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
      simp only [Sweep.assemblyOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        beq_eq_false_iff_ne]
      intro c hc
      by_cases hid : c.id = cid
      · rcases h c hc with h | h
        · exact absurd hid h
        · by_cases he : c.isEscape = true
          · exact .inr (checkOf_escape he h)
          · exact .inl (.inr (by simpa using he))
      · exact .inl (.inl hid)
    | _ => rfl
  | _ => rfl

theorem guardOk_of_none (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) {s : Federation.Step}
    (h : Sweep.assembly s = none) : guardOk cfg st T s = true := by
  cases s with
  | process i env e => cases e <;> simp_all [Sweep.assembly, guardOk]
  | _ => rfl

/-! ## The refined run -/

/-- The assembly conjunct on a composed step. -/
@[req "SPN-39"]
def assemblyOk (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) : Sweep.Step → Bool
  | .fed s => guardOk cfg st T s
  | _ => true

/-- `PreRelease`'s admission and the assembly conjunct. -/
def admits (cfg : Cfg) (honest : List Nat) (st : Sweep.State) (T : Sweep.Trace) (s : Sweep.Step) : Bool :=
  PreRelease.admits cfg.pre honest st T s && assemblyOk cfg st T s

/-- A reachable refined execution: `PreRelease.Execution` whose assemblies pass each class's check. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Sweep.Trace → Sweep.State → Prop
  | init (st : Sweep.State) (h : Sweep.Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Sweep.Step) (ha : admits cfg honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (Sweep.apply r st s)

/-- Every refined execution is a `PreRelease` one with the same trace and state. -/
@[req "SPN-39"]
theorem to_prerelease {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : Execution cfg r honest T st) : PreRelease.Execution cfg.pre r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | next s ha _ ih =>
    simp only [admits, Bool.and_eq_true] at ha
    exact .next s ha.1 ih

/-- Each step of a trace carries the assembly conjunct at its own state and history. -/
def Checked (cfg : Cfg) : Sweep.Trace → Prop
  | [] => True
  | (st, s) :: T => assemblyOk cfg st T s = true ∧ Checked cfg T

/-- The refinement is exactly the assembly conjunct. -/
@[req "SPN-39"]
theorem execution_iff {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State} :
    Execution cfg r honest T st ↔ PreRelease.Execution cfg.pre r honest T st ∧ Checked cfg T := by
  constructor
  · intro hx
    induction hx with
    | init st h => exact ⟨.init st h, trivial⟩
    | next s ha _ ih =>
      simp only [admits, Bool.and_eq_true] at ha
      exact ⟨.next s ha.1 ih.1, ha.2, ih.2⟩
  · rintro ⟨hx, hc⟩
    induction hx with
    | init st h => exact .init st h
    | next s ha _ ih =>
      exact .next s (by simp [admits, ha, hc.1]) (ih hc.2)

/-- A `Bool` form of `Assembly.Checked`, for decided runs. -/
def checks (cfg : Cfg) : Sweep.Trace → Bool
  | [] => true
  | (st, s) :: T => assemblyOk cfg st T s && checks cfg T

theorem checked_of_checks (cfg : Cfg) : ∀ {T : Sweep.Trace}, checks cfg T = true → Checked cfg T
  | [], _ => trivial
  | (_, _) :: _, h => by
    simp only [checks, Bool.and_eq_true] at h
    exact ⟨h.1, checked_of_checks cfg h.2⟩

/-- No step but an assembly is constrained: a `PreRelease` history with no assembly is a refined one. -/
@[req "DUR-19"]
theorem of_unassembled {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : PreRelease.Execution cfg.pre r honest T st)
    (hno : ∀ p ∈ T, ∀ s, p.2 = .fed s → Sweep.assembly s = none) : Execution cfg r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | @next T st s ha _ ih =>
    have hs : assemblyOk cfg st T s = true := by
      cases s with
      | fed s => exact guardOk_of_none cfg st T (hno _ List.mem_cons_self s rfl)
      | _ => rfl
    exact .next s (by simp [admits, ha, hs]) (ih fun p hp => hno p (List.mem_cons_of_mem _ hp))

/-- Arming and freezing need no assembly check: `PreRelease.lift_safety`'s histories, with no assembly and every
Escape withheld, are refined runs over every backend instant. -/
@[req "DUR-19"]
theorem lift_safety {cfg : Cfg} {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) (hno : ∀ p ∈ t, Sweep.assembly p.2 = none)
    (hfire : ∀ p ∈ t, ∀ i env, p.2 = .process i env .firePass →
      env.withheld = PreRelease.escapeIds (p.1.worlds i).node)
    (b : Backend) :
    Execution cfg r honest (Sweep.liftTrace b t) { fed := f, truth := b } ∧
      Sweep.fedTrace (Sweep.liftTrace b t) = t := by
  obtain ⟨h1, h2⟩ := PreRelease.lift_safety (cfg := cfg.pre) hx hno hfire b
  refine ⟨of_unassembled h1 ?_, h2⟩
  intro p hp s hs
  suffices ∀ (t : Federation.Trace), (∀ q ∈ t, Sweep.assembly q.2 = none) →
      ∀ p ∈ Sweep.liftTrace b t, ∀ s, p.2 = .fed s → Sweep.assembly s = none from this t hno p hp s hs
  intro t ht
  induction t with
  | nil => intro p hp; cases hp
  | cons q t ih =>
    intro p hp s hs
    simp only [Sweep.liftTrace, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only [Sweep.Step.fed.injEq] at hs
      subst hs
      exact ht q List.mem_cons_self
    · exact ih (fun q' hq => ht q' (List.mem_cons_of_mem _ hq)) p hp s hs

/-- The send's admission is `PreRelease`'s: no backend read is added at the send. -/
@[req "DUR-29"]
theorem send_admits (cfg : Cfg) (honest : List Nat) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (env : Env)
    (cid : Nat) :
    admits cfg honest st T (.fed (.process i env (.send cid))) =
      PreRelease.admits cfg.pre honest st T (.fed (.process i env (.send cid))) := by
  simp [admits, assemblyOk, guardOk]

/-! ## Assembly before send, for every class -/

/-- Node `i` assembled this candidate earlier in `T`: an assembly step for its id, taken in a state where a
resident with the same id, transaction and pair passed its class's check against the reads of that state and the
kernel's own package test. `T₁` is the history before that step. -/
def Assembled (cfg : Cfg) (r : Rules) (T : Sweep.Trace) (i : Nat) (c : Cand) : Prop :=
  ∃ T₁ T₂ st env d, T = T₂ ++ (st, .fed (.process i env (.packageAccepted c.id))) :: T₁ ∧
    d ∈ (st.fed.worlds i).node.cands ∧ d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧
    checkOf cfg st T₁ i d = true ∧ due r env (st.fed.worlds i).node d = true ∧
    releaseAuthorized r (st.fed.worlds i).node d = true ∧ d.released = true ∧
    heldQuorum (st.fed.worlds i).node.t d = true

theorem Assembled.cons {cfg : Cfg} {r : Rules} {T : Sweep.Trace} {i : Nat} {c : Cand} (x : Sweep.State × Sweep.Step)
    (h : Assembled cfg r T i c) : Assembled cfg r (x :: T) i c := by
  obtain ⟨T₁, T₂, st, env, d, rfl, rest⟩ := h
  exact ⟨T₁, x :: T₂, st, env, d, rfl, rest⟩

theorem Assembled.congr {cfg : Cfg} {r : Rules} {T : Sweep.Trace} {i : Nat} {c c' : Cand}
    (h : Assembled cfg r T i c) (h1 : c'.id = c.id) (h2 : c'.tx = c.tx) (h3 : c'.pair = c.pair) :
    Assembled cfg r T i c' := by
  obtain ⟨T₁, T₂, st, env, d, hT, hd, e1, e2, e3, rest⟩ := h
  exact ⟨T₁, T₂, st, env, d, by rw [h1]; exact hT, hd, e1.trans h1.symm, e2.trans h2.symm,
    e3.trans h3.symm, rest⟩

/-- A standing package test on any resident of an honest node was earned in this trace: some earlier assembly
step passed that resident's class check against that step's own reads, and the kernel's package test, on a
resident with the same id, transaction and pair. -/
@[req "SPN-39"]
theorem assembled_of_packageOk {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.fed.worlds i).node.cands, c.packageOk = true → Assembled cfg r T i c := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | next s ha _ ih =>
    intro c hc hp
    cases s with
    | chain b => exact (ih c hc hp).cons _
    | observe j b => exact (ih c hc hp).cons _
    | fed s =>
      simp only [Sweep.apply] at hc
      cases hact : Federation.actor s with
      | none =>
        rw [Federation.apply_no_actor r _ s hact i] at hc
        exact (ih c hc hp).cons _
      | some a =>
        obtain ⟨j, env, e⟩ := a
        rw [Federation.apply_of_actor r _ s hact i] at hc
        split at hc
        · rename_i hij
          subst hij
          rcases Sweep.packageOk_origin r env _ e hc hp with
            ⟨d, hd, h1, h2, h3, hpd⟩ | ⟨rfl, d, hd, h1, h2, h3, hdue, hauth, hrel, hq⟩
          · exact ((ih d hd hpd).congr h1.symm h2.symm h3.symm).cons _
          · have hs := Sweep.actor_packageAccepted hact
            subst hs
            simp only [admits, assemblyOk, guardOk, Bool.and_eq_true, List.all_eq_true] at ha
            have hck := ha.2 d hd
            simp only [h1, beq_self_eq_true, Bool.not_true, Bool.false_or] at hck
            exact ⟨_, [], _, env, d, rfl, hd, h1, h2, h3, hck, hdue, hauth, hrel, hq⟩
        · exact (ih c hc hp).cons _

/-- `DUR-29`'s order on every submission, of every class: what a send submits is a resident under that id whose
package test is standing and which the send's own state re-authorizes — due and released by `DUR-10`'s gate, read
at that step and not at the assembly — and whose package test was earned at an earlier assembly that passed its
class's check (`Assembly.Assembled`). -/
@[req "DUR-29"]
theorem submitted_in_order {cfg : Cfg} {r : Rules} (hr : r.reauth = .beforeSend) {honest : List Nat}
    {T : Sweep.Trace} {st : Sweep.State} (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {cid x : Nat}
    (ha : admits cfg honest st T (.fed (.process i env (.send cid))) = true)
    (hs : x ∈ Sweep.submits r st (.fed (.process i env (.send cid)))) :
    ∃ c ∈ (st.fed.worlds i).node.cands, c.id = cid ∧ c.tx.id = x ∧ c.packageOk = true ∧
      due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧ Assembled cfg r T i c := by
  have ha' : PreRelease.admits cfg.pre honest st T (.fed (.process i env (.send cid))) = true := by
    rw [← send_admits]; exact ha
  obtain ⟨c, hc, hid, hx', hp, hdue, hauth, -⟩ :=
    PreRelease.submitted_in_order hr (to_prerelease hx) ha' hs
  have hi : i ∈ honest := by
    simp only [PreRelease.admits, Sweep.admits, Federation.admits, Bool.and_eq_true,
      List.contains_iff_mem] at ha'
    exact ha'.1.1.1
  exact ⟨c, hc, hid, hx', hp, hdue, hauth, assembled_of_packageOk hx hi c hc hp⟩

/-! ## A ladder rung's assembly (`DUR-28`, `DUR-29`) -/

/-- The assembly of rung `m` of an Escape's ladder, over `BtcPolicy.Ladder`'s per-pass read `rd` at instant `b`
with possession `R`: `t` distinct signers on every input of that rung's own transaction, its coverage at the
ladder's pass and the floor at its exact finalized vsize, its ancestry as a replacement of the resident lower
rung if there is one (`Ladder.replacesOf`, `DUR-29`: "A resident lower rung is replaced by RBF"), and the
backend's verdict. -/
@[req "DUR-29"]
def rungCheck (cfg : Cfg) (rd : Ladder.Read) (b : Backend) (c : Cand) (R : List Authority.Sig) (m : Nat) : Bool :=
  match (Ladder.txs rd c)[m]? with
  | none => false
  | some tx =>
    Authority.quorum cfg.pre.sweep.keys rd.reg.t tx R &&
      (Ladder.coveredTx cfg.pre.sweep (Ladder.passAt cfg.pre.sweep rd b) tx &&
        PreRelease.feeOk cfg.pre (exactVsize cfg tx) tx) &&
      Ladder.ancestryTx cfg.pre.sweep rd.A b tx
        (Ladder.replacesOf (Ladder.txs rd c) (PreRelease.membership b (Ladder.txs rd c)) m) &&
      packageOk cfg b tx

/-- What an admitted rung assembly established: its own transaction's quorum, so no other rung's records count
(`Ladder.quorum_own_rung`), its coverage and exact fee, and `WTC-24`'s admitted verdict over the resident lower
rung it replaces, which under `WTC-25` it must spend exactly the same ordered outpoints as. -/
@[req "DUR-29"]
theorem rungCheck_sound {cfg : Cfg} {rd : Ladder.Read} {b : Backend} {c : Cand} {R : List Authority.Sig} {m : Nat}
    (h : rungCheck cfg rd b c R m = true) :
    ∃ tx, (Ladder.txs rd c)[m]? = some tx ∧ Authority.quorum cfg.pre.sweep.keys rd.reg.t tx R = true ∧
      Ladder.coveredTx cfg.pre.sweep (Ladder.passAt cfg.pre.sweep rd b) tx = true ∧
      PreRelease.feeOk cfg.pre (exactVsize cfg tx) tx = true ∧
      (∃ anc, Package.validate cfg.pre.sweep.ancestry cfg.pre.sweep.creator (Sweep.snapshot rd.A b) b.mempool
        rd.A (Sweep.candidateOf tx)
        (Ladder.replacesOf (Ladder.txs rd c) (PreRelease.membership b (Ladder.txs rd c)) m) = .admitted anc) ∧
      packageOk cfg b tx = true := by
  unfold rungCheck at h
  split at h
  · cases h
  · rename_i tx htx
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hq, hc, hf⟩, ha⟩, hk⟩ := h
    refine ⟨tx, htx, hq, hc, hf, ?_, hk⟩
    unfold Ladder.ancestryTx at ha
    revert ha
    cases Package.validate _ _ _ _ _ _ _ with
    | admitted anc => exact fun _ => ⟨anc, rfl⟩
    | refused _ => intro ha; cases ha

/-- On a ladder of the base alone, the base rung's assembly is the composed Escape's check over the same reads. -/
@[req "DUR-29"]
theorem rungCheck_base (cfg : Cfg) (rd : Ladder.Read) (C : List Nat) (b : Backend) (c : Cand)
    (R : List Authority.Sig) (h : ∀ k, rd.rungs k = []) (hc : c.isEscape = true) :
    rungCheck cfg rd b c R 0 = checkAt cfg rd.A C rd.reg R b c := by
  have hcls : classOf c = .escape := by simp [classOf, hc]
  have ht : target C b c = none := by simp [target, hcls]
  have hl : Ladder.txs rd c = [c.tx] := by simp [Ladder.txs, h]
  have hp := Ladder.passAt_no_rungs cfg.pre.sweep rd b h
  simp only [rungCheck, hl, List.getElem?_cons_zero, checkAt, exactOk, hcls, Sweep.possessed, Sweep.covered,
    Ladder.coveredTx, hp, Ladder.ancestryTx, ancestry, ht, Ladder.replacesOf, List.range_zero,
    List.find?_nil, Option.bind_none]

end BtcPolicy.Assembly
