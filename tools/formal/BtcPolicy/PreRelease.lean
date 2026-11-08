import BtcPolicy.Sweep
import BtcPolicy.Witness
import BtcPolicy.Silence
/-! `DUR-21`'s check before release, for the base Escape, in the composed sweep. The kernel's fire pass
withholds an Escape-role candidate whose id its step's verdict lists (`Kernel.Env.withholds`), and with
nothing listed it is the release it was before (`Kernel.firePass_nothing_withheld`). This module computes
that verdict from one node's observation and history and requires every fire pass of a composed run to
carry it. There is no second release machine: the state, the steps and the step function are
`BtcPolicy.Sweep`'s, and only the admission test is refined.

**The attempt.** `PreRelease.attempt` gathers, for one candidate at one node, the data `DUR-21` names in
its order: the ladder's rung transactions, here the base alone, the registered candidate's transaction;
one batched mempool read over the ladder (`PreRelease.membership`), which is also the read the pass
excludes resident rungs by (`PreRelease.pass_resident`); `DUR-22`'s sweep environment, the pass
(`Sweep.passAt`) and its protected value (`Coverage.denominator`); the rung's maximum finalized vsize
(`Witness.maxVsize` over the transaction's legacy length, its input count, this node's threshold and the
federation's key count); `DUR-23`'s fee and `DUR-24`'s coverage at that vsize; `DUR-26`'s selection, one
rung here; and `WTC-24`'s ancestry for the selected rung (`Sweep.ancestryOk`). `PreRelease.Attempt.verdict`
reads them in that order and names the first that fails; ancestry is read only after a rung is selected
(`PreRelease.ancestry_after_selection`). No possession enters: `DUR-28`'s quorum is assembly's, and
requiring it before the release that creates it would be circular (`PreRelease.verdict_reads_no_possession`).

**The observation.** The verdict reads the node's latest observation, `Sweep.State.obs`, which is an
instant the truth has been, now or earlier: observation delay is kept, and nothing says the instant is
current. A fire pass does not consume it, unlike an assembly. Reading the same instant at a later pass is
what a fresh `Sweep.Step.observe` of that instant would give, since an instant once the truth stays among
those a node may read. With no observation every Escape fails (`PreRelease.Stage.noRead`), which is
`DUR-32`'s "no preflight context".

**The refined run.** `PreRelease.Execution` is `Sweep.Execution` with one more conjunct on a fire pass: its
verdict is `PreRelease.failing` at the state and history it is taken in (`PreRelease.releaseOk`).
`PreRelease.to_sweep` is the restriction to the old abstraction, so every sweep, federation and kernel
result applies; `PreRelease.execution_iff` says the refinement is exactly that conjunct.
`Sweep.lift_unassembled` stays a result about `Sweep` alone: a federation history that releases an Escape
whatever the backend is a sweep history and in general not a refined one
(`Exhibits.PreRelease.bypass_not_refined`). Its refined form is `PreRelease.lift_safety`: a history with no
assembly whose fire passes withhold every Escape lifts over every backend, so arming, freezing, hot
releases, claw-backs, Lockdown, extraction and forgery wait on no Escape. `PreRelease.fire_available`: a
fire pass carrying the computed verdict is always admitted, so no Escape's failure blocks a pass.

**What it establishes.** `PreRelease.release_origin`: every row an honest fire pass adds to the partial
inventory is a candidate's that pass releases, on that candidate's transaction at the row's input, and an
Escape-role candidate's only after its verdict at that pass released rung 0. `PreRelease.inventory_provenance`:
every row of the inventory names an extracted signer or was so emitted (`PreRelease.Emitted`), and
`PreRelease.no_premature_exposure` drops the first alternative for a signer outside the cumulative extracted
set. `PreRelease.refusal_preserves` and `PreRelease.authority_persists` are the failure side.

**Not modelled.** The ladder beyond the base: here the base is selected or nothing is. `BtcPolicy.Ladder`
is the check over the optional ladder, with `DUR-26`'s bump target and `needed`, the latch's
`max(choice, current latch)` and a resident lower rung's replacement, and over a ladder of the base alone
its verdict is this module's (`Ladder.verdict_one_rung`). A resident txid outside the ladder in the batched read: the read
here is a lookup per rung and cannot return one. `DUR-25`'s re-evaluation at the exact finalized vsize
stays at assembly, where `Sweep.check` reads coverage and ancestry again; the fee floor is not read there.
The legacy length and each outpoint's value are per-txid model parameters, as in `Sweep.Book`. `DUR-22`'s
"Empty is an error" is read as a zero protected value. -/

namespace BtcPolicy.PreRelease
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Federation (Fed fanout outbox others mem_outbox mem_fanout node_id parts_grows
  extracted_grows advance)
open BtcPolicy.Coverage (Coin Outpoint)

/-- The sweep's parameters, `CHN-34`'s legacy length `B` of each transaction by txid, and the sealed
`escape_feerate_floor`. -/
structure Cfg where
  sweep : Sweep.Cfg
  legacyLen : Nat → Nat
  floor : Nat

/-- The step of `DUR-21`'s order at which an attempt stops. `latched` is `DUR-26`'s "if selected is not
admissible: fail" when some rung is admissible, which only a ladder above the base reaches
(`Ladder.Attempt.verdict`). -/
inductive Stage
  | noRead | ladder | empty | vsize | fee | coverage | latched | ancestry
  deriving DecidableEq, Repr

/-- The rung released, or the step that failed. -/
inductive Verdict
  | release (rung : Nat)
  | fail (s : Stage)
  deriving DecidableEq, Repr

def Verdict.ok : Verdict → Bool
  | .release _ => true
  | .fail _ => false

/-! ## The attempt, in `DUR-21`'s order -/

/-- The ladder's rung transactions: the base alone, the registered candidate's own transaction. -/
@[req "DUR-21"]
def ladder (c : Cand) : List Tx := [c.tx]

/-- "One batched mempool read over the whole ladder finds which rung, if any, is resident". -/
@[req "DUR-21"]
def membership (b : Backend) (l : List Tx) : List Bool :=
  l.map fun tx => (b.mempool.lookup tx.id).isSome

/-- The transaction's inputs at their `witness_utxo` values. -/
def totalIn (bk : Book) (tx : Tx) : Nat := (tx.inputs.map bk.value).sum

/-- The sum of the transaction's outputs. -/
def outSum (bk : Book) (tx : Tx) : Nat := ((bk.outputs tx.id).map bk.value).sum

/-- `CHN-34`'s maximum finalized vsize of a rung at this node's threshold. -/
@[req "DUR-25"]
def maxVsize (cfg : Cfg) (t : Nat) (tx : Tx) : Nat :=
  Witness.maxVsize (cfg.legacyLen tx.id) tx.inputs.length t cfg.sweep.keys.length

/-- `DUR-23` at a vsize: the fee is what the inputs pay beyond the outputs, and it reaches the floor
times the vsize, "compared in arithmetic that cannot overflow, never as a truncated integer feerate". -/
@[req "DUR-23"]
def feeOk (cfg : Cfg) (vs : Nat) (tx : Tx) : Bool :=
  decide (outSum cfg.sweep.book tx ≤ totalIn cfg.sweep.book tx) &&
    decide (cfg.floor * vs ≤ totalIn cfg.sweep.book tx - outSum cfg.sweep.book tx)

/-- `DUR-26` over a ladder of one rung: the base if it is admissible, and otherwise no rung. -/
@[req "DUR-26"]
def selectOne (admissible : Bool) : Option Nat := if admissible then some 0 else none

/-- What one node's attempt for one candidate reads, each value computed from the ones before it. -/
structure Attempt where
  base : Tx
  ladder : List Tx
  resident : List Bool
  pass : Coverage.Pass
  protectedValue : Nat
  vsize : Nat
  fee : Bool
  covered : Bool
  rung : Option Nat
  ancestry : Bool
  deriving DecidableEq, Repr

/-- The attempt at one instant `b`, with this node's authorized set `A` and registry `n`. -/
@[req "DUR-21"]
def attempt (cfg : Cfg) (A : List Nat) (n : Node) (b : Backend) (c : Cand) : Attempt :=
  let p := passAt cfg.sweep A n b
  let vs := maxVsize cfg n.t c.tx
  let f := feeOk cfg vs c.tx
  let cv := covered cfg.sweep A n b c
  { base := c.tx, ladder := ladder c, resident := membership b (ladder c), pass := p,
    protectedValue :=
      Coverage.denominator cfg.sweep.denominator cfg.sweep.external p (escapeOf cfg.sweep.book c.tx),
    vsize := vs, fee := f, covered := cv, rung := selectOne (f && cv),
    ancestry := ancestryOk cfg.sweep A b c }

/-- `DUR-21`'s order: the ladder exists; the environment is computed, and "Empty is an error"
(`DUR-22`); the vsize is positive; the rung is selected among the admissible; its ancestry is
validated; and only then is it released. -/
@[req "DUR-21"]
def Attempt.verdict (a : Attempt) : Verdict :=
  if a.ladder.isEmpty then .fail .ladder
  else if a.protectedValue == 0 then .fail .empty
  else if a.vsize == 0 then .fail .vsize
  else match a.rung with
    | none => .fail (if a.fee then .coverage else .fee)
    | some k => if a.ancestry then .release k else .fail .ancestry

/-- The verdict on one candidate at one node, from its latest observation, if any. -/
@[req "DUR-21"]
def verdict (cfg : Cfg) (A : List Nat) (n : Node) : Option Backend → Cand → Verdict
  | none, _ => .fail .noRead
  | some b, c => (attempt cfg A n b c).verdict

/-! ## What the verdict establishes -/

theorem maxVsize_pos (cfg : Cfg) (t : Nat) (tx : Tx) : maxVsize cfg t tx ≠ 0 := by
  unfold maxVsize Witness.maxVsize Witness.maxWeight
  omega

/-- The verdict releases the base exactly when there is an observation and at it the protected value
is not empty, the fee reaches the floor at the maximum finalized vsize, coverage holds against the
protected value, and the base's ancestry is admitted. No other rung is ever released here. -/
@[req "DUR-21"]
theorem verdict_release_iff (cfg : Cfg) (A : List Nat) (n : Node) (ob : Option Backend) (c : Cand) :
    verdict cfg A n ob c = .release 0 ↔ ∃ b, ob = some b ∧
      Coverage.denominator cfg.sweep.denominator cfg.sweep.external (passAt cfg.sweep A n b)
        (escapeOf cfg.sweep.book c.tx) ≠ 0 ∧
      feeOk cfg (maxVsize cfg n.t c.tx) c.tx = true ∧ covered cfg.sweep A n b c = true ∧
      ancestryOk cfg.sweep A b c = true := by
  cases ob with
  | none => simp [verdict]
  | some b =>
    have hv := maxVsize_pos cfg n.t c.tx
    simp only [verdict, Attempt.verdict, attempt, ladder, selectOne, List.isEmpty_cons,
      Bool.false_eq_true, ↓reduceIte, Option.some.injEq, exists_eq_left']
    by_cases h0 : Coverage.denominator cfg.sweep.denominator cfg.sweep.external (passAt cfg.sweep A n b)
        (escapeOf cfg.sweep.book c.tx) = 0
    · simp [h0]
    · have hv' : (maxVsize cfg n.t c.tx == 0) = false := by simpa using hv
      simp only [h0, hv', beq_iff_eq, ↓reduceIte, Bool.false_eq_true, ne_eq, not_false_eq_true,
        true_and]
      by_cases hf : feeOk cfg (maxVsize cfg n.t c.tx) c.tx = true <;>
        by_cases hc : covered cfg.sweep A n b c = true <;>
        by_cases ha : ancestryOk cfg.sweep A b c = true <;> simp_all

theorem verdict_ok_iff (cfg : Cfg) (A : List Nat) (n : Node) (ob : Option Backend) (c : Cand) :
    (verdict cfg A n ob c).ok = true ↔ verdict cfg A n ob c = .release 0 := by
  constructor
  · intro h
    cases ob with
    | none => simp [verdict, Verdict.ok] at h
    | some b =>
      revert h
      simp only [verdict, Attempt.verdict, attempt, selectOne]
      repeat' split
      all_goals simp_all [Verdict.ok]
  · intro h; rw [h]; rfl

/-- Ancestry is the last step: an attempt that fails there had its rung selected, the fee and the
coverage both passing at the maximum finalized vsize. -/
@[req "DUR-21"]
theorem ancestry_after_selection (cfg : Cfg) (A : List Nat) (n : Node) (b : Backend) (c : Cand)
    (h : verdict cfg A n (some b) c = .fail .ancestry) :
    feeOk cfg (maxVsize cfg n.t c.tx) c.tx = true ∧ covered cfg.sweep A n b c = true ∧
      ancestryOk cfg.sweep A b c = false := by
  have hv := maxVsize_pos cfg n.t c.tx
  simp only [verdict, Attempt.verdict, attempt, selectOne, ladder, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hv] at h
  by_cases h0 : Coverage.denominator cfg.sweep.denominator cfg.sweep.external (passAt cfg.sweep A n b)
      (escapeOf cfg.sweep.book c.tx) = 0 <;>
    by_cases hf : feeOk cfg (maxVsize cfg n.t c.tx) c.tx = true <;>
    by_cases hc : covered cfg.sweep A n b c = true <;>
    by_cases ha : ancestryOk cfg.sweep A b c = true <;> simp_all

/-- The pass excludes the outputs of exactly the selected Escapes the batched membership read finds
resident. -/
@[req "DUR-22"]
theorem pass_resident (cfg : Sweep.Cfg) (A : List Nat) (n : Node) (b : Backend) :
    (passAt cfg A n b).residentRungs =
      ((selectedEscapes n).filter fun d => (membership b (ladder d)).any id).flatMap
        fun d => cfg.book.outputs d.tx.id := by
  simp [passAt, VaultUnspent.passOf, membership, ladder]

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) (l : List α) :
    (l.map f).flatMap g = l.flatMap fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The verdict reads no possession: changing what any candidate's held set holds, the one being
judged included, changes nothing. -/
@[req "DUR-21"]
theorem verdict_reads_no_possession (cfg : Cfg) (A : List Nat) (n : Node) (ob : Option Backend)
    (c : Cand) (f : Cand → List Nat) (h : List Nat) :
    verdict cfg A { n with cands := n.cands.map fun d => { d with heldSigners := f d } } ob
        { c with heldSigners := h } = verdict cfg A n ob c := by
  have hsel : selectedEscapes { n with cands := n.cands.map fun d => { d with heldSigners := f d } } =
      (selectedEscapes n).map fun d => { d with heldSigners := f d } := by
    simp only [selectedEscapes, List.filter_map]
    congr 1
  cases ob with
  | none => rfl
  | some b =>
    simp only [verdict, attempt, passAt, covered, ancestryOk, candidateOf, ladder, membership,
      maxVsize, feeOk, hsel, List.map_map, List.filter_map, Function.comp_def, flatMap_map']

/-! ## The refined run -/

/-- The ids of the Escape-role candidates at node `i` whose verdict, at the state and history the step is
taken in, is not a release. -/
@[req "DUR-21"]
def failing (cfg : Cfg) (st : State) (T : Trace) (i : Nat) : List Nat :=
  ((st.fed.worlds i).node.cands.filter fun c =>
    c.isEscape && !(verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c).ok).map (·.id)

/-- Each Escape is judged on its own: an id is withheld when some Escape-role candidate with that id has
its own verdict fail, and no other candidate's verdict enters. -/
@[req "DUR-21"]
theorem mem_failing (cfg : Cfg) (st : State) (T : Trace) (i k : Nat) :
    k ∈ failing cfg st T i ↔ ∃ c ∈ (st.fed.worlds i).node.cands, c.isEscape = true ∧ c.id = k ∧
      verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c ≠ .release 0 := by
  simp only [failing, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨c, ⟨hc, he, hv⟩, rfl⟩
    refine ⟨c, hc, he, rfl, fun h => ?_⟩
    rw [← verdict_ok_iff] at h
    simp [h] at hv
  · rintro ⟨c, hc, he, rfl, hv⟩
    refine ⟨c, ⟨hc, he, ?_⟩, rfl⟩
    cases h : (verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c).ok
    · rfl
    · exact absurd ((verdict_ok_iff ..).1 h) hv

/-- With no observation every Escape-role candidate's id is withheld. -/
def escapeIds (n : Node) : List Nat := (n.cands.filter (·.isEscape)).map (·.id)

theorem failing_noRead (cfg : Cfg) {st : State} (T : Trace) {i : Nat} (h : st.obs i = none) :
    failing cfg st T i = escapeIds (st.fed.worlds i).node := by
  simp [failing, escapeIds, h, verdict, Verdict.ok]

/-- A fire pass carries the verdict computed at its own state and history. Every other step passes. -/
@[req "DUR-21"]
def releaseOk (cfg : Cfg) (st : State) (T : Trace) : Step → Bool
  | .fed (.process i env .firePass) => env.withheld == failing cfg st T i
  | _ => true

/-- The sweep's admission and the release conjunct. -/
def admits (cfg : Cfg) (honest : List Nat) (st : State) (T : Trace) (s : Step) : Bool :=
  Sweep.admits cfg.sweep honest st T s && releaseOk cfg st T s

/-- A reachable refined execution: `Sweep.Execution` whose fire passes carry the computed verdict. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Sweep.Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (ha : admits cfg honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (Sweep.apply r st s)

/-! ## The relation to the old abstraction -/

/-- Every refined execution is a sweep execution with the same trace and state. -/
@[req "DUR-21"]
theorem to_sweep {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) : Sweep.Execution cfg.sweep r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | next s ha _ ih =>
    simp only [admits, Bool.and_eq_true] at ha
    exact .next s ha.1 ih

/-- Each step of a trace carries the computed verdict at its own state and history. -/
def Checked (cfg : Cfg) : Trace → Prop
  | [] => True
  | (st, s) :: T => releaseOk cfg st T s = true ∧ Checked cfg T

/-- The refinement is exactly the release conjunct: a sweep execution is a refined one if and only if
each of its fire passes carries the computed verdict. -/
@[req "DUR-21"]
theorem execution_iff {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State} :
    Execution cfg r honest T st ↔ Sweep.Execution cfg.sweep r honest T st ∧ Checked cfg T := by
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

/-- Forgetting the backend leaves a federation execution. -/
theorem fed_execution {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) : Federation.Execution r honest (fedTrace T) st.fed :=
  Sweep.fed_execution (to_sweep hx)

/-- `DUR-11` on every refined execution. -/
@[req "DUR-11"]
theorem armed_freezes_hot {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) : Kernel.Inv (st.fed.worlds i) :=
  Sweep.armed_freezes_hot (to_sweep hx) hi

/-- `DUR-29`'s order on every submission of a refined execution, as `Sweep.submitted_in_order`. -/
@[req "DUR-29"]
theorem submitted_in_order {cfg : Cfg} {r : Rules} (hr : r.reauth = .beforeSend) {honest : List Nat}
    {T : Trace} {st : State} (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {cid x : Nat}
    (ha : admits cfg honest st T (.fed (.process i env (.send cid))) = true)
    (hs : x ∈ submits r st (.fed (.process i env (.send cid)))) :
    ∃ c ∈ (st.fed.worlds i).node.cands, c.id = cid ∧ c.tx.id = x ∧ c.packageOk = true ∧
      due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      (c.isEscape = true → Assembled cfg.sweep r T i c) := by
  simp only [admits, Bool.and_eq_true] at ha
  exact Sweep.submitted_in_order hr (to_sweep hx) ha.1 hs

/-- No Escape's verdict blocks a fire pass: at every state and history, an honest node's fire pass
carrying the computed verdict is admitted, whatever the environment's other fields. -/
@[req "DUR-21"]
theorem fire_available (cfg : Cfg) (honest : List Nat) (st : State) (T : Trace) {i : Nat}
    (hi : i ∈ honest) (env : Env) :
    admits cfg honest st T (.fed (.process i { env with withheld := failing cfg st T i } .firePass)) =
      true := by
  simp [admits, Sweep.admits, Federation.admits, Federation.ownEvent, assemblyOk, releaseOk, hi]

theorem releaseOk_lift (cfg : Cfg) {f : Fed} (b : Backend) (T : Trace) {s : Federation.Step}
    (hfire : ∀ i env, s = .process i env .firePass → env.withheld = escapeIds (f.worlds i).node) :
    releaseOk cfg { fed := f, truth := b } T (.fed s) = true := by
  cases s with
  | process i env e =>
    cases e with
    | firePass =>
      simp [releaseOk, hfire i env rfl, failing_noRead cfg (st := { fed := f, truth := b }) T rfl]
    | _ => rfl
  | _ => rfl

/-- Arming and freezing need no Escape decision. Every federation history with no assembly whose fire
passes withhold every Escape-role candidate, the verdict a node with no observation reaches, is a refined
execution over every backend instant: the receipts that arm, the holder decisions that freeze every hot
candidate, every hot release and claw-back release, Lockdown, extraction and forgery are in such a
history. `Sweep.lift_unassembled` lifts more, since there an Escape releases with no backend check; that
is the old abstraction's result and not this one's. -/
@[req "DUR-19"]
theorem lift_safety {cfg : Cfg} {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) (hno : ∀ p ∈ t, assembly p.2 = none)
    (hfire : ∀ p ∈ t, ∀ i env, p.2 = .process i env .firePass →
      env.withheld = escapeIds (p.1.worlds i).node)
    (b : Backend) :
    Execution cfg r honest (liftTrace b t) { fed := f, truth := b } ∧ fedTrace (liftTrace b t) = t := by
  refine ⟨?_, fedTrace_lift b t⟩
  induction hx with
  | init f h => exact .init _ ⟨h, rfl, fun _ => rfl⟩
  | @next t f s ha _ ih =>
    have hs : assembly s = none := hno _ List.mem_cons_self
    have hrel := releaseOk_lift cfg (f := f) b (liftTrace b t) (s := s)
      (fun i env he => hfire _ List.mem_cons_self i env he)
    have hx' := Execution.next (cfg := cfg) (.fed s)
      (by simp [admits, Sweep.admits, ha, assemblyOk_of_none cfg.sweep _ _ hs, hrel])
      (ih (fun p hp => hno p (List.mem_cons_of_mem _ hp))
        (fun p hp => hfire p (List.mem_cons_of_mem _ hp)))
    simpa [Sweep.apply, hs] using hx'

/-! ## Release origin -/

theorem fire_effects (r : Rules) (env : Env) (w : World) :
    (step r env w .firePass).2 = (firePass r env w.node).2 := rfl

/-- `DUR-21` at the release boundary: every row an honest node's fire pass adds to the partial inventory
is the partial of a candidate that pass releases, over that candidate's transaction at the row's input,
under its commitment, by this node; and when that candidate is registered in the Escape role, its verdict
at that pass, read from this node's observation and history, released rung 0. Proved from the step and its
admission, with no premise that the release was authorized. -/
@[req "DUR-21"]
theorem release_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {i : Nat}
    {env : Env} (ha : admits cfg honest st T (.fed (.process i env .firePass)) = true) {x : Exp}
    (hx : x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .firePass).2) :
    ∃ c ∈ (st.fed.worlds i).node.cands, x.signer = (st.fed.worlds i).node.id ∧ x.cid = c.id ∧
      x.msg = sighash c.tx x.input ∧ x.hot = c.hot ∧ env.withholds c = false ∧ c.released = false ∧
      due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      (c.isEscape = true →
        verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c = .release 0) := by
  simp only [admits, Bool.and_eq_true] at ha
  have hw : env.withheld = failing cfg st T i := by simpa [releaseOk] using ha.2
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
  obtain ⟨hsig, hey⟩ := mem_outbox hy
  rw [fire_effects] at hey
  obtain ⟨c, hc, hdue, hauth, hnw, hrel, heq⟩ := firePass_effect r env _ hey
  simp only [Effect.queuePartial.injEq] at heq
  obtain ⟨hm, hi0, hh, hcid⟩ := heq
  have hesc : c.isEscape = true →
      verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c = .release 0 := by
    intro he
    cases hv : (verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c).ok
    · have hk := (mem_failing cfg st T i c.id).2
        ⟨c, hc, he, rfl, fun h => by rw [h] at hv; simp [Verdict.ok] at hv⟩
      rw [← hw] at hk
      simp [Env.withholds, he, hk] at hnw
    · exact (verdict_ok_iff ..).1 hv
  rcases List.mem_cons.1 hxy with rfl | ho
  · exact ⟨c, hc, hsig, hcid, by rw [hm, hi0], hh, hnw, hrel, hdue, hauth, hesc⟩
  · simp only [others] at ho
    split at ho
    · rename_i d hd
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 ho
      have hdm := List.find?_some hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hdm
      have htx : d.tx.id = c.tx.id := by
        have := hdm.2.trans hm
        simpa [sighash] using this
      refine ⟨c, hc, hsig, hcid, ?_, hh, hnw, hrel, hdue, hauth, hesc⟩
      simp [sighash, htx]
    · simp at ho

/-- Node `x.signer` emitted row `x` at a fire pass of the trace, `T₁` the history before it, from a
candidate under the row's commitment, over that candidate's transaction at the row's input, whose
verdict there released rung 0 when it is registered in the Escape role. -/
def Emitted (cfg : Cfg) (r : Rules) (T : Trace) (x : Exp) : Prop :=
  ∃ T₁ T₂ st env, T = T₂ ++ (st, .fed (.process x.signer env .firePass)) :: T₁ ∧
    x ∈ fanout (st.fed.worlds x.signer) (step r env (st.fed.worlds x.signer) .firePass).2 ∧
    ∃ c ∈ (st.fed.worlds x.signer).node.cands, x.cid = c.id ∧ x.msg = sighash c.tx x.input ∧
      (c.isEscape = true →
        verdict cfg (authorizedAt st T₁ x.signer) (st.fed.worlds x.signer).node (st.obs x.signer) c =
          .release 0)

theorem Emitted.cons {cfg : Cfg} {r : Rules} {T : Trace} {x : Exp} (y : State × Step)
    (h : Emitted cfg r T x) : Emitted cfg r (y :: T) x := by
  obtain ⟨T₁, T₂, st, env, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, env, rfl, rest⟩

/-- A kernel step queues partials only at a fire pass. -/
theorem queue_only_firePass {r : Rules} {env : Env} {w : World} {e : Event} {m : Sighash}
    {k : Nat} {h : Bool} {c : Nat} (he : Effect.queuePartial m k h c ∈ (step r env w e).2) :
    e = .firePass := by
  cases e <;> simp only [step] at he ⊢ <;> try simp_all
  rename_i cid
  simp only [send] at he
  split at he
  · simp at he
  · split at he <;> simp at he

/-- The partial inventory of a refined execution, row by row: a row names a signer whose key is in the
cumulative extracted set, or an honest signer that emitted it at a fire pass of the trace past that pass's
verdict (`PreRelease.Emitted`). Both may hold: a key extracted from an honest node leaves the node on the
honest list. -/
@[req "DUR-21"]
theorem inventory_provenance {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {x : Exp} (hm : x ∈ st.fed.parts) :
    x.signer ∈ st.fed.extracted ∨ (x.signer ∈ honest ∧ Emitted cfg r T x) := by
  induction hx with
  | init st h => rw [h.1.2.1] at hm; cases hm
  | @next T st s ha hx ih =>
    have lift (hm : x ∈ st.fed.parts) :
        x.signer ∈ (Sweep.apply r st s).fed.extracted ∨
          (x.signer ∈ honest ∧ Emitted cfg r ((st, s) :: T) x) := by
      rcases ih hm with h | ⟨hh, he⟩
      · refine .inl ?_
        cases s with
        | fed s => exact extracted_grows r _ s h
        | chain b => exact h
        | observe j b => exact h
      · exact .inr ⟨hh, he.cons _⟩
    cases s with
    | chain b => exact lift hm
    | observe j b => exact lift hm
    | fed s =>
      have hfx := fed_execution hx
      cases s with
      | process i env e =>
        simp only [Sweep.apply, Federation.apply, List.mem_append] at hm
        rcases hm with hm | hm
        · exact lift hm
        · have hai := ha
          simp only [admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at hai
          have hi : i ∈ honest := hai.1.1.1
          obtain ⟨y, hy, -⟩ := List.mem_flatMap.1 hm
          have he := queue_only_firePass (mem_outbox hy).2
          subst he
          have hsig := (mem_fanout hm).1
          rw [node_id hfx hi] at hsig
          subst hsig
          obtain ⟨c, hc, -, hcid, hmsg, -, -, -, -, -, hv⟩ := release_origin ha hm
          exact .inr ⟨hi, T, [], st, env, rfl, hm, c, hc, hcid, hmsg, hv⟩
      | forge y =>
        simp only [Sweep.apply, Federation.apply, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact lift hm
        · simp only [admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at ha
          exact .inl (by simpa [Sweep.apply, Federation.apply] using ha.1.1)
      | deliver i env m => exact lift (by simpa [Sweep.apply, Federation.apply, advance] using hm)
      | deliverPartial i env y => exact lift (by simpa [Sweep.apply, Federation.apply, advance] using hm)
      | unstaged i cid => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | emit i cid => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | inject m => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | extract j => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)

/-- No premature exposure: a row of the inventory whose signer's key is not in the cumulative extracted
set was emitted by that signer's honest node, and if its candidate is registered in the Escape role, past
that node's verdict at that pass. -/
@[req "DUR-21"]
theorem no_premature_exposure {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {x : Exp} (hm : x ∈ st.fed.parts)
    (hs : x.signer ∉ st.fed.extracted) : x.signer ∈ honest ∧ Emitted cfg r T x :=
  (inventory_provenance hx hm).resolve_left hs

/-! ## Failure -/

theorem fire_world (r : Rules) (st : State) (i : Nat) (env : Env) :
    (Sweep.apply r st (.fed (.process i env .firePass))).fed.worlds i =
      (step r env (st.fed.worlds i) .firePass).1 := by
  simp [Sweep.apply, Federation.apply, advance]

/-- `DUR-21`: "MUST release nothing of it and burn none of its rungs if any step fails". At an admitted
fire pass, an Escape-role candidate whose verdict does not release stays in the registry as it was, its
release cursor included, and every row the pass adds is another candidate's. -/
@[req "DUR-21"]
theorem refusal_preserves {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace}
    {i : Nat} {env : Env} (ha : admits cfg honest st T (.fed (.process i env .firePass)) = true)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands) (he : c.isEscape = true)
    (hv : verdict cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c ≠ .release 0) :
    c ∈ ((Sweep.apply r st (.fed (.process i env .firePass))).fed.worlds i).node.cands ∧
      ∀ x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .firePass).2,
        ∃ d ∈ (st.fed.worlds i).node.cands, d ≠ c ∧ x.cid = d.id ∧ x.msg = sighash d.tx x.input := by
  have ha' := ha
  simp only [admits, Bool.and_eq_true] at ha'
  have hw : env.withheld = failing cfg st T i := by simpa [releaseOk] using ha'.2
  have hwc : env.withholds c = true := by
    have hk := (mem_failing cfg st T i c.id).2 ⟨c, hc, he, rfl, hv⟩
    rw [← hw] at hk
    simp [Env.withholds, he, hk]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [fire_world]
    exact (firePass_withheld r env _ hc hwc).1
  · obtain ⟨d, hd, -, hcid, hmsg, -, hdw, -⟩ := release_origin ha hx
    exact ⟨d, hd, fun h => by subst h; simp [hwc] at hdw, hcid, hmsg⟩

/-- Earlier exposure, delivered partials and extracted keys survive every step, a failed verdict
included: the partial inventory and the extracted set only grow; and at a fire pass every node's
exposure only grows and every candidate keeps its transaction and its held set, with an earlier release
still recorded. -/
@[req "DUR-21"]
theorem authority_persists (r : Rules) (st : State) (s : Step) :
    (∀ x ∈ st.fed.parts, x ∈ (Sweep.apply r st s).fed.parts) ∧
      (∀ j ∈ st.fed.extracted, j ∈ (Sweep.apply r st s).fed.extracted) ∧
      (∀ i env, s = .fed (.process i env .firePass) → ∀ j,
        (∀ x ∈ (st.fed.worlds j).exposure, x ∈ ((Sweep.apply r st s).fed.worlds j).exposure) ∧
        ∀ c ∈ (st.fed.worlds j).node.cands, ∃ d ∈ ((Sweep.apply r st s).fed.worlds j).node.cands,
          d.id = c.id ∧ d.tx = c.tx ∧ d.heldSigners = c.heldSigners ∧
            (c.released = true → d.released = true)) := by
  refine ⟨fun x hx => ?_, fun j hj => ?_, ?_⟩
  · cases s with
    | fed s => exact parts_grows r _ s hx
    | chain b => exact hx
    | observe k b => exact hx
  · cases s with
    | fed s => exact extracted_grows r _ s hj
    | chain b => exact hj
    | observe k b => exact hj
  · rintro i env rfl j
    by_cases hj : j = i
    · subst hj
      rw [fire_world]
      exact ⟨fun x hx => List.mem_append_left _ hx,
        fun c hc => firePass_mem r env _ hc⟩
    · have hw : (Sweep.apply r st (.fed (.process i env .firePass))).fed.worlds j = st.fed.worlds j := by
        simp [Sweep.apply, Federation.apply, advance, hj]
      rw [hw]
      exact ⟨fun x hx => hx, fun c hc => ⟨c, hc, rfl, rfl, rfl, id⟩⟩

/-! ## Running a schedule -/

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg honest st T s && legal cfg r honest ((st, s) :: T) (Sweep.apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {ss : List Step} (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

/-- A schedule with each fire pass's verdict written from the state and history it is taken in. A
schedule so filled may still be refused at any other step. -/
def fill (cfg : Cfg) (r : Rules) : Trace → State → List Step → List Step
  | _, _, [] => []
  | T, st, s :: ss =>
    let s' : Step := match s with
      | .fed (.process i env .firePass) =>
        .fed (.process i { env with withheld := failing cfg st T i } .firePass)
      | s => s
    s' :: fill cfg r ((st, s') :: T) (Sweep.apply r st s') ss

/-- A Bool form of `PreRelease.Checked`, for decided runs. -/
def checks (cfg : Cfg) : Trace → Bool
  | [] => true
  | (st, s) :: T => releaseOk cfg st T s && checks cfg T

theorem checked_of_checks (cfg : Cfg) : ∀ {T : Trace}, checks cfg T = true → Checked cfg T
  | [], _ => trivial
  | (_, _) :: _, h => by
    simp only [checks, Bool.and_eq_true] at h
    exact ⟨h.1, checked_of_checks cfg h.2⟩

/-! ## What the verdict reads, against SILENCE's projection

The verdict is computed from the node's registry, but only from what `Silence.pubNode` keeps of it: the
threshold, the ids, roles and transactions of its candidates, and the ids of its selected set. The arm
bit, `T`, the selected entries' duress bits, freezes and the windows a holder decision writes are not
read. Two nodes with one projection, at one observation and one authorized set, withhold the same ids
(`PreRelease.failingAt_pub`), so a fire pass carrying the computed verdict carries the same one in both
families of a SILENCE pair, and is a step the walk already takes for every verdict
(`Silence.withholds_pubCand`). -/

/-- `PreRelease.failing` at one node's own inputs: the ids of its Escape-role candidates whose verdict at
authorized set `A` and observation `ob` is not a release. -/
@[req "DUR-21"]
def failingAt (cfg : Cfg) (A : List Nat) (n : Node) (ob : Option Backend) : List Nat :=
  (n.cands.filter fun c => c.isEscape && !(verdict cfg A n ob c).ok).map (·.id)

theorem failing_eq (cfg : Cfg) (st : State) (T : Trace) (i : Nat) :
    failing cfg st T i = failingAt cfg (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) := rfl

theorem filter_flatMap_tx {β : Type} (l : List Cand) (p : Tx → Bool) (g : Tx → List β) :
    (l.filter fun c => p c.tx).flatMap (fun c => g c.tx) = ((l.map (·.tx)).filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a.tx <;> simp [h, ih]

/-- `DUR-22`'s pass reads the selected Escapes through their transactions alone. -/
theorem passAt_congr (cfg : Sweep.Cfg) (A : List Nat) {na nb : Node} (b : Backend)
    (h : (selectedEscapes na).map (·.tx) = (selectedEscapes nb).map (·.tx)) :
    passAt cfg A na b = passAt cfg A nb b := by
  have e : ∀ n : Node, (selectedEscapes n).map (fun c => escapeOf cfg.book c.tx) =
      ((selectedEscapes n).map (·.tx)).map (escapeOf cfg.book) := by
    intro n; simp
  have f : ∀ n : Node, ((selectedEscapes n).filter fun c => (b.mempool.lookup c.tx.id).isSome).flatMap
      (fun c => cfg.book.outputs c.tx.id) = (((selectedEscapes n).map (·.tx)).filter
        fun tx => (b.mempool.lookup tx.id).isSome).flatMap fun tx => cfg.book.outputs tx.id :=
    fun n => filter_flatMap_tx _ (fun tx => (b.mempool.lookup tx.id).isSome) (fun tx => cfg.book.outputs tx.id)
  unfold passAt
  rw [e na, e nb, f na, f nb, h]

/-- The verdict reads a node only through its threshold and its selected Escapes' transactions, and a
candidate only through its transaction. -/
@[req "DUR-21"]
theorem verdict_congr (cfg : Cfg) (A : List Nat) {na nb : Node} (ob : Option Backend) {c d : Cand}
    (ht : na.t = nb.t) (hs : (selectedEscapes na).map (·.tx) = (selectedEscapes nb).map (·.tx))
    (hc : c.tx = d.tx) : verdict cfg A na ob c = verdict cfg A nb ob d := by
  cases ob with
  | none => rfl
  | some b =>
    have hp := passAt_congr cfg.sweep A b hs
    simp only [verdict, attempt, covered, ancestryOk, ladder, maxVsize, feeOk, hp, ht, hc] <;> rfl

/-- The selected Escapes' transactions are public: two nodes with one projection select the same ones. -/
theorem selected_txs_pub {r : Rules} {na nb : Node} (h : Silence.pubNode r na = Silence.pubNode r nb) :
    (selectedEscapes na).map (·.tx) = (selectedEscapes nb).map (·.tx) := by
  have key : ∀ n : Node, (selectedEscapes n).map (·.tx) =
      ((n.cands.map (Silence.pubCand r (Silence.selIds n))).filter
        fun c => c.isEscape && Silence.inSel (Silence.selIds n) c.id).map (·.tx) := by
    intro n
    simp only [selectedEscapes, List.filter_map, List.map_map, Function.comp_def,
      Silence.pubCand_isEscape, Silence.pubCand_id, Silence.pubCand_tx, Silence.inSel_selIds]
  rw [key na, key nb, Silence.pub_cands h, Silence.pub_sel h]

/-- **The verdict reads nothing the SILENCE projection erases.** Two nodes with one `Silence.pubNode`,
at one authorized set and one observation, withhold exactly the same ids. In particular a duress
family's armed node and the normal family's unarmed node, coupled as `Silence.silence` couples them,
compute one verdict, so the refinement adds no observation the walk does not already cover. -/
@[req "DUR-1"]
theorem failingAt_pub (cfg : Cfg) {r : Rules} (A : List Nat) (ob : Option Backend) {na nb : Node}
    (h : Silence.pubNode r na = Silence.pubNode r nb) : failingAt cfg A na ob = failingAt cfg A nb ob := by
  have key : ∀ n : Node, failingAt cfg A n ob = ((n.cands.map (Silence.pubCand r (Silence.selIds n))).filter
      fun c => c.isEscape && !(verdict cfg A n ob c).ok).map (·.id) := by
    intro n
    have hv : ∀ c, verdict cfg A n ob (Silence.pubCand r (Silence.selIds n) c) = verdict cfg A n ob c :=
      fun c => verdict_congr cfg A ob rfl rfl (Silence.pubCand_tx _ c)
    simp only [failingAt, List.filter_map, List.map_map, Function.comp_def, Silence.pubCand_isEscape,
      Silence.pubCand_id, hv]
  have hf : (fun c => c.isEscape && !(verdict cfg A na ob c).ok) =
      (fun c => c.isEscape && !(verdict cfg A nb ob c).ok) := by
    funext c
    rw [verdict_congr cfg A ob (Silence.pub_t h) (selected_txs_pub h) rfl]
  rw [key na, key nb, Silence.pub_cands h, hf]

/-- The same at the step: a fire pass in each of two states whose acting nodes share one projection, one
observation and one authorized set carries one computed verdict. -/
theorem failing_pub (cfg : Cfg) {r : Rules} {sa sb : State} {Ta Tb : Trace} {i : Nat}
    (h : Silence.pubNode r (sa.fed.worlds i).node = Silence.pubNode r (sb.fed.worlds i).node)
    (ho : sa.obs i = sb.obs i) (hA : authorizedAt sa Ta i = authorizedAt sb Tb i) :
    failing cfg sa Ta i = failing cfg sb Tb i := by
  rw [failing_eq, failing_eq, ho, hA, failingAt_pub cfg _ _ h]

end BtcPolicy.PreRelease
