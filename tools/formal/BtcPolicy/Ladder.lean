import BtcPolicy.PreRelease
import BtcPolicy.Cursor
import BtcPolicy.BumpTarget
/-! `DUR-21`'s check before release over the optional fee ladder, `DUR-26`'s selection, `DUR-27`'s latch and
cumulative release, and `DUR-28`'s finalization from a node's own possession. The ladder is the one
`SPN-32` signs at ingress (`Ingress.Request.rungs`), at most `Classification.maxRungs` above the base, and
optional: a vault with no ladder is the base alone, and nothing here asks for a rung. The singleton claw-back
carries no ladder and is not read here; its higher-fee replacement is a separate request under the
claw-back rules.

**The attempt.** `Ladder.attempt` is `PreRelease.attempt` with the ladder's every rung in place of the base:
the rung transactions, the base first; one batched membership read over them (`PreRelease.membership`);
`DUR-22`'s pass, which now leaves out the outputs of every resident rung of every selected Escape
(`Ladder.passAt`, which is `Sweep.passAt` when no Escape has a rung: `Ladder.passAt_no_rungs`), and its
protected value; each rung's maximum finalized vsize (`PreRelease.maxVsize`); each rung's fee
(`PreRelease.feeOk`) and coverage at that vsize and pass, whose conjunction is the rung's admissibility
(`Ladder.admissible`); `DUR-26`'s selection (`Ladder.select`); and `WTC-24`'s ancestry for the selected
rung, read as a replacement of a resident lower rung when there is one (`Ladder.replacesOf`, `DUR-29`: "A
resident lower rung is replaced by RBF"). `Ladder.Attempt.verdict` reads them in that order and returns a
`PreRelease.Verdict`: the rung released, or the step that failed, with `PreRelease.Stage.latched` for a
selection that the latch refuses.

**Selection.** `Ladder.select` is `DUR-26`'s pseudo-code over the rung count, which rungs meet `required`
at their maximum finalized vsize, which are admissible, and the current latch. `required` is
`max(target, escape_feerate_floor)` with `target` the bump target of a median reading
(`BumpTarget.target`) or `0` on an error or no reading (`Ladder.target`). The rungs' order is their fee
order, which `CHN-16`'s "a strictly greater total fee" fixes and this module takes as given:
`Ingress` does not check `CHN-16`'s relations. What is proved: a selected rung is admissible and at or
above the latch (`Ladder.select_sound`), so a higher latched rung that is no longer admissible fails the
selection rather than letting a lower rung replace it; on one rung the general rule is `DUR-26`'s first
line (`Ladder.select_one_rung`); a pressure-reading error is the zero target (`Ladder.target_none`). No
fairness, confirmation or fee-market guarantee is stated: the selected rung may pay less than `required`
(`Exhibits.Ladder.tops_out`), and nothing here says it confirms.

**Release.** `Ladder.release` is one node's fire pass for one Escape. A failed verdict leaves the latch
and the release floor as they were and releases nothing (`Ladder.release_refused`). A verdict releasing
rung `k` runs `SPN-38`'s cursor (`Cursor.pass`) with `a` the lowest admissible rung and the latch `k`;
of the interval `[F, U]` the cursor gives, the rungs released are the admissible ones
(`Ladder.release_mem`, `Ladder.refused_not_released`), which is `DUR-27`'s "a rung the node's own
predicate refused MUST be released to nobody" stated as a filter. When the admissible rungs are an
interval through `k`, which `DUR-24`'s output-side coverage and `DUR-23`'s floor give a `CHN-16` ladder,
the filter removes nothing and the release is the cursor's interval whole (`Ladder.release_interval`).
A pass that releases at least one rung advances the latch to `k` and the floor to `U + 1`. A pass that
releases nothing leaves the latch and the floor where they were: with no rung affordable, `SPN-38`'s
"release nothing and advance no release bookkeeping on this pass", read as covering the latch; with the
interval empty or every rung of it refused, the floor by "Only a pass that released at least one rung MUST
set `release_floor = U + 1`", and the latch, as a reading, with it. The
latch is monotone and below the ladder's length (`Ladder.release_latch`), and the floor never moves back
(`Ladder.release_floor`).

**One rung is the base check.** On a ladder of the base alone the verdict at latch 0 is `PreRelease.verdict`,
over every read (`Ladder.verdict_one_rung`), so `PreRelease.failingAt` is the list this module's verdict
withholds (`Ladder.failingAt_one_rung`); and from a fresh latch and floor the release is rung 0 exactly
when that verdict releases it, after which the floor is `1`, `SPN-38`'s exhaustion, and no later pass
releases anything (`Ladder.release_one_rung`, `Ladder.release_exhausted`), as the kernel's `released`
bit has it. That holds when one rung is affordable: the kernel does not model `SPN-38`'s quota.

**The run.** `Ladder.Execution` is a run of one selected Escape over the federation: each node retains its
own ladder (`Ladder.LNode`: the base's user-signature hash and the rungs above it, which first deliveries may
leave different at different nodes), its latch and floor, and the partials it stored. An honest node's
pass reads a `Ladder.Read`, an authorized set, a registry, an observation and a median reading supplied
by the step, with its own ladder in place of the read's for this Escape: the reads are the run's input,
as an observation is, and binding them to a composed run's state is the integration's (see the proof-
boundary record). Partials (`Ladder.Part`) are keyed by the rung's txid, its user-signature hash, the
input and the signer. A node stores a delivered partial only under `NCH-24`'s checks: the rung found by
txid in its own ladder, the user-signature hash matching, the input in range, the signer a key
(`Ladder.stores`). The adversary extracts any key and forges under an extracted one.

**What it establishes.** `Ladder.inventory_provenance`: every partial in the inventory names an extracted
signer, or an honest signer that emitted it at one of its passes, for a rung of its own ladder with that
txid and user-signature hash, admissible at that pass's read, at or below the rung its verdict released
there (`Ladder.Emitted`). `Ladder.latch_bounded`: every node's latch stays inside its ladder.
`Ladder.held_origin`: a node possesses its own signatures and partials from the inventory on rungs it
retains with matching user-signature material. `Ladder.finalize` is `DUR-28`'s "highest rung at or below the
latch with `≥ t` distinct valid partials on every input" over that possession and not over the
inventory, with `Authority.quorum` per rung; a rung's count reads only its own transaction's records
(`Ladder.quorum_own_rung`, `Ladder.quorum_other_rung`). `Ladder.counted_retains`: a counted signer of a rung
is the finalizing node, an extracted key, or an honest node that retains a rung of that txid with the
same user-signature hash. `Ladder.common_base_fallback` is `DUR-28`'s downgrade to the base under its
premises: no key extracted, the base's quorum in the finalizing node's possession, and every rung above it
up to the latch retained, with matching user-signature material, by fewer than `t` honest nodes.

**Not modelled.** The reads' binding to a composed run's state and the kernel's own fire pass, which
releases the base alone (`Kernel.firePass`); a resident txid outside the ladder in the batched read, which
a lookup per rung cannot return; `DUR-25`'s re-evaluation at the exact finalized vsize, `DUR-29`'s
package and send-time checks and `DUR-31`'s re-classification, which are assembly's and submission's;
`CHN-16`'s relations between rungs; delivery, quota and window conditions, which the fallback takes as
premises and does not derive; freshness of the observation. -/

namespace BtcPolicy.Ladder
open BtcPolicy.Kernel BtcPolicy.Sweep

/-! ## The attempt -/

/-- The ladder's parameters: `PreRelease`'s, `SPN-38`'s `per_peer_quota_per_min`, and the cursor's anchor. -/
structure Cfg where
  pre : PreRelease.Cfg
  quota : Nat
  anchor : Cursor.Anchor

/-- What one node's fire pass reads: its authorized set, its registry, its latest observation, the median
feerate it read for `DUR-30` (`none` on an error or no reading), and the rung transactions above the base it
retains for each commitment id. -/
structure Read where
  A : List Nat
  reg : Node
  ob : Option Backend
  median : Option Nat
  rungs : Nat → List Tx := fun _ => []

/-- The read with this node's own rungs for commitment `cid`. -/
def Read.own (rd : Read) (cid : Nat) (l : List Tx) : Read :=
  { rd with rungs := fun k => if k = cid then l else rd.rungs k }

/-- The ladder's rung transactions: the base, the registered candidate's own, then the rungs above it. -/
@[req "DUR-21"]
def txs (rd : Read) (c : Cand) : List Tx := c.tx :: rd.rungs c.id

/-- A transaction the instant shows resident. -/
def resident (b : Backend) (tx : Tx) : Bool := (b.mempool.lookup tx.id).isSome

/-- `DUR-22`'s pass with the ladder: the selected Escapes as `Sweep.passAt` has them, less the outputs of
"every resident rung" of each, the base included. -/
@[req "DUR-22"]
def passAt (cfg : Sweep.Cfg) (rd : Read) (b : Backend) : Coverage.Pass :=
  VaultUnspent.passOf (snapshot rd.A b) ((selectedEscapes rd.reg).map fun c => escapeOf cfg.book c.tx)
    ((selectedEscapes rd.reg).flatMap fun c =>
      ((txs rd c).filter (resident b)).flatMap fun tx => cfg.book.outputs tx.id)
    (unconfirmedExternal rd.A b)

theorem flatMap_single_filter (l : List Cand) (p : Tx → Bool) (g : Tx → List Nat) :
    (l.flatMap fun c => ([c.tx].filter p).flatMap g) = (l.filter fun c => p c.tx).flatMap fun c => g c.tx := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih]
    by_cases h : p a.tx <;> simp [h]

/-- With no rung above any base, the pass is `Sweep.passAt`. -/
@[req "DUR-22"]
theorem passAt_no_rungs (cfg : Sweep.Cfg) (rd : Read) (b : Backend) (h : ∀ k, rd.rungs k = []) :
    passAt cfg rd b = Sweep.passAt cfg rd.A rd.reg b := by
  have : ∀ c : Cand, txs rd c = [c.tx] := fun c => by simp [txs, h]
  simp only [passAt, Sweep.passAt, this]
  rw [flatMap_single_filter]
  rfl

/-- A rung's fee: its inputs at their `witness_utxo` values beyond its outputs (`DUR-23`). -/
@[req "DUR-23"]
def feeOf (bk : Book) (tx : Tx) : Nat := PreRelease.totalIn bk tx - PreRelease.outSum bk tx

/-- `DUR-24` on one rung at a pass. -/
@[req "DUR-24"]
def coveredTx (cfg : Sweep.Cfg) (p : Coverage.Pass) (tx : Tx) : Bool :=
  Coverage.covers (cfg.book.delivered tx.id)
    (Coverage.denominator cfg.denominator cfg.external p (escapeOf cfg.book tx)) cfg.pct

/-- A rung's admissibility at a pass: `DUR-23`'s fee and `DUR-24`'s coverage, at its maximum finalized vsize
(`DUR-25`). -/
@[req "DUR-25"]
def admissible (cfg : PreRelease.Cfg) (t : Nat) (p : Coverage.Pass) (tx : Tx) : Bool :=
  PreRelease.feeOk cfg (PreRelease.maxVsize cfg t tx) tx && coveredTx cfg.sweep p tx

/-- `DUR-26`'s `target`: "bump target (`DUR-30`), or 0 on any error or no reading". -/
@[req "DUR-26"]
def target (median : Option Nat) : Nat := (median.map BumpTarget.target).getD 0

/-- `required = max(target, escape_feerate_floor)`. -/
@[req "DUR-26"]
def required (floor : Nat) (median : Option Nat) : Nat := max (target median) floor

/-- "A fee-pressure reading is never new liveness authority: an error reading it falls back to the sealed
floor." -/
@[req "DUR-26"]
theorem target_none (floor : Nat) : target none = target (some 0) ∧ required floor none = floor := by
  simp [target, required, BumpTarget.target]

/-- `DUR-26`, line by line, over `len` rungs indexed in fee order: `meets k` is "fee ≥ required × its
maximum finalized vsize", `adm k` its admissibility, `latch` the current latch. -/
@[req "DUR-26"]
def select (len : Nat) (meets adm : Nat → Bool) (latch : Nat) : Option Nat :=
  if len = 1 then (if adm 0 then some 0 else none)
  else
    let needed := ((List.range len).find? meets).getD (len - 1)
    let choice := ((List.range len).find? fun k => decide (needed ≤ k) && adm k) <|>
      (List.range len).reverse.find? adm
    match choice with
    | none => none
    | some ch => if max ch latch < len && adm (max ch latch) then some (max ch latch) else none

/-- A selection is a rung on the ladder that is admissible. -/
@[req "DUR-26"]
theorem select_some {len : Nat} {meets adm : Nat → Bool} {latch k : Nat}
    (h : select len meets adm latch = some k) : k < len ∧ adm k = true := by
  unfold select at h
  split at h
  · split at h
    · simp at h; subst h; exact ⟨by omega, by assumption⟩
    · simp at h
  · simp only at h
    split at h
    · simp at h
    · split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc
      · simp at h

/-- A selected rung is on the ladder, admissible, and at or above a latch on the ladder: "a lower rung
cannot replace a higher live one". -/
@[req "DUR-26"]
theorem select_sound {len : Nat} {meets adm : Nat → Bool} {latch k : Nat} (hl : latch < len)
    (h : select len meets adm latch = some k) : k < len ∧ adm k = true ∧ latch ≤ k := by
  refine ⟨(select_some h).1, (select_some h).2, ?_⟩
  unfold select at h
  split at h
  · split at h
    · simp at h; omega
    · simp at h
  · simp only at h
    split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact Nat.le_max_right _ _
      · simp at h

/-- On one rung the general rule at latch 0 is `DUR-26`'s first line, "rung 0 if admissible, else fail",
which is `PreRelease.selectOne`. -/
@[req "DUR-26"]
theorem select_one_rung (meets adm : Nat → Bool) :
    select 1 meets adm 0 = PreRelease.selectOne (adm 0) ∧
      (let needed := ((List.range 1).find? meets).getD 0
       let choice := ((List.range 1).find? fun k => decide (needed ≤ k) && adm k) <|>
         (List.range 1).reverse.find? adm
       match choice with
       | none => none
       | some ch => if max ch 0 < 1 && adm (max ch 0) then some (max ch 0) else none) =
        PreRelease.selectOne (adm 0) := by
  constructor
  · simp [select, PreRelease.selectOne]
  · cases h : adm 0 <;> cases hm : meets 0 <;> simp [List.range_succ, List.find?, h, hm, PreRelease.selectOne]

/-- The rung a selection at `k` replaces: the first resident rung below `k`, if any. -/
@[req "DUR-29"]
def replacesOf (l : List Tx) (res : List Bool) (k : Nat) : Option Nat :=
  ((List.range k).find? fun j => res.getD j false).bind fun j => (l[j]?).map (·.id)

/-- `WTC-24` on one rung at that snapshot, as a replacement of `replaces` when there is one. -/
@[req "WTC-24"]
def ancestryTx (cfg : Sweep.Cfg) (A : List Nat) (b : Backend) (tx : Tx) (replaces : Option Nat) : Bool :=
  (Package.validate cfg.ancestry cfg.creator (snapshot A b) b.mempool A (candidateOf tx) replaces).isAdmitted

/-- What one node's attempt for one Escape reads over its ladder, each value computed from the ones before
it. -/
structure Attempt where
  txs : List Tx
  resident : List Bool
  pass : Coverage.Pass
  protectedValue : Nat
  vsizes : List Nat
  fees : List Bool
  meets : List Bool
  adm : List Bool
  rung : Option Nat
  ancestry : Bool

def Attempt.admAt (a : Attempt) (j : Nat) : Bool := a.adm.getD j false

/-- The attempt at instant `b` and the current latch. -/
@[req "DUR-21"]
def attempt (cfg : PreRelease.Cfg) (rd : Read) (b : Backend) (c : Cand) (latch : Nat) : Attempt :=
  let l := txs rd c
  let p := passAt cfg.sweep rd b
  let res := PreRelease.membership b l
  let req := required cfg.floor rd.median
  let fees := l.map fun tx => PreRelease.feeOk cfg (PreRelease.maxVsize cfg rd.reg.t tx) tx
  let meets := l.map fun tx =>
    decide (req * PreRelease.maxVsize cfg rd.reg.t tx ≤ feeOf cfg.sweep.book tx)
  let adm := l.map (admissible cfg rd.reg.t p)
  let k := select l.length (fun j => meets.getD j false) (fun j => adm.getD j false) latch
  { txs := l, resident := res, pass := p,
    protectedValue :=
      Coverage.denominator cfg.sweep.denominator cfg.sweep.external p (escapeOf cfg.sweep.book c.tx),
    vsizes := l.map (PreRelease.maxVsize cfg rd.reg.t), fees := fees, meets := meets, adm := adm,
    rung := k,
    ancestry := match k with
      | none => false
      | some k => match l[k]? with
        | none => false
        | some tx => ancestryTx cfg.sweep rd.A b tx (replacesOf l res k) }

/-- `DUR-21`'s order over the ladder: the rungs exist; "Empty is an error"; every vsize is positive; a rung
is selected, and a failed selection names the fee when no rung reaches the floor, coverage when none is
admissible, and the latch when some rung is admissible but the latched one is not; its ancestry is
validated; and only then is it released. -/
@[req "DUR-21"]
def Attempt.verdict (a : Attempt) : PreRelease.Verdict :=
  if a.txs.isEmpty then .fail .ladder
  else if a.protectedValue == 0 then .fail .empty
  else if a.vsizes.any (· == 0) then .fail .vsize
  else match a.rung with
    | none => .fail (if a.adm.any id then .latched else if a.fees.any id then .coverage else .fee)
    | some k => if a.ancestry then .release k else .fail .ancestry

/-- The verdict on one Escape at one node and latch, from its latest observation, if any. -/
@[req "DUR-21"]
def verdict (cfg : PreRelease.Cfg) (rd : Read) (c : Cand) (latch : Nat) : PreRelease.Verdict :=
  match rd.ob with
  | none => .fail .noRead
  | some b => (attempt cfg rd b c latch).verdict

theorem attempt_rung (cfg : PreRelease.Cfg) (rd : Read) (b : Backend) (c : Cand) (latch : Nat) :
    (attempt cfg rd b c latch).rung = select (txs rd c).length
      (fun j => (attempt cfg rd b c latch).meets.getD j false) (attempt cfg rd b c latch).admAt latch := rfl

/-- A released rung was selected: it is on the ladder, admissible at the attempt's pass, and at or above
a latch on the ladder; and the attempt had an observation. -/
@[req "DUR-21"]
theorem verdict_release {cfg : PreRelease.Cfg} {rd : Read} {c : Cand} {latch k : Nat}
    (h : verdict cfg rd c latch = .release k) :
    ∃ b, rd.ob = some b ∧ (attempt cfg rd b c latch).rung = some k ∧
      (attempt cfg rd b c latch).ancestry = true ∧ k < (txs rd c).length ∧
      (attempt cfg rd b c latch).admAt k = true ∧
      (latch < (txs rd c).length → latch ≤ k) := by
  unfold verdict at h
  split at h
  · simp at h
  · rename_i b hb
    refine ⟨b, hb, ?_⟩
    unfold Attempt.verdict at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h
    · simp at h
    · rename_i k' hk
      split at h
      · simp only [PreRelease.Verdict.release.injEq] at h
        subst h
        rename_i ha
        have hsel := (attempt_rung cfg rd b c latch).symm.trans hk
        exact ⟨hk, ha, (select_some hsel).1, (select_some hsel).2, fun hl => (select_sound hl hsel).2.2⟩
      · simp at h

/-! ## One rung is the base check -/

/-- **One rung is the base check.** On a ladder of the base alone, at latch 0, the verdict is
`PreRelease.verdict`, over every read: the same observation, pass, protected value, vsize, fee, coverage,
selection and ancestry, and the same failing step. -/
@[req "DUR-21"]
theorem verdict_one_rung (cfg : PreRelease.Cfg) (rd : Read) (c : Cand) (h : ∀ k, rd.rungs k = []) :
    verdict cfg rd c 0 = PreRelease.verdict cfg rd.A rd.reg rd.ob c := by
  have ht : txs rd c = [c.tx] := by simp [txs, h]
  unfold verdict PreRelease.verdict
  split
  · rename_i hb; simp [hb]
  · rename_i b hb
    rw [hb]
    have hp := passAt_no_rungs cfg.sweep rd b h
    have hv := PreRelease.maxVsize_pos cfg rd.reg.t c.tx
    simp only [Attempt.verdict, attempt, PreRelease.Attempt.verdict, PreRelease.attempt, ht, hp,
      PreRelease.ladder, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, Bool.or_false, List.length_cons, List.length_nil]
    have hsel : ∀ (meets adm : Nat → Bool), select (0 + 1) meets adm 0 = PreRelease.selectOne (adm 0) :=
      fun meets adm => (select_one_rung meets adm).1
    simp only [hsel, List.getD_cons_zero, admissible, coveredTx, replacesOf]
    unfold Sweep.covered Sweep.ancestryOk
    by_cases hf : PreRelease.feeOk cfg (PreRelease.maxVsize cfg rd.reg.t c.tx) c.tx = true <;>
      by_cases hc : Coverage.covers (cfg.sweep.book.delivered c.tx.id)
        (Coverage.denominator cfg.sweep.denominator cfg.sweep.external (Sweep.passAt cfg.sweep rd.A rd.reg b)
          (escapeOf cfg.sweep.book c.tx)) cfg.sweep.pct = true <;>
      simp_all [PreRelease.selectOne, ancestryTx]
    all_goals (repeat' split) <;> simp_all

/-- `PreRelease.failingAt`, the ids the base-only check withholds, is the list this module's verdict
withholds on ladders of the base alone at latch 0, whatever the median reading. -/
@[req "DUR-21"]
theorem failingAt_one_rung (cfg : PreRelease.Cfg) (A : List Nat) (n : Node) (ob : Option Backend)
    (m : Option Nat) :
    PreRelease.failingAt cfg A n ob =
      (n.cands.filter fun c => c.isEscape &&
        !(verdict cfg { A := A, reg := n, ob := ob, median := m } c 0).ok).map (·.id) := by
  unfold PreRelease.failingAt
  congr 2
  funext c
  rw [verdict_one_rung cfg { A := A, reg := n, ob := ob, median := m } c (fun _ => rfl)]

/-! ## Release -/

/-- `SPN-38`'s `a`, "the lowest rung this node's own pre-release predicate currently admits". -/
@[req "SPN-38"]
def lowest (a : Attempt) : Nat := ((List.range a.txs.length).find? a.admAt).getD 0

/-- The cursor's candidate after a verdict releasing `k`: the latch advanced to `k`. -/
def cursorOf (a : Attempt) (tr : Track) (k : Nat) : Cursor.Candidate :=
  { floor := tr.floor, latch := k, a := lowest a, last := a.txs.length - 1 }

/-- The rungs of the cursor's interval `[F, U]` that the attempt admits: "a rung the node's own predicate
refused MUST be released to nobody". -/
@[req "DUR-27"]
def relOf (a : Attempt) (F U : Nat) : List Nat := (List.range' F (U + 1 - F)).filter a.admAt

/-- One pass after its attempt: nothing on a failed verdict; on a verdict releasing `k`, `SPN-38`'s pass
with the latch at `k`, of whose interval only the admissible rungs are released. A pass that releases
nothing leaves the latch and the floor as they were; one that releases a rung sets the latch to `k` and
the floor past the interval. -/
@[req "DUR-27"]
def after (cfg : Cfg) (a : Attempt) (inputs : Nat) (tr : Track) : Track × List Nat :=
  match a.verdict with
  | .fail _ => (tr, [])
  | .release k =>
    match Cursor.pass cfg.anchor cfg.quota inputs (cursorOf a tr k) with
    | (none, _) => (tr, [])
    | (some (F, U), c') =>
      if (relOf a F U).isEmpty then (tr, []) else ({ latch := k, floor := c'.floor }, relOf a F U)

/-- One node's fire pass for one Escape: the release state after it, and the rungs it releases. -/
@[req "DUR-27"]
def release (cfg : Cfg) (rd : Read) (c : Cand) (tr : Track) : Track × List Nat :=
  match rd.ob with
  | none => (tr, [])
  | some b => after cfg (attempt cfg.pre rd b c tr.latch) c.tx.inputs.length tr

theorem cursor_some {anchor : Cursor.Anchor} {q i : Nat} {c c' : Cursor.Candidate} {F U : Nat}
    (h : Cursor.pass anchor q i c = (some (F, U), c')) :
    F = max c.floor c.a ∧ F ≤ U ∧ U ≤ c.latch ∧ c' = { c with floor := U + 1 } := by
  unfold Cursor.pass at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨rfl, by omega, by omega, rfl⟩

/-- **Refusal preservation.** A pass whose verdict releases no rung releases nothing, and leaves the
latch and the release floor where they were: "MUST release nothing of it and burn none of its rungs". -/
@[req "DUR-21"]
theorem release_refused {cfg : Cfg} {rd : Read} {c : Cand} {tr : Track}
    (h : ∀ k, verdict cfg.pre rd c tr.latch ≠ .release k) : release cfg rd c tr = (tr, []) := by
  unfold release
  split
  · rfl
  · rename_i b hb
    unfold after
    split
    · rfl
    · rename_i k hk
      exact absurd (by simp [verdict, hb, hk]) (h k)

/-- **Per-rung authorization.** Every rung a pass releases was admissible at that pass's attempt and lies in
the interval `SPN-38`'s cursor gives, below the rung the verdict released, which is the latch after it. -/
@[req "DUR-27"]
theorem release_mem {cfg : Cfg} {rd : Read} {c : Cand} {tr : Track} {m : Nat}
    (h : m ∈ (release cfg rd c tr).2) :
    ∃ b k F U c', rd.ob = some b ∧ verdict cfg.pre rd c tr.latch = .release k ∧
      Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length (cursorOf (attempt cfg.pre rd b c tr.latch) tr k) =
        (some (F, U), c') ∧
      F ≤ m ∧ m ≤ U ∧ U ≤ k ∧ (attempt cfg.pre rd b c tr.latch).admAt m = true ∧
      (release cfg rd c tr).1.latch = k := by
  unfold release at h
  split at h
  · simp at h
  · rename_i b hb
    unfold after at h
    split at h
    · simp at h
    · rename_i k hk
      split at h
      · simp at h
      · rename_i F U c' hp
        split at h
        · simp at h
        · rename_i hne
          obtain ⟨hm, ha⟩ := List.mem_filter.1 h
          have hr := List.mem_range'_1.1 hm
          have hc := cursor_some hp
          refine ⟨b, k, F, U, c', hb, by simp [verdict, hb, hk], hp, hr.1, by omega,
            by simpa [cursorOf] using hc.2.2.1, ha, ?_⟩
          simp [release, hb, after, hk, hp, hne]

/-- A rung the attempt refused is never released, wherever it lies in the cursor's interval. -/
@[req "DUR-27"]
theorem refused_not_released {cfg : Cfg} {rd : Read} {c : Cand} {tr : Track} {b : Backend} {m : Nat}
    (hb : rd.ob = some b) (hm : (attempt cfg.pre rd b c tr.latch).admAt m = false) :
    m ∉ (release cfg rd c tr).2 := by
  intro h
  obtain ⟨b', -, -, -, -, hb', -, -, -, -, -, ha, -⟩ := release_mem h
  rw [hb] at hb'
  cases hb'
  rw [hm] at ha
  cases ha

/-- The latch never decreases and stays on the ladder; it moves only on a released verdict, to its rung. -/
@[req "DUR-27"]
theorem release_latch (cfg : Cfg) (rd : Read) (c : Cand) (tr : Track) (hl : tr.latch < (txs rd c).length) :
    tr.latch ≤ (release cfg rd c tr).1.latch ∧ (release cfg rd c tr).1.latch < (txs rd c).length := by
  unfold release
  split
  · exact ⟨Nat.le_refl _, hl⟩
  · rename_i b hb
    unfold after
    split
    · exact ⟨Nat.le_refl _, hl⟩
    · rename_i k hk
      obtain ⟨-, -, -, -, hlen, -, hge⟩ :=
        verdict_release (cfg := cfg.pre) (rd := rd) (c := c) (latch := tr.latch) (k := k)
          (by simp [verdict, hb, hk])
      split
      · exact ⟨Nat.le_refl _, hl⟩
      · split
        · exact ⟨Nat.le_refl _, hl⟩
        · exact ⟨hge hl, hlen⟩

/-- The release floor never moves back. -/
@[req "SPN-38"]
theorem release_floor (cfg : Cfg) (rd : Read) (c : Cand) (tr : Track) :
    tr.floor ≤ (release cfg rd c tr).1.floor := by
  unfold release
  split
  · exact Nat.le_refl _
  · unfold after
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · rename_i hp
        split
        · exact Nat.le_refl _
        · have hc := cursor_some hp
          rw [hc.2.2.2]
          simp only [cursorOf] at hc ⊢
          omega

/-- When the admissible rungs run unbroken from `a` through the released rung, which `DUR-23`'s floor and
`DUR-24`'s output-side coverage give a ladder in `CHN-16`'s shape, the release is the cursor's interval
whole: the filter removes nothing. -/
@[req "SPN-38"]
theorem release_interval {cfg : Cfg} {rd : Read} {c : Cand} {tr : Track} {b : Backend} {k F U : Nat}
    {c' : Cursor.Candidate} (hb : rd.ob = some b) (hv : verdict cfg.pre rd c tr.latch = .release k)
    (hp : Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length (cursorOf (attempt cfg.pre rd b c tr.latch) tr k) =
      (some (F, U), c'))
    (hint : ∀ j, lowest (attempt cfg.pre rd b c tr.latch) ≤ j → j ≤ k →
      (attempt cfg.pre rd b c tr.latch).admAt j = true) :
    (release cfg rd c tr).2 = List.range' F (U + 1 - F) := by
  have hc := cursor_some hp
  have hk : (attempt cfg.pre rd b c tr.latch).verdict = .release k := by simpa [verdict, hb] using hv
  have hrel : relOf (attempt cfg.pre rd b c tr.latch) F U = List.range' F (U + 1 - F) := by
    apply List.filter_eq_self.2
    intro j hj
    have hr := List.mem_range'_1.1 hj
    simp only [cursorOf] at hc
    exact hint j (by omega) (by omega)
  have hne : (List.range' F (U + 1 - F)).isEmpty = false := by
    cases hn : U + 1 - F with
    | zero => omega
    | succ n => simp [List.range']
  unfold release
  simp only [hb]
  unfold after
  simp only [hk, hp, hrel, hne]
  rfl

/-- From a fresh latch and floor, on a ladder of the base alone with one rung affordable, the pass
releases rung 0 exactly when `PreRelease.verdict` releases it, and leaves the floor at `1`, `SPN-38`'s
exhaustion, as the kernel's fire pass sets `released`. -/
@[req "DUR-21"]
theorem release_one_rung (cfg : Cfg) (rd : Read) (c : Cand) (h : ∀ k, rd.rungs k = [])
    (haff : Cursor.affordableRungs cfg.quota c.tx.inputs.length ≠ 0) :
    release cfg rd c {} =
      if PreRelease.verdict cfg.pre rd.A rd.reg rd.ob c = .release 0 then ({ latch := 0, floor := 1 }, [0])
      else ({}, []) := by
  rw [← verdict_one_rung cfg.pre rd c h]
  have ht : txs rd c = [c.tx] := by simp [txs, h]
  by_cases hv : verdict cfg.pre rd c 0 = .release 0
  · rw [if_pos hv]
    obtain ⟨b, hb, -, -, -, ha, -⟩ := verdict_release hv
    have hk : (attempt cfg.pre rd b c 0).verdict = .release 0 := by simpa [verdict, hb] using hv
    have hlen : (attempt cfg.pre rd b c 0).txs.length = 1 := by simp [attempt, ht]
    have hlow : lowest (attempt cfg.pre rd b c 0) = 0 := by
      simp [lowest, hlen, List.range_one, ha]
    unfold release
    simp only [hb]
    unfold after
    simp only [hk]
    have hp : Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
        (cursorOf (attempt cfg.pre rd b c 0) {} 0) = (some (0, 0), { floor := 1, latch := 0, a := 0, last := 0 }) := by
      simp [Cursor.pass, Cursor.quotaRungCap, cursorOf, hlen, hlow, haff]
    simp [hp, ha, relOf, List.range']
  · rw [if_neg hv]
    have hz : ∀ k, verdict cfg.pre rd c 0 ≠ .release k := by
      intro k hk
      obtain ⟨-, -, -, -, hlen, -, -⟩ := verdict_release hk
      rw [ht] at hlen
      have : k = 0 := by simp at hlen; omega
      subst this; exact hv hk
    exact release_refused hz

/-- After it, no pass releases anything: the floor is past the only rung. -/
@[req "SPN-38"]
theorem release_exhausted (cfg : Cfg) (rd : Read) (c : Cand) (h : ∀ k, rd.rungs k = []) :
    release cfg rd c { latch := 0, floor := 1 } = ({ latch := 0, floor := 1 }, []) := by
  have ht : txs rd c = [c.tx] := by simp [txs, h]
  unfold release
  split
  · rfl
  · rename_i b hb
    unfold after
    split
    · rfl
    · rename_i k hk
      obtain ⟨-, -, -, -, hlen, -, -⟩ :=
        verdict_release (cfg := cfg.pre) (rd := rd) (c := c) (latch := 0) (k := k)
          (by simp [verdict, hb, hk])
      rw [ht] at hlen
      have : k = 0 := by simp at hlen; omega
      subst this
      have hlen' : (attempt cfg.pre rd b c 0).txs.length = 1 := by simp [attempt, ht]
      have hn : (Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
          (cursorOf (attempt cfg.pre rd b c 0) { latch := 0, floor := 1 } 0)).1 = none := by
        unfold Cursor.pass Cursor.quotaRungCap
        simp only [cursorOf, hlen']
        split
        · rfl
        · rename_i hq
          split at hq
          · simp at hq
          · simp only [Option.some.injEq] at hq
            subst hq
            rw [if_pos (by omega)]
      rcases hq : Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
          (cursorOf (attempt cfg.pre rd b c 0) { latch := 0, floor := 1 } 0) with ⟨_ | ⟨F, U⟩, c'⟩
      · simp
      · rw [hq] at hn; simp at hn

/-! ## The run: one selected Escape across the federation -/

/-- A partial, keyed as `NCH-25` keys the store, "per `(rung, input, signer)`", the rung by its txid, with the
user-signature hash of the rung it was signed on. -/
structure Part where
  txid : Nat
  userSig : Nat
  input : Nat
  signer : Nat
  deriving DecidableEq, Repr

/-- The partial as a federation signature: its message is `Kernel.sighash` of its rung at its input. -/
def Part.sig (x : Part) : Authority.Sig := { msg := (x.txid, x.input), input := x.input, signer := x.signer }

/-- The run's parameters: the ladder's, the Escape, the federation's keys, the threshold, and what each node
retains of the ladder: the base's user-signature hash and the rungs above the base. Retention is fixed for
the run: `SPN-32` leaves "an already resident compatible pair … exactly as is", and first deliveries may
leave different nodes with different rungs. -/
structure RCfg where
  lc : Cfg
  esc : Cand
  keys : List Nat
  t : Nat
  baseSig : Nat → Nat
  above : Nat → List Rung

/-- Node `i`'s ladder, the base first. -/
def RCfg.lad (c : RCfg) (i : Nat) : List Rung := ⟨c.esc.tx, c.baseSig i⟩ :: c.above i

/-- One node's state for the Escape: its release state and the partials it stored. -/
structure LNode where
  track : Track := {}
  stored : List Authority.Sig := []

/-- The read node `i`'s pass takes, with its own rungs for the Escape. -/
def RCfg.read (c : RCfg) (i : Nat) (rd : Read) : Read := rd.own c.esc.id ((c.above i).map (·.tx))

theorem txs_read (c : RCfg) (i : Nat) (rd : Read) : txs (c.read i rd) c.esc = (c.lad i).map (·.tx) := by
  simp [txs, RCfg.read, Read.own, RCfg.lad]

/-- The partials node `i` emits for the released rungs `ms`: one per input of each, by `SPN-32`'s signature
made at ingress. -/
def emits (c : RCfg) (i : Nat) (ms : List Nat) : List Part :=
  ms.flatMap fun m => match (c.lad i)[m]? with
    | none => []
    | some r => (List.range r.tx.inputs.length).map fun k =>
        { txid := r.tx.id, userSig := r.userSig, input := k, signer := i }

/-- `NCH-24` at node `j`: "the rung is found by txid; the user-signature hash matches; the input and signer
are in range". The signature's verification is symbolic. -/
@[req "NCH-24"]
def stores (c : RCfg) (j : Nat) (x : Part) : Bool :=
  match (c.lad j).find? (·.tx.id == x.txid) with
  | none => false
  | some r => r.userSig == x.userSig && decide (x.input < r.tx.inputs.length) && c.keys.contains x.signer

/-- Node `i`'s own signatures, made at ingress on every rung it retains and every input. -/
def own (c : RCfg) (i : Nat) : List Authority.Sig :=
  (c.lad i).flatMap fun r => (List.range r.tx.inputs.length).map fun k =>
    { msg := sighash r.tx k, input := k, signer := i }

/-- `DUR-28`'s *Held partial* set at node `i`: its own signatures and the partials it stored. -/
@[req "DUR-28"]
def held (c : RCfg) (n : LNode) (i : Nat) : List Authority.Sig := own c i ++ n.stored

structure State where
  nodes : Nat → LNode
  parts : List Part := []
  extracted : List Nat := []

inductive Step
  /-- Node `i`'s fire pass for the Escape, at the read it takes. -/
  | pass (i : Nat) (rd : Read)
  /-- A partial of the inventory reaches node `j`. -/
  | deliver (j : Nat) (x : Part)
  /-- The adversary extracts node `j`'s key. -/
  | extract (j : Nat)
  /-- A partial forged under an extracted key. -/
  | forge (x : Part)

def update (f : Nat → LNode) (i : Nat) (n : LNode) : Nat → LNode := fun j => if j = i then n else f j

def apply (c : RCfg) (st : State) : Step → State
  | .pass i rd =>
    let r := release c.lc (c.read i rd) c.esc (st.nodes i).track
    { st with nodes := update st.nodes i { st.nodes i with track := r.1 }, parts := st.parts ++ emits c i r.2 }
  | .deliver j x =>
    if stores c j x then
      { st with nodes := update st.nodes j { st.nodes j with stored := (st.nodes j).stored ++ [x.sig] } }
    else st
  | .extract j => { st with extracted := st.extracted ++ [j] }
  | .forge x => { st with parts := st.parts ++ [x] }

/-- An honest node passes and stores; a delivered partial is one of the inventory; any key may be
extracted; a forgery needs an extracted key. -/
def admits (honest : List Nat) (st : State) : Step → Bool
  | .pass i _ => honest.contains i
  | .deliver j x => honest.contains j && st.parts.contains x
  | .extract _ => true
  | .forge x => st.extracted.contains x.signer

def Fresh (st : State) : Prop :=
  st.parts = [] ∧ st.extracted = [] ∧ ∀ i, (st.nodes i).track = {} ∧ (st.nodes i).stored = []

abbrev Trace := List (State × Step)

/-- A reachable run, retaining its trace, newest first. -/
inductive Execution (c : RCfg) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Fresh st) : Execution c honest [] st
  | next {T st} (s : Step) (ha : admits honest st s = true) : Execution c honest T st →
      Execution c honest ((st, s) :: T) (apply c st s)

/-! ## The latch and the floor on the run -/

theorem track_apply (c : RCfg) (st : State) (s : Step) (i : Nat) :
    ((apply c st s).nodes i).track = (st.nodes i).track ∨
      ∃ rd, s = .pass i rd ∧ ((apply c st s).nodes i).track = (release c.lc (c.read i rd) c.esc (st.nodes i).track).1 := by
  cases s with
  | pass j rd =>
    by_cases h : i = j
    · subst h; right; exact ⟨rd, rfl, by simp [apply, update]⟩
    · left; simp [apply, update, h]
  | deliver j x =>
    left; simp only [apply]; split
    · by_cases h : i = j <;> simp [update, h]
    · rfl
  | extract j => left; rfl
  | forge x => left; rfl

/-- **The latch stays on the ladder**: on every reachable state each node's latch is below the length of
the ladder it retains. -/
@[req "DUR-27"]
theorem latch_bounded {c : RCfg} {honest : List Nat} {T : Trace} {st : State} (hx : Execution c honest T st)
    (i : Nat) : (st.nodes i).track.latch < (c.lad i).length := by
  induction hx with
  | init st h => rw [(h.2.2 i).1]; simp [RCfg.lad]
  | @next T st s _ _ ih =>
    rcases track_apply c st s i with h | ⟨rd, -, h⟩
    · rw [h]; exact ih
    · rw [h]
      have hl : (st.nodes i).track.latch < (txs (c.read i rd) c.esc).length := by
        rw [txs_read, List.length_map]; exact ih
      have := (release_latch c.lc (c.read i rd) c.esc _ hl).2
      rwa [txs_read, List.length_map] at this

/-- **Monotone**: no step lowers a node's latch or its release floor. -/
@[req "DUR-27"]
theorem track_mono {c : RCfg} {honest : List Nat} {T : Trace} {st : State} (hx : Execution c honest T st)
    (s : Step) (i : Nat) :
    (st.nodes i).track.latch ≤ ((apply c st s).nodes i).track.latch ∧
      (st.nodes i).track.floor ≤ ((apply c st s).nodes i).track.floor := by
  rcases track_apply c st s i with h | ⟨rd, -, h⟩
  · rw [h]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [h]
    have hl : (st.nodes i).track.latch < (txs (c.read i rd) c.esc).length := by
      rw [txs_read, List.length_map]; exact latch_bounded hx i
    exact ⟨(release_latch c.lc (c.read i rd) c.esc _ hl).1, release_floor c.lc (c.read i rd) c.esc _⟩

/-! ## Provenance -/

/-- Node `x.signer` emitted `x` at a pass of the trace, `T₁` the history before it: a rung `m` of its own
ladder carrying `x`'s txid and user-signature hash, released at that pass by `Ladder.release`, admissible at
that pass's attempt and at or below the rung its verdict released. -/
def Emitted (c : RCfg) (T : Trace) (x : Part) : Prop :=
  ∃ T₁ T₂ st rd, T = T₂ ++ (st, .pass x.signer rd) :: T₁ ∧
    ∃ b k m r, (c.read x.signer rd).ob = some b ∧
      verdict c.lc.pre (c.read x.signer rd) c.esc (st.nodes x.signer).track.latch = .release k ∧
      m ∈ (release c.lc (c.read x.signer rd) c.esc (st.nodes x.signer).track).2 ∧ m ≤ k ∧
      (attempt c.lc.pre (c.read x.signer rd) b c.esc (st.nodes x.signer).track.latch).admAt m = true ∧
      (c.lad x.signer)[m]? = some r ∧ x.txid = r.tx.id ∧ x.userSig = r.userSig ∧
      x.input < r.tx.inputs.length

theorem Emitted.cons {c : RCfg} {T : Trace} {x : Part} (y : State × Step) (h : Emitted c T x) :
    Emitted c (y :: T) x := by
  obtain ⟨T₁, T₂, st, rd, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, rd, rfl, rest⟩

theorem mem_emits {c : RCfg} {i : Nat} {ms : List Nat} {x : Part} (h : x ∈ emits c i ms) :
    ∃ m ∈ ms, ∃ r, (c.lad i)[m]? = some r ∧ x.txid = r.tx.id ∧ x.userSig = r.userSig ∧
      x.input < r.tx.inputs.length ∧ x.signer = i := by
  obtain ⟨m, hm, hx⟩ := List.mem_flatMap.1 h
  split at hx
  · simp at hx
  · rename_i r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ⟨m, hm, r, hr, rfl, rfl, List.mem_range.1 hk, rfl⟩

/-- **Inventory provenance.** Every partial of the inventory names a signer whose key is in the cumulative
extracted set, or an honest signer that emitted it at one of its passes past that pass's per-rung check
(`Ladder.Emitted`). Both may hold: a key extracted from an honest node leaves the node on the honest list. -/
@[req "DUR-27"]
theorem inventory_provenance {c : RCfg} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution c honest T st) {x : Part} (hm : x ∈ st.parts) :
    x.signer ∈ st.extracted ∨ (x.signer ∈ honest ∧ Emitted c T x) := by
  induction hx with
  | init st h => rw [h.1] at hm; cases hm
  | @next T st s ha _ ih =>
    have lift (hm : x ∈ st.parts) :
        x.signer ∈ (apply c st s).extracted ∨ (x.signer ∈ honest ∧ Emitted c ((st, s) :: T) x) := by
      rcases ih hm with h | ⟨hh, he⟩
      · left
        cases s with
        | extract j => exact List.mem_append_left _ h
        | pass i rd => exact h
        | deliver j y => simp only [apply]; split <;> exact h
        | forge y => exact h
      · exact .inr ⟨hh, he.cons _⟩
    cases s with
    | pass i rd =>
      simp only [apply, List.mem_append] at hm
      rcases hm with hm | hm
      · exact lift hm
      · right
        have hi : i ∈ honest := by simpa [admits] using ha
        obtain ⟨m, hmm, r, hr, h1, h2, h3, hs⟩ := mem_emits hm
        subst hs
        obtain ⟨b, k, F, U, c', hb, hv, -, -, hmU, hUk, hadm, -⟩ := release_mem hmm
        exact ⟨hi, T, [], st, rd, rfl, b, k, m, r, hb, hv, hmm, by omega, hadm, hr, h1, h2, h3⟩
    | deliver j y =>
      have : x ∈ st.parts := by simp only [apply] at hm; split at hm <;> exact hm
      exact lift this
    | extract j => exact lift hm
    | forge y =>
      simp only [apply, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact lift hm
      · left; simpa [admits] using ha

/-- The parts only grow. -/
theorem parts_grow (c : RCfg) (st : State) (s : Step) {x : Part} (h : x ∈ st.parts) :
    x ∈ (apply c st s).parts := by
  cases s with
  | pass i rd => exact List.mem_append_left _ h
  | deliver j y => simp only [apply]; split <;> exact h
  | extract j => exact h
  | forge y => exact List.mem_append_left _ h

/-- **Possession.** What node `j` holds is its own signature on a rung it retains, or a partial of the
inventory that passed `NCH-24`'s checks against its own ladder. -/
@[req "DUR-28"]
theorem held_origin {c : RCfg} {honest : List Nat} {T : Trace} {st : State} (hx : Execution c honest T st)
    (j : Nat) {y : Authority.Sig} (hy : y ∈ held c (st.nodes j) j) :
    y ∈ own c j ∨ ∃ x ∈ st.parts, x.sig = y ∧ stores c j x = true := by
  rcases List.mem_append.1 hy with h | h
  · exact .inl h
  · right
    clear hy
    induction hx generalizing y with
    | init st hf => rw [(hf.2.2 j).2] at h; cases h
    | @next T st s ha _ ih =>
      cases s with
      | pass i rd =>
        have : y ∈ (st.nodes j).stored := by
          by_cases hij : j = i
          · subst hij; simpa [apply, update] using h
          · simpa [apply, update, hij] using h
        obtain ⟨x, hx, h1, h2⟩ := ih this
        exact ⟨x, parts_grow c st _ hx, h1, h2⟩
      | deliver i z =>
        by_cases hs : stores c i z = true
        · simp only [apply, hs, if_true] at h ⊢
          by_cases hij : j = i
          · subst hij
            simp only [update, if_true, List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact ih h
            · simp only [admits, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at ha
              exact ⟨z, ha.2, rfl, hs⟩
          · simp only [update, hij, if_false] at h
            exact ih h
        · simp only [apply, hs] at h ⊢
          exact ih h
      | extract i => exact ih h
      | forge z =>
        obtain ⟨x, hx, h1, h2⟩ := ih h
        exact ⟨x, parts_grow c st _ hx, h1, h2⟩

/-! ## Finalization from possession -/

/-- Whether rung `m` of ladder `l` has `DUR-28`'s quorum in the records `R`. -/
def quorumAt (keys : List Nat) (t : Nat) (l : List Rung) (R : List Authority.Sig) (m : Nat) : Bool :=
  match l[m]? with
  | none => false
  | some r => Authority.quorum keys t r.tx R

/-- `DUR-28`: "the highest rung at or below the latch with `≥ t` distinct valid partials on every input", over
the records `R`, which for a node are its *Held partial* set (`Ladder.held`), never the inventory. -/
@[req "DUR-28"]
def finalize (keys : List Nat) (t : Nat) (l : List Rung) (R : List Authority.Sig) : Nat → Option Nat
  | 0 => if quorumAt keys t l R 0 then some 0 else none
  | m + 1 => if quorumAt keys t l R (m + 1) then some (m + 1) else finalize keys t l R m

/-- What `finalize` returns has the quorum on every input and is at or below the latch. -/
@[req "DUR-28"]
theorem finalize_sound (keys : List Nat) (t : Nat) (l : List Rung) (R : List Authority.Sig) (top m : Nat)
    (h : finalize keys t l R top = some m) : quorumAt keys t l R m = true ∧ m ≤ top := by
  induction top with
  | zero =>
    unfold finalize at h
    split at h <;> simp_all
  | succ top ih =>
    unfold finalize at h
    split at h
    · simp at h; subst h; simp_all
    · exact ⟨(ih h).1, by have := (ih h).2; omega⟩

/-- No rung with the quorum at or below the latch is passed over. -/
@[req "DUR-28"]
theorem finalize_highest (keys : List Nat) (t : Nat) (l : List Rung) (R : List Authority.Sig) (top m : Nat)
    (hm : m ≤ top) (hq : quorumAt keys t l R m = true) :
    ∃ m', finalize keys t l R top = some m' ∧ m ≤ m' := by
  induction top with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact ⟨0, by simp [finalize, hq], Nat.le_refl 0⟩
  | succ top ih =>
    unfold finalize
    split
    · exact ⟨top + 1, rfl, hm⟩
    · rename_i hno
      have : m ≤ top := by
        rcases Nat.lt_or_ge m (top + 1) with h | h
        · omega
        · have : m = top + 1 := by omega
          subst this; exact absurd hq hno
      exact ih this

theorem signers_filter (keys : List Nat) (X : Tx) (k : Nat) (R : List Authority.Sig) :
    Authority.signers keys X k R = Authority.signers keys X k (R.filter fun s => s.msg.1 == X.id) := by
  unfold Authority.signers
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro s _
  cases hm : (s.msg == sighash X k) <;> simp only [Bool.false_and, Bool.true_and, Bool.and_assoc]
  · simp only [beq_iff_eq] at hm
    simp [hm, sighash]

/-- **No pooling across rungs.** A rung's count reads only the records on its own transaction: dropping every
other transaction's record changes nothing. -/
@[req "DUR-28"]
theorem quorum_own_rung (keys : List Nat) (t : Nat) (X : Tx) (R : List Authority.Sig) :
    Authority.quorum keys t X R = Authority.quorum keys t X (R.filter fun s => s.msg.1 == X.id) := by
  unfold Authority.quorum
  congr 1
  apply List.all_congr rfl
  intro k
  rw [signers_filter keys X k R]

/-- Signature authority for one rung cannot satisfy another rung's count: records on other transactions
alone give no quorum at a positive threshold. -/
@[req "DUR-28"]
theorem quorum_other_rung (keys : List Nat) (t : Nat) (X : Tx) (R : List Authority.Sig) (ht : 0 < t)
    (h : ∀ s ∈ R, s.msg.1 ≠ X.id) : Authority.quorum keys t X R = false := by
  rw [quorum_own_rung]
  have hn : (R.filter fun s => s.msg.1 == X.id) = [] := by
    apply List.filter_eq_nil_iff.2
    intro s hs
    simpa using h s hs
  rw [hn]
  unfold Authority.quorum
  cases hi : X.inputs with
  | nil => simp
  | cons a as =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.length_cons]
    apply List.all_eq_false.2
    exact ⟨0, List.mem_range.2 (by omega), by simp [Authority.signers]; omega⟩

/-! ## Who can be counted, and the common-base fallback -/

/-- The user-signature hash node `j` stores rung `id` against: that of the rung its lookup by txid finds. -/
def sigOf (l : List Rung) (id : Nat) : Option Nat := (l.find? (·.tx.id == id)).map (·.userSig)

/-- Node `s` retains rung `id` with the user-signature hash node `j` stores it against. -/
def compat (lj ls : List Rung) (id : Nat) : Bool :=
  match sigOf lj id with
  | none => false
  | some u => ls.any fun r => r.tx.id == id && r.userSig == u

/-- **Who can be counted.** A signer counted on a rung at node `j`'s possession is `j` itself, an extracted
key, or an honest node that retains a rung of that txid with the user-signature hash `j` stores it against. -/
@[req "DUR-28"]
theorem counted_retains {c : RCfg} {honest : List Nat} {T : Trace} {st : State} (hx : Execution c honest T st)
    (j : Nat) (X : Tx) (k : Nat) {s : Nat} (hs : s ∈ Authority.signers c.keys X k (held c (st.nodes j) j)) :
    s = j ∨ s ∈ st.extracted ∨ (s ∈ honest ∧ compat (c.lad j) (c.lad s) X.id = true) := by
  obtain ⟨-, hm⟩ := Authority.mem_signers.1 hs
  rcases held_origin hx j hm with ho | ⟨x, hxp, hsig, hst⟩
  · left
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 ho
    obtain ⟨k', -, he⟩ := List.mem_map.1 hr
    simp only [Authority.Sig.mk.injEq] at he
    exact he.2.2.symm
  · have hxs : x.signer = s := by simp only [Part.sig, Authority.Sig.mk.injEq] at hsig; exact hsig.2.2
    have hxt : x.txid = X.id := by
      simp only [Part.sig, Authority.Sig.mk.injEq, sighash, Prod.mk.injEq] at hsig; exact hsig.1.1
    subst hxs
    rcases inventory_provenance hx hxp with h | ⟨hh, he⟩
    · exact .inr (.inl h)
    · right; right
      refine ⟨hh, ?_⟩
      obtain ⟨-, -, -, -, -, -, -, m, r, -, -, -, -, -, hr, h1, h2, -⟩ := he
      unfold stores at hst
      split at hst
      · simp at hst
      · rename_i rj hj
        simp only [Bool.and_eq_true, beq_iff_eq] at hst
        have hsig' : sigOf (c.lad j) X.id = some x.userSig := by
          simp [sigOf, ← hxt, hj, hst.1.1]
        simp only [compat, hsig']
        apply List.any_eq_true.2
        exact ⟨r, List.mem_of_getElem? hr, by simp [← h1, hxt, h2]⟩

theorem compat_self (l : List Rung) (id : Nat) (h : ∃ r ∈ l, r.tx.id = id) : compat l l id = true := by
  obtain ⟨r, hr, hid⟩ := h
  have hf : ∃ r', l.find? (·.tx.id == id) = some r' := by
    cases hq : l.find? (·.tx.id == id) with
    | none =>
      have := List.find?_eq_none.1 hq r hr
      simp [hid] at this
    | some r' => exact ⟨r', rfl⟩
  obtain ⟨r', hq⟩ := hf
  have hm := List.mem_of_find?_eq_some hq
  have hp := List.find?_some hq
  simp only [beq_iff_eq] at hp
  simp only [compat, sigOf, hq, Option.map_some]
  exact List.any_eq_true.2 ⟨r', hm, by simp [hp]⟩

theorem finalize_base (keys : List Nat) (t : Nat) (l : List Rung) (R : List Authority.Sig) (top : Nat)
    (h0 : quorumAt keys t l R 0 = true) (hup : ∀ m, 1 ≤ m → m ≤ top → quorumAt keys t l R m = false) :
    finalize keys t l R top = some 0 := by
  induction top with
  | zero => simp [finalize, h0]
  | succ top ih =>
    unfold finalize
    rw [hup (top + 1) (by omega) (Nat.le_refl _)]
    exact ih fun m h1 h2 => hup m h1 (by omega)

/-- **The common-base fallback** (`DUR-28`): "stripping can therefore downgrade the sweep to the base at its own
fee when that base is admissible". Under its premises: no key is extracted; the finalizing honest node `j`
holds the base's quorum on every input, which is where "enough successful fire passes, quotas and partial
delivery within the fire windows" enters and is not derived; and every rung of `j`'s ladder above the base,
up to its latch, is retained with the user-signature hash `j` stores it against by fewer than `t` honest
nodes. Then `j` finalizes the base. Nothing here makes the base admissible or confirms it. -/
@[req "DUR-28"]
theorem common_base_fallback {c : RCfg} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution c honest T st) {j : Nat} (hj : j ∈ honest) (hext : st.extracted = [])
    (hbase : Authority.quorum c.keys c.t c.esc.tx (held c (st.nodes j) j) = true)
    (hshort : ∀ m r, 1 ≤ m → m ≤ (st.nodes j).track.latch → (c.lad j)[m]? = some r →
      (honest.filter fun s => compat (c.lad j) (c.lad s) r.tx.id).length < c.t) :
    finalize c.keys c.t (c.lad j) (held c (st.nodes j) j) (st.nodes j).track.latch = some 0 := by
  apply finalize_base
  · simpa [quorumAt, RCfg.lad] using hbase
  · intro m h1 h2
    unfold quorumAt
    split
    · rfl
    · rename_i r hr
      have hlt := hshort m r h1 h2 hr
      unfold Authority.quorum
      cases hi : r.tx.inputs with
      | nil => simp
      | cons a as =>
        simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.length_cons]
        apply List.all_eq_false.2
        refine ⟨0, List.mem_range.2 (by omega), ?_⟩
        have hsub : ∀ s ∈ Authority.signers c.keys r.tx 0 (held c (st.nodes j) j),
            s ∈ honest.filter fun s => compat (c.lad j) (c.lad s) r.tx.id := by
          intro s hs
          apply List.mem_filter.2
          rcases counted_retains hx j r.tx 0 hs with rfl | h | h
          · exact ⟨hj, compat_self _ _ ⟨r, List.mem_of_getElem? hr, rfl⟩⟩
          · rw [hext] at h; cases h
          · exact h
        have hle : (Authority.signers c.keys r.tx 0 (held c (st.nodes j) j)).length ≤ _ :=
          length_le_of_nodup_subset (nodup_eraseDups _) hsub
        simp only [decide_eq_true_eq, Nat.not_le]
        omega

/-! ## Running a schedule -/

def legal (c : RCfg) (honest : List Nat) : State → List Step → Bool
  | _, [] => true
  | st, s :: ss => admits honest st s && legal c honest (apply c st s) ss

def record (c : RCfg) : Trace → State → List Step → Trace × State
  | T, st, [] => (T, st)
  | T, st, s :: ss => record c ((st, s) :: T) (apply c st s) ss

theorem execution_of_legal {c : RCfg} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution c honest T st) {ss : List Step} (hl : legal c honest st ss = true) :
    Execution c honest (record c T st ss).1 (record c T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

/-! ## The reads on the composed run

A `Read` is what one fire pass reads. On a composed sweep run it is the acting node's own: its authorized set, its
registry and its latest observation in the state the fire pass is taken in, which is what `PreRelease.failing`
reads there. The median reading stays supplied, since the composed run carries no fee estimate, and so do the
rungs above the base: the kernel now retains them (`Kernel.Cand.above`) and releases them at its ladder pass
(`Kernel.ladderPass`), but the reads here do not take them from it yet, and `RCfg.read` puts a node's own rungs
in. -/

/-- The read node `i`'s fire pass takes on a composed sweep run, in state `st` after history `T`, with the median
`m` supplied. -/
@[req "DUR-21"]
def readOf (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (m : Option Nat) : Read :=
  { A := authorizedAt st T i, reg := (st.fed.worlds i).node, ob := st.obs i, median := m }

/-- A step of a checked trace carries `PreRelease.releaseOk` at its own state and the history before it. -/
theorem checked_at {cfg : PreRelease.Cfg} :
    ∀ {T₂ T₁ : Sweep.Trace} {st : Sweep.State} {s : Sweep.Step},
      PreRelease.Checked cfg (T₂ ++ (st, s) :: T₁) → PreRelease.releaseOk cfg st T₁ s = true
  | [], _, _, _, h => h.1
  | _ :: T₂, _, _, _, h => checked_at (T₂ := T₂) h.2

/-- **The kernel's fire pass is the ladder's verdict at the run's read.** On a trace whose fire passes carry
`DUR-21`'s verdict and whose ladder passes list no release, every fire pass of node `i` withholds exactly the ids of the Escape-role candidates whose
ladder verdict, at the read that pass takes on the run, at latch 0 and with no rung above the base, is not a
release, whatever the median reading. -/
@[req "DUR-21"]
theorem fire_withholds {cfg : PreRelease.Cfg} {T₁ T₂ : Sweep.Trace} {st : Sweep.State} {i : Nat} {env : Env}
    (hc : PreRelease.Checked cfg (T₂ ++ (st, .fed (.process i env .firePass)) :: T₁)) (m : Option Nat) :
    env.withheld = ((st.fed.worlds i).node.cands.filter fun c =>
      c.isEscape && !(verdict cfg (readOf st T₁ i m) c 0).ok).map (·.id) := by
  have h := checked_at hc
  simp only [PreRelease.releaseOk, beq_iff_eq] at h
  rw [h, PreRelease.failing_eq]
  exact failingAt_one_rung cfg _ _ _ m

/-- **The ladder's pass at the run's read releases the base where the kernel's fire pass does.** At the read a
fire pass takes on a checked trace, with no rung above the base, from a fresh latch and floor and with one rung
affordable, the ladder's pass for an Escape-role candidate `c` of node `i` releases rung 0 when that fire pass
does not withhold `c`'s id; and when the ladder's pass releases nothing, the fire pass withholds it. -/
@[req "DUR-27"]
theorem fire_release (lc : Cfg) {T₁ T₂ : Sweep.Trace} {st : Sweep.State} {i : Nat} {env : Env}
    (hc : PreRelease.Checked lc.pre (T₂ ++ (st, .fed (.process i env .firePass)) :: T₁)) (m : Option Nat)
    {c : Cand} (hm : c ∈ (st.fed.worlds i).node.cands) (he : c.isEscape = true)
    (haff : Cursor.affordableRungs lc.quota c.tx.inputs.length ≠ 0) :
    (c.id ∉ env.withheld → release lc (readOf st T₁ i m) c {} = ({ latch := 0, floor := 1 }, [0])) ∧
      (release lc (readOf st T₁ i m) c {} = ({}, []) → c.id ∈ env.withheld) := by
  have h := checked_at hc
  simp only [PreRelease.releaseOk, beq_iff_eq] at h
  have hr := release_one_rung lc (readOf st T₁ i m) c (fun _ => rfl) haff
  have hv : PreRelease.verdict lc.pre (readOf st T₁ i m).A (readOf st T₁ i m).reg (readOf st T₁ i m).ob c =
      PreRelease.verdict lc.pre (authorizedAt st T₁ i) (st.fed.worlds i).node (st.obs i) c := rfl
  rw [hv] at hr
  rw [h]
  constructor
  · intro hn
    rw [hr, if_pos]
    exact Classical.byContradiction fun hne =>
      hn ((PreRelease.mem_failing lc.pre st T₁ i c.id).2 ⟨c, hm, he, rfl, hne⟩)
  · intro hz
    refine (PreRelease.mem_failing lc.pre st T₁ i c.id).2 ⟨c, hm, he, rfl, fun hrel => ?_⟩
    rw [hr, if_pos hrel] at hz
    simp at hz

end BtcPolicy.Ladder
