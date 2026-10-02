import BtcPolicy.Req
import BtcPolicy.Formula
/-! `SPN-38`'s release cursor, with the cap's anchor as a guard parameter.

"Compute `rung_budget = max(saturating_sub(per_peer_quota_per_min, 2), 1)` and `affordable_rungs
= rung_budget ÷ inputs_per_variant` … Let `a` be the lowest rung this node's own pre-release
predicate currently admits … and `F = max(release_floor, a)`. A pass releases the interval `[F,
U]` where `quota_rung_cap = min(last_rung_index, F + affordable_rungs − 1)` … and `U = min(latch,
quota_rung_cap)`. If `F > U` the pass MUST release nothing and leave the cursor unchanged. The cap
MUST be anchored on `F` and never on `release_floor`".

The theorems here take the anchor as an argument; `Exhibits.lean` holds the ones over `current`,
so that flipping `current` goes red there and nowhere else. -/

namespace BtcPolicy.Cursor

/-- Where the cap is measured from. `onF` is `SPN-38` as it stands; `onCursor` is the 2026-09-11
defect `F51` records. -/
inductive Anchor
  | onF | onCursor
  deriving DecidableEq, Repr

/-- The anchor's name as `SPN-38` writes it, for the emitted formula. -/
def Anchor.name : Anchor → String
  | .onF => "F"
  | .onCursor => "release_floor"

/-- `SPN-38` as it stands. -/
@[req "SPN-38"]
def current : Anchor := .onF

/-! The formulas `SPN-38` writes, as the copies gate reads them: each RENDERED from an expression
(`BtcPolicy.Formula`) that the theorem beside it proves evaluates to the definition — or, for
the one sentence among them, `zeroRule`, a theorem that the branch it describes is the one the
definition takes — so the string in the Markdown and the rule the theorems are about cannot
drift apart silently. The cap
formula and the anchoring sentence are written from `current`, so the anchor flip changes the
emitted text as well as the exhibits. -/
open Formula in
def affordableExpr : Expr := .div (.var "rung_budget") (.var "inputs_per_variant")
open Formula in
def saturatingExpr : Expr := .max (.sub (.var "a") (.var "b")) (.lit 0)
open Formula in
def startExpr : Expr := .max (.var "release_floor") (.var "a")
open Formula in
def capExpr (anchor : Anchor) : Expr :=
  .min (.var "last_rung_index") (.sub (.add (.var anchor.name) (.var "affordable_rungs")) (.lit 1))

@[req "SPN-38"] def affordableFormula : String := s!"affordable_rungs = {Formula.renderNat affordableExpr}"
@[req "SPN-38"] def saturatingFormula : String := s!"saturating_sub(a, b) = {Formula.renderNat saturatingExpr}"
@[req "SPN-38"] def zeroRule : String := "If `affordable_rungs = 0`, release nothing"
@[req "SPN-38"] def startFormula : String := s!"F = {Formula.renderNat startExpr}"
@[req "SPN-38"] def capFormula : String := s!"quota_rung_cap = {Formula.renderNat (capExpr current)}"
@[req "SPN-38"] def anchorSentence : String :=
  match current with
  | .onF => "MUST be anchored on `F` and never on `release_floor`"
  | .onCursor => "MUST be anchored on `release_floor` and never on `F`"

/-- The rendered strings are the ones `SPN-38` carries, decided so a rendering change is red here
before the copies gate sees it. `capFormula` renders from `current`, so its exhibit lives in
`Exhibits.lean` with everything else over `current`. -/
@[req "SPN-38"]
theorem formulas_render :
    affordableFormula = "affordable_rungs = rung_budget ÷ inputs_per_variant" ∧
    saturatingFormula = "saturating_sub(a, b) = max(a − b, 0)" ∧
    startFormula = "F = max(release_floor, a)" ∧
    Formula.renderNat (capExpr .onF) = "min(last_rung_index, F + affordable_rungs − 1)" ∧
    Formula.renderNat (capExpr .onCursor) = "min(last_rung_index, release_floor + affordable_rungs − 1)" := by
  decide

@[req "SPN-38"] def reserve : Nat := 2
@[req "SPN-38"] def minimum : Nat := 1

/-- `rung_budget = max(saturating_sub(quota, 2), 1)`; `Nat` subtraction is the saturating one. -/
@[req "SPN-38"]
def rungBudget (quota : Nat) : Nat := max (quota - reserve) minimum

/-- `affordable_rungs = rung_budget ÷ inputs_per_variant`. -/
@[req "SPN-38"]
def affordableRungs (quota inputs : Nat) : Nat := rungBudget quota / inputs

/-- The boundary table's quantity: the cap, or `none` when `affordable_rungs = 0`. -/
@[req "SPN-38"]
def quotaRungCap (anchor : Anchor) (quota inputs floor a last : Nat) : Option Nat :=
  let aff := affordableRungs quota inputs
  if aff = 0 then none
  else
    let F := max floor a
    let base := match anchor with | .onF => F | .onCursor => floor
    some (min last (base + aff - 1))

/-! ## The formulas evaluate to the definitions -/

/-- `affordable_rungs = rung_budget ÷ inputs_per_variant` IS `affordableRungs`. -/
@[req "SPN-38"]
theorem affordable_expr_agrees (quota inputs : Nat) :
    Formula.evalNat (fun s => if s = "rung_budget" then rungBudget quota
      else if s = "inputs_per_variant" then inputs else 0) affordableExpr
      = affordableRungs quota inputs := rfl

/-- `saturating_sub(a, b) = max(a − b, 0)` IS `Nat` subtraction. -/
@[req "SPN-38"]
theorem saturating_expr_agrees (a b : Nat) :
    Formula.evalNat (fun s => if s = "a" then a else if s = "b" then b else 0) saturatingExpr
      = a - b := by
  simp [Formula.evalNat, saturatingExpr]

/-- `F = max(release_floor, a)` IS the `F` of `quotaRungCap`. -/
@[req "SPN-38"]
theorem start_expr_agrees (floor a : Nat) :
    Formula.evalNat (fun s => if s = "release_floor" then floor else if s = "a" then a else 0)
      startExpr = max floor a := rfl

/-- `quota_rung_cap = min(last_rung_index, F + affordable_rungs − 1)` IS the cap `quotaRungCap`
computes on `F` when a rung is affordable; and with the anchor variable bound to the cursor
instead, it is the withdrawn cap. -/
@[req "SPN-38"]
theorem cap_expr_agrees (quota inputs floor a last : Nat)
    (haff : affordableRungs quota inputs ≠ 0) :
    Formula.evalNat (fun s => if s = "last_rung_index" then last
      else if s = "F" then max floor a
      else if s = "affordable_rungs" then affordableRungs quota inputs else 0) (capExpr .onF)
      = (quotaRungCap .onF quota inputs floor a last).getD 0 ∧
    Formula.evalNat (fun s => if s = "last_rung_index" then last
      else if s = "release_floor" then floor
      else if s = "affordable_rungs" then affordableRungs quota inputs else 0) (capExpr .onCursor)
      = (quotaRungCap .onCursor quota inputs floor a last).getD 0 := by
  simp [Formula.evalNat, capExpr, Anchor.name, quotaRungCap, haff]

/-- One row of the table: `(quota, inputs, floor, a, last, cap)`. -/
abbrev Row := Nat × Nat × Nat × Nat × Nat × Option Nat

/-- The boundary rows `SPN-38` publishes. The last three are the `a > 0` rows; only two of them
distinguish the anchors (`a_gt_zero_is_not_sufficient`). -/
@[req "SPN-38"]
def rows : List Row :=
  [ (0, 1, 0, 0, 3, some 0), (1, 1, 0, 0, 3, some 0), (2, 2, 0, 0, 3, none),
    (3, 2, 0, 0, 3, none), (600, 598, 0, 0, 3, some 0), (600, 599, 0, 0, 3, none),
    (600, 1, 2, 0, 3, some 3), (3, 1, 0, 1, 3, some 1), (3, 1, 0, 3, 3, some 3),
    (600, 1, 0, 2, 3, some 3) ]

/-- The gate's two side checks per row under a given anchor: the batch fits the budget, and a
released cap is at or above `F`. -/
def rowOk (anchor : Anchor) (r : Row) : Bool :=
  match quotaRungCap anchor r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 with
  | none => true
  | some cap =>
      let F := max r.2.2.1 r.2.2.2.1
      decide (cap ≥ F ∧ (cap - F + 1) * r.2.1 ≤ rungBudget r.1)

/-- On every row with `a ≤ floor` the two anchors agree, for EVERY quota, inputs, floor and last.
This is why the pre-`F51` table could not see the defect: every row had `a = 0`. -/
@[req "SPN-38"]
theorem anchors_agree_when_a_le_floor (quota inputs floor a last : Nat) (h : a ≤ floor) :
    quotaRungCap .onF quota inputs floor a last = quotaRungCap .onCursor quota inputs floor a last := by
  unfold quotaRungCap
  simp [Nat.max_eq_left h]

/-- The `F51` rows: admitted with the anchor on `F`, capped below `F` with it on the cursor. -/
@[req "SPN-38"]
theorem f51_rows :
    quotaRungCap .onF 3 1 0 1 3 = some 1 ∧ quotaRungCap .onCursor 3 1 0 1 3 = some 0 ∧
    quotaRungCap .onF 3 1 0 3 3 = some 3 ∧ quotaRungCap .onCursor 3 1 0 3 3 = some 0 := by
  decide

/-- `a > 0` is NECESSARY for the anchors to differ, not sufficient: the table's third `a > 0` row
gives the same cap under both, because the budget from the cursor reaches past `a`. A gate that
required "some row with `a > 0`" was satisfied by a row that distinguished nothing. -/
@[req "SPN-38"]
theorem a_gt_zero_is_not_sufficient :
    quotaRungCap .onF 600 1 0 2 3 = quotaRungCap .onCursor 600 1 0 2 3 := by decide

/-- Exactly when the cursor anchor livelocks a row: the cursor-anchored cap falls below `F`, i.e.
the budget from the cursor does not reach the lowest admissible rung. For every input with a rung
affordable (`haff`) and `F` on the ladder (`hlast`). -/
@[req "SPN-38"]
theorem cursor_anchor_livelocks_iff (quota inputs floor a last : Nat)
    (haff : affordableRungs quota inputs ≠ 0) (hlast : max floor a ≤ last) :
    (∃ cap, quotaRungCap .onCursor quota inputs floor a last = some cap ∧ cap < max floor a) ↔
      floor + affordableRungs quota inputs - 1 < a := by
  have hpos : 0 < affordableRungs quota inputs := Nat.pos_of_ne_zero haff
  generalize hA : affordableRungs quota inputs = aff at *
  unfold quotaRungCap
  rw [hA]
  simp [haff]
  omega

/-! ## The pass, iterated: livelock as a fixpoint -/

structure Candidate where
  floor : Nat   -- release_floor, the next-unscheduled-rung cursor
  latch : Nat
  a : Nat
  last : Nat
  deriving DecidableEq, Repr

/-- One fire pass under a fixed quota: the interval released, if any, and the candidate after.
"Only a pass that released at least one rung MUST set `release_floor = U + 1`." -/
@[req "SPN-38"]
def pass (anchor : Anchor) (quota inputs : Nat) (c : Candidate) : Option (Nat × Nat) × Candidate :=
  match quotaRungCap anchor quota inputs c.floor c.a c.last with
  | none => (none, c)
  | some cap =>
    let F := max c.floor c.a
    let U := min c.latch cap
    if F > U then (none, c) else (some (F, U), { c with floor := U + 1 })

def iterate (anchor : Anchor) (quota inputs : Nat) : Nat → Candidate → Candidate
  | 0, c => c
  | k + 1, c => iterate anchor quota inputs k (pass anchor quota inputs c).2

/-- "If `affordable_rungs = 0`, release nothing" IS `quotaRungCap`'s `none` branch: no cap, so no
interval, for every anchor and every input. `zeroRule` is a sentence, not a formula; this is the
theorem beside it. -/
@[req "SPN-38"]
theorem zero_rule_agrees (anchor : Anchor) (quota inputs floor a last : Nat)
    (h : affordableRungs quota inputs = 0) :
    quotaRungCap anchor quota inputs floor a last = none ∧
    (pass anchor quota inputs { floor := floor, latch := last, a := a, last := last }).1 = none := by
  constructor
  · simp [quotaRungCap, h]
  · simp [pass, quotaRungCap, h]

/-- `F51` as a candidate: `a = 1` above a cursor at 0, latch 3, quota 3. -/
@[req "SPN-38"]
def f51Candidate : Candidate := { floor := 0, latch := 3, a := 1, last := 3 }

/-- On `F` the first pass releases `[1, 1]` and moves the cursor to 2. -/
@[req "SPN-38"]
theorem f51_admitted_on_F :
    (pass .onF 3 1 f51Candidate).1 = some (1, 1) ∧ (pass .onF 3 1 f51Candidate).2.floor = 2 := by
  decide

/-- On the cursor it releases nothing and moves nothing. -/
@[req "SPN-38"]
theorem f51_refused_on_cursor : pass .onCursor 3 1 f51Candidate = (none, f51Candidate) := by
  decide

/-- The livelock in general: a pass that releases nothing is the identity on the candidate, so
the candidate is a fixpoint of every later pass. -/
@[req "SPN-38"]
theorem stuck_forever (anchor : Anchor) (quota inputs : Nat) (c : Candidate)
    (h : (pass anchor quota inputs c).1 = none) (k : Nat) :
    iterate anchor quota inputs k c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hc : (pass anchor quota inputs c).2 = c := by
      unfold pass at *
      split at h <;> simp_all
      split at h <;> simp_all
    simp [iterate, hc, ih]

/-- Progress on `F`: whenever a rung at or above `F` is reachable — `F ≤ last`, `F ≤ latch`, and
the budget affords one rung — the pass releases a non-empty interval from `F` and the cursor
advances past it. For every candidate and every quota. -/
@[req "SPN-38"]
theorem progress_on_F (quota inputs : Nat) (c : Candidate)
    (haff : affordableRungs quota inputs ≠ 0)
    (hlast : max c.floor c.a ≤ c.last) (hlatch : max c.floor c.a ≤ c.latch) :
    ∃ U, (pass .onF quota inputs c).1 = some (max c.floor c.a, U) ∧
      max c.floor c.a ≤ U ∧ (pass .onF quota inputs c).2.floor = U + 1 := by
  have hpos : 0 < affordableRungs quota inputs := Nat.pos_of_ne_zero haff
  generalize hA : affordableRungs quota inputs = aff at *
  unfold pass quotaRungCap
  rw [hA]
  simp [haff]
  have h1 : max c.floor c.a ≤ min c.latch (min c.last (max c.floor c.a + aff - 1)) := by
    omega
  refine ⟨min c.latch (min c.last (max c.floor c.a + aff - 1)), ?_, h1, ?_⟩
  · simp [Nat.not_lt.mpr h1]
  · simp [Nat.not_lt.mpr h1]

/-- The batch a pass releases fits the per-pass budget: `(U − F + 1) × inputs ≤ rung_budget`. -/
@[req "SPN-38"]
theorem batch_fits (quota inputs : Nat) (c : Candidate) (F U : Nat)
    (h : (pass .onF quota inputs c).1 = some (F, U)) :
    (U - F + 1) * inputs ≤ rungBudget quota := by
  have hdiv : affordableRungs quota inputs * inputs ≤ rungBudget quota :=
    Nat.div_mul_le_self (rungBudget quota) inputs
  generalize hA : affordableRungs quota inputs = aff at *
  generalize hB : rungBudget quota = B at *
  unfold pass quotaRungCap at h
  rw [hA] at h
  by_cases haff : aff = 0
  · simp [haff] at h
  · simp [haff] at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨hF, hU⟩ := h
      subst hF; subst hU
      have : (min c.latch (min c.last (max c.floor c.a + aff - 1)) - max c.floor c.a + 1) ≤ aff := by
        omega
      calc (min c.latch (min c.last (max c.floor c.a + aff - 1)) - max c.floor c.a + 1) * inputs
          ≤ aff * inputs := Nat.mul_le_mul_right _ this
        _ ≤ B := hdiv

/-! ## The cumulative prefix across passes, and `DUR-28` across nodes

`DUR-27`: "**Prefix** here is the CUMULATIVE release obligation across fire passes, not a
retransmission of its beginning on every pass; `SPN-38` owns how the passes are batched and
advances the cursor that makes them cumulative." `DUR-30`: "the cumulative prefix release of
`SPN-38` and `DUR-27` makes their released sets overlap, and `DUR-28` finalizes “the highest rung
at or below the latch with `≥ t` distinct valid partials on every input”, so a rung that enough
nodes reached still completes." `F51` records the sentence this replaced: that a median split
stops the sweep. -/

/-- Every interval `k` passes released, in order. -/
@[req "SPN-38"]
def releases (anchor : Anchor) (quota inputs : Nat) : Nat → Candidate → List (Nat × Nat)
  | 0, _ => []
  | k + 1, c =>
    (pass anchor quota inputs c).1.toList ++ releases anchor quota inputs k (pass anchor quota inputs c).2

/-- A rung is released iff some released interval holds it. -/
@[req "SPN-38"]
def released (rs : List (Nat × Nat)) (rung : Nat) : Bool := rs.any fun (F, U) => F ≤ rung && rung ≤ U

/-- `DUR-28`: "the highest rung at or below the latch with `≥ t` distinct valid partials on every
input", searched down from the finalizing node's latch over every node's released intervals;
`none` when no rung has `t`. One input stands for every input, which the same lists cover. -/
@[req "DUR-28"]
def finalized (t : Nat) (nodes : List (List (Nat × Nat))) : Nat → Option Nat
  | 0 => if t ≤ nodes.countP (released · 0) then some 0 else none
  | r + 1 => if t ≤ nodes.countP (released · (r + 1)) then some (r + 1) else finalized t nodes r

theorem released_cons (F U rung : Nat) (rs : List (Nat × Nat)) :
    released ((F, U) :: rs) rung = ((F ≤ rung && rung ≤ U) || released rs rung) := rfl

/-- A pass never moves the latch. -/
theorem pass_latch (anchor : Anchor) (quota inputs : Nat) (c : Candidate) :
    (pass anchor quota inputs c).2.latch = c.latch := by
  unfold pass
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- A released interval is non-empty and ends at or below the latch: `U = min(latch, …)`. -/
theorem pass_interval (anchor : Anchor) (quota inputs : Nat) (c : Candidate) (F U : Nat)
    (h : (pass anchor quota inputs c).1 = some (F, U)) : F ≤ U ∧ U ≤ c.latch := by
  unfold pass at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨hF, hU⟩ := h
      subst hF; subst hU
      constructor <;> omega

/-- Nothing above the latch is ever released, however many passes: `DUR-27`'s "a rung the node's
own predicate refused MUST be released to nobody", for the latch. -/
@[req "DUR-27"]
theorem released_le_latch (anchor : Anchor) (quota inputs k : Nat) :
    ∀ (c : Candidate) (r : Nat), released (releases anchor quota inputs k c) r = true → r ≤ c.latch := by
  induction k with
  | zero => intro c r h; simp [releases, released] at h
  | succ k ih =>
    intro c r h
    simp only [releases, released, List.any_append, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases hp : (pass anchor quota inputs c).1 with _ | ⟨F, U⟩
      · simp [hp] at h
      · have := pass_interval anchor quota inputs c F U hp
        simp [hp] at h
        omega
    · have := ih _ r h
      rwa [pass_latch] at this

/-- The cumulative prefix: on `F`, with a rung affordable, every rung from `F` up to the latch
and the ladder's end is released once enough passes have run — `k` passes reach `k ×
affordable_rungs` rungs past `F`. For every candidate. -/
@[req "SPN-38"]
theorem prefix_covered (quota inputs : Nat) (haff : affordableRungs quota inputs ≠ 0) (k : Nat) :
    ∀ (c : Candidate) (r : Nat), max c.floor c.a ≤ r → r ≤ c.latch → r ≤ c.last →
      r < max c.floor c.a + k * affordableRungs quota inputs →
      released (releases .onF quota inputs k c) r = true := by
  have hpos : 0 < affordableRungs quota inputs := Nat.pos_of_ne_zero haff
  generalize hA : affordableRungs quota inputs = aff at *
  induction k with
  | zero => intro c r h1 _ _ hk; simp at hk; omega
  | succ k ih =>
    intro c r h1 h2 h3 hk
    rw [Nat.succ_mul] at hk
    have hle : max c.floor c.a ≤ min c.latch (min c.last (max c.floor c.a + aff - 1)) := by omega
    have hp : pass .onF quota inputs c =
        (some (max c.floor c.a, min c.latch (min c.last (max c.floor c.a + aff - 1))),
          { c with floor := min c.latch (min c.last (max c.floor c.a + aff - 1)) + 1 }) := by
      unfold pass quotaRungCap
      rw [hA]
      simp [haff, Nat.not_lt.mpr hle]
    simp only [releases, hp, Option.toList, List.singleton_append, released_cons, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    by_cases hr : r ≤ min c.latch (min c.last (max c.floor c.a + aff - 1))
    · left; exact ⟨h1, hr⟩
    · right
      apply ih
      · show max (min c.latch (min c.last (max c.floor c.a + aff - 1)) + 1) c.a ≤ r
        omega
      · exact h2
      · exact h3
      · show r < max (min c.latch (min c.last (max c.floor c.a + aff - 1)) + 1) c.a + k * aff
        omega

/-- What `finalized` returns has `t` partials and sits at or below the latch it searched from. -/
theorem finalized_sound (t : Nat) (nodes : List (List (Nat × Nat))) (top m : Nat)
    (h : finalized t nodes top = some m) : t ≤ nodes.countP (released · m) ∧ m ≤ top := by
  induction top with
  | zero =>
    unfold finalized at h
    split at h <;> simp_all
  | succ top ih =>
    unfold finalized at h
    split at h
    · simp at h; subst h; simp_all
    · have := ih h; omega

/-- A rung with `t` partials at or below the latch is not passed over: finalization returns it or
a higher one. -/
@[req "DUR-28"]
theorem finalized_reaches (t : Nat) (nodes : List (List (Nat × Nat))) (top m : Nat)
    (hm : m ≤ top) (hcount : t ≤ nodes.countP (released · m)) :
    ∃ m', finalized t nodes top = some m' ∧ m ≤ m' := by
  induction top with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact ⟨0, by simp [finalized, hcount], Nat.le_refl 0⟩
  | succ top ih =>
    unfold finalized
    split
    · exact ⟨top + 1, rfl, hm⟩
    · rename_i hno
      have : m ≤ top := by
        rcases Nat.lt_or_ge m (top + 1) with h | h
        · omega
        · have : m = top + 1 := by omega
          subst this; exact absurd hcount hno
      exact ih this

/-- `DUR-30`'s split, in general: two honest nodes with the same lowest admissible rung `a`, fresh
cursors, and latches one apart — `L` and `L + 1` from two medians — both release `[a, L]` once
enough passes have run, and `DUR-28` from any latch at or above `L` finalizes exactly `L`, the
lower latch: the rung both reached. For every `a`, `L`, ladder and budget. -/
@[req "DUR-28"]
theorem split_finalizes_lower_latch (quota inputs a L last k top : Nat)
    (haff : affordableRungs quota inputs ≠ 0) (haL : a ≤ L) (hlast : L + 1 ≤ last)
    (hk : L < a + k * affordableRungs quota inputs) (htop : L ≤ top) :
    let lower := releases .onF quota inputs k { floor := 0, latch := L, a := a, last := last }
    let upper := releases .onF quota inputs k { floor := 0, latch := L + 1, a := a, last := last }
    finalized 2 [lower, upper] top = some L := by
  intro lower upper
  have hl : released lower L = true :=
    prefix_covered quota inputs haff k _ L (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hu : released upper L = true :=
    prefix_covered quota inputs haff k _ L (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hcount : 2 ≤ [lower, upper].countP (released · L) := by simp [hl, hu]
  obtain ⟨m, hm, hLm⟩ := finalized_reaches 2 [lower, upper] top L htop hcount
  obtain ⟨hc, _⟩ := finalized_sound 2 [lower, upper] top m hm
  -- two partials over two nodes means the lower-latch node released `m`, so `m ≤ L`
  have hlow : released lower m = true := by
    cases hlo : released lower m with
    | true => rfl
    | false =>
      simp [List.countP_cons, hlo] at hc
      split at hc <;> omega
  have := released_le_latch .onF quota inputs k _ m hlow
  dsimp only at this
  rw [hm]
  congr 1
  omega

/-- The same two nodes under the withdrawn cursor anchor, with `a` above the budget's reach from
the cursor (`F51`): nothing is released, so no rung has two partials and finalization returns
nothing from either latch. -/
@[req "SPN-38"]
theorem split_on_cursor_finalizes_nothing :
    let lower := releases .onCursor 3 1 3 { floor := 0, latch := 2, a := 1, last := 3 }
    let upper := releases .onCursor 3 1 3 { floor := 0, latch := 3, a := 1, last := 3 }
    lower = [] ∧ upper = [] ∧ finalized 2 [lower, upper] 3 = none ∧
      finalized 2 [lower, upper] 2 = none := by
  decide

end BtcPolicy.Cursor
