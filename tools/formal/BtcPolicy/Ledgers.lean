import BtcPolicy.Req
import BtcPolicy.Shapes
/-! `POL-20`'s counting theorem over a list of honest ledgers.

"Its admitted outflow is at most `((n − c) / (t − c)) × cap`: at the cut each honest ledger still
charges its counted reservations, each ledger holds at most `cap`, and every counted spend charges
at least `t − c` honest ledgers."

Three clauses, TWO hypotheses: `hq` fuses the first and the third, because `charging` counts the
ledgers that charge a spend AT the cut. The conclusion is the same bound cleared of its division,
`(t − c) × A ≤ (n − c) × cap`, with `A` the cohort's outflow. This is the counting argument alone;
that `POL-18`/`POL-19`'s reserve, refund and age-out transitions establish these hypotheses for
`POL-20`'s cohort is `BtcPolicy.Ledger`'s accounting bridge (`BtcPolicy.Budget` holds the
coefficient's algebra and `ADR-0014`'s trace as data). A general identity, so no guard parameter
and no twin (`ADR-0023` decision 6). -/

namespace BtcPolicy.Ledgers

/-- A counted spend: its id and its amount. -/
abbrev Spend := Nat × Nat

/-- One honest ledger at the interval's end: which spends it still charges. -/
abbrev Ledger := Nat → Bool

/-- What a ledger charges over a cohort: the amount of every spend it charges. -/
@[req "POL-20"]
def charge (cohort : List Spend) (l : Ledger) : Nat :=
  (cohort.map fun s => if l s.1 then s.2 else 0).sum

/-- How many ledgers charge a spend. -/
@[req "POL-20"]
def charging (ledgers : List Ledger) (id : Nat) : Nat := ledgers.countP fun l => l id

/-- The cohort's outflow. -/
@[req "POL-20"]
def outflow (cohort : List Spend) : Nat := (cohort.map (·.2)).sum

/-! ## Four list lemmas, on core Lean -/

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    omega

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_left {α : Type} (xs : List α) (q : Nat) (f : α → Nat) :
    (xs.map fun x => q * f x).sum = q * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_zero {α : Type} (xs : List α) : (xs.map fun _ => (0 : Nat)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]

/-- Double counting: a sum over ledgers of a sum over spends is the same total the other way. -/
theorem sum_comm {α β : Type} (as : List α) (bs : List β) (f : α → β → Nat) :
    (as.map fun a => (bs.map fun b => f a b).sum).sum =
      (bs.map fun b => (as.map fun a => f a b).sum).sum := by
  induction as with
  | nil => simp [sum_map_zero]
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← sum_map_add]

/-- What every ledger charges for one spend, summed over the ledgers, is the amount times the
number of ledgers charging it. -/
theorem sum_charge_one (ledgers : List Ledger) (id amount : Nat) :
    (ledgers.map fun l => if l id then amount else 0).sum = amount * charging ledgers id := by
  unfold charging
  induction ledgers with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    split <;> simp [Nat.mul_add] <;> omega

/-- "each ledger holds at most `cap`": the ledgers together charge at most `(n − c) × cap`. -/
theorem total_le (cohort : List Spend) (ledgers : List Ledger) (cap : Nat)
    (hcap : ∀ l ∈ ledgers, charge cohort l ≤ cap) :
    (ledgers.map (charge cohort)).sum ≤ ledgers.length * cap := by
  induction ledgers with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := hcap l (by simp)
    have := ih fun m hm => hcap m (by simp [hm])
    rw [Nat.succ_mul]; omega

/-- The counting theorem. `q` is `t − c` and `ledgers.length` is `n − c`: with every honest
ledger charging at most `cap` and every counted spend charged by at least `q` of them,
`q × A ≤ (n − c) × cap`. For every cohort, every list of ledgers, every cap. -/
@[req "POL-20"]
theorem counting (cohort : List Spend) (ledgers : List Ledger) (cap q : Nat)
    (hcap : ∀ l ∈ ledgers, charge cohort l ≤ cap)
    (hq : ∀ s ∈ cohort, q ≤ charging ledgers s.1) :
    q * outflow cohort ≤ ledgers.length * cap := by
  have swap : (ledgers.map (charge cohort)).sum =
      (cohort.map fun s => s.2 * charging ledgers s.1).sum := by
    unfold charge
    rw [sum_comm]
    congr 1
    apply List.map_congr_left
    intro s _
    exact sum_charge_one ledgers s.1 s.2
  have lower : q * outflow cohort ≤ (cohort.map fun s => s.2 * charging ledgers s.1).sum := by
    unfold outflow
    rw [← sum_map_mul_left]
    apply sum_map_le
    intro s hs
    calc q * s.2 = s.2 * q := Nat.mul_comm _ _
      _ ≤ s.2 * charging ledgers s.1 := Nat.mul_le_mul_left _ (hq s hs)
  exact Nat.le_trans lower (swap ▸ total_le cohort ledgers cap hcap)

/-! ## The corollaries per shape, `n = 2t − 1` -/

/-- `c = 0`: `t × A ≤ n × cap`, the cleared form of "the coefficient at `c = 0` is `(2 − 1/t)`". -/
@[req "POL-20"]
theorem c0_bound (cohort : List Spend) (ledgers : List Ledger) (cap t : Nat)
    (hn : ledgers.length + 1 = 2 * t)
    (hcap : ∀ l ∈ ledgers, charge cohort l ≤ cap)
    (hq : ∀ s ∈ cohort, t ≤ charging ledgers s.1) :
    t * outflow cohort ≤ (2 * t - 1) * cap := by
  have h := counting cohort ledgers cap t hcap hq
  rw [show ledgers.length = 2 * t - 1 by omega] at h
  exact h

/-- `c = t − 1`: one honest acceptance per spend, `t` honest ledgers, `A ≤ t × cap` — "the full
`c = t − 1` tolerance admits at most `t × cap`". -/
@[req "POL-20"]
theorem full_tolerance_bound (cohort : List Spend) (ledgers : List Ledger) (cap t : Nat)
    (hn : ledgers.length = t)
    (hcap : ∀ l ∈ ledgers, charge cohort l ≤ cap)
    (hq : ∀ s ∈ cohort, 1 ≤ charging ledgers s.1) :
    outflow cohort ≤ t * cap := by
  have h := counting cohort ledgers cap 1 hcap hq
  rw [hn, Nat.one_mul] at h
  exact h

/-- Every published shape, `c = 0`, one spend of `A = cap`, `n` ledgers each charging it: both
premises hold — each ledger charges exactly its cap — so they are satisfiable and nothing above
holds vacuously. The conclusion is `t × A ≤ n × cap`, which is not tight here. -/
@[req "POL-20"]
theorem shapes_attained :
    ∀ p ∈ Shapes.shapes,
      let ledgers : List Ledger := List.replicate p.2 fun _ => true
      let cohort : List Spend := [(0, 7)]
      (∀ l ∈ ledgers, charge cohort l ≤ 7) ∧ (∀ s ∈ cohort, p.1 ≤ charging ledgers s.1) ∧
        p.1 * outflow cohort ≤ p.2 * 7 := by
  decide

end BtcPolicy.Ledgers
