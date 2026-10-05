import BtcPolicy.Req
/-! `DUR-24`'s coverage predicate, `MAN-9`'s floor, and `DUR-22`'s denominator (`F54`, `F59`).

`DUR-22`'s protected value is "computed on every pass from this node's current reads and never
stored". It is built here as a set, never as arithmetic: the read is FILTERED by the exclusions
and then every distinct input outpoint of every selected Escape is added ONCE at its
`witness_utxo` value, "a counted input takes precedence over every exclusion, so a selected
Escape spending another's change output is still counted". The shape this module had before
`F59` — the read plus the restorations minus the exclusions, as numbers — falls below the floor
on exactly that case, and `Exhibits.subtracting_breaks_floor_on_that_pass` records it.

What the construction buys is the floor: on every pass the denominator is at least the combined
inputs of the Escapes selected on it. That, and not a value frozen at the arm, is what carries
`MAN-9`'s lower bound across passes, and it also caps a node's sweep burn. Two guard parameters
(`ADR-0023` decision 6) hold the two withdrawn readings: restoring only the Escape under
evaluation (`F54`), and excluding an unconfirmed external deposit even when a selected Escape
spends it (`F59`). Both let two input-disjoint Escapes confirm.

The guarantee is per node, over the Escapes it had selected at its first release: an Escape
selected later, or one another node selected, can confirm beside it. Those residuals are
exhibits in `Exhibits.lean`, not defects to repair (`F59`). -/

namespace BtcPolicy.Coverage

/-- `DUR-24` per rung: `delivered × 100 ≥ protected_value × escape_coverage_pct`. -/
@[req "DUR-24"]
def covers (delivered prot pct : Nat) : Bool := delivered * 100 ≥ prot * pct

/-- `MAN-9`'s bounds on `escape_coverage_pct`: "outside `51..=100`" is refused. -/
@[req "MAN-9"] def floorPct : Nat := 51
@[req "MAN-9"] def ceilingPct : Nat := 100

/-- `MAN-9`'s reason for the floor: at 50 two halves both cover. The floor is not slack. -/
@[req "MAN-9"]
theorem fifty_admits_two : covers 50 100 50 = true ∧ covers 50 100 50 = true ∧ 50 + 50 ≤ 100 := by
  decide

/-! ## The pass -/

abbrev Outpoint := Nat
/-- An outpoint with the `witness_utxo` value claimed for it. -/
abbrev Coin := Outpoint × Nat

/-- A selected Escape as the denominator sees it: what it spends, what it pays (excluded from
the read, `DUR-22`), and what it delivers to the escape descriptor (`DUR-24`). -/
structure Escape where
  id : Nat
  inputs : List Coin
  outputs : List Outpoint
  delivered : Nat
  deriving DecidableEq, Repr

/-- One evaluation pass at one node: this node's vault-unspent read, the set it has selected,
and the resident rungs whose outputs are excluded. -/
structure Pass where
  read : List Coin
  selected : List Escape
  residentRungs : List Outpoint
  /-- The outpoints that are unconfirmed **external** deposits at this pass: "their parents are
  not vault-authorized and can be replaced out from under the sweep" (`DUR-22`). An input absent
  from the read because a resident Escape spent it is NOT one of these — that is `F54`'s case,
  and the two must not be confused. -/
  unconfirmedExternal : List Outpoint
  deriving DecidableEq, Repr

/-! ## Guard parameters -/

/-- `DUR-22` counts "every distinct input outpoint of EVERY selected Escape … once at its
`witness_utxo` value"; `restoreOne` is the 2026-09-12 form `F54` records, which restored only
the Escape under evaluation, so a resident Escape's inputs left the denominator. The
constructors keep the withdrawn design's own word, restore. -/
inductive Denominator
  | restoreAll | restoreOne
  deriving DecidableEq, Repr

@[req "DUR-22"]
def current : Denominator := .restoreAll

/-- `DUR-22` excludes unconfirmed external deposits "unless a selected Escape spends them, in
which case they are counted"; `alwaysExcluded` is the reading before `F59`, under which a coin
absent from the read on one pass and present on the next leaves the floor. -/
inductive External
  | countedWhenSpent | alwaysExcluded
  deriving DecidableEq, Repr

@[req "DUR-22"]
def currentExternal : External := .countedWhenSpent

/-! ## The construction -/

/-- Add one coin to a set keyed by outpoint: two selected Escapes naming one outpoint
contribute it once. Where their claimed values disagree the greater is kept, which `DUR-22`
does not settle — a modelling choice, conservative in the direction the clause cares about,
since an inflated claim can only refuse a real Escape and never admit one. -/
def insertCoin (c : Coin) : List Coin → List Coin
  | [] => [c]
  | d :: ds => if d.1 == c.1 then (d.1, max d.2 c.2) :: ds else d :: insertCoin c ds

def dedupCoins : List Coin → List Coin
  | [] => []
  | c :: cs => insertCoin c (dedupCoins cs)

def sumValues (cs : List Coin) : Nat := (cs.map (·.2)).sum

/-- Every distinct input outpoint of the Escapes this pass counts, at its `witness_utxo` value,
"whatever the read says of it — unspent, resident, confirmed spent or unconfirmed". -/
@[req "DUR-22"]
def countedInputs (rule : Denominator) (ext : External) (p : Pass) (under : Escape) : List Coin :=
  let raw : List Coin :=
    match rule with
    | .restoreAll => p.selected.flatMap Escape.inputs
    | .restoreOne => under.inputs
  match ext with
  | .countedWhenSpent => dedupCoins raw
  | .alwaysExcluded => dedupCoins (raw.filter fun c => !(p.unconfirmedExternal.contains c.1))

/-- `DUR-22`'s protected value: the read filtered by the exclusions, then the counted inputs
added once each. A counted input takes precedence over every exclusion, and nothing is ever
subtracted. -/
@[req "DUR-22"]
def denominator (rule : Denominator) (ext : External) (p : Pass) (under : Escape) : Nat :=
  let counted := countedInputs rule ext p under
  sumValues counted +
    sumValues (p.read.filter fun c =>
      !((p.selected.flatMap Escape.outputs ++ p.residentRungs).contains c.1) &&
      !(counted.any fun d => d.1 == c.1))

/-- The combined inputs of the Escapes selected on this pass: the floor. -/
@[req "DUR-22"]
def selectedInputs (p : Pass) : Nat := sumValues (dedupCoins (p.selected.flatMap Escape.inputs))

/-! ## What the construction gives -/

/-- Within one pass every selected Escape is measured against the same value: under the rule as
it stands the Escape under evaluation is not an argument to the result. -/
@[req "DUR-22"]
theorem same_denominator_every_escape (ext : External) (p : Pass) (a b : Escape) :
    denominator .restoreAll ext p a = denominator .restoreAll ext p b := rfl

/-- The floor: on every pass the denominator is at least the combined inputs of the Escapes
selected on it. The filter can only drop coins from the base; it can never reach the counted
inputs, which is why the construction is a filter and not a subtraction. -/
@[req "DUR-22"]
theorem denominator_floor (p : Pass) (under : Escape) :
    selectedInputs p ≤ denominator .restoreAll .countedWhenSpent p under := by
  unfold selectedInputs denominator countedInputs
  exact Nat.le_add_right _ _

/-- The shape this module carried before `F59`: read plus restorations minus exclusions, as
numbers. A selected Escape spending another's change output — which `CHN-30` permits — lets the
exclusions outweigh the read, and the result falls below the floor;
`Exhibits.subtracting_breaks_floor_on_that_pass` is the trace. -/
def subtractShape (readTotal restored excludedTotal : Nat) : Nat :=
  readTotal + restored - excludedTotal

/-- `DUR-22`: "empty is an error". The model does not enforce it, and this theorem is why the
clause must: a zero denominator is covered by a zero delivery, so an empty vault would admit an
Escape that sweeps nothing. -/
@[req "DUR-22"]
theorem empty_is_covered_by_nothing (pct : Nat) : covers 0 0 pct = true := by
  unfold covers; simp

/-- The cross-pass theorem, and the reason the floor is the load-bearing property: at any coverage
at or above `MAN-9`'s floor, two Escapes whose deliveries together are within a nonzero `S`, each
measured against a denominator no smaller than `S` on whichever pass this node measured it, cannot
both cover — whatever moved the denominator between the passes, and whether or not the two
denominators are equal. -/
@[req "DUR-22"]
theorem floor_single_sweep (S d1 d2 P1 P2 pct : Nat) (hS : 0 < S) (hpct : floorPct ≤ pct)
    (hdisj : d1 + d2 ≤ S) (hf1 : S ≤ P1) (hf2 : S ≤ P2)
    (h1 : covers d1 P1 pct = true) (h2 : covers d2 P2 pct = true) : False := by
  unfold covers floorPct at *
  simp at h1 h2
  have e1 : S * pct ≤ P1 * pct := Nat.mul_le_mul_right pct hf1
  have e2 : S * pct ≤ P2 * pct := Nat.mul_le_mul_right pct hf2
  have f1 : S * 51 ≤ S * pct := Nat.mul_le_mul_left S hpct
  have g : (d1 + d2) * 100 ≤ S * 100 := Nat.mul_le_mul_right 100 hdisj
  omega

/-- The same statement with one denominator: two subsets of one value, each delivering more
than half of it, share a coin. `MAN-9` refuses a coverage at or below fifty for this reason. -/
@[req "MAN-9"]
theorem two_disjoint_cannot_both_cover (P d1 d2 pct : Nat) (hP : 0 < P) (hpct : floorPct ≤ pct)
    (hdisj : d1 + d2 ≤ P) (h1 : covers d1 P pct = true) (h2 : covers d2 P pct = true) : False :=
  floor_single_sweep P d1 d2 P P pct hP hpct hdisj (Nat.le_refl P) (Nat.le_refl P) h1 h2

/-- The per-node single sweep over the model: two selected Escapes whose combined deliveries
are within the floor cannot both cover, on whichever passes this node measured each of them.
The denominators are the construction, and the floor is what connects them — the hypotheses
that remain are a coverage at or above `MAN-9`'s floor, a nonzero `S` within each pass's selected
inputs, conservation (`CHN-14`: an Escape delivers only what it spends) and input-disjointness,
which is what "share a coin" denies. -/
@[req "DUR-22"]
theorem per_node_single_sweep (p₁ p₂ : Pass) (a b : Escape) (pct S : Nat)
    (hpct : floorPct ≤ pct) (hS : 0 < S)
    (hconserve : a.delivered + b.delivered ≤ S)
    (hf₁ : S ≤ selectedInputs p₁) (hf₂ : S ≤ selectedInputs p₂)
    (h₁ : covers a.delivered (denominator .restoreAll .countedWhenSpent p₁ a) pct = true)
    (h₂ : covers b.delivered (denominator .restoreAll .countedWhenSpent p₂ b) pct = true) :
    False :=
  floor_single_sweep S a.delivered b.delivered _ _ pct hS hpct hconserve
    (Nat.le_trans hf₁ (denominator_floor p₁ a)) (Nat.le_trans hf₂ (denominator_floor p₂ b)) h₁ h₂

/-- `DUR-24`'s fee cap, which the floor is what makes true: an Escape that covers burns at most
`100 − escape_coverage_pct` percent of the coins it moves. Written without subtraction: the
burn's hundred plus the covered fraction is at most the whole. -/
@[req "DUR-24"]
theorem burn_bound (i d P pct : Nat) (hle : d ≤ i) (hfloor : i ≤ P)
    (hc : covers d P pct = true) : (i - d) * 100 + i * pct ≤ i * 100 := by
  unfold covers at hc
  simp at hc
  have h1 : i * pct ≤ P * pct := Nat.mul_le_mul_right pct hfloor
  have hs : (i - d) * 100 + d * 100 = i * 100 := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

/-- One swept Escape, as the aggregate bound counts it: the coins it moved, what it delivered,
and the denominator of the pass it was measured on. -/
abbrev BurnRow := Nat × Nat × Nat

/-- And in aggregate over every Escape this node sweeps: `DUR-22`'s burn bound, which needs
only each Escape's own inputs to be within its own pass's denominator — the floor, per pass,
never one value across them. -/
@[req "DUR-22"]
theorem burn_bound_aggregate (rows : List BurnRow) (pct : Nat)
    (h : ∀ r ∈ rows, r.2.1 ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ covers r.2.1 r.2.2 pct = true) :
    ((rows.map fun r => r.1 - r.2.1).sum) * 100 + ((rows.map (·.1)).sum) * pct
      ≤ ((rows.map (·.1)).sum) * 100 := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have ihs := ih fun x hx => h x (by simp [hx])
    have hb := burn_bound r.1 r.2.1 r.2.2 pct hr.1 hr.2.1 hr.2.2
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    omega

/-- Under `restoreOne` the denominator collapses to the Escape's own inputs once the resident
Escape's coins have left the read: the base filter keeps nothing the counted set does not
already hold. -/
@[req "DUR-22"]
theorem restoreOne_is_the_remainder (ext : External) (p : Pass) (under : Escape)
    (hread : ∀ c ∈ p.read, ((countedInputs .restoreOne ext p under).any fun d => d.1 == c.1) = true) :
    denominator .restoreOne ext p under = sumValues (countedInputs .restoreOne ext p under) := by
  unfold denominator
  have hnil : (p.read.filter fun c =>
      !((p.selected.flatMap Escape.outputs ++ p.residentRungs).contains c.1) &&
      !((countedInputs .restoreOne ext p under).any fun d => d.1 == c.1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp [hread c hc]
  simp only [hnil, sumValues, List.map_nil, List.sum_nil, Nat.add_zero]

/-- So a second Escape that sweeps everything the first left behind covers, at every coverage
the manifest can seal: the shrink defeats every sealable floor, not only the trace's. -/
@[req "DUR-22"]
theorem restoreOne_admits_the_remainder (ext : External) (p : Pass) (under : Escape) (pct : Nat)
    (hpct : pct ≤ ceilingPct)
    (hread : ∀ c ∈ p.read, ((countedInputs .restoreOne ext p under).any fun d => d.1 == c.1) = true)
    (hdel : sumValues (countedInputs .restoreOne ext p under) ≤ under.delivered) :
    covers under.delivered (denominator .restoreOne ext p under) pct = true := by
  rw [restoreOne_is_the_remainder ext p under hread]
  unfold covers ceilingPct at *
  have h1 : sumValues (countedInputs .restoreOne ext p under) * pct
      ≤ sumValues (countedInputs .restoreOne ext p under) * 100 := Nat.mul_le_mul_left _ hpct
  have h2 : sumValues (countedInputs .restoreOne ext p under) * 100 ≤ under.delivered * 100 :=
    Nat.mul_le_mul_right 100 hdel
  simp; omega

end BtcPolicy.Coverage
