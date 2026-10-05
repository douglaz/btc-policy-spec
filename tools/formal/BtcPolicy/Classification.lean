import BtcPolicy.Req
/-! `CHN-30`'s transaction classes and its vault-output count rule, the request shapes of
`CHN-32`, `SPN-44` and `CHN-35`, `POL-11`'s hot outflow and `POL-12`'s fee cap.

The output is abstract. Its `kind` is the descriptor its script derives from, and that is an
assumption, not a derivation: `POL-4` decides membership "by **re-derivation and script
equality**", and this module takes that decision as given and names it `member`. Every theorem
here is about classification assuming `member` implements `POL-4`, not yet about real scripts;
`Membership.kindOf` discharges the assumption behind its named `derive` boundary.

`CHN-35`'s no-change rule is a guard parameter (`ADR-0023` decision 6), and the repeated burn
`F57` records is its twin under the withdrawn value. Every theorem over `current`, and every
theorem the mixed arm of `classify` decides (`DEF-15`), lives in `Exhibits.lean`, so flipping the
rule or faulting the arm goes red there and nowhere else. -/

namespace BtcPolicy.Classification

/-- What an output's script derives from, as `POL-4` would decide it. -/
inductive Kind
  | vault | escape | hot | unknown
  deriving DecidableEq, Repr

structure Output where
  value : Nat
  kind : Kind

/-- The named assumption `member`: an output's `kind` IS `POL-4`'s decision for its script. -/
@[req "POL-4"]
def member (o : Output) : Kind := o.kind

/-- A vault-change output: excluded from the class decision, counted by the count rule. -/
@[req "CHN-30"]
def inVault (o : Output) : Bool := member o == .vault

/-- The hot allowlist. `CHN-30`: "the escape descriptor is itself an allowlist entry", so an escape
output is a member too. -/
@[req "CHN-30"]
def inAllowlist (o : Output) : Bool := member o == .escape || member o == .hot

/-- `POL-10`'s destination test with classification left out: every output is vault change or on
the allowlist. -/
@[req "POL-10"]
def allowlisted (outs : List Output) : Bool := outs.all fun o => inVault o || inAllowlist o

inductive Class
  | escape | hot | refresh
  deriving DecidableEq, Repr

/-- One destination output's class. The escape test runs FIRST: run the allowlist test first and
every escape output reads as hot. -/
@[req "CHN-30"]
def outputClass (o : Output) : Option Class :=
  if member o == .escape then some .escape
  else if inAllowlist o then some .hot
  else none

/-- `CHN-30`, vault change excluded from the decision. The mixed decision is one line so the CI
control can fault it. -/
@[req "CHN-30"]
def classify (outs : List Output) : Option Class :=
  let dest := (outs.filter (!inVault ·)).map outputClass
  if dest.isEmpty then some .refresh
  else if dest.contains none then none
  else if dest.contains (some .escape) && dest.contains (some .hot) then none -- mixed
  else if dest.all (· == some .escape) then some .escape
  else some .hot

/-- An escape output is on the allowlist and still classifies escape-class: the order is what
tells them apart. -/
@[req "CHN-30"]
theorem escape_tested_first (v : Nat) :
    inAllowlist ⟨v, .escape⟩ = true ∧ classify [⟨v, .escape⟩] = some .escape := ⟨rfl, rfl⟩

/-- `CHN-30`: "In EVERY class, the number of outputs that derive from the vault descriptor MUST NOT
exceed the number of inputs". -/
@[req "CHN-30"]
def vaultOutputsBounded (inputs : Nat) (outs : List Output) : Bool :=
  (outs.filter inVault).length ≤ inputs

/-! ## `CHN-35`'s no-change rule -/

/-- `required` is `CHN-35` as it stands; `permitted` is `ADR-0022` decision 3 as first written,
which permitted vault change and which `F57` withdrew. -/
inductive NoChange
  | required | permitted
  deriving DecidableEq, Repr

/-- `CHN-35` as it stands. -/
@[req "CHN-35"]
def current : NoChange := .required

@[req "CHN-35"] def clawbackSequence : Nat := 0xfffffffd

/-- `CHN-35`: a claw-back over a non-empty set of coins, escape-class, with no vault-derived output
under `required`, every `nSequence` `0xfffffffd` and `nLockTime = 0`. -/
@[req "CHN-35"]
def clawbackOk (rule : NoChange) (nSequence : List Nat) (nLockTime : Nat) (outs : List Output) :
    Bool :=
  !nSequence.isEmpty && classify outs == some .escape &&
    (match rule with | .required => !outs.any inVault | .permitted => true) &&
    vaultOutputsBounded nSequence.length outs &&
    nSequence.all (· == clawbackSequence) && nLockTime == 0

/-! ## Request shapes -/

/-- Each request kind carries the fields checked in this module. Refresh sequence validation
is outside this abstraction; only claw-back carries sequence and lock-time fields here. -/
inductive Request
  /-- One input count for all members: `CHN-23` pairs them "over the same non-empty coin set",
  and `CHN-16` gives every rung "the same ordered input set". -/
  | spend (inputs : Nat) (primary escape : List Output) (ladder : List (List Output))
  | refresh (inputs : Nat) (outs : List Output)
  /-- Every input's `nSequence`, then `nLockTime`. -/
  | clawback (nSequence : List Nat) (nLockTime : Nat) (outs : List Output)

@[req "CHN-16"] def maxRungs : Nat := 3
@[req "SPN-44"] def maxRefreshInputs : Nat := 24

/-- `CHN-32`: "A request's Escape that classifies as anything other than escape-class MUST be
refused". The count rule also applies to every transaction, including ladder rungs. -/
@[req "CHN-32"]
def validateRequestShape (rule : NoChange) : Request → Bool
  | .spend inputs primary escape ladder =>
      0 < inputs && classify primary == some .hot && classify escape == some .escape &&
        ladder.length ≤ maxRungs && ladder.all (classify · == some .escape) &&
        (primary :: escape :: ladder).all (vaultOutputsBounded inputs)
  | .refresh inputs outs =>
      0 < inputs && !outs.isEmpty && classify outs == some .refresh &&
        vaultOutputsBounded inputs outs && inputs ≤ maxRefreshInputs
  | .clawback nSequence nLockTime outs => clawbackOk rule nSequence nLockTime outs

/-- `POL-7` refuses "a transaction with no inputs; one with no outputs". The empty-input spend
passes classification and counts; the empty-input refresh also fails the count rule.
Only a refresh can have no outputs and still have its class. -/
@[req "POL-7"]
theorem empty_refused (rule : NoChange) :
    validateRequestShape rule (.spend 0 [⟨1, .hot⟩] [⟨1, .escape⟩] []) = false ∧
    validateRequestShape rule (.refresh 0 [⟨1, .vault⟩]) = false ∧
    validateRequestShape rule (.refresh 1 []) = false := by
  cases rule <;> decide

/-- `CHN-35`: "any non-empty set of vault coins", "Every input's `nSequence` MUST be
`0xfffffffd`", and "`nLockTime` MUST be `0`". Each refusal isolates one of these guards. -/
@[req "CHN-35"]
theorem malformed_clawback_refused (rule : NoChange) :
    validateRequestShape rule (.clawback [] 0 [⟨99, .escape⟩]) = false ∧
    validateRequestShape rule (.clawback [clawbackSequence, 0xffffffff] 0 [⟨99, .escape⟩])
      = false ∧
    validateRequestShape rule (.clawback [clawbackSequence] 1 [⟨99, .escape⟩]) = false := by
  cases rule <;> decide

/-- `CHN-32`'s "anything other than": every transaction of an admitted request has its member's
class, under either rule. -/
@[req "CHN-32"]
theorem admitted_members_classed (rule : NoChange) (r : Request)
    (h : validateRequestShape rule r = true) :
    match r with
    | .spend _ primary escape ladder =>
        classify primary = some .hot ∧ classify escape = some .escape ∧
          ∀ t ∈ ladder, classify t = some .escape
    | .refresh _ outs => classify outs = some .refresh
    | .clawback _ _ outs => classify outs = some .escape := by
  cases r <;> simp [validateRequestShape, clawbackOk] at h <;> simp_all

/-- One admitted request of each kind, the ladder and the input count at their bounds, so nothing
here holds vacuously; one past either bound is refused. -/
@[req "CHN-32"]
theorem each_kind_admitted (rule : NoChange) :
    validateRequestShape rule (.spend 1 [⟨90, .hot⟩, ⟨9, .vault⟩] [⟨99, .escape⟩]
      [[⟨98, .escape⟩], [⟨97, .escape⟩], [⟨96, .escape⟩]]) = true ∧
    validateRequestShape rule (.refresh 24 [⟨99, .vault⟩]) = true ∧
    validateRequestShape rule (.clawback [clawbackSequence, clawbackSequence] 0 [⟨99, .escape⟩])
      = true ∧
    validateRequestShape rule (.spend 1 [⟨90, .hot⟩] [⟨99, .escape⟩]
      [[⟨98, .escape⟩], [⟨97, .escape⟩], [⟨96, .escape⟩], [⟨95, .escape⟩]]) = false ∧
    validateRequestShape rule (.refresh 25 [⟨99, .vault⟩]) = false := by
  cases rule <;> decide

/-- `CHN-30`'s count rule: a refresh fanning one coin into two vault outputs is refresh-class and
refused; one in, one out passes. -/
@[req "CHN-30"]
theorem fan_out_refused (rule : NoChange) :
    classify [⟨50, .vault⟩, ⟨50, .vault⟩] = some .refresh ∧
    vaultOutputsBounded 1 [⟨50, .vault⟩, ⟨50, .vault⟩] = false ∧
    validateRequestShape rule (.refresh 1 [⟨50, .vault⟩, ⟨50, .vault⟩]) = false ∧
    validateRequestShape rule (.refresh 1 [⟨100, .vault⟩]) = true := by
  cases rule <;> decide

/-- Fan-out is refused independently in the primary, Escape, and ladder; a second input admits
the otherwise unchanged shape. -/
@[req "CHN-30"]
theorem spend_fan_out_refused (rule : NoChange) :
    let hot := [⟨90, .hot⟩, ⟨4, .vault⟩, ⟨5, .vault⟩]
    let escape := [⟨90, .escape⟩, ⟨4, .vault⟩, ⟨5, .vault⟩]
    validateRequestShape rule (.spend 1 hot [⟨99, .escape⟩] []) = false ∧
    validateRequestShape rule (.spend 2 hot [⟨99, .escape⟩] []) = true ∧
    validateRequestShape rule (.spend 1 [⟨99, .hot⟩] escape []) = false ∧
    validateRequestShape rule (.spend 2 [⟨99, .hot⟩] escape []) = true ∧
    validateRequestShape rule (.spend 1 [⟨99, .hot⟩] [⟨99, .escape⟩] [escape]) = false ∧
    validateRequestShape rule (.spend 2 [⟨99, .hot⟩] [⟨99, .escape⟩] [escape]) = true := by
  cases rule <;> decide

/-- `CHN-32`: a SpendRequest whose primary is escape-class is refused, for every Escape and ladder. -/
@[req "CHN-32"]
theorem escape_primary_refused (rule : NoChange) (inputs : Nat) (primary escape : List Output)
    (ladder : List (List Output)) (h : classify primary = some .escape) :
    validateRequestShape rule (.spend inputs primary escape ladder) = false := by
  simp [validateRequestShape, h]

/-- `CHN-32`: a ClawbackRequest whose transaction is hot-class is refused, under either rule. -/
@[req "CHN-32"]
theorem hot_clawback_refused (rule : NoChange) (nSequence : List Nat) (nLockTime : Nat)
    (outs : List Output) (h : classify outs = some .hot) :
    validateRequestShape rule (.clawback nSequence nLockTime outs) = false := by
  simp [validateRequestShape, clawbackOk, h]

/-! ## `POL-11`'s hot outflow -/

/-- `POL-11`'s saturation bound, the largest `u64`. -/
@[req "POL-11"] def maxValue : Nat := 2 ^ 64 - 1

/-- The values `POL-11` counts: every output except vault-derived and escape-derived ones, so an
output no descriptor recognises counts. -/
@[req "POL-11"]
def counted (outs : List Output) : List Nat :=
  (outs.filter fun o => !inVault o && member o != .escape).map (·.value)

@[req "POL-11"]
def hotOutflow (outs : List Output) : Nat :=
  (counted outs).foldr (fun v acc => min (v + acc) maxValue) 0

/-- `POL-11`: "`hot_outflow > hot_max_per_tx` MUST be refused". -/
@[req "POL-11"]
def hotBudgetOk (outs : List Output) (cap : Nat) : Bool := hotOutflow outs ≤ cap

/-- The saturating sum is the plain sum, capped. -/
@[req "POL-11"]
theorem hotOutflow_eq_min (outs : List Output) :
    hotOutflow outs = min (counted outs).sum maxValue := by
  unfold hotOutflow
  generalize counted outs = vs
  induction vs with
  | nil => simp
  | cons v vs ih => simp [List.foldr, ih]; omega

/-- It agrees with the plain `Nat` sum wherever saturation is unreachable. -/
@[req "POL-11"]
theorem hotOutflow_agrees (outs : List Output) (h : (counted outs).sum ≤ maxValue) :
    hotOutflow outs = (counted outs).sum := by
  rw [hotOutflow_eq_min]; omega

/-- Over-counting can only refuse: an output added anywhere never lowers the outflow. -/
@[req "POL-11"]
theorem hotOutflow_monotone (l₁ l₂ : List Output) (o : Output) :
    hotOutflow (l₁ ++ l₂) ≤ hotOutflow (l₁ ++ o :: l₂) := by
  rw [hotOutflow_eq_min, hotOutflow_eq_min]
  simp only [counted, List.filter_append, List.filter_cons, List.map_append, List.sum_append]
  split <;> simp <;> omega

/-- Equality passes, any outflow over the cap is refused, and the exclusions are the stated ones:
vault and escape outputs are not counted, a hot and an unrecognised one are. -/
@[req "POL-11"]
theorem hot_budget_boundary (outs : List Output) (cap : Nat) :
    hotBudgetOk outs (hotOutflow outs) = true ∧
    (cap < hotOutflow outs → hotBudgetOk outs cap = false) ∧
    hotOutflow [⟨5, .vault⟩, ⟨7, .escape⟩, ⟨11, .hot⟩, ⟨13, .unknown⟩] = 24 := by
  refine ⟨by simp [hotBudgetOk], fun h => ?_, by decide⟩
  simp [hotBudgetOk]; omega

/-! ## `POL-12`'s fee cap -/

/-- `POL-12`: "The 10% is a fixed constant for every class". -/
@[req "POL-12"] def feeCapPct : Nat := 10

/-- `POL-12`: `total_out > total_in` is refused before any subtraction; then
`fee × 100 > 10 × total_in` is. -/
@[req "POL-12"]
def feeCapOk (totalIn totalOut : Nat) : Bool :=
  totalOut ≤ totalIn && (totalIn - totalOut) * 100 ≤ feeCapPct * totalIn

/-- An overspend is refused by the first conjunct: the second alone passes it, because `Nat`
subtraction truncates the negative fee to zero. -/
@[req "POL-12"]
theorem overspend_refused (totalIn totalOut : Nat) (h : totalIn < totalOut) :
    feeCapOk totalIn totalOut = false ∧ (totalIn - totalOut) * 100 ≤ feeCapPct * totalIn := by
  simp [feeCapOk]; omega

/-- Exactly ten percent passes; one satoshi more is refused. -/
@[req "POL-12"]
theorem fee_cap_boundary : feeCapOk 1000 900 = true ∧ feeCapOk 1000 899 = false := by decide

/-! ## `F57`'s twin: the burn under `permitted`

`CHN-35`: "with vault change permitted, an attacker holding the user key and the coordinator
credential could pay a little to the escape wallet, burn `POL-12`'s ten percent, return the rest
as change, wait a block and repeat until the vault was fees". -/

/-- The change the burn returns to the vault from a coin of value `v`. -/
@[req "CHN-35"]
def change (v dust : Nat) : Nat := v - v * feeCapPct / 100 - dust

/-- The burn over one coin: `dust` to the escape wallet, the rest back to the vault as change,
`POL-12`'s ten percent to fees. -/
@[req "CHN-35"]
def burn (v dust : Nat) : List Output := [⟨dust, .escape⟩, ⟨change v dust, .vault⟩]

/-- The burn as a one-input ClawbackRequest, admitted by its shape under `rule` and by `POL-12`. -/
@[req "CHN-35"]
def burnAdmitted (rule : NoChange) (v dust : Nat) : Bool :=
  validateRequestShape rule (.clawback [clawbackSequence] 0 (burn v dust)) &&
    feeCapOk v ((burn v dust).map (·.value)).sum

/-- Under `permitted` the burn is admitted over every coin that can pay the dust, and so again over
its change, which is a vault coin: the same theorem each block until the change cannot pay the
dust. -/
@[req "CHN-35"]
theorem permitted_burns_again (v dust : Nat) (h : dust ≤ v) :
    burnAdmitted .permitted v dust = true ∧
      (dust ≤ change v dust → burnAdmitted .permitted (change v dust) dust = true) := by
  have key : ∀ w, dust ≤ w → burnAdmitted .permitted w dust = true := by
    intro w hw
    simp [burnAdmitted, validateRequestShape, clawbackOk, burn, classify, outputClass, inVault,
      member, vaultOutputsBounded, feeCapOk, feeCapPct, change]
    omega
  exact ⟨key v h, key _⟩

/-- Under `required` an admitted claw-back pays no vault coin at all, so no coin it spends comes
back to be swept again. -/
@[req "CHN-35"]
theorem required_pays_no_vault_coin (nSequence : List Nat) (nLockTime : Nat) (outs : List Output)
    (h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true) :
    ∀ o ∈ outs, inVault o = false := by
  simp [validateRequestShape, clawbackOk] at h
  simp_all

/-! ## `DEF-15`'s exhibit -/

/-- `CHN-31`'s "99%-to-hot plus dust-to-escape spend". -/
@[req "CHN-31"]
def mixedSpend : List Output := [⟨99, .hot⟩, ⟨1, .escape⟩]

end BtcPolicy.Classification
