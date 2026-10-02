import BtcPolicy.Req
/-! `POL-6`'s evaluation order and `API-13`'s closed code set (`ADR-0023` decision 10 item 6).
"Evaluation MUST run these checks in this order and return the first failure. The order is
load-bearing: `DEST_NOT_ALLOWED` outranks `HOT_BUDGET_EXCEEDED`, and `HOT_BUDGET_EXCEEDED` outranks
`FEE_EXCEEDS_CAP`". A request is abstracted to the defects each check can find; the checks
themselves (`POL-7` to `POL-12`) are not modelled, only which code each returns when it fails.
The set of codes the evaluation can return is closed and decided over every request, and
`API-24`'s claim about a `ClawbackRequest` — which codes are unreachable on it and that
`HOT_BUDGET_EXCEEDED` is reachable because "`POL-6`'s evaluation precedes classification" — is a
theorem over that set (`F57` recorded the row that had it wrong). -/

namespace BtcPolicy.Policy

/-- `API-13`: "The refusal `code` is one of exactly these strings and no other". -/
inductive Code
  | WRONG_DESCRIPTOR | UNKNOWN_INPUT | DEST_NOT_ALLOWED | CHANGE_NOT_DERIVABLE | FEE_EXCEEDS_CAP
  | BAD_SIGHASH | USER_SIG_INVALID | COMMITMENT_EXPIRED | PSBT_INCONSISTENT | BAD_PIN
  | FRAUD_SUSPECTED | COORD_AUTH_INVALID | NONCE_REPLAYED | COORD_NONCE_CAPACITY
  | CANDIDATE_CAPACITY | EXPIRY_TOO_SHORT | REFRESH_TOO_SOON | REFRESH_FEE_EXCEEDS_CAP
  | REFRESH_SUBORDINATED | HOT_BUDGET_EXCEEDED | HOT_VELOCITY_EXCEEDED
  deriving DecidableEq, Repr

/-- The twenty-one codes, in `API-13`'s table order. -/
@[req "API-13"]
def Code.all : List Code :=
  [ .WRONG_DESCRIPTOR, .UNKNOWN_INPUT, .DEST_NOT_ALLOWED, .CHANGE_NOT_DERIVABLE, .FEE_EXCEEDS_CAP,
    .BAD_SIGHASH, .USER_SIG_INVALID, .COMMITMENT_EXPIRED, .PSBT_INCONSISTENT, .BAD_PIN,
    .FRAUD_SUSPECTED, .COORD_AUTH_INVALID, .NONCE_REPLAYED, .COORD_NONCE_CAPACITY,
    .CANDIDATE_CAPACITY, .EXPIRY_TOO_SHORT, .REFRESH_TOO_SOON, .REFRESH_FEE_EXCEEDS_CAP,
    .REFRESH_SUBORDINATED, .HOT_BUDGET_EXCEEDED, .HOT_VELOCITY_EXCEEDED ]

/-- The list is the type: no code is outside it. -/
@[req "API-13"]
theorem Code.all_complete (c : Code) : c ∈ Code.all := by cases c <;> decide

/-- `POL-6`'s five checks. -/
inductive Check
  | psbtConsistency | inputOwnership | destinations | hotBudget | feeCap
  deriving DecidableEq, Repr

/-- `POL-6`'s order, rows 1 to 5. -/
@[req "POL-6"]
def Check.order : List Check :=
  [.psbtConsistency, .inputOwnership, .destinations, .hotBudget, .feeCap]

/-- Row 3's two outcomes. -/
inductive Dest
  | allowed | notAllowed | changeNotDerivable
  deriving DecidableEq, Repr

/-- Row 5's two refusals: "`PSBT_INCONSISTENT` or `FEE_EXCEEDS_CAP`". -/
inductive Fee
  | ok | inconsistent | overCap
  deriving DecidableEq, Repr

/-- A request as the checks see it: which defects it carries. -/
structure Request where
  psbtInconsistent : Bool
  unknownInput : Bool
  dest : Dest
  overHotCap : Bool
  fee : Fee
  deriving DecidableEq, Repr

/-- What each check returns when it fails, from `POL-6`'s refusal-code column. -/
@[req "POL-6"]
def failure (r : Request) : Check → Option Code
  | .psbtConsistency => if r.psbtInconsistent then some .PSBT_INCONSISTENT else none
  | .inputOwnership => if r.unknownInput then some .UNKNOWN_INPUT else none
  | .destinations =>
    match r.dest with
    | .allowed => none
    | .notAllowed => some .DEST_NOT_ALLOWED
    | .changeNotDerivable => some .CHANGE_NOT_DERIVABLE
  | .hotBudget => if r.overHotCap then some .HOT_BUDGET_EXCEEDED else none
  | .feeCap =>
    match r.fee with
    | .ok => none
    | .inconsistent => some .PSBT_INCONSISTENT
    | .overCap => some .FEE_EXCEEDS_CAP

/-- "run these checks in this order and return the first failure". The order is a parameter so
that the load-bearing claim can be stated against another order. -/
@[req "POL-6"]
def evaluate (order : List Check) (r : Request) : Option Code := order.findSome? (failure r)

/-- The evaluation as `POL-6` fixes it. -/
@[req "POL-6"]
def evaluateSpend (r : Request) : Option Code := evaluate Check.order r

/-- `POL-6`: "`DEST_NOT_ALLOWED` outranks `HOT_BUDGET_EXCEEDED`" — a request that reaches the
destination check (`h1`, `h2`) and is non-allowlisted gets it, whatever its Hot cap and its fee. -/
@[req "POL-6"]
theorem dest_outranks_budget (r : Request) (h1 : r.psbtInconsistent = false)
    (h2 : r.unknownInput = false) (h3 : r.dest = .notAllowed) :
    evaluateSpend r = some .DEST_NOT_ALLOWED := by
  simp [evaluateSpend, evaluate, Check.order, failure, h1, h2, h3]

/-- `POL-6`: "`HOT_BUDGET_EXCEEDED` outranks `FEE_EXCEEDS_CAP`" — a request that reaches the budget
check over the cap gets it, whatever its fee. -/
@[req "POL-6"]
theorem budget_outranks_fee (r : Request) (h1 : r.psbtInconsistent = false)
    (h2 : r.unknownInput = false) (h3 : r.dest = .allowed) (h4 : r.overHotCap = true) :
    evaluateSpend r = some .HOT_BUDGET_EXCEEDED := by
  simp [evaluateSpend, evaluate, Check.order, failure, h1, h2, h3, h4]

/-- The two-defect inputs, as exhibits: a theft to a stranger over the cap, and an over-cap
spend over the fee cap. -/
def strangerOverCap : Request :=
  { psbtInconsistent := false, unknownInput := false, dest := .notAllowed, overHotCap := true, fee := .ok }
def overCapOverFee : Request :=
  { psbtInconsistent := false, unknownInput := false, dest := .allowed, overHotCap := true, fee := .overCap }

/-- "The order is load-bearing": with the budget check moved ahead of the destination check, the
theft to a stranger is named as an over-cap spend and takes `SPN-19`'s propagation path; with
the fee cap ahead of the budget, the over-cap spend is named `FEE_EXCEEDS_CAP`. -/
@[req "POL-6"]
theorem order_is_load_bearing :
    evaluateSpend strangerOverCap = some .DEST_NOT_ALLOWED ∧
    evaluate [.psbtConsistency, .inputOwnership, .hotBudget, .destinations, .feeCap] strangerOverCap =
      some .HOT_BUDGET_EXCEEDED ∧
    evaluateSpend overCapOverFee = some .HOT_BUDGET_EXCEEDED ∧
    evaluate [.psbtConsistency, .inputOwnership, .destinations, .feeCap, .hotBudget] overCapOverFee =
      some .FEE_EXCEEDS_CAP := by
  decide

/-! ## The reachable set -/

/-- Every request the checks distinguish: 72. -/
def Request.all : List Request :=
  [true, false].flatMap fun p => [true, false].flatMap fun u =>
    [Dest.allowed, .notAllowed, .changeNotDerivable].flatMap fun d => [true, false].flatMap fun o =>
      [Fee.ok, .inconsistent, .overCap].map fun f =>
        { psbtInconsistent := p, unknownInput := u, dest := d, overHotCap := o, fee := f }

theorem Request.all_complete (r : Request) : r ∈ Request.all := by
  rcases r with ⟨p, u, d, o, f⟩
  cases p <;> cases u <;> cases d <;> cases o <;> cases f <;> decide

/-- The codes `POL-6`'s evaluation can return: its refusal-code column, deduplicated. -/
@[req "POL-6"]
def reachable : List Code :=
  [ .PSBT_INCONSISTENT, .UNKNOWN_INPUT, .DEST_NOT_ALLOWED, .CHANGE_NOT_DERIVABLE,
    .HOT_BUDGET_EXCEEDED, .FEE_EXCEEDS_CAP ]

/-- Sound and complete, decided over every request: the evaluation returns only these codes,
and each of them on some request. -/
@[req "POL-6"]
theorem reachable_exact :
    (Request.all.all fun r => match evaluateSpend r with
      | none => true
      | some c => reachable.contains c) = true ∧
    (reachable.all fun c => Request.all.any fun r => evaluateSpend r == some c) = true := by
  decide

@[req "POL-6"]
theorem evaluate_in_reachable (r : Request) (c : Code) (h : evaluateSpend r = some c) :
    c ∈ reachable := by
  have hall := reachable_exact.1
  rw [List.all_eq_true] at hall
  have := hall r (Request.all_complete r)
  rw [h] at this
  simpa [List.contains_iff_mem] using this

/-! ## `API-24`: the codes on a `ClawbackRequest` -/

/-- `API-24`: "`BAD_PIN`, `HOT_VELOCITY_EXCEEDED` and the three `REFRESH_*` codes are unreachable
on it". -/
@[req "API-24"]
def clawbackUnreachable : List Code :=
  [ .BAD_PIN, .HOT_VELOCITY_EXCEEDED, .REFRESH_TOO_SOON, .REFRESH_FEE_EXCEEDS_CAP, .REFRESH_SUBORDINATED ]

/-- `SPN-50` hands a `ClawbackRequest` to the same evaluation: the clawback's `POL-6` step is the
spend's. What differs is upstream of it (no PIN, no velocity reservation, no refresh bounds) and
is what `clawbackUnreachable` lists. -/
@[req "API-24"]
def evaluateClawback (r : Request) : Option Code := evaluateSpend r

/-- `API-24` as a theorem over the sets: none of the five codes it excludes is one `POL-6` can
return; `HOT_BUDGET_EXCEEDED` is one, "because `POL-6`'s evaluation precedes classification"
(`F57`: the row that excluded it was wrong); and the evaluation is the spend's. -/
@[req "API-24"]
theorem clawback_codes :
    (clawbackUnreachable.all fun c => !reachable.contains c) = true ∧
    Code.HOT_BUDGET_EXCEEDED ∈ reachable ∧
    evaluateClawback = evaluateSpend := by
  refine ⟨by decide, by decide, rfl⟩

end BtcPolicy.Policy
