import BtcPolicy.Req
/-! `SPN-5`'s gate table as a closed function: "Three columns
matter beyond the refusal: whether the gate consumed the nonce, whether a failure propagates
the request to peers, and whether it stages — counts this node as a holder of the Carrier
(`DUR-5`). Staging implies propagating." The thirty gates and the three marker rows are data
here, the three columns are small closed types, and "staging implies propagating" is decided
over every row. The gate's own content (what it checks) stays prose in the document; the three
columns are what `Render.spn5Gates` holds the document's table to (`F57`: gate 23's row). -/

namespace BtcPolicy.Gates

/-- The `nonce` column: not yet consumed, the consuming step itself, consumed before this gate,
nothing (a step that never fails or a replay), or the withdrawn row's dash. -/
inductive Nonce
  | no | yes | consumed | blank | dash
  deriving DecidableEq, Repr

/-- The `propagates` column; row 22's "only `HOT_BUDGET_EXCEEDED`" is its own value. -/
inductive Propagates
  | no | yes | onlyHotBudget | blank | dash
  deriving DecidableEq, Repr

/-- The `stages` column; row 22's "same" means the same set as `propagates`. -/
inductive Stages
  | no | yes | same | blank | dash
  deriving DecidableEq, Repr

structure Row where
  /-- The `#` cell: the gate number, or `—` for a marker row. -/
  label : String
  nonce : Nonce
  propagates : Propagates
  stages : Stages
  deriving DecidableEq, Repr

def r (label : String) (n : Nonce) (p : Propagates) (s : Stages) : Row :=
  { label := label, nonce := n, propagates := p, stages := s }

/-- `SPN-5`'s table, row for row: thirty gates and the three marker rows between them. -/
@[req "SPN-5"]
def rows : List Row :=
  [ r "1" .no .no .no, r "2" .no .no .no, r "3" .no .no .no, r "4" .no .no .no,
    r "5" .no .no .no, r "6" .no .no .no, r "7" .no .no .no, r "8" .no .no .no,
    r "—" .yes .blank .blank,
    r "9" .consumed .no .no, r "10" .consumed .yes .no,
    r "—" .blank .blank .blank,
    r "11" .consumed .no .no, r "12" .blank .blank .blank,
    r "13" .consumed .yes .yes, r "14" .consumed .yes .yes,
    r "—" .blank .blank .blank,
    r "15" .consumed .no .no, r "16" .consumed .yes .yes, r "17" .consumed .no .no,
    r "18" .consumed .no .no, r "19" .blank .yes .yes, r "20" .blank .no .no,
    r "21" .consumed .yes .yes, r "22" .consumed .onlyHotBudget .same,
    r "23" .consumed .no .no, r "24" .consumed .yes .yes, r "25" .consumed .no .no,
    r "26" .dash .dash .dash, r "27" .consumed .yes .yes, r "28" .consumed .no .no,
    r "29" .consumed .yes .yes, r "30" .blank .blank .blank ]

/-- The closed function: a gate's three columns, by its number. -/
@[req "SPN-5"]
def columns (gate : Nat) : Option (Nonce × Propagates × Stages) :=
  (rows.find? fun row => row.label == toString gate).map fun row => (row.nonce, row.propagates, row.stages)

/-- "Staging implies propagating": a row that stages propagates, and row 22 stages the same set
it propagates. -/
def stagingImpliesPropagating (row : Row) : Bool :=
  match row.stages, row.propagates with
  | .yes, .yes => true
  | .yes, _ => false
  | .same, .onlyHotBudget => true
  | .same, _ => false
  | _, _ => true

@[req "SPN-5"]
theorem staging_implies_propagating : rows.all stagingImpliesPropagating = true := by decide

/-- Thirty gates, each with a row, and every number resolves. -/
@[req "SPN-5"]
theorem thirty_gates :
    rows.length = 33 ∧ (List.range 30).all (fun i => (columns (i + 1)).isSome) = true := by decide

/-- `F57`: gate 23 — "classify; hot-class only; not mixed" — refuses locally: the nonce is
consumed, nothing propagates, nothing stages. -/
@[req "SPN-5"]
theorem gate23_refuses_locally : columns 23 = some (.consumed, .no, .no) := by decide

/-! ## The cells as the document renders them (backticked, so the match region reads them) -/

def nonceCell : Nonce → String
  | .no => "`no`" | .yes => "`yes`" | .consumed => "`consumed`" | .blank => "" | .dash => "—"

def propagatesCell : Propagates → String
  | .no => "`no`" | .yes => "`yes`" | .onlyHotBudget => "only `HOT_BUDGET_EXCEEDED`"
  | .blank => "" | .dash => "—"

def stagesCell : Stages → String
  | .no => "`no`" | .yes => "`yes`" | .same => "`same`" | .blank => "" | .dash => "—"

end BtcPolicy.Gates
