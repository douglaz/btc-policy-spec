import BtcPolicy.Policy
import BtcPolicy.Membership
import BtcPolicy.Encode
/-! Pure evaluation over decoded PSBT data. Derivation remains the named `derive` boundary.
`POL-6`: "Evaluation MUST run these checks in this order and return the first failure."
`Policy.evaluateSpend` owns that order; this module supplies its request.

Destination characterisation, exact acceptance, hint independence, first-failing-output proofs
and decided PSBT exhibits live in `Exhibits.lean`. The planted hint-trust mutation must leave
this upstream module buildable so those independent failures are checked in one build. -/

namespace BtcPolicy.Evaluate

/-- Ordered transaction data and independent PSBT maps; malformed map counts remain representable. -/
@[req "POL-7"]
structure Psbt where
  txInputs : List Encode.Input
  txOutputs : List Encode.Output
  inputMaps : List (Option Encode.Output) -- each input map's optional witness_utxo
  outputHints : List Bool -- each output map's bip32_derivation is nonempty
  deriving DecidableEq, Repr

@[req "POL-1"]
structure Cfg where
  derive : Membership.SinglePath → Nat → Option Membership.Script
  max : Nat
  vault : Membership.Descriptor
  escape : Membership.Descriptor
  allow : List Membership.Descriptor
  hotMaxPerTx : Nat

@[req "POL-7"]
def Consistent (p : Psbt) : Prop :=
  p.txInputs ≠ [] ∧ p.txOutputs ≠ [] ∧
  p.inputMaps.length = p.txInputs.length ∧ p.outputHints.length = p.txOutputs.length ∧
  none ∉ p.inputMaps

instance (p : Psbt) : Decidable (Consistent p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The tests retain their listed order, including on multiply malformed data. -/
@[req "POL-7"]
def inconsistent (p : Psbt) : Bool :=
  p.txInputs.isEmpty || p.txOutputs.isEmpty ||
  p.inputMaps.length != p.txInputs.length || p.outputHints.length != p.txOutputs.length ||
  p.inputMaps.any Option.isNone

@[req "POL-4"]
def output (cfg : Cfg) (o : Encode.Output) : Classification.Output :=
  { value := o.amount,
    kind := Membership.kindOf cfg.derive cfg.max cfg.vault cfg.escape cfg.allow o.script }

@[req "POL-4"]
theorem output_member (cfg : Cfg) (o : Encode.Output) :
    Classification.member (output cfg o) =
      Membership.kindOf cfg.derive cfg.max cfg.vault cfg.escape cfg.allow o.script :=
  Membership.member_discharged cfg.derive cfg.max cfg.vault cfg.escape cfg.allow o.script o.amount

@[req "POL-10"]
def outputs (cfg : Cfg) (p : Psbt) : List Classification.Output := p.txOutputs.map (output cfg)

@[req "POL-9"]
def owned (cfg : Cfg) (o : Encode.Output) : Bool :=
  Membership.matchesScript cfg.derive cfg.max cfg.vault o.script

@[req "POL-9"]
def Owned (cfg : Cfg) (p : Psbt) : Prop :=
  ∀ o, some o ∈ p.inputMaps → owned cfg o = true

@[req "POL-9"]
def unknownInput (cfg : Cfg) (p : Psbt) : Bool :=
  p.inputMaps.any fun m => m.any fun o => !owned cfg o

/-- The hint is available only to make the negative control fault actual recognition. -/
@[req "POL-10"]
def recognised (cfg : Cfg) (o : Encode.Output) (_hint : Bool) : Bool :=
  Classification.allowlisted [output cfg o] -- hint-trust

/-- Scan in transaction order; map lengths are checked before this scan is read. -/
@[req "POL-10"]
def firstUnknown (cfg : Cfg) : List Encode.Output → List Bool → Option Bool
  | [], _ => none
  | o :: os, hs =>
      if recognised cfg o (hs.headD false) then firstUnknown cfg os hs.tail
      else some (hs.headD false)

@[req "POL-10"]
def destination (cfg : Cfg) (p : Psbt) : Policy.Dest :=
  match firstUnknown cfg p.txOutputs p.outputHints with
  | none => .allowed
  | some true => .changeNotDerivable
  | some false => .notAllowed

@[req "POL-12"]
def totalIn (p : Psbt) : Nat := (p.inputMaps.filterMap id |>.map (·.amount)).sum

@[req "POL-12"]
def totalOut (p : Psbt) : Nat := (p.txOutputs.map (·.amount)).sum

@[req "POL-12"]
def feeOf (totalIn totalOut : Nat) : Policy.Fee :=
  if totalIn < totalOut then .inconsistent
  else if Classification.feeCapOk totalIn totalOut then .ok else .overCap

@[req "POL-6"]
def request (cfg : Cfg) (p : Psbt) : Policy.Request :=
  if inconsistent p then
    ⟨true, false, .allowed, false, .ok⟩
  else
    ⟨false, unknownInput cfg p, destination cfg p,
      !Classification.hotBudgetOk (outputs cfg p) cfg.hotMaxPerTx,
      feeOf (totalIn p) (totalOut p)⟩

@[req "POL-6"]
def evaluate (cfg : Cfg) (p : Psbt) : Option Policy.Code :=
  Policy.evaluateSpend (request cfg p)

@[req "POL-7"]
theorem inconsistent_iff (p : Psbt) :
    inconsistent p = true ↔ p.txInputs = [] ∨ p.txOutputs = [] ∨
      p.inputMaps.length ≠ p.txInputs.length ∨ p.outputHints.length ≠ p.txOutputs.length ∨
      none ∈ p.inputMaps := by
  simp [inconsistent, List.any_eq_true, Option.isNone_iff_eq_none, or_assoc]

@[req "POL-7"]
theorem consistent_iff (p : Psbt) : inconsistent p = false ↔ Consistent p := by
  simp only [Bool.eq_false_iff, ne_eq, inconsistent_iff]
  simp [Consistent]

@[req "POL-7"]
theorem psbtInconsistent_iff (cfg : Cfg) (p : Psbt) :
    (request cfg p).psbtInconsistent = true ↔ p.txInputs = [] ∨ p.txOutputs = [] ∨
      p.inputMaps.length ≠ p.txInputs.length ∨ p.outputHints.length ≠ p.txOutputs.length ∨
      none ∈ p.inputMaps := by
  simp only [request]
  split <;> simp_all [← inconsistent_iff]

@[req "POL-9"]
theorem unknownInput_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).unknownInput = true ↔
      ∃ o, some o ∈ p.inputMaps ∧
        Membership.matchesScript cfg.derive cfg.max cfg.vault o.script = false := by
  simp [request, (consistent_iff p).mpr h, unknownInput, List.any_eq_true, Option.any,
    owned]
  constructor
  · rintro ⟨m, hm, h⟩; cases m with
    | none => simp at h
    | some o => exact ⟨o, hm, by simpa using h⟩
  · rintro ⟨o, ho, h⟩; exact ⟨some o, ho, by simpa using h⟩

@[req "POL-9"]
theorem unknownInput_false_iff (cfg : Cfg) (p : Psbt) :
    unknownInput cfg p = false ↔ Owned cfg p := by
  simp [unknownInput, Owned, List.any_eq_false, Option.any]
  constructor
  · intro h o ho; simpa using h (some o) ho
  · intro h m hm; cases m with
    | none => trivial
    | some o => simpa using h o hm

@[req "POL-11"]
theorem overHotCap_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).overHotCap = true ↔
      Classification.hotBudgetOk (outputs cfg p) cfg.hotMaxPerTx = false := by
  simp [request, (consistent_iff p).mpr h]

@[req "POL-12"]
theorem feeOf_ok_iff (i o : Nat) :
    feeOf i o = .ok ↔ Classification.feeCapOk i o = true := by
  by_cases h : i < o
  · simp [feeOf, h, (Classification.overspend_refused i o h).1]
  · simp [feeOf, h]

@[req "POL-12"]
theorem feeOf_inconsistent_iff (i o : Nat) : feeOf i o = .inconsistent ↔ i < o := by
  unfold feeOf
  split <;> simp_all
  split <;> simp_all

@[req "POL-12"]
theorem fee_ok_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).fee = .ok ↔ Classification.feeCapOk (totalIn p) (totalOut p) = true := by
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte]
  exact feeOf_ok_iff _ _

@[req "POL-12"]
theorem fee_inconsistent_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).fee = .inconsistent ↔ totalIn p < totalOut p := by
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte]
  exact feeOf_inconsistent_iff _ _

@[req "POL-12"]
theorem fee_overCap_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).fee = .overCap ↔ totalOut p ≤ totalIn p ∧
      Classification.feeCapOk (totalIn p) (totalOut p) = false := by
  simp [request, (consistent_iff p).mpr h, feeOf]
  split <;> simp_all
  omega

end BtcPolicy.Evaluate
