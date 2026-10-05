import BtcPolicy.Policy
import BtcPolicy.Membership
import BtcPolicy.Encode
/-! Pure evaluation over decoded PSBT data. Derivation remains the named `derive` boundary.
`POL-6`: "Evaluation MUST run these checks in this order and return the first failure."
`Policy.evaluateSpend` owns that order; this module supplies its request.

This module proves destination characterisation, exact acceptance, hint independence for
equal-length hint lists (including malformed maps), and the first failing output under
consistency and input-ownership assumptions. Decided PSBT exhibits live in `Exhibits.lean`. -/

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

/-- Recognition uses the derived output kind to test vault or allowlist membership. -/
@[req "POL-10"]
def recognised (cfg : Cfg) (o : Encode.Output) : Bool :=
  Classification.allowlisted [output cfg o]

/-- One slot per transaction output, retaining recognised positions and each output's own hint.
The verdict and diagnostics consume this same scan, including malformed hint lists. -/
@[req "POL-10"]
def outputChecks (cfg : Cfg) : List Encode.Output → List Bool → List (Option Bool)
  | [], _ => []
  | o :: os, hs =>
      (if recognised cfg o then none else some (hs.headD false)) :: -- hint-trust
        outputChecks cfg os hs.tail

/-- Scan in transaction order; map lengths are checked before this scan is read. -/
@[req "POL-10"]
def firstUnknown (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) : Option Bool :=
  (outputChecks cfg os hs).findSome? id

@[req "POL-10"]
theorem firstUnknown_nil (cfg : Cfg) (hs : List Bool) :
    firstUnknown cfg [] hs = none := rfl

@[req "POL-10"]
theorem firstUnknown_cons (cfg : Cfg) (o : Encode.Output) (os : List Encode.Output)
    (hs : List Bool) :
    firstUnknown cfg (o :: os) hs =
      if recognised cfg o then firstUnknown cfg os hs.tail else some (hs.headD false) := by
  cases hr : recognised cfg o <;> simp [firstUnknown, outputChecks, hr]

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

instance (cfg : Cfg) (p : Psbt) : Decidable (Owned cfg p) :=
  decidable_of_iff (unknownInput cfg p = false) (unknownInput_false_iff cfg p)

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

@[req "POL-10"]
def softenCode : Policy.Code → Policy.Code
  | .CHANGE_NOT_DERIVABLE => .DEST_NOT_ALLOWED
  | c => c

/-- Only the destination refusal spelling is collapsed; acceptance and other codes stay put.
Replacing the hints with an equal-length list preserves the verdict after that collapse,
including malformed PSBTs whose output-map count differs from the transaction output count. -/
@[req "POL-10"]
theorem hints_never_admit (cfg : Cfg) (p : Psbt) (hs : List Bool)
    (hlen : hs.length = p.outputHints.length) :
    (evaluate cfg { p with outputHints := hs }).map softenCode =
      (evaluate cfg p).map softenCode := by
  have scan : ∀ os a b, (firstUnknown cfg os a).isSome = (firstUnknown cfg os b).isSome := by
    intro os
    induction os with
    | nil => intro a b; rfl
    | cons o os ih =>
      intro a b
      simp only [firstUnknown_cons, recognised]
      split
      · exact ih a.tail b.tail
      · rfl
  have same : inconsistent { p with outputHints := hs } = inconsistent p := by
    simp [inconsistent, hlen]
  simp only [evaluate, request, same]
  by_cases hc : inconsistent p = true
  · simp [hc]
  · simp only [hc]
    have hscan := scan p.txOutputs hs p.outputHints
    simp only [destination, unknownInput, outputs, totalIn, totalOut]
    cases ha : firstUnknown cfg p.txOutputs hs with
    | none =>
      cases hb : firstUnknown cfg p.txOutputs p.outputHints with
      | none => rfl
      | some b => simp [ha, hb] at hscan
    | some a =>
      cases hb : firstUnknown cfg p.txOutputs p.outputHints with
      | none => simp [ha, hb] at hscan
      | some b =>
        generalize p.inputMaps.any (fun m => m.any fun o => !owned cfg o) = u
        cases u <;> cases a <;> cases b <;>
          simp [Policy.evaluateSpend, Policy.evaluate, Policy.Check.order, Policy.failure,
            softenCode, List.findSome?]

@[req "POL-10"]
theorem hints_acceptance_iff (cfg : Cfg) (p : Psbt) (hs : List Bool)
    (hlen : hs.length = p.outputHints.length) :
    evaluate cfg { p with outputHints := hs } = none ↔ evaluate cfg p = none := by
  have h := hints_never_admit cfg p hs hlen
  have hnone := congrArg (fun x => x = none) h
  simpa using hnone

@[req "POL-10"]
theorem recognised_iff (cfg : Cfg) (o : Encode.Output) :
    recognised cfg o = true ↔ (output cfg o).kind ≠ .unknown := by
  simp only [recognised, Classification.allowlisted, List.all_cons, List.all_nil,
    Bool.and_true, Classification.inVault, Classification.inAllowlist]
  rw [output_member]
  cases hk : Membership.kindOf cfg.derive cfg.max cfg.vault cfg.escape cfg.allow o.script <;>
    simp [output, hk]

@[req "POL-10"]
theorem firstUnknown_none_iff (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) :
    firstUnknown cfg os hs = none ↔ ∀ o ∈ os, (output cfg o).kind ≠ .unknown := by
  induction os generalizing hs with
  | nil => simp [firstUnknown_nil]
  | cons o os ih =>
    simp only [firstUnknown_cons]
    split <;> simp_all [recognised_iff]

/-- A recognised prefix followed by an unknown output identifies the least unknown position.
The suffix is unrestricted, including all of its hints. -/
@[req "POL-10"]
def FirstAt (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) (hint : Bool) : Prop :=
  ∃ pre o post, os = pre ++ o :: post ∧
    (∀ x ∈ pre, (output cfg x).kind ≠ .unknown) ∧
    (output cfg o).kind = .unknown ∧ hs[pre.length]?.getD false = hint

@[req "POL-10"]
theorem firstUnknown_some_iff (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) (b : Bool) :
    firstUnknown cfg os hs = some b ↔ FirstAt cfg os hs b := by
  induction os generalizing hs with
  | nil => simp [firstUnknown_nil, FirstAt]
  | cons o os ih =>
    simp only [firstUnknown_cons]
    by_cases hk : (output cfg o).kind = .unknown
    · have hr : recognised cfg o = false := by
        simpa [Bool.eq_false_iff, recognised_iff] using hk
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hb
        exact ⟨[], o, os, rfl, by simp, hk, by cases hs <;> simpa using hb⟩
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        cases pre with
        | nil => simp only [List.nil_append, List.cons.injEq] at he
                 obtain ⟨rfl, rfl⟩ := he
                 cases hs <;> simpa using hb
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, _⟩ := he
          exact False.elim (hp o (by simp) hk)
    · have hr := (recognised_iff cfg o).mpr hk
      simp only [hr, ↓reduceIte, ih]
      constructor
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        refine ⟨o :: pre, x, post, by simp [he], ?_, hx, ?_⟩
        · simpa using And.intro hk hp
        · simpa using hb
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, _⟩ := he
          exact False.elim (hk hx)
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, he⟩ := he
          exact ⟨pre, x, post, he, fun z hz => hp z (by simp [hz]), hx, by simpa using hb⟩

@[req "POL-10"]
theorem allowlisted_iff (cfg : Cfg) (p : Psbt) :
    Classification.allowlisted (outputs cfg p) = true ↔
      ∀ o ∈ p.txOutputs, (output cfg o).kind ≠ .unknown := by
  simp only [outputs, Classification.allowlisted, List.all_map, List.all_eq_true]
  apply forall_congr'; intro o
  apply imp_congr_right; intro _
  simpa [recognised, Classification.allowlisted] using recognised_iff cfg o

@[req "POL-10"]
theorem dest_allowed_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .allowed ↔
      ∀ o ∈ p.txOutputs, (output cfg o).kind ≠ .unknown := by
  rw [← firstUnknown_none_iff cfg p.txOutputs p.outputHints]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-10"]
theorem dest_notAllowed_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .notAllowed ↔ FirstAt cfg p.txOutputs p.outputHints false := by
  rw [← firstUnknown_some_iff]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-10"]
theorem dest_changeNotDerivable_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .changeNotDerivable ↔ FirstAt cfg p.txOutputs p.outputHints true := by
  rw [← firstUnknown_some_iff]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-6"]
theorem acceptance_exact (cfg : Cfg) (p : Psbt) :
    evaluate cfg p = none ↔ Consistent p ∧ Owned cfg p ∧
      Classification.allowlisted (outputs cfg p) = true ∧
      Classification.hotBudgetOk (outputs cfg p) cfg.hotMaxPerTx = true ∧
      Classification.feeCapOk (totalIn p) (totalOut p) = true := by
  have abstract (r : Policy.Request) : Policy.evaluateSpend r = none ↔
      r.psbtInconsistent = false ∧ r.unknownInput = false ∧ r.dest = .allowed ∧
      r.overHotCap = false ∧ r.fee = .ok := by
    rcases r with ⟨a,b,c,d,e⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  by_cases hc : Consistent p
  · rw [evaluate, abstract]
    have hd := dest_allowed_iff cfg p hc
    rw [← allowlisted_iff] at hd
    simp only [request, (consistent_iff p).mpr hc, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    simp [hc, hd, unknownInput_false_iff, feeOf_ok_iff]
  · have hi : inconsistent p = true := by
      cases hi : inconsistent p
      · exact False.elim (hc ((consistent_iff p).mp hi))
      · rfl
    simp [evaluate, request, hi, hc, Policy.evaluateSpend, Policy.evaluate,
      Policy.Check.order, Policy.failure]

@[req "POL-10"]
theorem first_failing_output (cfg : Cfg) (p : Psbt) (hc : Consistent p) (ho : Owned cfg p)
    (pre : List Encode.Output) (o : Encode.Output) (post : List Encode.Output)
    (hp : p.txOutputs = pre ++ o :: post)
    (hr : ∀ x ∈ pre, (output cfg x).kind ≠ .unknown) (hu : (output cfg o).kind = .unknown) :
    evaluate cfg p = some (if p.outputHints[pre.length]?.getD false then
      .CHANGE_NOT_DERIVABLE else .DEST_NOT_ALLOWED) := by
  have hs := (firstUnknown_some_iff cfg p.txOutputs p.outputHints
    (p.outputHints[pre.length]?.getD false)).mpr ⟨pre, o, post, hp, hr, hu, rfl⟩
  have hi := (unknownInput_false_iff cfg p).mpr ho
  simp only [evaluate, request, (consistent_iff p).mpr hc, Bool.false_eq_true, ↓reduceIte,
    hi, destination, hs]
  cases p.outputHints[pre.length]?.getD false <;>
    simp [Policy.evaluateSpend, Policy.evaluate, Policy.Check.order, Policy.failure]

/-! ## Complete pure-check diagnostics

Check-local lists exist independently of reachability. `faults` selects only the first
refusing eligible check; its empty list also represents acceptance and ineligible refusals.
The caller supplies one decoded transaction; chain checks and the outer transaction role
remain outside this model. -/

@[req "API-25"]
inductive Side
  | input | output
  deriving DecidableEq, Repr

@[req "API-25"]
structure Fault where
  side : Side
  index : Nat
  code : Policy.Code
  deriving DecidableEq, Repr

/-- Retain original positions even when a passing slot emits no entry. -/
@[req "API-25"]
def indexedFaults (side : Side) : List (Option Policy.Code) → Nat → List Fault
  | [], _ => []
  | c :: cs, i =>
      match c with
      | none => indexedFaults side cs (i + 1)
      | some code => ⟨side, i, code⟩ :: indexedFaults side cs (i + 1)

@[req "POL-7"]
def structural (p : Psbt) : Bool :=
  p.txInputs.isEmpty || p.txOutputs.isEmpty ||
    p.inputMaps.length != p.txInputs.length || p.outputHints.length != p.txOutputs.length

@[req "POL-7"]
theorem structural_false_iff (p : Psbt) :
    structural p = false ↔ p.txInputs ≠ [] ∧ p.txOutputs ≠ [] ∧
      p.inputMaps.length = p.txInputs.length ∧ p.outputHints.length = p.txOutputs.length := by
  simp [structural, and_assoc]

@[req "POL-7"]
def missingFaults (p : Psbt) : List Fault :=
  indexedFaults .input (p.inputMaps.map fun m => if m.isNone then some .PSBT_INCONSISTENT else none) 0

@[req "POL-9"]
def ownershipFaults (cfg : Cfg) (p : Psbt) : List Fault :=
  indexedFaults .input
    (p.inputMaps.map fun m => if m.any (fun o => !owned cfg o) then some .UNKNOWN_INPUT else none) 0

@[req "POL-10"]
def hintCode (hint : Bool) : Policy.Code :=
  if hint then .CHANGE_NOT_DERIVABLE else .DEST_NOT_ALLOWED

@[req "POL-10"]
def destinationFaults (cfg : Cfg) (p : Psbt) : List Fault :=
  indexedFaults .output ((outputChecks cfg p.txOutputs p.outputHints).map (Option.map hintCode)) 0

@[req "API-25"]
def faults (cfg : Cfg) (p : Psbt) : List Fault :=
  if structural p then []
  else if inconsistent p then missingFaults p
  else if unknownInput cfg p then ownershipFaults cfg p
  else destinationFaults cfg p -- fault-output-order

@[req "API-25"]
def transmitted (cfg : Cfg) (p : Psbt) : List Fault := (faults cfg p).take 32

@[req "API-25"]
def truncated (cfg : Cfg) (p : Psbt) : Bool := 32 < (faults cfg p).length

@[req "API-25"]
theorem indexedFaults_empty_iff (side : Side) (cs : List (Option Policy.Code)) (start : Nat) :
    indexedFaults side cs start = [] ↔ ∀ c ∈ cs, c = none := by
  induction cs generalizing start with
  | nil => simp [indexedFaults]
  | cons c cs ih => cases c <;> simp [indexedFaults, ih]

/-- Exact membership proves both inclusion of every failing slot and absence of invented entries. -/
@[req "API-25"]
theorem indexedFaults_mem_iff (side : Side) (cs : List (Option Policy.Code)) (start : Nat)
    (f : Fault) :
    f ∈ indexedFaults side cs start ↔
      f.side = side ∧ ∃ j, cs[j]? = some (some f.code) ∧ f.index = start + j := by
  induction cs generalizing start with
  | nil => simp [indexedFaults]
  | cons c cs ih =>
    cases c with
    | none =>
      simp only [indexedFaults, ih]
      constructor
      · rintro ⟨hs, j, hj, hi⟩
        exact ⟨hs, j + 1, by simpa using hj, by omega⟩
      · rintro ⟨hs, j, hj, hi⟩
        cases j with
        | zero => simp at hj
        | succ j => exact ⟨hs, j, by simpa using hj, by omega⟩
    | some code =>
      simp only [indexedFaults, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hs, j, hj, hi⟩)
        · exact ⟨rfl, 0, rfl, by simp⟩
        · exact ⟨hs, j + 1, by simpa using hj, by omega⟩
      · rintro ⟨hs, j, hj, hi⟩
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          left
          cases f
          simp_all
        | succ j => exact Or.inr ⟨hs, j, by simpa using hj, by omega⟩

@[req "API-25"]
theorem indexedFaults_ascending (side : Side) (cs : List (Option Policy.Code)) (start : Nat) :
    (indexedFaults side cs start).Pairwise (fun a b => a.index < b.index) := by
  induction cs generalizing start with
  | nil => simp [indexedFaults]
  | cons c cs ih =>
    cases c with
    | none => exact ih _
    | some code =>
      simp only [indexedFaults, List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro f hf
      obtain ⟨_, j, _, hj⟩ := (indexedFaults_mem_iff _ _ _ _).mp hf
      change start < f.index
      omega

@[req "POL-7"]
theorem missingFaults_empty_iff (p : Psbt) : missingFaults p = [] ↔ none ∉ p.inputMaps := by
  simp only [missingFaults, indexedFaults_empty_iff, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  simp only [ite_eq_right_iff, Option.isNone_iff_eq_none, Option.some_ne_none, imp_false]
  constructor
  · intro h hn; exact h none hn rfl
  · intro hn a ha he; subst a; exact hn ha

@[req "POL-7"]
theorem missingFaults_reached_empty_iff (p : Psbt) (hs : structural p = false) :
    missingFaults p = [] ↔ Consistent p := by
  obtain ⟨hi, ho, hm, hh⟩ := (structural_false_iff p).mp hs
  simp [missingFaults_empty_iff, Consistent, hi, ho, hm, hh]

@[req "POL-9"]
theorem ownershipFaults_empty_iff (cfg : Cfg) (p : Psbt) :
    ownershipFaults cfg p = [] ↔ Owned cfg p := by
  rw [← unknownInput_false_iff]
  simp [ownershipFaults, indexedFaults_empty_iff, unknownInput, List.any_eq_false]

@[req "POL-10"]
theorem outputChecks_empty_iff (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) :
    (∀ c ∈ outputChecks cfg os hs, c = none) ↔ ∀ o ∈ os, recognised cfg o = true := by
  induction os generalizing hs with
  | nil => simp [outputChecks]
  | cons o os ih => cases hr : recognised cfg o <;> simp [outputChecks, hr, ih]

@[req "POL-10"]
theorem destinationFaults_empty_iff (cfg : Cfg) (p : Psbt) :
    destinationFaults cfg p = [] ↔ ∀ o ∈ p.txOutputs, recognised cfg o = true := by
  simp [destinationFaults, indexedFaults_empty_iff, outputChecks_empty_iff]

/-- The missing-metadata row is reached only after the structural rows pass. -/
@[req "POL-7"]
theorem missingFaults_selected (cfg : Cfg) (p : Psbt) (hs : structural p = false)
    (hm : none ∈ p.inputMaps) :
    faults cfg p = missingFaults p ∧ missingFaults p ≠ [] := by
  have hi : inconsistent p = true := (inconsistent_iff p).mpr (by simp [hm])
  simp [faults, hs, hi, missingFaults_empty_iff, hm]

@[req "POL-9"]
theorem ownershipFaults_selected (cfg : Cfg) (p : Psbt) (hc : Consistent p)
    (ho : ¬ Owned cfg p) :
    faults cfg p = ownershipFaults cfg p ∧ ownershipFaults cfg p ≠ [] := by
  have hs : structural p = false := by
    rcases hc with ⟨hi, hout, hm, hh, _⟩
    simp [structural, hi, hout, hm, hh]
  have hu : unknownInput cfg p = true := by
    cases hu : unknownInput cfg p with
    | false => exact False.elim (ho ((unknownInput_false_iff cfg p).mp hu))
    | true => rfl
  simp [faults, hs, (consistent_iff p).mpr hc, hu, ownershipFaults_empty_iff, ho]

/-- This boundary also includes the passing destination check: later budget and fee verdicts
never supply diagnostics. -/
@[req "POL-10"]
theorem destinationFaults_selected (cfg : Cfg) (p : Psbt) (hc : Consistent p)
    (ho : Owned cfg p) : faults cfg p = destinationFaults cfg p := by
  have hs : structural p = false := by
    rcases hc with ⟨hi, hout, hm, hh, _⟩
    simp [structural, hi, hout, hm, hh]
  simp [faults, hs, (consistent_iff p).mpr hc, (unknownInput_false_iff cfg p).mpr ho]

@[req "API-25"]
theorem structural_suppresses_faults (cfg : Cfg) (p : Psbt) (hs : structural p = true) :
    faults cfg p = [] := by simp [faults, hs]

@[req "API-25"]
theorem indexedFaults_head_code (side : Side) (cs : List (Option Policy.Code)) (start : Nat) :
    (indexedFaults side cs start).head?.map Fault.code = cs.findSome? id := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [indexedFaults, ih]

@[req "API-25"]
theorem indexedFaults_constant_code (side : Side) (xs : List α) (bad : α → Bool)
    (code : Policy.Code) (start : Nat) (f : Fault)
    (hf : f ∈ indexedFaults side (xs.map fun x => if bad x then some code else none) start) :
    f.code = code := by
  induction xs generalizing start with
  | nil => simp [indexedFaults] at hf
  | cons x xs ih =>
    cases hx : bad x <;> simp [indexedFaults, hx] at hf
    · exact ih _ hf
    · rcases hf with rfl | hf
      · rfl
      · exact ih _ hf

@[req "POL-10"]
theorem destinationFaults_head_code (cfg : Cfg) (p : Psbt) :
    (destinationFaults cfg p).head?.map Fault.code =
      (firstUnknown cfg p.txOutputs p.outputHints).map hintCode := by
  rw [destinationFaults, indexedFaults_head_code]
  unfold firstUnknown
  generalize outputChecks cfg p.txOutputs p.outputHints = cs
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [ih]

/-- Nonempty diagnostics agree with the unchanged ordered evaluator, for every decoded PSBT. -/
@[req "API-25"]
theorem faults_head_code (cfg : Cfg) (p : Psbt) (f : Fault)
    (hf : (faults cfg p).head? = some f) : evaluate cfg p = some f.code := by
  by_cases hs : structural p = true
  · simp [faults, hs] at hf
  · by_cases hc : inconsistent p = true
    · have hm : f ∈ missingFaults p := by
        exact List.mem_of_head? (by simpa [faults, hs, hc] using hf)
      have code := indexedFaults_constant_code .input p.inputMaps Option.isNone
        .PSBT_INCONSISTENT 0 f hm
      simp [evaluate, request, hc, code, Policy.evaluateSpend, Policy.evaluate,
        Policy.Check.order, Policy.failure]
    · by_cases ho : unknownInput cfg p = true
      · have hm : f ∈ ownershipFaults cfg p := by
          exact List.mem_of_head? (by simpa [faults, hs, hc, ho] using hf)
        have code := indexedFaults_constant_code .input p.inputMaps
          (fun m => m.any fun o => !owned cfg o) .UNKNOWN_INPUT 0 f hm
        simp [evaluate, request, hc, ho, code, Policy.evaluateSpend, Policy.evaluate,
          Policy.Check.order, Policy.failure]
      · have hd := destinationFaults_head_code cfg p
        have hhead : (destinationFaults cfg p).head? = some f := by
          simpa [faults, hs, hc, ho] using hf
        rw [hhead] at hd
        cases hu : firstUnknown cfg p.txOutputs p.outputHints with
        | none => simp [hu] at hd
        | some b =>
          have code : f.code = hintCode b := by simpa [hu] using hd
          cases b <;> simp [evaluate, request, hc, ho, destination, hu, code, hintCode,
            Policy.evaluateSpend, Policy.evaluate, Policy.Check.order, Policy.failure]

@[req "API-25"]
theorem faults_nonempty_refuses (cfg : Cfg) (p : Psbt) (h : faults cfg p ≠ []) :
    ∃ f, (faults cfg p).head? = some f ∧ evaluate cfg p = some f.code := by
  cases he : faults cfg p with
  | nil => exact False.elim (h he)
  | cons f fs => exact ⟨f, by simp, faults_head_code cfg p f (by simp [he])⟩

@[req "API-25"]
theorem accepted_faults_empty (cfg : Cfg) (p : Psbt) (h : evaluate cfg p = none) :
    faults cfg p = [] := by
  by_cases hn : faults cfg p = []
  · exact hn
  · obtain ⟨f, _, hf⟩ := faults_nonempty_refuses cfg p hn
    simp [h] at hf

@[req "POL-10"]
theorem outputChecks_get (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) (j : Nat) :
    (outputChecks cfg os hs)[j]? =
      os[j]?.map (fun o => if recognised cfg o then none else some (hs[j]?.getD false)) := by
  induction os generalizing hs j with
  | nil => simp [outputChecks]
  | cons o os ih =>
    cases j with
    | zero => cases hs <;> simp [outputChecks, List.headD]
    | succ j => simpa [outputChecks] using ih hs.tail j

@[req "POL-7"]
theorem missingFaults_mem_iff (p : Psbt) (f : Fault) :
    f ∈ missingFaults p ↔ f.side = .input ∧
      p.inputMaps[f.index]? = some none ∧ f.code = .PSBT_INCONSISTENT := by
  rw [missingFaults, indexedFaults_mem_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨hs, j, hj, rfl⟩
    simp only [List.getElem?_map] at hj
    cases hm : p.inputMaps[f.index]? with
    | none => simp [hm] at hj
    | some m => cases m <;> simp_all
  · rintro ⟨hs, hm, hc⟩
    exact ⟨hs, f.index, by simp [List.getElem?_map, hm, hc], rfl⟩

@[req "POL-9"]
theorem ownershipFaults_mem_iff (cfg : Cfg) (p : Psbt) (f : Fault) :
    f ∈ ownershipFaults cfg p ↔ f.side = .input ∧ f.code = .UNKNOWN_INPUT ∧
      ∃ o, p.inputMaps[f.index]? = some (some o) ∧ owned cfg o = false := by
  rw [ownershipFaults, indexedFaults_mem_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨hs, j, hj, rfl⟩
    simp only [List.getElem?_map] at hj
    cases hm : p.inputMaps[f.index]? with
    | none => simp [hm] at hj
    | some m =>
      cases m with
      | none => simp [hm] at hj
      | some o =>
        cases ho : owned cfg o <;> simp_all
  · rintro ⟨hs, hc, o, hm, ho⟩
    exact ⟨hs, f.index, by simp [List.getElem?_map, hm, hc, ho], rfl⟩

@[req "POL-10"]
theorem destinationFaults_mem_iff (cfg : Cfg) (p : Psbt) (f : Fault) :
    f ∈ destinationFaults cfg p ↔ f.side = .output ∧
      f.code = hintCode (p.outputHints[f.index]?.getD false) ∧
      ∃ o, p.txOutputs[f.index]? = some o ∧ recognised cfg o = false := by
  rw [destinationFaults, indexedFaults_mem_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨hs, j, hj, rfl⟩
    simp only [List.getElem?_map, outputChecks_get] at hj
    cases hm : p.txOutputs[f.index]? with
    | none => simp [hm] at hj
    | some o => cases ho : recognised cfg o <;> simp_all
  · rintro ⟨hs, hc, o, hm, ho⟩
    exact ⟨hs, f.index, by simp [List.getElem?_map, outputChecks_get, hm, hc, ho], rfl⟩

@[req "API-25"]
def Fault.position (f : Fault) : Side × Nat := (f.side, f.index)

@[req "POL-10"]
theorem destinationFaults_hints (cfg : Cfg) (p : Psbt) (hs : List Bool) :
    (destinationFaults cfg { p with outputHints := hs }).map Fault.position =
      (destinationFaults cfg p).map Fault.position := by
  have scan (os : List Encode.Output) (a b : List Bool) (start : Nat) :
      (indexedFaults .output ((outputChecks cfg os a).map (Option.map hintCode)) start).map Fault.position =
      (indexedFaults .output ((outputChecks cfg os b).map (Option.map hintCode)) start).map Fault.position := by
    induction os generalizing a b start with
    | nil => rfl
    | cons o os ih =>
      cases hr : recognised cfg o <;>
        simp [outputChecks, hr, indexedFaults, Fault.position] <;> exact ih _ _ _
  exact scan p.txOutputs hs p.outputHints 0

/-- Equal-length replacement retains even malformed-map cases: structural refusal is unchanged. -/
@[req "API-25"]
theorem faults_hints_positions (cfg : Cfg) (p : Psbt) (hs : List Bool)
    (hlen : hs.length = p.outputHints.length) :
    (faults cfg { p with outputHints := hs }).map Fault.position =
      (faults cfg p).map Fault.position := by
  have hstruct : structural { p with outputHints := hs } = structural p := by
    simp [structural, hlen]
  have hcons : inconsistent { p with outputHints := hs } = inconsistent p := by
    simp [inconsistent, hlen]
  simp only [faults, hstruct, hcons]
  split
  · rfl
  · split
    · rfl
    · change (if unknownInput cfg p then ownershipFaults cfg p else
          destinationFaults cfg { p with outputHints := hs }).map Fault.position = _
      split
      · rfl
      · exact destinationFaults_hints cfg p hs

@[req "API-25"]
theorem faults_ascending (cfg : Cfg) (p : Psbt) :
    (faults cfg p).Pairwise (fun a b => a.index < b.index) := by
  unfold faults
  split
  · simp
  · split
    · exact indexedFaults_ascending _ _ _
    · split <;> exact indexedFaults_ascending _ _ _

@[req "API-25"]
theorem faults_one_side (cfg : Cfg) (p : Psbt) :
    ∃ side, ∀ f ∈ faults cfg p, f.side = side := by
  have scan (side : Side) (cs : List (Option Policy.Code)) :
      ∀ f ∈ indexedFaults side cs 0, f.side = side := by
    intro f hf
    exact ((indexedFaults_mem_iff _ _ _ _).mp hf).1
  unfold faults
  split
  · exact ⟨.input, by simp⟩
  · split
    · exact ⟨.input, scan _ _⟩
    · split
      · exact ⟨.input, scan _ _⟩
      · exact ⟨.output, scan _ _⟩

@[req "API-25"]
theorem faults_indices_nodup (cfg : Cfg) (p : Psbt) :
    ((faults cfg p).map Fault.index).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (faults_ascending cfg p).imp (fun h => Nat.ne_of_lt h)

@[req "API-25"]
theorem faults_index_bounds (cfg : Cfg) (p : Psbt) (f : Fault) (hf : f ∈ faults cfg p) :
    f.index < (match f.side with | .input => p.txInputs.length | .output => p.txOutputs.length) := by
  unfold faults at hf
  split at hf
  · simp at hf
  · rename_i hs
    have hstruct : structural p = false := by simpa using hs
    have hmaps := ((structural_false_iff p).mp hstruct).2.2.1
    split at hf
    · obtain ⟨hside, hm, _⟩ := (missingFaults_mem_iff p f).mp hf
      simpa [hside, hmaps] using (List.getElem?_eq_some_iff.mp hm).1
    · split at hf
      · obtain ⟨hside, _, o, hm, _⟩ := (ownershipFaults_mem_iff cfg p f).mp hf
        simpa [hside, hmaps] using (List.getElem?_eq_some_iff.mp hm).1
      · obtain ⟨hside, _, o, hm, _⟩ := (destinationFaults_mem_iff cfg p f).mp hf
        simpa [hside] using (List.getElem?_eq_some_iff.mp hm).1

@[req "API-25"]
theorem transmitted_prefix (cfg : Cfg) (p : Psbt) :
    transmitted cfg p <+: faults cfg p ∧ (transmitted cfg p).length ≤ 32 ∧
      transmitted cfg p = (faults cfg p).take 32 := by
  simp [transmitted, List.take_prefix]
  omega

@[req "API-25"]
theorem truncated_exact (cfg : Cfg) (p : Psbt) :
    truncated cfg p = true ↔ 32 < (faults cfg p).length := by simp [truncated]

@[req "API-25"]
theorem truncation_boundary (cfg : Cfg) (p : Psbt) :
    ((faults cfg p).length ≤ 32 → transmitted cfg p = faults cfg p ∧ truncated cfg p = false) ∧
    (32 < (faults cfg p).length → (transmitted cfg p).length = 32 ∧ truncated cfg p = true) := by
  constructor
  · intro h
    simp [transmitted, truncated, List.take_of_length_le h, Nat.not_lt_of_ge h]
  · intro h
    simp [transmitted, truncated, h, Nat.min_eq_left (Nat.le_of_lt h)]

end BtcPolicy.Evaluate
