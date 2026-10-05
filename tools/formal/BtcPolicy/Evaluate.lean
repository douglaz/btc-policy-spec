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

/-- Scan in transaction order; map lengths are checked before this scan is read. -/
@[req "POL-10"]
def firstUnknown (cfg : Cfg) : List Encode.Output → List Bool → Option Bool
  | [], _ => none
  | o :: os, hs =>
      if recognised cfg o then firstUnknown cfg os hs.tail -- hint-trust
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
      simp only [firstUnknown, recognised]
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
  | nil => simp [firstUnknown]
  | cons o os ih =>
    simp only [firstUnknown]
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
  | nil => simp [firstUnknown, FirstAt]
  | cons o os ih =>
    simp only [firstUnknown]
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

end BtcPolicy.Evaluate
