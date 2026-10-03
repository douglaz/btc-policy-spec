import BtcPolicy.Classification
/-! `POL-4`'s descriptor membership as structure (`ADR-0023` decision 10 item 6): "decided by
re-derivation and script equality, never by address string comparison and never by trusting a
PSBT's `bip32_derivation` hint". The three steps are the three definitions below; what each
step does NOT contain is the point. Deriving a scriptPubKey from a single-path descriptor and an
index — BIP32 child key derivation and script construction for every context of `MAN-39`'s
grammar — is `derive`, a parameter of every definition and theorem here: the named boundary
(decision 3 keeps secp256k1 and the hashes out of Lean). The structure covered is the whole of
what `POL-4` requires beyond that boundary: BIP389 multipath expansion, the wildcard-or-definite
index set with its inclusive bound, failure skipping, and exact script equality.
Multipath expansion is represented by the supplied paths; parsing, BIP32 derivation, script
construction and cryptography remain outside this formal model.

The `member` assumption milestone 2 named (`Classification.member`: an output's `kind` IS
`POL-4`'s decision) is discharged by `kindOf`: the kind of a script is computed from `matchesScript`
over the vault, escape and allowlist descriptors, and an output built with it satisfies every
`Classification` theorem by construction. What remains assumed is `derive` itself. -/

namespace BtcPolicy.Membership
open BtcPolicy.Classification (Kind)

abbrev Script := List Nat

/-- One single-path descriptor after multipath expansion: its identity (keys, origin, script
context — everything `derive` reads) and whether it carries a wildcard. -/
structure SinglePath where
  id : Nat
  wildcard : Bool
  deriving DecidableEq, Repr

/-- A descriptor as `MAN-39` admits it: one or more single paths. "A BIP389 `<0;1>` descriptor
yields two, so both the external and the internal chain are scanned." -/
structure Descriptor where
  paths : List SinglePath
  deriving DecidableEq, Repr

/-- `POL-4` step 1: "expand `d` into its single-path descriptors". -/
@[req "POL-4"]
def expand (d : Descriptor) : List SinglePath := d.paths

/-- `POL-4` step 2: "derive indices `0..=max` if it has a wildcard, or index 0 only if it is
definite". -/
@[req "POL-4"]
def indices (max : Nat) (p : SinglePath) : List Nat :=
  if p.wildcard then List.range (max + 1) else [0]

/-- `POL-4`: "An index the library cannot derive is skipped"; "`s` matches iff some derived
scriptPubKey equals `s` byte-for-byte". Failure is `none`, never a script sentinel. -/
@[req "POL-4"]
def matchesScript (derive : SinglePath → Nat → Option Script) (max : Nat) (d : Descriptor)
    (s : Script) : Bool :=
  (expand d).any fun p => (indices max p).any fun i => derive p i == some s

/-- Membership is exactly a successful derivation at a scanned path and index. -/
@[req "POL-4"]
theorem matchesScript_iff (derive : SinglePath → Nat → Option Script) (max : Nat)
    (d : Descriptor) (s : Script) :
    matchesScript derive max d s = true ↔
      ∃ p ∈ d.paths, ∃ i ∈ indices max p, derive p i = some s := by
  simp only [matchesScript, expand, List.any_eq_true, beq_iff_eq]

/-- Agreement through the bound suffices, including the definite path's index zero.
No property of derivation outside the descriptor or above the bound is assumed. -/
@[req "POL-4"]
theorem matchesScript_local (derive₁ derive₂ : SinglePath → Nat → Option Script)
    (max : Nat) (d : Descriptor) (s : Script)
    (h : ∀ p ∈ d.paths, ∀ i ≤ max, derive₁ p i = derive₂ p i) :
    matchesScript derive₁ max d s = matchesScript derive₂ max d s := by
  have bounded (p : SinglePath) (i : Nat) (hi : i ∈ indices max p) : i ≤ max := by
    unfold indices at hi
    split at hi <;> simp only [List.mem_range, List.mem_singleton] at hi <;> omega
  apply Bool.eq_iff_iff.mpr
  rw [matchesScript_iff, matchesScript_iff]
  constructor
  · rintro ⟨p, hp, i, hi, hs⟩
    exact ⟨p, hp, i, hi, (h p hp i (bounded p i hi)).symm.trans hs⟩
  · rintro ⟨p, hp, i, hi, hs⟩
    exact ⟨p, hp, i, hi, (h p hp i (bounded p i hi)).trans hs⟩

/-- A successful derivation matches at every index the scan covers. -/
@[req "POL-4"]
theorem matches_of_derived (derive : SinglePath → Nat → Option Script) (max : Nat)
    (d : Descriptor) (p : SinglePath) (hp : p ∈ d.paths) (i : Nat)
    (hi : i ∈ indices max p) (s : Script) (hs : derive p i = some s) :
    matchesScript derive max d s = true :=
  (matchesScript_iff derive max d s).mpr ⟨p, hp, i, hi, hs⟩

/-- `POL-4`: "The scan is inclusive of `max`". Success at that index matches. -/
@[req "POL-4"]
theorem matches_at_max (derive : SinglePath → Nat → Option Script) (max : Nat)
    (d : Descriptor) (p : SinglePath) (hp : p ∈ d.paths) (hw : p.wildcard = true)
    (s : Script) (hs : derive p max = some s) :
    matchesScript derive max d s = true :=
  matches_of_derived derive max d p hp max (by simp [indices, hw]) s hs

/-- A wildcard path's successful target beyond the bound does not match if its result differs
from every derivation actually scanned in this descriptor. Aliases are permitted elsewhere;
BIP32 supplies no blanket injectivity or path separation assumption here. -/
@[req "POL-4"]
theorem not_matches_beyond_max (derive : SinglePath → Nat → Option Script)
    (max : Nat) (d : Descriptor) (p : SinglePath) (_hp : p ∈ d.paths)
    (_hw : p.wildcard = true) (s : Script) (hs : derive p (max + 1) = some s)
    (hseparate : ∀ q ∈ d.paths, ∀ i ∈ indices max q, derive q i ≠ derive p (max + 1)) :
    matchesScript derive max d s = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨q, hq, i, hi, he⟩ := (matchesScript_iff derive max d s).mp h
  exact hseparate q hq i hi (he.trans hs.symm)

/-- Both chains of a multipath descriptor are scanned when their derivations succeed. -/
@[req "POL-4"]
theorem both_chains_scanned (derive : SinglePath → Nat → Option Script) (max : Nat)
    (ext int : SinglePath) (i : Nat) (hi : i ∈ indices max ext) (hi' : i ∈ indices max int)
    (sExt sInt : Script) (he : derive ext i = some sExt) (hn : derive int i = some sInt) :
    matchesScript derive max { paths := [ext, int] } sExt = true ∧
    matchesScript derive max { paths := [ext, int] } sInt = true :=
  ⟨matches_of_derived derive max _ ext (by simp) i hi sExt he,
   matches_of_derived derive max _ int (by simp) i hi' sInt hn⟩

/-- `POL-4`: "A definite descriptor ignores `max`". This holds for every queried script,
including when derivation fails. -/
@[req "POL-4"]
theorem definite_ignores_bound (derive : SinglePath → Nat → Option Script) (p : SinglePath)
    (hd : p.wildcard = false) (max max' : Nat) (s : Script) :
    indices max p = [0] ∧
    matchesScript derive max { paths := [p] } s =
      matchesScript derive max' { paths := [p] } s := by
  simp [matchesScript, expand, indices, hd]

/-- An everywhere-failing derivation matches no script, including the empty script. -/
@[req "POL-4"]
theorem none_matches_nothing (max : Nat) (d : Descriptor) (s : Script) :
    matchesScript (fun _ _ => none) max d s = false := by
  simp [matchesScript]

/-! ## Discharging `Classification.member` -/

/-- The kind of a script, computed: vault change first (`CHN-30` excludes it from the class
decision), then the escape descriptor, then the allowlist (`CHN-30`: "the escape descriptor is
itself an allowlist entry", so the escape test runs first, as `Classification.outputClass`
requires), else a stranger. -/
@[req "CHN-30"]
def kindOf (derive : SinglePath → Nat → Option Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) : Kind :=
  if matchesScript derive max vault s then .vault
  else if matchesScript derive max escape s then .escape
  else if allow.any (fun d => matchesScript derive max d s) then .hot
  else .unknown

/-- An output built from a script carries `POL-4`'s decision: `Classification.member` reads it
back, so every theorem there holds of such outputs with the assumption discharged down to
`derive`. -/
@[req "POL-4"]
theorem member_discharged (derive : SinglePath → Nat → Option Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) (value : Nat) :
    BtcPolicy.Classification.member { value := value, kind := kindOf derive max vault escape allow s } =
      kindOf derive max vault escape allow s := rfl

/-- A script the escape descriptor derives is escape-kind even when the allowlist also holds it,
and a script only an allowlist descriptor derives is hot: the order `CHN-30` fixes. -/
@[req "CHN-30"]
theorem kindOf_order (derive : SinglePath → Nat → Option Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) (hv : matchesScript derive max vault s = false) :
    (matchesScript derive max escape s = true → kindOf derive max vault escape allow s = .escape) ∧
    (matchesScript derive max escape s = false → allow.any (fun d => matchesScript derive max d s) = true →
      kindOf derive max vault escape allow s = .hot) := by
  constructor
  · intro he; simp [kindOf, hv, he]
  · intro he ha; simp [kindOf, hv, he, ha]

end BtcPolicy.Membership
