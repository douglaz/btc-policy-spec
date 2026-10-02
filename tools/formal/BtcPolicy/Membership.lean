import BtcPolicy.Classification
/-! `POL-4`'s descriptor membership as structure (`ADR-0023` decision 10 item 6): "decided by
re-derivation and script equality, never by address string comparison and never by trusting a
PSBT's `bip32_derivation` hint". The three steps are the three definitions below; what each
step does NOT contain is the point. Deriving a scriptPubKey from a single-path descriptor and an
index — BIP32 child key derivation and script construction for every context of `MAN-39`'s
grammar — is `derive`, a parameter of every definition and theorem here: the named boundary
(decision 3 keeps secp256k1 and the hashes out of Lean). The structure covered is the whole of
what `POL-4` requires beyond that boundary: BIP389 multipath expansion, the wildcard-or-definite
index set with its inclusive bound, and byte-for-byte equality.

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

/-- `POL-4` step 3: "`s` matches iff some derived scriptPubKey equals `s` byte-for-byte". -/
@[req "POL-4"]
def matchesScript (derive : SinglePath → Nat → Script) (max : Nat) (d : Descriptor) (s : Script) : Bool :=
  (expand d).any fun p => (indices max p).any fun i => derive p i == s

/-- A derived script matches its own descriptor at every index the scan covers. -/
theorem matches_of_derived (derive : SinglePath → Nat → Script) (max : Nat) (d : Descriptor)
    (p : SinglePath) (hp : p ∈ d.paths) (i : Nat) (hi : i ∈ indices max p) :
    matchesScript derive max d (derive p i) = true := by
  simp only [matchesScript, expand, List.any_eq_true, beq_iff_eq]
  exact ⟨p, hp, i, hi, rfl⟩

/-- "The scan is inclusive of `max`": a wildcard path's script at `max` matches. -/
@[req "POL-4"]
theorem matches_at_max (derive : SinglePath → Nat → Script) (max : Nat) (d : Descriptor)
    (p : SinglePath) (hp : p ∈ d.paths) (hw : p.wildcard = true) :
    matchesScript derive max d (derive p max) = true :=
  matches_of_derived derive max d p hp max (by simp [indices, hw])

/-- The scan stops at `max`: a script derived only at `max + 1` does not match, given that
derivation is injective in the index and distinct paths derive distinct scripts (what BIP32
gives a well-formed descriptor set; an assumption on `derive`). -/
@[req "POL-4"]
theorem not_matches_beyond_max (derive : SinglePath → Nat → Script)
    (hinj : ∀ p i j, derive p i = derive p j → i = j)
    (hdistinct : ∀ p q, p ≠ q → ∀ i j, derive p i ≠ derive q j)
    (max : Nat) (d : Descriptor) (p : SinglePath) (_hp : p ∈ d.paths) :
    matchesScript derive max d (derive p (max + 1)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [matchesScript, expand, List.any_eq_true, beq_iff_eq, indices] at h
  obtain ⟨q, _, i, hi, h⟩ := h
  by_cases hq : q = p
  · subst hq
    have := hinj q i (max + 1) h
    split at hi <;> simp [List.mem_range] at hi <;> omega
  · exact hdistinct q p hq i (max + 1) h

/-- Both chains of a multipath descriptor are scanned: the internal chain's scripts match as
the external chain's do. -/
@[req "POL-4"]
theorem both_chains_scanned (derive : SinglePath → Nat → Script) (max : Nat)
    (ext int : SinglePath) (i : Nat) (hi : i ∈ indices max ext) (hi' : i ∈ indices max int) :
    matchesScript derive max { paths := [ext, int] } (derive ext i) = true ∧
    matchesScript derive max { paths := [ext, int] } (derive int i) = true :=
  ⟨matches_of_derived derive max _ ext (by simp) i hi,
   matches_of_derived derive max _ int (by simp) i hi'⟩

/-- "A definite descriptor ignores `max`": its index set is `[0]` for every bound, so its one
script matches under every bound and nothing else of it does. -/
@[req "POL-4"]
theorem definite_ignores_bound (derive : SinglePath → Nat → Script) (p : SinglePath)
    (hd : p.wildcard = false) (max max' : Nat) :
    indices max p = [0] ∧
    matchesScript derive max { paths := [p] } (derive p 0) = matchesScript derive max' { paths := [p] } (derive p 0) := by
  simp [matchesScript, expand, indices, hd]

/-! ## Discharging `Classification.member` -/

/-- The kind of a script, computed: vault change first (`CHN-30` excludes it from the class
decision), then the escape descriptor, then the allowlist (`CHN-30`: "the escape descriptor is
itself an allowlist entry", so the escape test runs first, as `Classification.outputClass`
requires), else a stranger. -/
@[req "CHN-30"]
def kindOf (derive : SinglePath → Nat → Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) : Kind :=
  if matchesScript derive max vault s then .vault
  else if matchesScript derive max escape s then .escape
  else if allow.any (fun d => matchesScript derive max d s) then .hot
  else .unknown

/-- An output built from a script carries `POL-4`'s decision: `Classification.member` reads it
back, so every theorem there holds of such outputs with the assumption discharged down to
`derive`. -/
@[req "POL-4"]
theorem member_discharged (derive : SinglePath → Nat → Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) (value : Nat) :
    BtcPolicy.Classification.member { value := value, kind := kindOf derive max vault escape allow s } =
      kindOf derive max vault escape allow s := rfl

/-- A script the escape descriptor derives is escape-kind even when the allowlist also holds it,
and a script only an allowlist descriptor derives is hot: the order `CHN-30` fixes. -/
@[req "CHN-30"]
theorem kindOf_order (derive : SinglePath → Nat → Script) (max : Nat) (vault escape : Descriptor)
    (allow : List Descriptor) (s : Script) (hv : matchesScript derive max vault s = false) :
    (matchesScript derive max escape s = true → kindOf derive max vault escape allow s = .escape) ∧
    (matchesScript derive max escape s = false → allow.any (fun d => matchesScript derive max d s) = true →
      kindOf derive max vault escape allow s = .hot) := by
  constructor
  · intro he; simp [kindOf, hv, he]
  · intro he ha; simp [kindOf, hv, he, ha]

end BtcPolicy.Membership
