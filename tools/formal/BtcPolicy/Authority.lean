import BtcPolicy.Kernel
/-! Authority over every input: what a Normal-path spend of one transaction needs, counted per
input, beside the kernel's counts that let input 0 stand for every input and one candidate for one
rung.

**What it states.** A federation signature is identified by its message, its input and its signer
(`Authority.Sig`). The rung and the commitment it was released under are provenance, carried by
`Kernel.Exp` and dropped by `Authority.sig`: two commitments over one transaction share every
per-input message, because `Kernel.sighash` reads only the transaction's identity and the input
index. `Authority.normal` is `DUR-28`'s "`≥ t` distinct valid partials on every input" together
with the user's signature on every input (`CHN-12`). The signers may differ from input to input:
nothing asks for one common signer set (`Authority.normal_iff`). A signer outside the federation's
keys counts for nothing, and a signer counts once per input however many copies are held.

**What it does not state.** Validity is symbolic: a record is a signature, with no ECDSA, no BIP143
bytes and no binding to them (`ADR-0023` decision 12), and the user's signature is a record per
input with no key behind it. Normal authorization is not assembly eligibility (`Kernel.packageAccepted`,
which reads `Kernel.heldQuorum` on one candidate), not package admissibility (`Package.validate`), not
submission (`Kernel.Effect.broadcast`) and not inclusion in a chain, which is an environmental step.
Who holds a list of records is the caller's: `Federation.held` is a node's possession and the
partial inventory is exposure.

**Agreement with the kernel.** On a transaction with exactly one input, and keys covering every
signer counted, `Kernel.exposedQuorum` and `Kernel.heldQuorum` are `Authority.quorum` over the same
rows (`Authority.exposed_refines`, `Authority.held_refines`). The restriction is necessary: on a
two-input transaction a threshold at input 0 is not authorization (`Authority.input_zero_insufficient`). -/

namespace BtcPolicy.Authority
open BtcPolicy.Kernel

/-- One federation signature by its identity: the message it signs, its input and its signer.
`NCH-25` keys the store "per `(rung, input, signer)`"; the rung is a transaction, so its message
names it. -/
structure Sig where
  msg : Sighash
  input : Nat
  signer : Nat
  deriving DecidableEq, Repr

/-- An exposure row's signature, without its class bit and commitment id. -/
def sig (x : Exp) : Sig := { msg := x.msg, input := x.input, signer := x.signer }

/-- The user's signature on one input, by message and input. -/
structure UserSig where
  msg : Sighash
  input : Nat
  deriving DecidableEq, Repr

/-- The distinct signers among `keys` with a record in `R` for input `k` of `X`. -/
def signers (keys : List Nat) (X : Tx) (k : Nat) (R : List Sig) : List Nat :=
  ((R.filter fun s => s.msg == sighash X k && s.input == k && keys.contains s.signer).map
    Sig.signer).eraseDups

/-- `DUR-28`'s "`≥ t` distinct valid partials on every input", over the records `R`: a transaction
with at least one input, and at each of its inputs `t` distinct signers among `keys`. -/
@[req "DUR-28"]
def quorum (keys : List Nat) (t : Nat) (X : Tx) (R : List Sig) : Bool :=
  !X.inputs.isEmpty && (List.range X.inputs.length).all fun k => t ≤ (signers keys X k R).length

/-- The user's signature on every input of `X`. `CHN-12` has the node "verify the user's partial
signature cryptographically against its own recomputed sighash on every input before it evaluates
policy"; here a signature is a record. -/
@[req "CHN-12"]
def userSigned (X : Tx) (U : List UserSig) : Bool :=
  (List.range X.inputs.length).all fun k => U.contains { msg := sighash X k, input := k }

/-- Normal authorization of `X`: the user's signature and `t` distinct federation signers on every
input (`CHN-9`'s witness, read symbolically). -/
@[req "DUR-28"]
def normal (keys : List Nat) (t : Nat) (X : Tx) (U : List UserSig) (R : List Sig) : Bool :=
  userSigned X U && quorum keys t X R

theorem mem_signers {keys : List Nat} {X : Tx} {k : Nat} {R : List Sig} {s : Nat} :
    s ∈ signers keys X k R ↔ s ∈ keys ∧ ({ msg := sighash X k, input := k, signer := s } : Sig) ∈ R := by
  simp only [signers, List.mem_eraseDups, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨m, i, s'⟩, ⟨hm, ⟨h1, h2⟩, hk⟩, rfl⟩
    simp only at h1 h2
    subst h2
    subst h1
    exact ⟨hk, hm⟩
  · rintro ⟨hk, hm⟩
    exact ⟨_, ⟨hm, ⟨rfl, rfl⟩, hk⟩, rfl⟩

/-- `t` counted signers at one input are exactly `t` distinct keys with a record there. -/
theorem le_signers_iff {keys : List Nat} {t : Nat} {X : Tx} {k : Nat} {R : List Sig} :
    t ≤ (signers keys X k R).length ↔ ∃ S : List Nat, S.Nodup ∧ t ≤ S.length ∧
      ∀ s ∈ S, s ∈ keys ∧ ({ msg := sighash X k, input := k, signer := s } : Sig) ∈ R := by
  constructor
  · intro h
    exact ⟨_, nodup_eraseDups _, h, fun s hs => mem_signers.1 hs⟩
  · rintro ⟨S, hn, hl, hs⟩
    exact Nat.le_trans hl (length_le_of_nodup_subset hn fun s h => mem_signers.2 (hs s h))

/-- Normal authorization, per input: a nonempty input list, and at each input the user's signature
and its own `t` distinct authorized signers with a record there. The signer list is chosen per
input, so two inputs may be authorized by different subsets of the federation. -/
@[req "DUR-28"]
theorem normal_iff {keys : List Nat} {t : Nat} {X : Tx} {U : List UserSig} {R : List Sig} :
    normal keys t X U R = true ↔ X.inputs ≠ [] ∧ ∀ k < X.inputs.length,
      ({ msg := sighash X k, input := k } : UserSig) ∈ U ∧
      ∃ S : List Nat, S.Nodup ∧ t ≤ S.length ∧
        ∀ s ∈ S, s ∈ keys ∧ ({ msg := sighash X k, input := k, signer := s } : Sig) ∈ R := by
  simp only [normal, quorum, userSigned, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.mem_range, List.contains_eq_mem, decide_eq_true_eq, ← le_signers_iff]
  constructor
  · rintro ⟨hu, hne, hq⟩
    exact ⟨hne, fun k hk => ⟨hu k hk, hq k hk⟩⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun k hk => (h k hk).1, hne, fun k hk => (h k hk).2⟩

/-- More records and more keys never lower a count. -/
theorem signers_mono {keys keys' : List Nat} {X : Tx} {k : Nat} {R R' : List Sig}
    (hk : ∀ s ∈ keys, s ∈ keys') (hR : ∀ x ∈ R, x ∈ R') :
    (signers keys X k R).length ≤ (signers keys' X k R').length :=
  length_le_of_nodup_subset (nodup_eraseDups _) fun s hs =>
    let h := mem_signers.1 hs
    mem_signers.2 ⟨hk s h.1, hR _ h.2⟩

/-- Authorization only grows with what is held: removing nothing from a holder's records and the
user's signatures keeps it. -/
theorem normal_mono {keys : List Nat} {t : Nat} {X : Tx} {U U' : List UserSig} {R R' : List Sig}
    (hU : ∀ u ∈ U, u ∈ U') (hR : ∀ x ∈ R, x ∈ R') (h : normal keys t X U R = true) :
    normal keys t X U' R' = true := by
  rw [normal_iff] at h ⊢
  refine ⟨h.1, fun k hk => ?_⟩
  obtain ⟨hu, S, hn, hl, hs⟩ := h.2 k hk
  exact ⟨hU _ hu, S, hn, hl, fun s h => ⟨(hs s h).1, hR _ (hs s h).2⟩⟩

/-- One input short blocks the whole transaction: if at some input of `X` the records available
anywhere, `A`, have fewer than `t` authorized signers, then no holder whose records are drawn from
`A` has Normal authorization of `X`, whatever the other inputs hold and whatever user signatures it
has. -/
@[req "DUR-28"]
theorem unauthorized_of_input {keys : List Nat} {t : Nat} {X : Tx} {U : List UserSig}
    {R A : List Sig} {k : Nat} (hk : k < X.inputs.length) (hR : ∀ x ∈ R, x ∈ A)
    (hA : (signers keys X k A).length < t) : normal keys t X U R = false := by
  cases hn : normal keys t X U R with
  | false => rfl
  | true =>
    obtain ⟨_, S, hS, hl, hs⟩ := ((normal_iff.1 hn).2 k hk)
    have := Nat.le_trans hl (Nat.le_trans (le_signers_iff.2 ⟨S, hS, Nat.le_refl _, hs⟩)
      (signers_mono (fun s h => h) hR))
    omega

theorem filter_sig (xs : List Exp) (keys : List Nat) (X : Tx) (k : Nat)
    (hk : ∀ x ∈ xs, x.signer ∈ keys) :
    ((xs.map sig).filter fun s => s.msg == sighash X k && s.input == k && keys.contains s.signer).map
      Sig.signer = (xs.filter fun x => x.msg == sighash X k && x.input == k).map Exp.signer := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : keys.contains x.signer = true := by simpa using hk x (by simp)
    have ih := ih fun y hy => hk y (List.mem_cons_of_mem x hy)
    by_cases hc : (x.msg == sighash X k && x.input == k) = true
    · simp only [List.map_cons, List.filter_cons, sig, hc, hx, Bool.and_self, ↓reduceIte, ih]
    · have hcf := Bool.eq_false_iff.2 hc
      simp only [List.map_cons, List.filter_cons, sig, hcf, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, ih]

/-- The refinement at the kernel's exposure count. On a one-input transaction, with every signer of
the world's exposure among `keys`, `Kernel.exposedQuorum` is `Authority.quorum` over the exposure's
signatures: the kernel's input 0 is the only input, and the counted rows are the same rows. -/
@[req "POL-18"]
theorem exposed_refines (keys : List Nat) (w : World) (c : Cand) (h1 : c.tx.inputs.length = 1)
    (hk : ∀ x ∈ w.exposure, x.signer ∈ keys) :
    exposedQuorum w c = quorum keys w.node.t c.tx (w.exposure.map sig) := by
  have hne : c.tx.inputs.isEmpty = false := by
    cases h : c.tx.inputs with
    | nil => rw [h] at h1; cases h1
    | cons _ _ => rfl
  have hr : List.range 1 = [0] := rfl
  unfold exposedQuorum quorum signers
  rw [hne, h1, hr, List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, Bool.true_and,
    filter_sig _ keys c.tx 0 hk]

/-- The records `Kernel.Cand.heldSigners` stands for, on its one input and one rung: each held
signer's signature on input 0 of the candidate's transaction. -/
def heldSigs (c : Cand) : List Sig :=
  c.heldSigners.map fun s => { msg := sighash c.tx 0, input := 0, signer := s }

theorem filter_held (keys : List Nat) (m : Sighash) (l : List Nat) (hk : ∀ s ∈ l, s ∈ keys) :
    ((l.map fun s => ({ msg := m, input := 0, signer := s } : Sig)).filter fun s =>
      s.msg == m && s.input == 0 && keys.contains s.signer).map Sig.signer = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : keys.contains s = true := by simpa using hk s (by simp)
    simp only [List.map_cons, List.filter_cons, beq_self_eq_true, hs, Bool.and_self, ↓reduceIte,
      ih fun x hx => hk x (List.mem_cons_of_mem s hx)]

/-- The refinement at the kernel's possession count. On a one-input transaction, with every held
signer among `keys`, `Kernel.heldQuorum` is `Authority.quorum` over `Authority.heldSigs`: one
candidate is one rung, and its held set is the signers of its one input. -/
@[req "DUR-28"]
theorem held_refines (keys : List Nat) (t : Nat) (c : Cand) (h1 : c.tx.inputs.length = 1)
    (hk : ∀ s ∈ c.heldSigners, s ∈ keys) :
    heldQuorum t c = quorum keys t c.tx (heldSigs c) := by
  have hne : c.tx.inputs.isEmpty = false := by
    cases h : c.tx.inputs with
    | nil => rw [h] at h1; cases h1
    | cons _ _ => rfl
  have hr : List.range 1 = [0] := rfl
  unfold heldQuorum quorum signers heldSigs
  rw [hne, h1, hr, List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, Bool.true_and,
    filter_held keys _ _ hk]

namespace Cases

def X : Tx := ⟨7, [0, 1], 0⟩
def c : Cand := { RegistrationCases.c1 with tx := X }
def w : World :=
  { node := { RegistrationCases.A with t := 3 },
    exposure := [0, 1, 2].map fun s => { msg := sighash X 0, input := 0, signer := s, hot := true, cid := 1 } }

end Cases

/-- No general projection: on a two-input transaction, three signers at input 0 meet
`Kernel.exposedQuorum` at threshold 3, and `Authority.quorum` over the same rows fails, since input
1 has no signer. Discarding every input but 0 does not preserve authorization. -/
@[req "DUR-28"]
theorem input_zero_insufficient :
    Cases.c.tx.inputs.length = 2 ∧ exposedQuorum Cases.w Cases.c = true ∧
      quorum [0, 1, 2] 3 Cases.c.tx (Cases.w.exposure.map sig) = false := by
  decide

end BtcPolicy.Authority
