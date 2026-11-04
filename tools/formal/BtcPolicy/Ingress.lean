import BtcPolicy.Federation
import BtcPolicy.Evaluate
import BtcPolicy.Encode
/-! Checked ingress: the lifecycle `accept` derived from the request's decoded data. The kernel's
`Kernel.Event.accept` carries its two candidates as given, and `SPN-28`'s note says
`Kernel.accept` "takes as given" the recorded class. Here a SpendRequest that has reached gate 17
(`SPN-5`) is evaluated by the existing checks and nothing else: `Evaluate.evaluate`, which runs
`POL-6`'s order as `Policy.evaluateSpend` owns it, with membership from `Evaluate.Cfg.derive`
(`Membership.kindOf`), and `Classification.classify` over the same decoded outputs. The verdict is
the kernel event the node takes, or no kernel transition. No second policy evaluator is written.

**What is derived.** On acceptance (`Ingress.check` is `Verdict.accepted`): the spend's class and its
Hot outflow, read from one scan of its outputs (`Ingress.accepted_spend`); the Escape's class
(`Ingress.accepted_escape`); the transaction identity from the transaction fields alone,
so request copies that differ in maps, hints or upstream verdicts carry one transaction
(`Ingress.tx_of_fields`); the commitment id from `CHN-24`'s fields (`Ingress.commitment`); the
ordered pair, spend first (`Ingress.accepted_roles`); and that every member of the group passed
before the event exists (`Ingress.accepted_validates`). Over a federation whose honest acceptances
are all checked (`Ingress.CheckedTrace`) and whose transaction identity is collision-free,
`Federation.HotBinding` follows for a hot target (`Ingress.hot_binding`), and
`Ingress.no_exposed_quorum` is `Federation.no_exposed_quorum` with those two premises in place of
the binding. With the commitment id collision-free, one commitment id gives one transaction and one
amount across acceptances (`Ingress.one_amount_per_commitment`).

**Kept as named boundaries.** `CHN-12`'s user signatures and `SPN-25`'s prevout comparison are a
supplied verdict per member (`Member.upstream`): cryptography and backend truth, not decided here.
Ownership is `POL-9`'s script equality on the PSBT's `witness_utxo`, which proves no ownership and no
value. The identities are hashes, kept symbolic: `Ctx.txId`, `Ctx.commitId` and `Ctx.outpoint` are
parameters, and a theorem that needs one collision-free takes it as a premise, which `Ingress.code`
shows satisfiable (`Ingress.code_injective`). Decoding is the admitted domain: a member whose
commitment falls outside `Encode.Commitment.WF` is `Verdict.malformed`. The fire time is the
request's (`Request.fireAt`): `SPN-30`'s schedule is not checked here. `CHN-14`–`CHN-16`'s ladder
relations other than `CHN-15`'s sequence value, and verifying a rung against the Escape's own
prevouts, are not modelled. All honest nodes evaluate under one `Ctx`.

**What it leaves to the kernel and the ledger.** Gate 24's verdict is an input, `Ledger.admits` as
`Ledger.sysStep` reads it, so its refusal precedes gate 25's; gates 27 and 29 are `Kernel.accept`'s. A staged refusal is `Kernel.Event.refuse`; under
`Kernel.current` its Carrier opens nothing (`Kernel.refused_holder_preserves_opening`). A refusal that
stages nothing has no kernel transition, as `Kernel.Event.refuse` says. Gates before 17, and gates
19 to 21, are outside. -/

namespace BtcPolicy.Ingress
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## An identity that is collision-free -/

/-- An injective code of a byte string, standing in for a collision-free hash. -/
def code : Encode.Bytes → Nat
  | [] => 0
  | b :: bs => 2 ^ b * (2 * code bs + 1)

theorem pow_odd_inj {a b p q : Nat} (h : 2 ^ a * (2 * p + 1) = 2 ^ b * (2 * q + 1)) :
    a = b ∧ p = q := by
  have side : ∀ {a b p q : Nat}, a < b → 2 ^ a * (2 * p + 1) ≠ 2 ^ b * (2 * q + 1) := by
    intro a b p q hab h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : 2 ^ (a + d + 1) * (2 * q + 1) = 2 ^ a * (2 * (2 ^ d * (2 * q + 1))) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [h2] at h
    have := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h
    omega
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (side hab)
  · exact ⟨rfl, by have := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h; omega⟩
  · exact absurd h.symm (side hab)

theorem code_injective : ∀ a b : Encode.Bytes, code a = code b → a = b
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have : 0 < 2 ^ b * (2 * code bs + 1) := Nat.mul_pos (Nat.two_pow_pos b) (by omega)
    simp only [code] at h; exact absurd h (Nat.ne_of_lt this)
  | a :: as, [], h => by
    have : 0 < 2 ^ a * (2 * code as + 1) := Nat.mul_pos (Nat.two_pow_pos a) (by omega)
    simp only [code] at h; exact absurd h.symm (Nat.ne_of_lt this)
  | a :: as, b :: bs, h => by
    obtain ⟨rfl, hp⟩ := pow_odd_inj h
    rw [code_injective as bs hp]

/-! ## The request -/

/-- What every node shares: the policy configuration (one manifest), the vault's `wallet_id`, the
node's own `policy_version` (`CHN-24`: "never the request's"), and the three identities, which are
hashes and stay symbolic. -/
structure Ctx where
  cfg : Evaluate.Cfg
  walletId : Encode.Bytes
  policyVersion : Nat
  txId : Encode.Bytes → Nat
  commitId : Encode.Bytes → Nat
  outpoint : Encode.Bytes → Nat

/-- One decoded transaction of the request, the transaction fields the PSBT does not carry in its
maps, and the supplied upstream verdict: the first refusal of `CHN-12`'s user signatures and
`SPN-25`'s prevout comparison, or `none`. -/
structure Member where
  psbt : Evaluate.Psbt
  version : Nat
  lockTime : Nat
  upstream : Option Policy.Code := none
  deriving DecidableEq, Repr

/-- A SpendRequest from gate 17 on: the spend, the Escape, the fee-bump rungs, the
coordinator-proposed expiry and the fire time the node's schedule computed. -/
structure Request where
  spend : Member
  escape : Member
  rungs : List Member := []
  expiry : Nat
  fireAt : Option Wall
  deriving DecidableEq, Repr

/-- The transaction fields alone, framed as a commitment with every non-transaction field fixed, so
`Encode.encode_injective` applies to it. -/
def Member.frame (m : Member) : Encode.Commitment :=
  { walletId := List.replicate 32 0, version := m.version, lockTime := m.lockTime,
    inputs := m.psbt.txInputs, outputs := m.psbt.txOutputs, fee := 0, expiry := 0,
    policyVersion := 0 }

/-- `CHN-24`'s fields for this member under this request: the fee is `Σ witness_utxo − Σ outputs`,
saturating. -/
@[req "CHN-24"]
def commitment (ctx : Ctx) (q : Request) (m : Member) : Encode.Commitment :=
  { walletId := ctx.walletId, version := m.version, lockTime := m.lockTime,
    inputs := m.psbt.txInputs, outputs := m.psbt.txOutputs,
    fee := Evaluate.totalIn m.psbt - Evaluate.totalOut m.psbt, expiry := q.expiry,
    policyVersion := ctx.policyVersion }

/-- The decoded outputs, classified once: `CHN-30` "from the spend's own outputs". -/
@[req "CHN-30"]
def outputs (ctx : Ctx) (m : Member) : List Classification.Output :=
  Evaluate.outputs ctx.cfg m.psbt

@[req "CHN-30"]
def classOf (ctx : Ctx) (m : Member) : Option Classification.Class :=
  Classification.classify (outputs ctx m)

/-- The kernel's transaction: identity from the transaction fields, inputs by outpoint, and
`POL-11`'s outflow from the same outputs `classOf` reads. -/
@[req "POL-11"]
def tx (ctx : Ctx) (m : Member) : Tx :=
  { id := ctx.txId (Encode.encode m.frame),
    inputs := m.psbt.txInputs.map fun i => ctx.outpoint (i.txid ++ Encode.be 4 i.vout),
    outflow := Classification.hotOutflow (outputs ctx m) }

/-- A candidate as checked ingress hands it to `Kernel.accept`. `born` writes the release state. -/
@[req "SPN-28"]
def cand (ctx : Ctx) (q : Request) (m : Member) (hot : Bool) (fireAt : Option Wall) : Cand :=
  { id := ctx.commitId (Encode.encode (commitment ctx q m)), tx := tx ctx m, hot := hot,
    quorum := false, frozen := false, terminal := false, settled := false, broadcast := false,
    released := false, heldSigners := [], packageOk := false, fireAt := fireAt,
    windowClose := none, expiry := Wall.sample q.expiry }

/-- `CHN-15`: "every input's `nSequence` to `0xfffffffd`, on the base and on every rung". -/
@[req "CHN-15"]
def escapeSequence : Nat := 0xfffffffd

/-- The admitted domain of one member: its commitment's fields in range. -/
def admissible (ctx : Ctx) (q : Request) (m : Member) : Bool := decide (commitment ctx q m).WF

/-- Gate 22 on the spend (`SPN-26`): upstream, then `POL-6`; gate 23: hot-class (`CHN-32`) and
`CHN-30`'s count of vault-derived outputs. -/
@[req "SPN-26"]
def spendFault (ctx : Ctx) (m : Member) : Option Policy.Code :=
  m.upstream <|> Evaluate.evaluate ctx.cfg m.psbt <|>
    (if classOf ctx m == some .hot &&
        Classification.vaultOutputsBounded m.psbt.txInputs.length (outputs ctx m)
      then none else some .PSBT_INCONSISTENT)

/-- Gate 25 on the Escape and on each rung (`SPN-27`): the same three steps, then escape-class
(`CHN-32`) with `CHN-30`'s count of vault-derived outputs, and `CHN-15`'s sequence. -/
@[req "SPN-27"]
def escapeFault (ctx : Ctx) (m : Member) : Option Policy.Code :=
  m.upstream <|> Evaluate.evaluate ctx.cfg m.psbt <|>
    (if classOf ctx m == some .escape &&
        Classification.vaultOutputsBounded m.psbt.txInputs.length (outputs ctx m)
      then none else some .PSBT_INCONSISTENT) <|>
    (if m.psbt.txInputs.all (·.sequence == escapeSequence) then none else some .PSBT_INCONSISTENT)

/-- What checked ingress decides. `malformed` is gate 17 or 18's HTTP 400, `refused` a refusal that
stages nothing, `staged` one `SPN-5` stages, `accepted` the pair handed to `Kernel.accept`. -/
inductive Verdict
  | malformed
  | refused (code : Policy.Code)
  | staged (code : Policy.Code) (pair : Nat × Nat)
  | accepted (sp es : Cand)
  deriving DecidableEq, Repr

/-- Gates 17, 18, 22, 23, 24 and 25 in `SPN-5`'s order. Gate 22 propagates and stages "only
`HOT_BUDGET_EXCEEDED`"; a staged refusal's binding is the computed pair, available after `SPN-23`.
`fits` is gate 24's verdict on this spend, `Ledger.admits` over the ledger as `Ledger.checked` leaves
it at this step, so a gate-24 refusal comes before any gate-25 refusal. On the accepted path
`Ledger.sysStep` decides gate 24 again on the `accept` event, over the same ledger. -/
@[req "SPN-5"]
def check (ctx : Ctx) (fits : Bool) (q : Request) : Verdict :=
  let sp := cand ctx q q.spend true q.fireAt
  let es := cand ctx q q.escape false none
  if !(admissible ctx q q.spend && admissible ctx q q.escape) then .malformed
  else if 3 < q.rungs.length then .refused .PSBT_INCONSISTENT
  else if !q.rungs.all (admissible ctx q) then .malformed
  else match spendFault ctx q.spend with
    | some .HOT_BUDGET_EXCEEDED => .staged .HOT_BUDGET_EXCEEDED (sp.id, es.id)
    | some c => .refused c
    | none =>
      if !fits then .staged .HOT_VELOCITY_EXCEEDED (sp.id, es.id)
      else match escapeFault ctx q.escape <|> q.rungs.findSome? (escapeFault ctx) with
      | some c => .refused c
      | none => .accepted sp es

/-- The kernel event a verdict is, at this Carrier: `accept`, `refuse`, or none. -/
def Verdict.event (cid : Nat) (duress : Bool) (E : Wall) : Verdict → Option Event
  | .accepted sp es => some (.accept cid duress E sp es)
  | .staged c pair => some (.refuse cid duress E (some pair) c)
  | _ => none

/-! ## What an acceptance carries -/

theorem orElse_none {α : Type} {a b : Option α} (h : (a <|> b) = none) : a = none ∧ b = none := by
  cases a <;> simp_all

/-- `SPN-32`'s "sign the spend, the Escape and every rung at ingress" runs only on a group that
passed: an accepted verdict means every member is admissible and passed its checks, and the
candidates are the ones the request derives. -/
@[req "SPN-32"]
theorem accepted_validates {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    admissible ctx q q.spend = true ∧ admissible ctx q q.escape = true ∧
    q.rungs.length ≤ 3 ∧ (∀ m ∈ q.rungs, admissible ctx q m = true) ∧
    spendFault ctx q.spend = none ∧ escapeFault ctx q.escape = none ∧
    (∀ m ∈ q.rungs, escapeFault ctx m = none) ∧ fits = true ∧
    sp = cand ctx q q.spend true q.fireAt ∧ es = cand ctx q q.escape false none := by
  unfold check at h
  simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h1 h2 h3
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at h1
  simp only [Nat.not_lt] at h2
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h3
  split at h
  · cases h
  · cases h
  · rename_i hs
    split at h
    · cases h
    · rename_i hf
      split at h
      · cases h
      · rename_i he
        cases h
        obtain ⟨he1, he2⟩ := orElse_none he
        exact ⟨h1.1, h1.2, h2, h3, hs, he1, List.findSome?_eq_none_iff.1 he2,
          by simpa using hf, rfl, rfl⟩

/-- The two members' roles are fixed by the request: the spend is the hot member and the Escape the
non-hot one, so a checked acceptance never hands `Kernel.accept` a swapped pair. -/
@[req "SPN-32"]
theorem accepted_roles {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) : sp.hot = true ∧ es.hot = false := by
  obtain ⟨-, -, -, -, -, -, -, -, rfl, rfl⟩ := accepted_validates h
  exact ⟨rfl, rfl⟩

/-- `SPN-28`: the recorded class is hot, read with the outflow from one scan of the spend's decoded
outputs, and the outflow is within `POL-11`'s per-transaction cap. Acceptance goes through
`Evaluate.acceptance_exact`. -/
@[req "SPN-28"]
theorem accepted_spend {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    classOf ctx q.spend = some .hot ∧
    sp.tx.outflow = Classification.hotOutflow (outputs ctx q.spend) ∧
    sp.tx.outflow ≤ ctx.cfg.hotMaxPerTx ∧
    Evaluate.Consistent q.spend.psbt ∧ Evaluate.Owned ctx.cfg q.spend.psbt ∧
    Classification.allowlisted (outputs ctx q.spend) = true := by
  obtain ⟨-, -, -, -, hs, -, -, -, rfl, -⟩ := accepted_validates h
  unfold spendFault at hs
  obtain ⟨-, hs⟩ := orElse_none hs
  obtain ⟨he, hc⟩ := orElse_none hs
  obtain ⟨hcons, hown, hall, hbud, -⟩ := (Evaluate.acceptance_exact ctx.cfg q.spend.psbt).1 he
  refine ⟨?_, rfl, ?_, hcons, hown, hall⟩
  · generalize classOf ctx q.spend = k at hc ⊢
    rcases k with _ | ⟨_ | _ | _⟩ <;> simp_all
  · simpa [Classification.hotBudgetOk] using hbud

/-- The Escape: escape-class, with no fire time (`SPN-37`: registered "with **no** fire window").
Its zero outflow is `Exhibits.Ingress.escape_zero_outflow`, which reads the current
classification. -/
@[req "SPN-27"]
theorem accepted_escape {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    classOf ctx q.escape = some .escape ∧ es.fireAt = none := by
  obtain ⟨-, -, -, -, -, he, -, -, -, rfl⟩ := accepted_validates h
  unfold escapeFault at he
  obtain ⟨-, he⟩ := orElse_none he
  obtain ⟨-, he⟩ := orElse_none he
  obtain ⟨hc, -⟩ := orElse_none he
  have hcl : classOf ctx q.escape = some .escape := by
    generalize classOf ctx q.escape = k at hc ⊢
    rcases k with _ | ⟨_ | _ | _⟩ <;> simp_all
  exact ⟨hcl, rfl⟩

/-- The transaction a member carries reads only the transaction fields: two copies of a request that
differ in input maps, hints or upstream verdicts carry one transaction, and so one sighash per
input (`Kernel.sighash`). -/
@[req "CHN-30"]
theorem tx_of_fields (ctx : Ctx) (m m' : Member) (hi : m.psbt.txInputs = m'.psbt.txInputs)
    (ho : m.psbt.txOutputs = m'.psbt.txOutputs) (hv : m.version = m'.version)
    (hl : m.lockTime = m'.lockTime) : tx ctx m = tx ctx m' := by
  simp only [tx, Member.frame, outputs, Evaluate.outputs, hi, ho, hv, hl]

/-- `POL-10`: replacing a member's output hints with an equal-length list changes neither the
candidates nor whether the member passes. -/
@[req "POL-10"]
theorem hints_never_pass (ctx : Ctx) (m : Member) (hs : List Bool)
    (hlen : hs.length = m.psbt.outputHints.length) :
    let m' := { m with psbt := { m.psbt with outputHints := hs } }
    (spendFault ctx m' = none ↔ spendFault ctx m = none) ∧
    (escapeFault ctx m' = none ↔ escapeFault ctx m = none) ∧
    tx ctx m' = tx ctx m := by
  have he := Evaluate.hints_acceptance_iff ctx.cfg m.psbt hs hlen
  refine ⟨?_, ?_, tx_of_fields ctx _ _ rfl rfl rfl rfl⟩
  · simp [spendFault, classOf, outputs, Evaluate.outputs, he]
  · simp [escapeFault, classOf, outputs, Evaluate.outputs, he]

/-! ## One commitment, one amount -/

/-- `CHN-24`'s two halves at a checked acceptance: with the commitment id collision-free, two
acceptances under one commitment id carry one transaction, so one `POL-11` amount and one sighash
per input, and one expiry. This is `Ledger.bridge`'s `hamt` at the candidates `Kernel.accept`
receives; that every ledger row comes from such an acceptance is not stated here. -/
@[req "CHN-24"]
theorem one_amount_per_commitment {ctx : Ctx}
    (hid : ∀ a b, ctx.commitId a = ctx.commitId b → a = b) {fits fits' : Bool} {q q' : Request} {sp es sp' es' : Cand}
    (h : check ctx fits q = .accepted sp es) (h' : check ctx fits' q' = .accepted sp' es')
    (hcid : sp.id = sp'.id) : sp.tx = sp'.tx ∧ sp.expiry = sp'.expiry := by
  obtain ⟨ha, -, -, -, -, -, -, -, rfl, -⟩ := accepted_validates h
  obtain ⟨ha', -, -, -, -, -, -, -, rfl, -⟩ := accepted_validates h'
  have hc := Encode.encode_injective _ _ (of_decide_eq_true ha) (of_decide_eq_true ha')
    (hid _ _ hcid)
  simp only [commitment, Encode.Commitment.mk.injEq] at hc
  obtain ⟨-, hv, hl, hi, ho, -, hx, -⟩ := hc
  exact ⟨tx_of_fields ctx _ _ hi ho hv hl, by simp only [cand, hx]⟩

/-! ## Over a federation -/

/-- Every honest acceptance in the trace is the event checked ingress produced for some request,
under one shared `Ctx`, with gate 24 left to the ledger: `Ledger.sysStep` decides it on the event. -/
def CheckedTrace (ctx : Ctx) (t : Federation.Trace) : Prop :=
  ∀ y ∈ t, ∀ i env cid d E sp es, y.2 = .process i env (.accept cid d E sp es) →
    ∃ q, check ctx true q = .accepted sp es

/-- The pairs a trace hands `Kernel.accept`, for deciding `CheckedTrace` on a fixture. -/
def acceptPairs : Federation.Trace → List (Cand × Cand)
  | [] => []
  | (_, .process _ _ (.accept _ _ _ sp es)) :: t => (sp, es) :: acceptPairs t
  | _ :: t => acceptPairs t

theorem mem_acceptPairs {i : Nat} {env : Env} {cid : Nat} {d : Bool} {E : Wall} {sp es : Cand} :
    ∀ {t : Federation.Trace} {y : Federation.Fed × Federation.Step}, y ∈ t →
      y.2 = .process i env (.accept cid d E sp es) → (sp, es) ∈ acceptPairs t
  | [], _, hy, _ => by cases hy
  | z :: t, y, hy, hs => by
    have tail : (sp, es) ∈ acceptPairs t → (sp, es) ∈ acceptPairs (z :: t) := by
      intro h
      obtain ⟨g, s⟩ := z
      cases s with
      | process j env' e => cases e <;> simp [acceptPairs, h]
      | _ => simpa [acceptPairs] using h
    rcases List.mem_cons.1 hy with rfl | hy
    · obtain ⟨g, s⟩ := y; simp only at hs; subst hs; simp [acceptPairs]
    · exact tail (mem_acceptPairs hy hs)

theorem checkedTrace_of (ctx : Ctx) (t : Federation.Trace) (qs : List Request)
    (h : (acceptPairs t).all (fun p => qs.any fun q => check ctx true q == .accepted p.1 p.2) = true) :
    CheckedTrace ctx t := by
  intro y hy i env cid d E sp es hs
  obtain ⟨q, -, hq⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ (mem_acceptPairs hy hs))
  exact ⟨q, by simpa using hq⟩

/-- A candidate's transaction and class come from an admissible member of that class. -/
def Classed (ctx : Ctx) (c : Cand) : Prop :=
  ∃ m : Member, m.frame.WF ∧ c.tx = tx ctx m ∧
    classOf ctx m = some (if c.hot then .hot else .escape)

theorem frame_wf {ctx : Ctx} {q : Request} {m : Member} (h : admissible ctx q m = true) :
    m.frame.WF := by
  have h := of_decide_eq_true h
  simp only [commitment, Member.frame] at h ⊢
  obtain ⟨-, hv, hl, hni, hi, hno, ho, -, -, -⟩ := h
  exact ⟨by simp, hv, hl, hni, hi, hno, ho, by simp, by simp, by simp⟩

theorem accepted_classed {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) : Classed ctx sp ∧ Classed ctx es := by
  obtain ⟨ha, he, -, -, -, -, -, -, hsp, hes⟩ := accepted_validates h
  have hs := (accepted_spend h).1
  have hc := (accepted_escape h).1
  subst hsp hes
  exact ⟨⟨q.spend, frame_wf ha, rfl, hs⟩, ⟨q.escape, frame_wf he, rfl, hc⟩⟩

/-- Every candidate resident at an honest node, at every state of a checked execution, is
classed. -/
theorem resident_classed {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t) :
    (∀ i ∈ honest, ∀ c ∈ (f.worlds i).node.cands, Classed ctx c) ∧
    ∀ y ∈ t, ∀ i ∈ honest, ∀ c ∈ (y.1.worlds i).node.cands, Classed ctx c := by
  induction hx with
  | init f h =>
    refine ⟨fun i hi c hc => ?_, fun y hy => by cases hy⟩
    rw [(h.2.2 i hi).2.2.2.1] at hc; cases hc
  | @next t f s ha hx ih =>
    have hct : CheckedTrace ctx t := fun y hy => hc y (List.mem_cons_of_mem _ hy)
    obtain ⟨now, past⟩ := ih hct
    refine ⟨?_, fun y hy => ?_⟩
    · intro i hi c hcm
      cases hact : Federation.actor s with
      | none =>
        rw [Federation.apply_no_actor r f s hact i] at hcm
        exact now i hi c hcm
      | some a =>
        obtain ⟨j, env, e⟩ := a
        rw [Federation.apply_of_actor r f s hact i] at hcm
        split at hcm
        · subst i
          rcases Federation.cand_origin r env (f.worlds j) e hcm with
            ⟨d, hd, dh, dt, -⟩ | ⟨cid, dd, E, sp, es, rfl, -, hse⟩
          · obtain ⟨m, hw, htx, hcl⟩ := now j hi d hd
            exact ⟨m, hw, dt ▸ htx, dh ▸ hcl⟩
          · have hs : s = .process j env (.accept cid dd E sp es) := by
              cases s <;> simp_all [Federation.actor]
            obtain ⟨q, hq⟩ := hc (f, s) List.mem_cons_self j env cid dd E sp es hs
            obtain ⟨csp, ces⟩ := accepted_classed hq
            rcases hse with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · obtain ⟨m, hw, htx, hcl⟩ := csp
              exact ⟨m, hw, ht ▸ htx, hh ▸ hcl⟩
            · obtain ⟨m, hw, htx, hcl⟩ := ces
              exact ⟨m, hw, ht ▸ htx, hh ▸ hcl⟩
        · exact now i hi c hcm
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact now
      · exact past y hy

/-- A queued input-0 row is a resident candidate's input-0 message, with that candidate's class. -/
theorem queued_cand {r : Rules} {env : Env} {w : World} {e : Event} {x : Exp}
    (hx : x ∈ Federation.fanout w (step r env w e).2) (h0 : x.input = 0) :
    ∃ c ∈ w.node.cands, x.msg = sighash c.tx 0 ∧ x.hot = c.hot := by
  have hq := (Federation.mem_fanout hx).2.resolve_right (by rw [h0]; simp)
  obtain ⟨eff, he, hx⟩ := List.mem_filterMap.1 hq
  cases eff with
  | broadcast _ => cases hx
  | queuePartial m i h cid =>
    simp only [Option.some.injEq] at hx
    subst hx
    cases e with
    | firePass =>
      simp only [step] at he
      unfold firePass at he
      split at he
      · cases he
      · obtain ⟨c, hc, hce⟩ := List.mem_map.1 he
        simp only [Effect.queuePartial.injEq] at hce
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hce
        exact ⟨c, (List.mem_filter.1 hc).1, rfl, rfl⟩
    | send cid' =>
      simp only [step, send] at he
      split at he
      · cases he
      · split at he <;> simp at he
    | _ => simp [step] at he

/-- `Federation.HotBinding` derived: in a checked federation execution, with the transaction identity
collision-free, no partial of a signer outside the extracted set, queued under a non-hot candidate,
shares a hot-class transaction's input-0 message. A non-hot candidate is an escape-class member, and
one identity is one transaction, so one class. -/
@[req "DUR-8"]
theorem hot_binding {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t)
    (hid : ∀ a b, ctx.txId a = ctx.txId b → a = b) {m : Member} (hw : m.frame.WF)
    (hhot : classOf ctx m = some .hot) :
    Federation.HotBinding f (sighash (tx ctx m) 0) := by
  intro x hxm hext hmsg h0
  rcases Federation.part_origin hx hxm with he | ⟨hs, g, env, e, hm, hq⟩
  · exact absurd he hext
  obtain ⟨c, hcm, hcmsg, hch⟩ := queued_cand hq h0
  obtain ⟨m', hw', htx, hcl⟩ := (resident_classed hx hc).2 _ hm x.signer hs c hcm
  rw [hch]
  rw [hmsg, htx] at hcmsg
  simp only [sighash, tx, Prod.mk.injEq, and_true] at hcmsg
  have hf := Encode.encode_injective _ _ hw hw' (hid _ _ hcmsg)
  have ho : m.psbt.txOutputs = m'.psbt.txOutputs := by
    simp only [Member.frame, Encode.Commitment.mk.injEq] at hf
    exact hf.2.2.2.2.1
  have : classOf ctx m' = some .hot := by
    rw [← hhot]; simp only [classOf, outputs, Evaluate.outputs, ho]
  cases hh : c.hot
  · rw [hh] at hcl; rw [hcl] at this; cases this
  · rfl

/-- `DUR-8`'s "never a signing quorum" over a checked federation execution, for a target the checks
accepted: `Federation.no_exposed_quorum` with its message binding replaced by two premises, every
honest acceptance checked and a collision-free transaction identity. What stays: `hr`, `noNormal`,
`bound`. -/
@[req "DUR-8"]
theorem no_exposed_quorum {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t)
    (hid : ∀ a b, ctx.txId a = ctx.txId b → a = b) (n : Node) {fits : Bool} {q : Request} {sp es : Cand}
    (hq : check ctx fits q = .accepted sp es)
    (noNormal : NoHonestNormalDecision r (fun j => Federation.project j t) f.extracted
      (sighash sp.tx 0))
    (bound : f.extracted.eraseDups.length < n.t) :
    exposedQuorum { node := n, exposure := f.parts } sp = false := by
  obtain ⟨ha, -, -, -, -, -, -, -, hsp, -⟩ := accepted_validates hq
  have hb : Federation.HotBinding f (sighash sp.tx 0) := by
    rw [hsp]; exact hot_binding hx hc hid (frame_wf ha) (accepted_spend hq).1
  exact Federation.no_exposed_quorum hr hx n sp hb noNormal bound

end BtcPolicy.Ingress
