import BtcPolicy.RungIngress
import BtcPolicy.Witness
/-! Checked ingress with `CHN-16`'s relations between the Escape's rungs. Beside `BtcPolicy.RungIngress`, whose
`RungIngress.check` checks each rung on its own: its decoding, the count bound, `SPN-27`'s three steps,
escape-class and `CHN-15`'s sequence. `Ingress.check`, `RungIngress.check` and every result about them keep their
statements; the results here are new theorems beside them.

**The relations.** `LadderShape.stepOk` is `CHN-16` for one rung over the rung below it: `CHN-15`'s sequence on
every input, the base's `nVersion`, `nLockTime = 0`, the base's ordered outpoints, the base's ordered output
scripts, every output value at or below the same output's on the rung below, and a fee increase of at least the
rung's maximum finalized vsize at 1 sat/vB (`LadderShape.vsize`, which is `Witness.maxVsize` over
`Witness.legacy`'s length, `CHN-34`). `LadderShape.ladderOk` applies it to each rung in order, the first over the
base. The fees are the Escape's: its input total less each rung's outputs (`LadderShape.feeOver`). `Evaluate.totalIn`
reads a member's own input maps, so each rung's maps must be the Escape's (`LadderShape.prevoutFault`), which is how
`SPN-27`'s "verify each rung as an Escape against the Escape's own prevouts" is read here; then every rung's own fee
is its fee over the Escape's data. The Escape's data stays the supplied upstream premise it is in
`BtcPolicy.Ingress` (`Ingress.Member.upstream`).

**The check.** `LadderShape.gates` is `Ingress.check`'s gate sequence with gate 25 as a parameter
(`LadderShape.ingress_gates`). `LadderShape.check` runs it with gate 25 in `SPN-27`'s order
(`LadderShape.escapeGate`): the Escape's own checks, then the ladder rules, then each rung as an Escape against the
Escape's prevouts. Before gate 25 it decides as `RungIngress.check` (`LadderShape.check_before`), so no ladder failure
moves ahead of a malformed member, the count bound, the spend's refusals or gate 24's staging; on a request that
reaches gate 25 and whose Escape passes its own checks, a ladder failure refuses `PSBT_INCONSISTENT` and stages
nothing (`LadderShape.check_refused`). An acceptance is exactly
`RungIngress.check`'s acceptance with the relations and the common prevout data
(`LadderShape.check_accepted_iff`); a request with no rung is checked exactly as before (`LadderShape.check_nil`).

**What an acceptance carries.** `LadderShape.Valid`, the relations as stated, each rung's own fee included
(`LadderShape.accepted_valid`); every retained rung spends the base's inputs in order (`LadderShape.accepted_inputs`);
with a collision-free transaction identity the ladder's txids are distinct (`LadderShape.accepted_ids`). A sublist
of an accepted ladder is accepted over the same spend (`LadderShape.check_sublist`), so stripping rungs before
first acceptance and nodes taking different subsets of one signed ladder stay inside the check. Over a federation,
`LadderShape.CheckedTrace` is a `RungIngress.CheckedTrace` (`LadderShape.to_rung`), so every result over that one
applies.

**Not here.** `CHN-17`'s construction, the sealed ceiling and every composer rule: no node-side ceiling is added.
`CHN-14`'s vault-only inputs are each member's input-ownership check in `Evaluate.evaluate`, and its escape
destinations each member's output classification, as before; the base's own `nLockTime` is not checked, as in `BtcPolicy.Ingress`. The template's `t` and `n` are parameters, as the sealed
descriptor gives them. The retained-lifetime form of these relations, over every resident candidate of a run, is not
proved here. -/

namespace BtcPolicy.LadderShape
open BtcPolicy.Kernel
open BtcPolicy.Ingress (Ctx Member Verdict admissible spendFault escapeFault cand escapeSequence orElse_none)

/-! ## The relations -/

/-- A member's transaction, as `Witness.legacy` serializes it. -/
def wtx (m : Member) : Witness.Tx :=
  { version := m.version, lockTime := m.lockTime, inputs := m.psbt.txInputs, outputs := m.psbt.txOutputs }

/-- `CHN-34`'s maximum finalized vsize of a member under the template's `t` and `n`: `Witness.maxVsize` over the
length of the member's legacy serialization and its input count. -/
@[req "CHN-34"]
def vsize (t n : Nat) (m : Member) : Nat :=
  Witness.maxVsize (Witness.legacy (wtx m)).length m.psbt.txInputs.length t n

theorem vsize_pos (t n : Nat) (m : Member) : 0 < vsize t n m := by
  unfold vsize Witness.maxVsize Witness.maxWeight
  omega

/-- A member's total fee over its own input maps, as `Ingress.commitment` binds it. -/
def fee (m : Member) : Nat := Evaluate.totalIn m.psbt - Evaluate.totalOut m.psbt

/-- A member's total fee over the Escape's prevout data: the Escape's input total less this member's outputs. -/
def feeOver (base m : Member) : Nat := Evaluate.totalIn base.psbt - Evaluate.totalOut m.psbt

/-- The ordered outpoints a member spends. -/
def outpoints (m : Member) : List (Encode.Bytes × Nat) := m.psbt.txInputs.map fun i => (i.txid, i.vout)

/-- The ordered output scripts. -/
def scripts (m : Member) : List Encode.Bytes := m.psbt.txOutputs.map (·.script)

/-- Output by output, each value at or below the value at the same position, over two lists of one length. -/
def below : List Encode.Output → List Encode.Output → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a.amount ≤ b.amount) && below as bs
  | _, _ => false

/-- `CHN-16` for one rung over the rung below it: "the same `nVersion` as the base, `nLockTime = 0`, the same
ordered input set, the same ordered output script set, every output value at or below the value of the same output
on the rung below", and "a fee increase of at least `maximum_finalized_vsize × 1 sat/vB` over the rung below", with
`CHN-15`'s sequence on every input. The fees are over the Escape's prevout data. -/
@[req "CHN-16"]
def stepOk (t n : Nat) (base lower m : Member) : Bool :=
  m.psbt.txInputs.all (·.sequence == escapeSequence) && m.version == base.version && m.lockTime == 0 &&
    outpoints m == outpoints base && scripts m == scripts base &&
    below m.psbt.txOutputs lower.psbt.txOutputs &&
    decide (feeOver base lower + vsize t n m ≤ feeOver base m)

/-- The ladder over the base: each rung over the one below it, the first over the base. -/
@[req "CHN-16"]
def ladderOk (t n : Nat) (base : Member) : Member → List Member → Bool
  | _, [] => true
  | lower, m :: ms => stepOk t n base lower m && ladderOk t n base m ms

/-! ## Gate 25 in `SPN-27`'s order -/

/-- `SPN-27`'s ladder rules: "It MUST apply the ladder rules of `CHN-14`–`CHN-16` to every rung with refusals
`escape:bump_ladder`". -/
@[req "SPN-27"]
def ladderFault (t n : Nat) (base : Member) (rungs : List Member) : Option Policy.Code :=
  if ladderOk t n base base rungs then none else some .PSBT_INCONSISTENT

/-- A rung whose input maps are not the Escape's is not verified against the Escape's prevouts. -/
def prevoutFault (base m : Member) : Option Policy.Code :=
  if m.psbt.inputMaps == base.psbt.inputMaps then none else some .PSBT_INCONSISTENT

/-- One rung "as an Escape against the Escape's own prevouts": its maps are the Escape's, then gate 25 on it. -/
@[req "SPN-27"]
def rungFault (ctx : Ctx) (base m : Member) : Option Policy.Code :=
  prevoutFault base m <|> escapeFault ctx m

/-- Gate 25: the Escape's own checks, then the ladder rules, then each rung. -/
@[req "SPN-27"]
def escapeGate (ctx : Ctx) (t n : Nat) (q : Ingress.Request) : Option Policy.Code :=
  escapeFault ctx q.escape <|> ladderFault t n q.escape q.rungs <|> q.rungs.findSome? (rungFault ctx q.escape)

/-- `Ingress.check`'s gates 17, 18, 22, 23, 24 and 25 in `SPN-5`'s order, with gate 25's verdict a parameter. -/
@[req "SPN-5"]
def gates (ctx : Ctx) (fits : Bool) (q : Ingress.Request) (g25 : Option Policy.Code) : Verdict :=
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
      else match g25 with
      | some c => .refused c
      | none => .accepted sp es

/-- `Ingress.check` is these gates with its own gate 25. -/
theorem ingress_gates (ctx : Ctx) (fits : Bool) (q : Ingress.Request) :
    Ingress.check ctx fits q =
      gates ctx fits q (escapeFault ctx q.escape <|> q.rungs.findSome? (escapeFault ctx)) := by
  unfold Ingress.check gates
  rfl

/-- `RungIngress.check` with gate 25 in `SPN-27`'s order; on acceptance the Escape carries its ladder. -/
@[req "SPN-27"]
def check (ctx : Ctx) (t n : Nat) (fits : Bool) (q : RungIngress.Request) : Verdict :=
  match gates ctx fits q.plain (escapeGate ctx t n q.plain) with
  | .accepted sp es => .accepted sp (RungIngress.withLadder ctx q es)
  | v => v

/-! ## The gate order -/

/-- A request that reaches gate 25: every member decodes, the count bound holds, the spend passes and gate 24
fits. -/
def Reaches (ctx : Ctx) (fits : Bool) (q : Ingress.Request) : Prop :=
  admissible ctx q q.spend = true ∧ admissible ctx q q.escape = true ∧ q.rungs.length ≤ 3 ∧
    (∀ m ∈ q.rungs, admissible ctx q m = true) ∧ spendFault ctx q.spend = none ∧ fits = true

theorem gates_reach {ctx : Ctx} {fits : Bool} {q : Ingress.Request} (h : Reaches ctx fits q)
    (g : Option Policy.Code) :
    gates ctx fits q g = match g with
      | some c => .refused c
      | none => .accepted (cand ctx q q.spend true q.fireAt) (cand ctx q q.escape false none) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have h4' : q.rungs.all (admissible ctx q) = true := List.all_eq_true.2 h4
  have h3' : ¬ 3 < q.rungs.length := Nat.not_lt.2 h3
  subst h6
  simp only [gates, h1, h2, h4', h5, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h3']

/-- Before gate 25 the verdict does not read gate 25. -/
theorem gates_before {ctx : Ctx} {fits : Bool} {q : Ingress.Request} (h : ¬ Reaches ctx fits q)
    (g g' : Option Policy.Code) : gates ctx fits q g = gates ctx fits q g' := by
  unfold gates
  simp only
  split; · rfl
  split; · rfl
  split; · rfl
  rename_i h1 h2 h3
  split
  · rfl
  · rfl
  · rename_i hs
    split
    · rfl
    · rename_i hf
      exfalso
      apply h
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, Bool.not_eq_false] at h1
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h3
      exact ⟨h1.1, h1.2, Nat.not_lt.1 h2, h3, hs, by simpa using hf⟩

theorem gates_accepted {ctx : Ctx} {fits : Bool} {q : Ingress.Request} {g : Option Policy.Code}
    {sp es : Cand} (h : gates ctx fits q g = .accepted sp es) :
    Reaches ctx fits q ∧ g = none ∧ sp = cand ctx q q.spend true q.fireAt ∧
      es = cand ctx q q.escape false none := by
  by_cases hr : Reaches ctx fits q
  · rw [gates_reach hr] at h
    cases g with
    | some c => cases h
    | none => cases h; exact ⟨hr, rfl, rfl, rfl⟩
  · exfalso
    rw [gates_before hr g (some .PSBT_INCONSISTENT)] at h
    unfold gates at h
    simp only at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · cases h

theorem check_accepted {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand} :
    check ctx t n fits q = .accepted sp es ↔
      ∃ es₀, gates ctx fits q.plain (escapeGate ctx t n q.plain) = .accepted sp es₀ ∧
        es = RungIngress.withLadder ctx q es₀ := by
  unfold check
  cases hc : gates ctx fits q.plain (escapeGate ctx t n q.plain) with
  | accepted sp' es' =>
    simp only [Verdict.accepted.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨es', ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  | _ => simp

/-- **Gate order.** Short of gate 25 this check decides as `RungIngress.check`: a malformed member, the count
bound, the spend's refusals, gate 22's budget staging and gate 24's velocity staging all come first. -/
@[req "SPN-5"]
theorem check_before {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request}
    (h : ¬ Reaches ctx fits q.plain) : check ctx t n fits q = RungIngress.check ctx fits q := by
  unfold check RungIngress.check
  rw [ingress_gates, gates_before h (escapeGate ctx t n q.plain)
    (escapeFault ctx q.plain.escape <|> q.plain.rungs.findSome? (escapeFault ctx))]
  try rfl

/-- With no rung the check is `RungIngress.check`. -/
theorem check_nil (ctx : Ctx) (t n : Nat) (fits : Bool) (q : RungIngress.Request) (h : q.rungs = []) :
    check ctx t n fits q = RungIngress.check ctx fits q := by
  have hr : q.plain.rungs = [] := by simp [RungIngress.Request.plain, h]
  have hg : escapeGate ctx t n q.plain =
      (escapeFault ctx q.plain.escape <|> q.plain.rungs.findSome? (escapeFault ctx)) := by
    simp only [escapeGate, ladderFault, hr, ladderOk, ↓reduceIte, List.findSome?_nil]
    cases escapeFault ctx q.plain.escape <;> rfl
  unfold check RungIngress.check
  rw [ingress_gates, hg]
  try rfl

/-- **What gate 25 adds.** This check accepts exactly what `RungIngress.check` accepts, with the same candidates,
when the ladder passes `CHN-16`'s relations over the Escape and every rung carries the Escape's input maps. -/
@[req "CHN-16"]
theorem check_accepted_iff {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand} :
    check ctx t n fits q = .accepted sp es ↔
      RungIngress.check ctx fits q = .accepted sp es ∧
        ladderOk t n q.escape.member q.escape.member (q.rungs.map (·.member)) = true ∧
        ∀ s ∈ q.rungs, s.member.psbt.inputMaps = q.escape.member.psbt.inputMaps := by
  constructor
  · intro h
    obtain ⟨es₀, hg, rfl⟩ := check_accepted.1 h
    obtain ⟨hr, hn, rfl, rfl⟩ := gates_accepted hg
    unfold escapeGate at hn
    obtain ⟨hb, hn⟩ := orElse_none hn
    obtain ⟨hl, hn⟩ := orElse_none hn
    have hm := List.findSome?_eq_none_iff.1 hn
    have hrungs : ∀ m ∈ q.plain.rungs, prevoutFault q.plain.escape m = none ∧ escapeFault ctx m = none :=
      fun m hm' => orElse_none (hm m hm')
    have hold : (escapeFault ctx q.plain.escape <|> q.plain.rungs.findSome? (escapeFault ctx)) = none := by
      rw [hb, List.findSome?_eq_none_iff.2 (fun m hm' => (hrungs m hm').2)]; rfl
    refine ⟨?_, ?_, fun s hs => ?_⟩
    · refine RungIngress.check_accepted.2 ⟨_, ?_, rfl⟩
      rw [ingress_gates, hold, gates_reach hr]
    · unfold ladderFault at hl
      split at hl
      · assumption
      · cases hl
    · have hp := (hrungs s.member (List.mem_map.2 ⟨s, hs, rfl⟩)).1
      unfold prevoutFault at hp
      split at hp
      · rename_i he; simpa using he
      · cases hp
  · rintro ⟨h, hl, hp⟩
    obtain ⟨es₀, hc, rfl⟩ := RungIngress.check_accepted.1 h
    obtain ⟨h1, h2, h3, h4, h5, hb, hrs, hf, rfl, rfl⟩ := Ingress.accepted_validates hc
    have hr : Reaches ctx fits q.plain := ⟨h1, h2, h3, h4, h5, hf⟩
    have hn : escapeGate ctx t n q.plain = none := by
      have hl' : ladderFault t n q.plain.escape q.plain.rungs = none := by
        simp only [ladderFault, RungIngress.Request.plain] at hl ⊢; simp [hl]
      have hfs : q.plain.rungs.findSome? (rungFault ctx q.plain.escape) = none := by
        refine List.findSome?_eq_none_iff.2 fun m hm => ?_
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
        have : prevoutFault q.plain.escape s.member = none := by
          simp [prevoutFault, RungIngress.Request.plain, hp s hs]
        simp only [rungFault, this, hrs _ hm]; rfl
      simp only [escapeGate, hb, hl', hfs]; rfl
    refine check_accepted.2 ⟨_, ?_, rfl⟩
    rw [hn, gates_reach hr]

/-- A rung's acceptance under this check is one under `RungIngress.check`, with the same candidates. -/
theorem check_refines {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand}
    (h : check ctx t n fits q = .accepted sp es) : RungIngress.check ctx fits q = .accepted sp es :=
  (check_accepted_iff.1 h).1

/-- **A ladder failure refuses at gate 25.** A request that reaches gate 25, whose Escape passes its own checks and
whose ladder fails a relation, is refused `PSBT_INCONSISTENT` before any rung's own verification: the verdict stages
nothing and is no kernel event. -/
@[req "SPN-27"]
theorem check_refused {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request}
    (hr : Reaches ctx fits q.plain) (hb : escapeFault ctx q.escape.member = none)
    (hl : ladderOk t n q.escape.member q.escape.member (q.rungs.map (·.member)) = false) :
    check ctx t n fits q = .refused .PSBT_INCONSISTENT := by
  have hg : escapeGate ctx t n q.plain = some .PSBT_INCONSISTENT := by
    simp only [escapeGate, ladderFault, RungIngress.Request.plain] at hb hl ⊢
    simp [hb, hl]
  unfold check
  rw [gates_reach hr, hg]

/-! ## What an acceptance carries -/

/-- `CHN-16` for one rung over the rung below it, as decoded data, with each member's own fee. -/
structure Step (t n : Nat) (base lower m : Member) : Prop where
  sequence : ∀ i ∈ m.psbt.txInputs, i.sequence = escapeSequence
  version : m.version = base.version
  lockTime : m.lockTime = 0
  outpoints : outpoints m = outpoints base
  prevouts : m.psbt.inputMaps = base.psbt.inputMaps
  sameScripts : scripts m = scripts base
  width : m.psbt.txOutputs.length = lower.psbt.txOutputs.length
  values : ∀ k (h₁ : k < m.psbt.txOutputs.length) (h₂ : k < lower.psbt.txOutputs.length),
    m.psbt.txOutputs[k].amount ≤ lower.psbt.txOutputs[k].amount
  feeUp : fee lower < fee m
  increment : fee lower + vsize t n m ≤ fee m

/-- Each rung over the one below it. -/
def Chain (t n : Nat) (base : Member) : Member → List Member → Prop
  | _, [] => True
  | lower, m :: ms => Step t n base lower m ∧ Chain t n base m ms

/-- `CHN-16`'s ladder over decoded data: at most `Classification.maxRungs` rungs, each over the one below it, the
first over the base. -/
@[req "CHN-16"]
def Valid (t n : Nat) (base : Member) (rungs : List Member) : Prop :=
  rungs.length ≤ Classification.maxRungs ∧ Chain t n base base rungs

theorem below_iff : ∀ (xs ys : List Encode.Output), below xs ys = true ↔
    xs.length = ys.length ∧ ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length), xs[k].amount ≤ ys[k].amount
  | [], [] => by simp [below]
  | [], _ :: _ => by simp [below]
  | _ :: _, [] => by simp [below]
  | a :: as, b :: bs => by
    simp only [below, Bool.and_eq_true, decide_eq_true_eq, below_iff as bs, List.length_cons,
      Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨hab, hl, hk⟩
      refine ⟨hl, fun k h₁ h₂ => ?_⟩
      cases k with
      | zero => exact hab
      | succ k => exact hk k (by omega) (by omega)
    · rintro ⟨hl, hk⟩
      exact ⟨hk 0 (by omega) (by omega), hl, fun k h₁ h₂ => hk (k + 1) (by omega) (by omega)⟩

theorem fee_eq {base m : Member} (h : m.psbt.inputMaps = base.psbt.inputMaps) : fee m = feeOver base m := by
  simp [fee, feeOver, Evaluate.totalIn, h]

theorem stepOk_sound {t n : Nat} {base lower m : Member} (h : stepOk t n base lower m = true)
    (hlm : lower.psbt.inputMaps = base.psbt.inputMaps) (hmm : m.psbt.inputMaps = base.psbt.inputMaps) :
    Step t n base lower m := by
  simp only [stepOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, ho⟩, hsc⟩, hbl⟩, hf⟩ := h
  have hs' : ∀ i ∈ m.psbt.txInputs, i.sequence = escapeSequence := fun i hi => by simpa using hs i hi
  obtain ⟨hw, hk⟩ := (below_iff _ _).1 hbl
  have hpos := vsize_pos t n m
  rw [← fee_eq hlm, ← fee_eq hmm] at hf
  exact ⟨hs', hv, hl, ho, hmm, hsc, hw, hk, by omega, hf⟩

theorem ladderOk_sound {t n : Nat} {base : Member} :
    ∀ {lower : Member} {ms : List Member}, ladderOk t n base lower ms = true →
      lower.psbt.inputMaps = base.psbt.inputMaps → (∀ m ∈ ms, m.psbt.inputMaps = base.psbt.inputMaps) →
      Chain t n base lower ms
  | _, [], _, _, _ => trivial
  | _, m :: ms, h, hl, hm => by
    simp only [ladderOk, Bool.and_eq_true] at h
    have hmm := hm m List.mem_cons_self
    exact ⟨stepOk_sound h.1 hl hmm,
      ladderOk_sound h.2 hmm (fun x hx => hm x (List.mem_cons_of_mem _ hx))⟩

/-- **The derived ladder.** Every acceptance carries `CHN-16`'s relations over its decoded members, each rung's own
fee strictly above the one below it by at least its maximum finalized vsize, and the Escape retains those rungs, in
order, with their user-signature hashes. -/
@[req "CHN-16"]
theorem accepted_valid {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand}
    (h : check ctx t n fits q = .accepted sp es) :
    Valid t n q.escape.member (q.rungs.map (·.member)) ∧ es.above = q.rungs.map (RungIngress.rung ctx) ∧
      es.baseSig = q.escape.userSig := by
  obtain ⟨hc, hl, hp⟩ := check_accepted_iff.1 h
  obtain ⟨hab, hbs, -, -, -⟩ := RungIngress.accepted_rungs hc
  obtain ⟨-, -, hlen, -⟩ := RungIngress.accepted_validates hc
  refine ⟨⟨by simpa [Classification.maxRungs] using hlen, ?_⟩, hab, hbs⟩
  refine ladderOk_sound hl rfl fun m hm => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
  exact hp s hs

theorem chain_step {t n : Nat} {base : Member} :
    ∀ {lower : Member} {ms : List Member}, Chain t n base lower ms → ∀ m ∈ ms, ∃ l, Step t n base l m
  | _, [], _, _, hm => by cases hm
  | lower, x :: ms, ⟨hs, hc⟩, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨lower, hs⟩
    · exact chain_step hc m hm

theorem tx_inputs (ctx : Ctx) {m m' : Member} (h : outpoints m = outpoints m') :
    (Ingress.tx ctx m).inputs = (Ingress.tx ctx m').inputs := by
  have := congrArg (List.map fun p : Encode.Bytes × Nat => ctx.outpoint (p.1 ++ Encode.be 4 p.2)) h
  simpa [outpoints, Ingress.tx, List.map_map, Function.comp_def] using this

/-- Every rung an accepted Escape retains spends the base's inputs, in the base's order. -/
@[req "CHN-16"]
theorem accepted_inputs {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand}
    (h : check ctx t n fits q = .accepted sp es) : ∀ g ∈ es.ladder, g.tx.inputs = es.tx.inputs := by
  obtain ⟨⟨-, hch⟩, hab, -⟩ := accepted_valid h
  obtain ⟨hc, -, -⟩ := check_accepted_iff.1 h
  obtain ⟨-, rfl, -, -⟩ := RungIngress.accepted_validates hc
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · rfl
  rw [hab] at hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨l, hst⟩ := chain_step hch s.member (List.mem_map.2 ⟨s, hs, rfl⟩)
  simpa [RungIngress.rung, RungIngress.withLadder, Ingress.cand, RungIngress.Request.plain] using
    tx_inputs ctx hst.outpoints

theorem chain_lt {t n : Nat} {base : Member} :
    ∀ {lower : Member} {ms : List Member}, Chain t n base lower ms → ∀ m ∈ ms, fee lower < fee m
  | _, [], _, _, hm => by cases hm
  | lower, x :: ms, ⟨hs, hc⟩, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hs.feeUp
    · exact Nat.lt_trans hs.feeUp (chain_lt hc m hm)

theorem chain_pairwise {t n : Nat} {base : Member} :
    ∀ {lower : Member} {ms : List Member}, Chain t n base lower ms →
      (lower :: ms).Pairwise fun a b => fee a < fee b
  | _, [], _ => List.pairwise_singleton _ _
  | _, _ :: _, hc => List.pairwise_cons.2 ⟨chain_lt hc, chain_pairwise hc.2⟩

/-- With a collision-free transaction identity, the txids of an accepted Escape's ladder, the base first, are
distinct: each rung's fee is above every fee below it, so its outputs differ. -/
@[req "CHN-16"]
theorem accepted_ids {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand}
    (hid : ∀ a b, ctx.txId a = ctx.txId b → a = b) (h : check ctx t n fits q = .accepted sp es) :
    (es.ladder.map (·.tx.id)).Nodup := by
  obtain ⟨⟨-, hch⟩, hab, -⟩ := accepted_valid h
  obtain ⟨hc, -, hp⟩ := check_accepted_iff.1 h
  obtain ⟨hc0, rfl, -, -⟩ := RungIngress.accepted_validates hc
  obtain ⟨-, hab0, -, hadm, -, -, -, -, -, -⟩ := Ingress.accepted_validates hc0
  have hl : (Kernel.Cand.ladder (RungIngress.withLadder ctx q (cand ctx q.plain q.escape.member false none))).map
      (·.tx.id) = (q.escape.member :: q.rungs.map (·.member)).map fun m => (Ingress.tx ctx m).id := by
    simp [Kernel.Cand.ladder, RungIngress.withLadder, RungIngress.rung, Ingress.cand, RungIngress.Request.plain]
  rw [hl]
  have hmaps : ∀ m ∈ q.escape.member :: q.rungs.map (·.member),
      m.psbt.inputMaps = q.escape.member.psbt.inputMaps ∧ m.frame.WF := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨rfl, Ingress.frame_wf hab0⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
      exact ⟨hp s hs, Ingress.frame_wf (hadm _ hm)⟩
  refine List.pairwise_map.2 ((chain_pairwise hch).imp_of_mem fun {a b} ha hb hlt heq => ?_)
  obtain ⟨hma, hwa⟩ := hmaps a ha
  obtain ⟨hmb, hwb⟩ := hmaps b hb
  have hf := Encode.encode_injective _ _ hwa hwb (hid _ _ heq)
  have ho : a.psbt.txOutputs = b.psbt.txOutputs := by
    simp only [Ingress.Member.frame, Encode.Commitment.mk.injEq] at hf
    exact hf.2.2.2.2.1
  have : fee a = fee b := by simp [fee, Evaluate.totalIn, Evaluate.totalOut, hma, hmb, ho]
  omega

/-! ## Rungs dropped from an accepted ladder -/

theorem below_trans : ∀ {xs ys zs : List Encode.Output}, below xs ys = true → below ys zs = true →
    below xs zs = true
  | [], [], [], _, _ => rfl
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    simp only [below, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
    exact ⟨Nat.le_trans h₁.1 h₂.1, below_trans h₁.2 h₂.2⟩
  | [], [], _ :: _, _, h => by simp [below] at h
  | [], _ :: _, _, h, _ => by simp [below] at h
  | _ :: _, [], _, h, _ => by simp [below] at h
  | _ :: _, _ :: _, [], _, h => by simp [below] at h

theorem stepOk_trans {t n : Nat} {base a b c : Member} (h₁ : stepOk t n base a b = true)
    (h₂ : stepOk t n base b c = true) : stepOk t n base a c = true := by
  simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hb₁⟩, hf₁⟩ := h₁
  obtain ⟨⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, ho⟩, hsc⟩, hb₂⟩, hf₂⟩ := h₂
  exact ⟨⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, ho⟩, hsc⟩, below_trans hb₂ hb₁⟩, by omega⟩

theorem ladderOk_lower {t n : Nat} {base lower a : Member} (h : stepOk t n base lower a = true) :
    ∀ {ms : List Member}, ladderOk t n base a ms = true → ladderOk t n base lower ms = true
  | [], _ => rfl
  | m :: ms, hm => by
    simp only [ladderOk, Bool.and_eq_true] at hm ⊢
    exact ⟨stepOk_trans h hm.1, hm.2⟩

theorem ladderOk_sublist {t n : Nat} {base : Member} {ms' ms : List Member} (hs : ms'.Sublist ms) :
    ∀ {lower : Member}, ladderOk t n base lower ms = true → ladderOk t n base lower ms' = true := by
  induction hs with
  | slnil => intro _ _; rfl
  | cons a _ ih =>
    intro lower h
    simp only [ladderOk, Bool.and_eq_true] at h
    exact ih (ladderOk_lower h.1 h.2)
  | cons_cons a _ ih =>
    intro lower h
    simp only [ladderOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-- **Dropping rungs keeps the request inside the check.** Any sublist of an accepted request's ladder, over the
same spend, Escape, expiry and fire time, is accepted with the same spend candidate: rungs stripped before first
acceptance, and nodes initially given different subsets of one signed ladder, stay inside the check. -/
@[req "CHN-16"]
theorem check_sublist {ctx : Ctx} {t n : Nat} {fits : Bool} {q : RungIngress.Request} {sp es : Cand}
    (h : check ctx t n fits q = .accepted sp es) {rs : List RungIngress.Signed} (hs : rs.Sublist q.rungs) :
    ∃ es', check ctx t n fits { q with rungs := rs } = .accepted sp es' := by
  obtain ⟨hc, hl, hp⟩ := check_accepted_iff.1 h
  obtain ⟨hc0, -, -, -⟩ := RungIngress.accepted_validates hc
  obtain ⟨h1, h2, h3, h4, h5, hb, hrs, hf, hsp, -⟩ := Ingress.accepted_validates hc0
  let q' : RungIngress.Request := { q with rungs := rs }
  have hsm : (rs.map (·.member)).Sublist (q.rungs.map (·.member)) := hs.map _
  have hmem : ∀ m ∈ q'.plain.rungs, m ∈ q.plain.rungs := fun m hm => hsm.subset hm
  have hr : Reaches ctx fits q'.plain :=
    ⟨h1, h2, Nat.le_trans hsm.length_le h3, fun m hm => h4 m (hmem m hm), h5, hf⟩
  refine ⟨RungIngress.withLadder ctx q' (cand ctx q'.plain q'.plain.escape false none), check_accepted.2 ⟨_, ?_, rfl⟩⟩
  have hl' : ladderFault t n q'.plain.escape q'.plain.rungs = none := by
    have := ladderOk_sublist hsm hl
    simp only [ladderFault, RungIngress.Request.plain, q'] at this ⊢
    simp [this]
  have hfs : q'.plain.rungs.findSome? (rungFault ctx q'.plain.escape) = none := by
    refine List.findSome?_eq_none_iff.2 fun m hm => ?_
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hm
    have : prevoutFault q'.plain.escape s.member = none := by
      simp [prevoutFault, RungIngress.Request.plain, q', hp s (hs.subset hs')]
    simp only [rungFault, this, hrs _ (hmem _ hm)]; rfl
  have hn : escapeGate ctx t n q'.plain = none := by
    simp only [escapeGate, hl', hfs]
    simp only [RungIngress.Request.plain, q'] at hb ⊢
    simp [hb]
  rw [hn, gates_reach hr, hsp]
  rfl

/-! ## Over a federation -/

/-- `RungIngress.CheckedTrace` with this check: every honest acceptance is the event this check produced for some
request, and every claw-back `Ingress.checkClawback`'s candidate. -/
def CheckedTrace (ctx : Ctx) (t n : Nat) (tr : Federation.Trace) : Prop :=
  (∀ y ∈ tr, ∀ i env cid d E sp es, y.2 = .process i env (.accept cid d E sp es) →
    ∃ q, check ctx t n true q = .accepted sp es) ∧
  ∀ y ∈ tr, ∀ i env c, y.2 = .process i env (.clawback c) →
    ∃ q, Ingress.checkClawback ctx Classification.current q = some c

/-- A run checked by this ingress is checked by `RungIngress.check`, so every result over that check applies to
it. -/
theorem to_rung {ctx : Ctx} {t n : Nat} {tr : Federation.Trace} (h : CheckedTrace ctx t n tr) :
    RungIngress.CheckedTrace ctx tr := by
  refine ⟨fun y hy i env cid d E sp es hs => ?_, h.2⟩
  obtain ⟨q, hq⟩ := h.1 y hy i env cid d E sp es hs
  exact ⟨q, check_refines hq⟩

/-- A fixture's trace is checked when each acceptance is some request's verdict and each claw-back some
ClawbackRequest's candidate. -/
theorem checkedTrace_of (ctx : Ctx) (t n : Nat) (tr : Federation.Trace) (qs : List RungIngress.Request)
    (qcs : List Ingress.ClawbackRequest)
    (h : (Ingress.acceptPairs tr).all (fun p => qs.any fun q => check ctx t n true q == .accepted p.1 p.2) = true)
    (hcl : (Ingress.clawCands tr).all
      (fun c => qcs.any fun q => Ingress.checkClawback ctx Classification.current q == some c) = true) :
    CheckedTrace ctx t n tr := by
  refine ⟨fun y hy i env cid d E sp es hs => ?_, fun y hy i env c hs => ?_⟩
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ (Ingress.mem_acceptPairs hy hs))
    exact ⟨q, by simpa using hq⟩
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcl _ (Ingress.mem_clawCands hy hs))
    exact ⟨q, by simpa using hq⟩

/-- Every honest acceptance on a run checked by this ingress registers a ladder that is `CHN-16`'s over its decoded
request, each rung spending the base's inputs in order. -/
@[req "CHN-16"]
theorem acceptance_valid {ctx : Ctx} {t n : Nat} {tr : Federation.Trace} (h : CheckedTrace ctx t n tr) :
    ∀ y ∈ tr, ∀ i env cid d E sp es, y.2 = .process i env (.accept cid d E sp es) →
      ∃ q : RungIngress.Request, Valid t n q.escape.member (q.rungs.map (·.member)) ∧
        es.above = q.rungs.map (RungIngress.rung ctx) ∧ ∀ g ∈ es.ladder, g.tx.inputs = es.tx.inputs := by
  intro y hy i env cid d E sp es hs
  obtain ⟨q, hq⟩ := h.1 y hy i env cid d E sp es hs
  exact ⟨q, (accepted_valid hq).1, (accepted_valid hq).2.1, accepted_inputs hq⟩

end BtcPolicy.LadderShape
