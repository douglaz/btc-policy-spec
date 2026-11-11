import BtcPolicy.RungIngress
/-! The user-signature hash carried with a partial, from the sender's retained variant to the receiver's store, on the
composed run. A partial row (`Kernel.Exp`) carries no user-signature hash, so `RungIngress.storable` compares none and
two nodes retaining one rung txid under different hashes store each other's partials on it
(`Exhibits.RungAssembly.hash_mismatch_sent`). This module is a labelled layer over `Federation.Execution`: no new
kernel event, and no `Kernel`, `Federation` or `RungIngress` definition changes. Their results keep their statements;
the results here are new theorems beside them.

**The label.** `VariantReceipt.variantOf` is the user-signature hash of a node's retained variant for a partial: the
first resident candidate with the partial's commitment id whose ladder has a rung with the partial's message at its
input, and that rung's hash (`SPN-36` stores the hash with the variant). Every honest emission is an envelope, the
partial with the hash of the sender's variant in the world the partial left (`VariantReceipt.envelopes`), the world
`Federation.fanout` reads; the label came from the sender's retained variant (`VariantReceipt.envelope_origin`), and
every queued partial has one (`VariantReceipt.queued_envelope`). A labelled trace carries one label with each step
(`VariantReceipt.LTrace`); a delivery's label is an envelope an honest node sent with that partial, or any label at all
under an extracted signer (`VariantReceipt.labelOk`), the authentication boundary `Step.forge`'s guard draws.

**The relation to `Federation`.** Forgetting the labels of a labelled execution leaves a `Federation.Execution`
(`VariantReceipt.to_fed`), so every result about it applies; and every `Federation.Execution` is the forgetting of a
labelled one (`VariantReceipt.of_fed`, through `VariantReceipt.lift`). The labels constrain only the store, never the
federation's steps.

**The store.** `VariantReceipt.storable` is `NCH-24`'s "the rung is found by txid; the user-signature hash matches; the
input and signer are in range" on one labelled partial: the signer is one of the receiver's configured keys, and a
resident candidate with the commitment id has a first rung with the partial's message at its input, the input in that
rung's range, and, on an Escape-role candidate, the label equal to that rung's hash. It is stricter than
`RungIngress.storable` (`VariantReceipt.storable_sub`). `VariantReceipt.kept` keeps what that store took, as
`RungIngress.kept` does, except that a record already kept is not added again (`NCH-25`), and
`VariantReceipt.held` is `RungIngress.held` with this store. A kept record came from a delivery whose store test passed
in its own world with its own label (`VariantReceipt.stored_checked`); on an Escape-role candidate, from a signer not
extracted, the label is both the receiver's own retained hash at arrival and the sender's retained hash at emission
(`VariantReceipt.stored_binds`). This possession is contained in `RungIngress.held` (`VariantReceipt.held_sub`), so
every signature in it is the node's own or a partial of the inventory (`VariantReceipt.held_origin`). A refused
delivery and a duplicate one leave it as it was (`VariantReceipt.refused_adds_nothing`,
`VariantReceipt.duplicate_keeps`), while the partial stays exposed in the inventory (`VariantReceipt.exposure_kept`).

**Not modelled here.** The kernel's own `Kernel.receivePartial` runs on every delivery as before: its signer set
reads no hash and is not this store. A candidate that is not Escape-role (a spend, a Hot member, a singleton
claw-back) is not compared: its rows carry no signing-variant hash source here, and its base hash's default value is
never read as one. The candidate's expiry is not tested, as in `RungIngress.storable`. `RungAssembly`'s assembly
still reads `RungIngress.held`; routing it through this module's `held` is a later change. -/

namespace BtcPolicy.VariantReceipt
open BtcPolicy.Kernel
open BtcPolicy.Federation (Fed fanout)

/-! ## The retained variant -/

/-- The first rung of a candidate's ladder, the base first, whose transaction has message `m` at input `k`. -/
def rungOf (c : Cand) (m : Sighash) (k : Nat) : Option Rung := c.ladder.find? fun g => m == sighash g.tx k

theorem rungOf_some {c : Cand} {m : Sighash} {k : Nat} {g : Rung} (h : rungOf c m k = some g) :
    g ∈ c.ladder ∧ m = sighash g.tx k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The user-signature hash of node `n`'s retained variant for a partial on message `m`, input `k`, commitment `cid`:
the first resident candidate with this commitment id whose ladder has a rung with this message at this input, and
that rung's hash. -/
@[req "SPN-36"]
def variantOf (n : Node) (m : Sighash) (k cid : Nat) : Option Nat :=
  (n.cands.find? fun c => c.id == cid && (rungOf c m k).isSome).bind fun c => (rungOf c m k).map (·.userSig)

theorem variantOf_some {n : Node} {m : Sighash} {k cid h : Nat} (hv : variantOf n m k cid = some h) :
    ∃ c ∈ n.cands, c.id = cid ∧ ∃ g ∈ c.ladder, m = sighash g.tx k ∧ g.userSig = h := by
  unfold variantOf at hv
  cases hf : n.cands.find? (fun c => c.id == cid && (rungOf c m k).isSome) with
  | none => rw [hf] at hv; cases hv
  | some c =>
    rw [hf] at hv
    change Option.map (·.userSig) (rungOf c m k) = some h at hv
    have hc := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    cases hr : rungOf c m k with
    | none => rw [hr] at hv; cases hv
    | some g =>
      rw [hr] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      obtain ⟨hg, hm⟩ := rungOf_some hr
      exact ⟨c, hc, hp.1, g, hg, hm, hv⟩

/-! ## The envelopes -/

/-- The partials a node's step sends (`Federation.fanout`), each with the hash of the sender's retained variant in
the world it left. -/
def emitted (r : Rules) (w : World) (env : Env) (e : Event) : List (Exp × Option Nat) :=
  (fanout w (step r env w e).2).map fun x => (x, variantOf w.node x.msg x.input x.cid)

/-- Every honest emission of a composed trace as a labelled envelope. `NCH-23` puts the user-signature hash in the
partial payload. -/
@[req "NCH-23"]
def envelopes (r : Rules) : Federation.Trace → List (Exp × Option Nat)
  | [] => []
  | (f, .process i env e) :: t => emitted r (f.worlds i) env e ++ envelopes r t
  | _ :: t => envelopes r t

theorem mem_envelopes {r : Rules} {t : Federation.Trace} {z : Exp × Option Nat} :
    z ∈ envelopes r t ↔
      ∃ g i env e, (g, Federation.Step.process i env e) ∈ t ∧ z ∈ emitted r (g.worlds i) env e := by
  induction t with
  | nil => simp [envelopes]
  | cons y t ih =>
    obtain ⟨f, s⟩ := y
    cases s
    case process i env e =>
      simp only [envelopes, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨g, j, env', e', hm, h⟩)
        · exact ⟨f, i, env, e, .inl rfl, h⟩
        · exact ⟨g, j, env', e', .inr hm, h⟩
      · rintro ⟨g, j, env', e', hm | hm, h⟩
        · simp only [Prod.mk.injEq, Federation.Step.process.injEq] at hm
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
          exact .inl h
        · exact .inr ⟨g, j, env', e', hm, h⟩
    all_goals
      simp only [envelopes, ih, List.mem_cons]
      constructor
      · rintro ⟨g, j, env', e', hm, h⟩
        exact ⟨g, j, env', e', .inr hm, h⟩
      · rintro ⟨g, j, env', e', hm | hm, h⟩
        · simp at hm
        · exact ⟨g, j, env', e', hm, h⟩

theorem envelopes_append (r : Rules) (t₂ t₁ : Federation.Trace) :
    envelopes r (t₂ ++ t₁) = envelopes r t₂ ++ envelopes r t₁ := by
  induction t₂ with
  | nil => rfl
  | cons y t₂ ih =>
    obtain ⟨f, s⟩ := y
    cases s <;> simp [envelopes, ih]

/-- **Where a label comes from.** A labelled envelope was sent at an honest step, as a partial of that step's
fan-out, and its label is the hash of a rung, with the partial's message at its input, of a candidate the sender
retained under the partial's commitment id in the world the partial left. -/
@[req "NCH-23"]
theorem envelope_origin {r : Rules} {t : Federation.Trace} {x : Exp} {h : Nat}
    (hm : (x, some h) ∈ envelopes r t) :
    ∃ g i env e, (g, Federation.Step.process i env e) ∈ t ∧
      x ∈ fanout (g.worlds i) (step r env (g.worlds i) e).2 ∧
      ∃ c ∈ (g.worlds i).node.cands, c.id = x.cid ∧
        ∃ rg ∈ c.ladder, x.msg = sighash rg.tx x.input ∧ rg.userSig = h := by
  obtain ⟨g, i, env, e, hg, hz⟩ := mem_envelopes.1 hm
  obtain ⟨y, hy, he⟩ := List.mem_map.1 hz
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hv⟩ := he
  exact ⟨g, i, env, e, hg, hy, variantOf_some hv⟩

/-- A partial of an honest step's fan-out is an envelope, with the hash of the sender's variant in that step's
world. -/
theorem queued_envelope {r : Rules} {t : Federation.Trace} {g : Fed} {i : Nat} {env : Env} {e : Event} {x : Exp}
    (hg : (g, Federation.Step.process i env e) ∈ t) (hx : x ∈ fanout (g.worlds i) (step r env (g.worlds i) e).2) :
    (x, variantOf (g.worlds i).node x.msg x.input x.cid) ∈ envelopes r t :=
  mem_envelopes.2 ⟨g, i, env, e, hg, List.mem_map.2 ⟨x, hx, rfl⟩⟩

theorem queued_has_envelope {r : Rules} {t : Federation.Trace} {x : Exp} (hq : Federation.Queued r t x) :
    ∃ h, (x, h) ∈ envelopes r t := by
  obtain ⟨g, env, e, hg, hx⟩ := hq
  exact ⟨_, queued_envelope hg hx⟩

/-- A step of a federation execution was taken at a reachable state and was admitted there. -/
theorem fed_mem {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {g : Fed} {s : Federation.Step} (hm : (g, s) ∈ t) :
    (∃ t₁, Federation.Execution r honest t₁ g) ∧ Federation.admits honest g s = true := by
  induction hx with
  | init f h => cases hm
  | @next t f s' ha hx ih =>
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨⟨t, hx⟩, ha⟩
    · exact ih hm

/-- Over an execution, an envelope's partial names its sender: an honest node sent it at a step of its own, with the
hash of its own retained variant in that step's world. -/
@[req "NCH-23"]
theorem envelope_sender {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {x : Exp} {h : Option Nat} (hm : (x, h) ∈ envelopes r t) :
    x.signer ∈ honest ∧ ∃ g env e, (g, Federation.Step.process x.signer env e) ∈ t ∧
      x ∈ fanout (g.worlds x.signer) (step r env (g.worlds x.signer) e).2 ∧
      h = variantOf (g.worlds x.signer).node x.msg x.input x.cid := by
  obtain ⟨g, i, env, e, hg, hz⟩ := mem_envelopes.1 hm
  obtain ⟨y, hy, he⟩ := List.mem_map.1 hz
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨t₁, hx₁⟩, ha⟩ := fed_mem hx hg
  simp only [Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at ha
  have hs : y.signer = i := (Federation.mem_fanout hy).1.trans (Federation.node_id hx₁ ha.1)
  subst hs
  exact ⟨ha.1, g, env, e, hg, hy, rfl⟩

/-! ## The labelled layer -/

/-- A composed history, newest first, each step with the state it was taken in and its label. -/
abbrev LTrace := List (Fed × Federation.Step × Option Nat)

/-- The composed history without its labels. -/
def forget (T : LTrace) : Federation.Trace := T.map fun a => (a.1, a.2.1)

theorem forget_append (T₂ T₁ : LTrace) : forget (T₂ ++ T₁) = forget T₂ ++ forget T₁ := List.map_append

/-- Which label a step may carry after history `t` in state `f`: a delivery's is an envelope an honest node sent with
that partial, or, under an extracted signer, any label at all. Every other step's label is not read. -/
@[req "NCH-24"]
def labelOk (r : Rules) (t : Federation.Trace) (f : Fed) : Federation.Step → Option Nat → Bool
  | .deliverPartial _ _ x, h => (envelopes r t).contains (x, h) || f.extracted.contains x.signer
  | _, _ => true

/-- A reachable labelled execution: a federation step, admitted as `Federation.admits` admits it, with an admissible
label. -/
inductive Execution (r : Rules) (honest : List Nat) : LTrace → Fed → Prop
  | init (f : Fed) (h : Federation.Fresh honest f) : Execution r honest [] f
  | next {T f} (s : Federation.Step) (h : Option Nat) (ha : Federation.admits honest f s = true)
      (hl : labelOk r (forget T) f s h = true) : Execution r honest T f →
      Execution r honest ((f, s, h) :: T) (Federation.apply r f s)

/-- **The layer over `Federation`.** Forgetting the labels leaves a `Federation.Execution`. -/
@[req "NCH-24"]
theorem to_fed {r : Rules} {honest : List Nat} {T : LTrace} {f : Fed} (hx : Execution r honest T f) :
    Federation.Execution r honest (forget T) f := by
  induction hx with
  | init f h => exact .init f h
  | next s h ha _ _ ih => exact .next s ha ih

/-- A delivery's label in the lifted history: that of the newest envelope of the partial, if any. -/
def labelFor (r : Rules) (t : Federation.Trace) : Federation.Step → Option Nat
  | .deliverPartial _ _ x => ((envelopes r t).find? fun z => z.1 == x).bind (·.2)
  | _ => none

/-- A composed history with each delivery labelled by `labelFor`. -/
def lift (r : Rules) : Federation.Trace → LTrace
  | [] => []
  | (f, s) :: t => (f, s, labelFor r t s) :: lift r t

theorem forget_lift (r : Rules) : ∀ t : Federation.Trace, forget (lift r t) = t
  | [] => rfl
  | (f, s) :: t => by
    show (f, s) :: forget (lift r t) = (f, s) :: t
    rw [forget_lift r t]

/-- `labelFor`'s label is admissible at every admitted step of an execution: a delivered partial was queued by its
honest signer, so it has an envelope, or its signer is extracted (`Federation.part_origin`). -/
theorem labelFor_ok {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) (s : Federation.Step) (ha : Federation.admits honest f s = true) :
    labelOk r t f s (labelFor r t s) = true := by
  cases s
  case deliverPartial i env x =>
    simp only [Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at ha
    simp only [labelOk, labelFor, Bool.or_eq_true, List.contains_iff_mem]
    rcases Federation.part_origin hx ha.2 with he | ⟨-, hq⟩
    · exact .inr he
    · left
      obtain ⟨h, hh⟩ := queued_has_envelope hq
      cases hf : (envelopes r t).find? (fun z => z.1 == x) with
      | none => exact absurd (List.find?_eq_none.1 hf _ hh) (by simp)
      | some p =>
        have hp := List.find?_some hf
        have hpm := List.mem_of_find?_eq_some hf
        obtain ⟨p1, p2⟩ := p
        simp only [beq_iff_eq] at hp
        subst hp
        exact hpm
  all_goals rfl

/-- **Labels constrain only the store.** Every `Federation.Execution` is the forgetting of a labelled execution. -/
@[req "NCH-24"]
theorem of_fed {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) : Execution r honest (lift r t) f := by
  induction hx with
  | init f h => exact .init f h
  | @next t f s ha hx ih =>
    have hl : labelOk r (forget (lift r t)) f s (labelFor r t s) = true := by
      rw [forget_lift]; exact labelFor_ok hx s ha
    exact .next s _ ha hl ih

/-- A step of a labelled execution was admitted at its own state, after a reachable history, with an admissible
label. -/
theorem prefix_exec {r : Rules} {honest : List Nat} :
    ∀ {T : LTrace} {f : Fed}, Execution r honest T f →
      ∀ {T₂ T₁ : LTrace} {g : Fed} {s : Federation.Step} {h : Option Nat}, T = T₂ ++ (g, s, h) :: T₁ →
        Execution r honest T₁ g ∧ Federation.admits honest g s = true ∧ labelOk r (forget T₁) g s h = true := by
  intro T f hx
  induction hx with
  | init f h => intro T₂ T₁ g s h' hT; cases T₂ <;> cases hT
  | next s' h' ha hl hx ih =>
    intro T₂ T₁ g s h hT
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx, ha, hl⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      exact ih hT.2

/-! ## The store -/

/-- `NCH-24`'s store test on one labelled partial, by message `m`, input `k`, signer `s` and commitment `cid`, with
label `h`: "the rung is found by txid; the user-signature hash matches; the input and signer are in range". The signer
is one of the receiver's keys, and a resident candidate with this commitment id has a first rung with this message at
this input, the input in that rung's range, and, if the candidate is Escape-role, the label is that rung's hash. A
candidate that is not Escape-role is not compared. -/
@[req "NCH-24"]
def storable (keys : List Nat) (n : Node) (m : Sighash) (k s cid : Nat) (h : Option Nat) : Bool :=
  keys.contains s && n.cands.any fun c => c.id == cid &&
    match rungOf c m k with
    | none => false
    | some g => decide (k < g.tx.inputs.length) && (!c.isEscape || h == some g.userSig)

theorem storable_iff {keys : List Nat} {n : Node} {m : Sighash} {k s cid : Nat} {h : Option Nat} :
    storable keys n m k s cid h = true ↔ s ∈ keys ∧ ∃ c ∈ n.cands, c.id = cid ∧ ∃ g, rungOf c m k = some g ∧
      k < g.tx.inputs.length ∧ (c.isEscape = true → h = some g.userSig) := by
  unfold storable
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hs, c, hc, hid, hr⟩
    refine ⟨hs, c, hc, hid, ?_⟩
    cases hg : rungOf c m k with
    | none => rw [hg] at hr; cases hr
    | some g =>
      rw [hg] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hr
      refine ⟨g, rfl, hr.1, fun he => ?_⟩
      rcases hr.2 with h' | h'
      · rw [h'] at he; cases he
      · exact h'
  · rintro ⟨hs, c, hc, hid, g, hg, hk, he⟩
    refine ⟨hs, c, hc, hid, ?_⟩
    rw [hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    refine ⟨hk, ?_⟩
    cases hce : c.isEscape
    · exact .inl rfl
    · exact .inr (he hce)

/-- The store test here is stricter than `RungIngress.storable`. -/
@[req "NCH-24"]
theorem storable_sub {keys : List Nat} {n : Node} {m : Sighash} {k s cid : Nat} {h : Option Nat}
    (hs : storable keys n m k s cid h = true) : RungIngress.storable n m k cid = true := by
  obtain ⟨-, c, hc, hid, g, hg, hk, -⟩ := storable_iff.1 hs
  obtain ⟨hgm, hm⟩ := rungOf_some hg
  unfold RungIngress.storable
  refine List.any_eq_true.2 ⟨c, hc, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq]
  exact ⟨hid, g, hgm, hm, hk⟩

/-- One node's labelled history, in `Kernel.History`'s form with each frame's label. -/
abbrev LHistory := List (World × Env × Event × Option Nat)

/-- One node's own labelled history out of a labelled composed one, as `Federation.project`. -/
def lproject (i : Nat) : LTrace → LHistory
  | [] => []
  | (f, s, h) :: T =>
    match Federation.actor s with
    | some (j, env, e) => if j = i then (f.worlds i, env, e, h) :: lproject i T else lproject i T
    | none => lproject i T

/-- A labelled frame without its label. -/
def unlabel (a : World × Env × Event × Option Nat) : World × Env × Event := (a.1, a.2.1, a.2.2.1)

/-- The labelled projection without its labels is the projection of the forgotten history. -/
theorem lproject_forget (i : Nat) : ∀ T : LTrace, (lproject i T).map unlabel = Federation.project i (forget T)
  | [] => rfl
  | (f, s, h) :: T => by
    show (lproject i ((f, s, h) :: T)).map unlabel = Federation.project i ((f, s) :: forget T)
    cases hs : Federation.actor s with
    | none => simp only [lproject, Federation.project, hs]; exact lproject_forget i T
    | some a =>
      obtain ⟨j, env, e⟩ := a
      simp only [lproject, Federation.project, hs]
      split
      · simp only [List.map_cons, lproject_forget i T]; rfl
      · exact lproject_forget i T

theorem lproject_mem {i : Nat} : ∀ {T : LTrace} {a : World × Env × Event × Option Nat}, a ∈ lproject i T →
    ∃ T₁ T₂ g s, T = T₂ ++ (g, s, a.2.2.2) :: T₁ ∧ Federation.actor s = some (i, a.2.1, a.2.2.1) ∧
      a.1 = g.worlds i
  | [], _, hm => by cases hm
  | (g, s, lab) :: T, a, hm => by
    have tail (hm : a ∈ lproject i T) : ∃ T₁ T₂ g' s', (g, s, lab) :: T = T₂ ++ (g', s', a.2.2.2) :: T₁ ∧
        Federation.actor s' = some (i, a.2.1, a.2.2.1) ∧ a.1 = g'.worlds i := by
      obtain ⟨T₁, T₂, g', s', rfl, h1, h2⟩ := lproject_mem hm
      exact ⟨T₁, (g, s, lab) :: T₂, g', s', rfl, h1, h2⟩
    cases hs : Federation.actor s with
    | none => simp only [lproject, hs] at hm; exact tail hm
    | some y =>
      obtain ⟨j, env, e⟩ := y
      simp only [lproject, hs] at hm
      by_cases hj : j = i
      · subst hj
        simp only [if_true] at hm
        rcases List.mem_cons.1 hm with rfl | hm
        · exact ⟨T, [], g, s, rfl, hs, rfl⟩
        · exact tail hm
      · simp only [hj, if_false] at hm
        exact tail hm

/-- One labelled frame's delivery, with its commitment id, if this store test passed when it arrived. -/
def arrival (keys : List Nat) (a : World × Env × Event × Option Nat) : List (Nat × Authority.Sig) :=
  match a.2.2.1 with
  | .receivePartial m k s cid =>
    if storable keys a.1.node m k s cid a.2.2.2 then [(cid, { msg := m, input := k, signer := s })] else []
  | _ => []

/-- The records `K`, then each new record not already among them. -/
def addNew (K new : List (Nat × Authority.Sig)) : List (Nat × Authority.Sig) := K ++ new.filter fun p => !K.contains p

/-- `RungIngress.kept` with this store test, the partials the store took over the history, kept while their
commitment's candidate stays resident; a record already kept is not added again. `NCH-25`: "A duplicate is an
idempotent `ACCEPTED` and never displaces the first." -/
@[req "NCH-25"]
def kept (keys : List Nat) : LHistory → Node → List (Nat × Authority.Sig)
  | [], _ => []
  | a :: h, n => (addNew (kept keys h a.1.node) (arrival keys a)).filter fun p => n.cands.any (·.id == p.1)

/-- Node `i`'s possession over the ladder at the end of a labelled composed trace: its own signatures and the
partials this store kept. -/
@[req "DUR-28"]
def held (keys : List Nat) (i : Nat) (T : LTrace) (f : Fed) : List Authority.Sig :=
  RungIngress.ownSigs (f.worlds i).node ++ (kept keys (lproject i T) (f.worlds i).node).map Prod.snd

theorem mem_kept {keys : List Nat} : ∀ {h : LHistory} {n : Node} {p : Nat × Authority.Sig}, p ∈ kept keys h n →
    ∃ a ∈ h, a.2.2.1 = .receivePartial p.2.msg p.2.input p.2.signer p.1 ∧
      storable keys a.1.node p.2.msg p.2.input p.2.signer p.1 a.2.2.2 = true
  | [], _, _, hp => by cases hp
  | a :: h, n, p, hp => by
    simp only [kept, addNew, List.mem_filter, List.mem_append] at hp
    rcases hp.1 with hp | hp
    · obtain ⟨b, hb, he⟩ := mem_kept hp
      exact ⟨b, List.mem_cons_of_mem a hb, he⟩
    · refine ⟨a, List.mem_cons_self, ?_⟩
      have hp := hp.1
      obtain ⟨w, env, e, lab⟩ := a
      cases e with
      | receivePartial m k s cid =>
        simp only [arrival] at hp
        split at hp
        · rename_i hs
          simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨rfl, hs⟩
        · cases hp
      | _ => simp [arrival] at hp

theorem kept_resident {keys : List Nat} : ∀ {h : LHistory} {n : Node} {p : Nat × Authority.Sig},
    p ∈ kept keys h n → n.cands.any (·.id == p.1) = true
  | [], _, _, hp => by cases hp
  | _ :: _, _, _, hp => (List.mem_filter.1 hp).2

theorem kept_sub {keys : List Nat} : ∀ {h : LHistory} {n : Node} {p : Nat × Authority.Sig},
    p ∈ kept keys h n → p ∈ RungIngress.kept (h.map unlabel) n
  | [], _, _, hp => by cases hp
  | a :: h, n, p, hp => by
    simp only [kept, addNew, RungIngress.kept, List.map_cons, List.mem_filter, List.mem_append] at hp ⊢
    refine ⟨?_, hp.2⟩
    rcases hp.1 with hp | hp
    · exact .inl (kept_sub hp)
    · right
      have hp := hp.1
      obtain ⟨w, env, e, lab⟩ := a
      cases e with
      | receivePartial m k s cid =>
        simp only [arrival, unlabel, RungIngress.arrival] at hp ⊢
        split at hp
        · rename_i hs
          rw [if_pos (storable_sub hs)]
          exact hp
        · cases hp
      | _ => simp [arrival] at hp

/-- **The new store is stricter.** Possession under this store is contained in `RungIngress.held`. -/
@[req "DUR-28"]
theorem held_sub {keys : List Nat} {i : Nat} {T : LTrace} {f : Fed} {x : Authority.Sig}
    (h : x ∈ held keys i T f) : x ∈ RungIngress.held i (forget T) f := by
  unfold RungIngress.held RungIngress.received
  rcases List.mem_append.1 h with h | h
  · exact List.mem_append.2 (.inl h)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    refine List.mem_append.2 (.inr (List.mem_map.2 ⟨p, ?_, rfl⟩))
    rw [← lproject_forget]
    exact kept_sub hp

/-- **Possession comes from delivery.** Each signature an honest node holds under this store is its own or a partial
of the inventory, with the same message, input and signer. -/
@[req "DUR-28"]
theorem held_origin {keys : List Nat} {r : Rules} {honest : List Nat} {T : LTrace} {f : Fed}
    (hx : Execution r honest T f) {i : Nat} (hi : i ∈ honest) {x : Authority.Sig} (hm : x ∈ held keys i T f) :
    x.signer = i ∨ ∃ y ∈ f.parts, Authority.sig y = x :=
  RungIngress.held_origin (to_fed hx) hi (held_sub hm)

/-- Whose frame a step is, when it is a partial's arrival: an admitted step whose event is `receivePartial` is a
delivery of a partial with those components. -/
theorem receive_step {honest : List Nat} {g : Fed} {s : Federation.Step} {i : Nat} {env : Env} {m : Sighash}
    {k sg cid : Nat} (ha : Federation.admits honest g s = true)
    (hs : Federation.actor s = some (i, env, .receivePartial m k sg cid)) :
    ∃ x : Exp, s = .deliverPartial i env x ∧ x.msg = m ∧ x.input = k ∧ x.signer = sg ∧ x.cid = cid := by
  cases s
  case process j env' e =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs
    simp [Federation.admits, Federation.ownEvent] at ha
  case deliverPartial j env' x =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq, Event.receivePartial.injEq] at hs
    obtain ⟨rfl, rfl, h1, h2, h3, h4⟩ := hs
    exact ⟨x, rfl, h1, h2, h3, h4⟩
  all_goals simp [Federation.actor] at hs

/-- **Every kept record was checked.** A record kept over node `i`'s labelled history came from a delivery step of
the trace, of a partial with the record's message, input, signer and commitment, whose store test passed in that
step's world with that step's label, and whose label was an envelope an honest node had sent with that partial, or
its signer was extracted, at that step. -/
@[req "NCH-24"]
theorem stored_checked {keys : List Nat} {r : Rules} {honest : List Nat} {T : LTrace} {f : Fed}
    (hx : Execution r honest T f) {i : Nat} {n : Node} {p : Nat × Authority.Sig}
    (hp : p ∈ kept keys (lproject i T) n) :
    ∃ T₁ T₂ g env x h, T = T₂ ++ (g, .deliverPartial i env x, h) :: T₁ ∧
      x.msg = p.2.msg ∧ x.input = p.2.input ∧ x.signer = p.2.signer ∧ x.cid = p.1 ∧
      Execution r honest T₁ g ∧
      storable keys (g.worlds i).node x.msg x.input x.signer x.cid h = true ∧
      ((x, h) ∈ envelopes r (forget T₁) ∨ x.signer ∈ g.extracted) := by
  obtain ⟨a, ha, he, hs⟩ := mem_kept hp
  obtain ⟨T₁, T₂, g, s, hT, hact, hw⟩ := lproject_mem ha
  obtain ⟨hx₁, had, hl⟩ := prefix_exec hx hT
  rw [he] at hact
  obtain ⟨x, rfl, h1, h2, h3, h4⟩ := receive_step had hact
  rw [hw] at hs
  simp only [labelOk, Bool.or_eq_true, List.contains_iff_mem] at hl
  refine ⟨T₁, T₂, g, a.2.1, x, a.2.2.2, hT, h1, h2, h3, h4, hx₁, ?_, hl⟩
  rw [h1, h2, h3, h4]
  exact hs

/-- **The stored partial binds the variant** (`NCH-24`'s "the user-signature hash matches"). A record kept by node `i`
at the end of a labelled execution, from a signer not extracted at the end, came from a delivery step whose label is
an envelope: an honest node, the partial's signer, sent that partial at an earlier step of its own, with the hash of
its own retained variant in that step's world as the label. At arrival, the store test passed at node `i`: a resident
candidate with the commitment id has a first rung `rg` with the partial's message at its input, in range; if that
candidate is Escape-role, the label is `rg`'s hash, and the sender's retained candidate under the same commitment id
had a rung with the same message at that input and that same hash. -/
@[req "NCH-24"]
theorem stored_binds {keys : List Nat} {r : Rules} {honest : List Nat} {T : LTrace} {f : Fed}
    (hx : Execution r honest T f) {i : Nat} {p : Nat × Authority.Sig}
    (hp : p ∈ kept keys (lproject i T) (f.worlds i).node) (hs : p.2.signer ∉ f.extracted) :
    ∃ T₁ T₂ g env x h gs env' e', T = T₂ ++ (g, .deliverPartial i env x, h) :: T₁ ∧
      x.msg = p.2.msg ∧ x.input = p.2.input ∧ x.signer = p.2.signer ∧ x.cid = p.1 ∧
      (x, h) ∈ envelopes r (forget T₁) ∧ x.signer ∈ honest ∧
      (gs, Federation.Step.process x.signer env' e') ∈ forget T₁ ∧
      x ∈ fanout (gs.worlds x.signer) (step r env' (gs.worlds x.signer) e').2 ∧
      h = variantOf (gs.worlds x.signer).node x.msg x.input x.cid ∧
      ∃ c ∈ (g.worlds i).node.cands, c.id = x.cid ∧ ∃ rg, rungOf c x.msg x.input = some rg ∧
        x.input < rg.tx.inputs.length ∧
        (c.isEscape = true → h = some rg.userSig ∧
          ∃ c' ∈ (gs.worlds x.signer).node.cands, c'.id = x.cid ∧
            ∃ rg' ∈ c'.ladder, x.msg = sighash rg'.tx x.input ∧ rg'.userSig = rg.userSig) := by
  obtain ⟨T₁, T₂, g, env, x, h, hT, h1, h2, h3, h4, hx₁, hst, hl⟩ := stored_checked hx hp
  have henv : (x, h) ∈ envelopes r (forget T₁) := by
    rcases hl with hl | hl
    · exact hl
    · have hg : (g, Federation.Step.deliverPartial i env x) ∈ forget T := by
        rw [hT, forget_append]
        exact List.mem_append_right _ List.mem_cons_self
      rw [h3] at hl
      exact absurd ((Federation.persists (to_fed hx) hg).2 _ hl) hs
  obtain ⟨hhon, gs, env', e', hgs, hfan, hv⟩ := envelope_sender (to_fed hx₁) henv
  obtain ⟨-, c, hc, hid, rg, hrg, hk, hesc⟩ := storable_iff.1 hst
  refine ⟨T₁, T₂, g, env, x, h, gs, env', e', hT, h1, h2, h3, h4, henv, hhon, hgs, hfan, hv, c, hc, hid, rg, hrg, hk,
    fun he => ⟨hesc he, ?_⟩⟩
  have hv' : variantOf (gs.worlds x.signer).node x.msg x.input x.cid = some rg.userSig := by
    rw [← hv]; exact hesc he
  exact variantOf_some hv'

/-! ## A refused or a duplicate delivery -/

/-- A refused arrival adds nothing: the records kept after it are those kept before, filtered by residency. -/
@[req "NCH-24"]
theorem kept_refused {keys : List Nat} {w : World} {env : Env} {m : Sighash} {k s cid : Nat} {h : Option Nat}
    {lh : LHistory} {n : Node} (hs : storable keys w.node m k s cid h = false) :
    kept keys ((w, env, .receivePartial m k s cid, h) :: lh) n =
      (kept keys lh w.node).filter fun p => n.cands.any (·.id == p.1) := by
  simp [kept, addNew, arrival, hs]

/-- A duplicate arrival adds nothing: when every record it brings is already kept, the records kept after it are
those kept before, filtered by residency, the first record unchanged (`NCH-25`). -/
@[req "NCH-25"]
theorem kept_duplicate {keys : List Nat} {a : World × Env × Event × Option Nat} {lh : LHistory} {n : Node}
    (hd : ∀ q ∈ arrival keys a, q ∈ kept keys lh a.1.node) :
    kept keys (a :: lh) n = (kept keys lh a.1.node).filter fun p => n.cands.any (·.id == p.1) := by
  have he : (arrival keys a).filter (fun p => !(kept keys lh a.1.node).contains p) = [] :=
    List.filter_eq_nil_iff.2 (fun q hq => by simpa using hd q hq)
  simp only [kept, addNew]
  rw [he, List.append_nil]

theorem ownSigs_receive (n : Node) (m : Sighash) (k s cid : Nat) :
    RungIngress.ownSigs (Kernel.receivePartial n m k s cid) = RungIngress.ownSigs n := by
  unfold RungIngress.ownSigs Kernel.receivePartial
  rw [List.flatMap_map]
  apply RungIngress.flatMap_congr
  intro c _
  split <;> rfl

theorem resident_receive (n : Node) (m : Sighash) (k s cid q : Nat) :
    (Kernel.receivePartial n m k s cid).cands.any (·.id == q) = n.cands.any (·.id == q) := by
  unfold Kernel.receivePartial
  rw [List.any_map]
  apply RungIngress.any_congr
  intro c _
  simp only [Function.comp]
  split <;> rfl

/-- A delivery to node `i` whose arrival adds no record not already kept leaves node `i`'s possession as it was. -/
theorem held_deliver {keys : List Nat} {r : Rules} {f : Fed} {i : Nat} {env : Env} {x : Exp} {h : Option Nat}
    {T : LTrace}
    (hd : ∀ q ∈ arrival keys (f.worlds i, env, .receivePartial x.msg x.input x.signer x.cid, h),
      q ∈ kept keys (lproject i T) (f.worlds i).node) :
    held keys i ((f, .deliverPartial i env x, h) :: T) (Federation.apply r f (.deliverPartial i env x)) =
      held keys i T f := by
  have hw : (Federation.apply r f (.deliverPartial i env x)).worlds i =
      (step r env (f.worlds i) (.receivePartial x.msg x.input x.signer x.cid)).1 := by
    rw [Federation.apply_of_actor r f _ rfl i, if_pos rfl]
  have hp : lproject i ((f, .deliverPartial i env x, h) :: T) =
      (f.worlds i, env, .receivePartial x.msg x.input x.signer x.cid, h) :: lproject i T := by
    simp [lproject, Federation.actor]
  unfold held
  rw [hp, hw, kept_duplicate hd]
  simp only [step, ownSigs_receive]
  congr 2
  apply List.filter_eq_self.2
  intro q hq
  rw [resident_receive]
  exact kept_resident hq

/-- **A refused envelope adds nothing.** A delivery whose store test fails at the receiver, for instance on a label
that is not the receiver's retained hash, leaves the receiver's possession exactly as it was: no new record and no
new quorum contributor, and nothing it held, its own signatures or an earlier record still resident, is removed. -/
@[req "NCH-24"]
theorem refused_adds_nothing {keys : List Nat} {r : Rules} {f : Fed} {i : Nat} {env : Env} {x : Exp}
    {h : Option Nat} {T : LTrace}
    (hs : storable keys (f.worlds i).node x.msg x.input x.signer x.cid h = false) :
    held keys i ((f, .deliverPartial i env x, h) :: T) (Federation.apply r f (.deliverPartial i env x)) =
      held keys i T f :=
  held_deliver (fun q hq => by simp [arrival, hs] at hq)

/-- **A duplicate is idempotent** (`NCH-25`). A delivery of a partial whose record node `i` already keeps leaves its
possession exactly as it was, the first record unchanged, so no distinct-signer count rises. -/
@[req "NCH-25"]
theorem duplicate_keeps {keys : List Nat} {r : Rules} {f : Fed} {i : Nat} {env : Env} {x : Exp}
    {h : Option Nat} {T : LTrace}
    (hk : (x.cid, ({ msg := x.msg, input := x.input, signer := x.signer } : Authority.Sig)) ∈
      kept keys (lproject i T) (f.worlds i).node) :
    held keys i ((f, .deliverPartial i env x, h) :: T) (Federation.apply r f (.deliverPartial i env x)) =
      held keys i T f := by
  refine held_deliver (fun q hq => ?_)
  simp only [arrival] at hq
  split at hq
  · simp only [List.mem_singleton] at hq
    subst hq
    exact hk
  · cases hq

/-- A delivery leaves the partial inventory as it was. -/
theorem deliver_parts (r : Rules) (f : Fed) (i : Nat) (env : Env) (x : Exp) :
    (Federation.apply r f (.deliverPartial i env x)).parts = f.parts := rfl

/-- **Exposure survives a refused store.** Whatever the inventory held at any state of a labelled execution, the final
state holds: a delivery removes nothing from it (`VariantReceipt.deliver_parts`), and the inventory only grows
(`Federation.parts_grows`), so an envelope a store refuses keeps the exposed partial in the world-level account. -/
@[req "POL-18"]
theorem exposure_kept {r : Rules} {honest : List Nat} {T : LTrace} {f : Fed} (hx : Execution r honest T f)
    {g : Fed} {s : Federation.Step} {h : Option Nat} (hg : (g, s, h) ∈ T) {y : Exp} (hy : y ∈ g.parts) :
    y ∈ f.parts :=
  (Federation.persists (to_fed hx) (List.mem_map.2 ⟨(g, s, h), hg, rfl⟩)).1 y hy

end BtcPolicy.VariantReceipt
