import BtcPolicy.Ingress
/-! Checked ingress that registers the Escape's ladder, and a node's possession over that ladder. Beside
`BtcPolicy.Ingress`, whose `Ingress.check` hands `Kernel.accept` an Escape with no rung above its base
(`Ingress.resident_no_rungs`), so that on a checked run no ladder pass queues a partial. `Ingress.check`,
`Ingress.CheckedTrace` and their results keep their statements; the results here are new theorems beside them.

**The request.** `RungIngress.Request` is `Ingress.Request` with the Escape and each rung carrying the
user-signature hash `CHN-29` gives each candidate variant (`RungIngress.Signed`). The hash is `WIR-23`'s digest
over the user's signatures, which the decoded members do not carry: it is supplied with the member, symbolic as
`Ingress.Ctx.txId` is, and never checked here (`CHN-12`'s verdict stays `Ingress.Member.upstream`).
`RungIngress.Request.plain` drops the hashes.

**The check.** `RungIngress.check` is `Ingress.check` on the plain request, and on acceptance it writes the
Escape's ladder into the candidate: each rung's transaction (`Ingress.tx`) with its hash, in the request's
order, and the base's hash (`RungIngress.withLadder`). No second evaluator is written: every verdict but the
acceptance is `Ingress.check`'s (`RungIngress.check_other`), the spend is `Ingress.check`'s, and dropping the
ladder from an accepted Escape gives `Ingress.check`'s (`RungIngress.check_strip`); a request with no rung and
the base hash 0 is checked exactly as before (`RungIngress.check_ofPlain`). Every rung of an accepted Escape
passed gate 25 (`SPN-27`) and is an escape-class transaction of an admissible member
(`RungIngress.accepted_rungs`). On a repeat, `Kernel.accept`'s registration compares a resident Escape's ordered rung txids with the request's
(`Kernel.pairAdmits`, `SPN-32`) and refuses a repeat whose ladder differs; a birth keeps the incoming ladder
(`Kernel.born`).

**Over a federation.** `RungIngress.CheckedTrace` is `Ingress.CheckedTrace` with this check. On such a run every
honest node's resident candidates are classed and every rung they retain is escape-class
(`RungIngress.resident_classed`); with a collision-free transaction identity `Federation.HotBinding` follows for
a hot target (`RungIngress.hot_binding`), now through `Ingress.queued_cand`'s rung alternative, and
`RungIngress.no_exposed_quorum` is `Federation.no_exposed_quorum` with those premises in place of the binding.

**Possession over the ladder.** `Federation.ownSigs` and `Federation.storable` read each candidate's base alone,
so a delivered rung partial is not stored there. `RungIngress.ownSigs` is `SPN-32`'s "sign the spend, the Escape
and every rung at ingress" over every rung a resident candidate retains (`Kernel.Cand.ladder`), and
`RungIngress.storable` keeps `Federation.storable`'s part of the store test, `NCH-24`'s "the rung is found by txid"
with the input's range, over that ladder; `RungIngress.held` is `Federation.held` with these two. It contains `Federation.held`
(`RungIngress.held_sub`), equals it where no candidate retains a rung (`RungIngress.held_bare`), so on every run
checked by `Ingress.check` (`RungIngress.held_plain`), and every signature in it is the node's own or a partial
of the inventory (`RungIngress.held_origin`). A rung's count reads only the records on its own transaction
(`Ladder.quorum_own_rung`).

**Not modelled here.** Of `NCH-24`'s test, the signer's range and the candidate's expiry, as in
`Federation.storable`, and "the user-signature hash matches": a partial row (`Kernel.Exp`) carries no
user-signature hash, so the store test here does not compare one, and two nodes retaining one rung txid under
different hashes store each other's partials on it. So the store test here accepts more than `NCH-24`'s, never
less: a node may hold, assemble and send a rung on a partial the protocol drops
(`Exhibits.RungAssembly.hash_mismatch_sent`). That comparison is `Ladder.stores`', on `Ladder`'s own run.
`CHN-14`–`CHN-16`'s relations between the rungs are not checked, as in `BtcPolicy.Ingress`; `BtcPolicy.LadderShape`
checks `CHN-16`'s beside this check. -/

namespace BtcPolicy.RungIngress
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Ingress (Ctx Member Verdict tx classOf admissible escapeFault Classed checkClawback)
open BtcPolicy.Federation (Fed)

/-! ## The request and the check -/

/-- A decoded member with the user-signature hash of its variant (`CHN-29`), supplied with it. -/
structure Signed where
  member : Member
  userSig : Nat
  deriving DecidableEq, Repr

/-- A SpendRequest from gate 17 on, as `Ingress.Request`, with the Escape and each rung signed. -/
structure Request where
  spend : Member
  escape : Signed
  rungs : List Signed := []
  expiry : Nat
  fireAt : Option Wall
  deriving DecidableEq, Repr

/-- The request without its user-signature hashes. -/
def Request.plain (q : Request) : Ingress.Request :=
  { spend := q.spend, escape := q.escape.member, rungs := q.rungs.map (·.member), expiry := q.expiry,
    fireAt := q.fireAt }

/-- A plain request with the base hash 0 and every rung's hash 0. -/
def Request.ofPlain (q : Ingress.Request) : Request :=
  { spend := q.spend, escape := ⟨q.escape, 0⟩, rungs := q.rungs.map (⟨·, 0⟩), expiry := q.expiry,
    fireAt := q.fireAt }

/-- One rung as the node retains it (`SPN-36`): its transaction and its user-signature hash. -/
@[req "SPN-36"]
def rung (ctx : Ctx) (s : Signed) : Rung := { tx := tx ctx s.member, userSig := s.userSig }

/-- The Escape's candidate with the request's ladder written in: the rungs in the request's order and the
base's hash. -/
def withLadder (ctx : Ctx) (q : Request) (es : Cand) : Cand :=
  { es with above := q.rungs.map (rung ctx), baseSig := q.escape.userSig }

/-- `Ingress.check` on the plain request; on acceptance the Escape carries its ladder. -/
@[req "SPN-32"]
def check (ctx : Ctx) (fits : Bool) (q : Request) : Verdict :=
  match Ingress.check ctx fits q.plain with
  | .accepted sp es => .accepted sp (withLadder ctx q es)
  | v => v

theorem check_accepted {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand} :
    check ctx fits q = .accepted sp es ↔
      ∃ es₀, Ingress.check ctx fits q.plain = .accepted sp es₀ ∧ es = withLadder ctx q es₀ := by
  unfold check
  cases hc : Ingress.check ctx fits q.plain with
  | accepted sp' es' =>
    simp only [Verdict.accepted.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨es', ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  | _ => simp

/-- Every verdict but the acceptance is `Ingress.check`'s. -/
theorem check_other {ctx : Ctx} {fits : Bool} {q : Request}
    (h : ∀ sp es, Ingress.check ctx fits q.plain ≠ .accepted sp es) :
    check ctx fits q = Ingress.check ctx fits q.plain := by
  unfold check
  cases hc : Ingress.check ctx fits q.plain with
  | accepted sp es => exact absurd hc (h sp es)
  | _ => rfl

/-- What an acceptance carries: `Ingress.check` accepted the plain request with the same spend, the Escape is
that check's candidate with the ladder written in, and every rung is admissible and passed gate 25. -/
@[req "SPN-27"]
theorem accepted_validates {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    Ingress.check ctx fits q.plain = .accepted sp (Ingress.cand ctx q.plain q.escape.member false none) ∧
      es = withLadder ctx q (Ingress.cand ctx q.plain q.escape.member false none) ∧
      q.rungs.length ≤ 3 ∧
      ∀ s ∈ q.rungs, admissible ctx q.plain s.member = true ∧ escapeFault ctx s.member = none := by
  obtain ⟨es₀, hc, rfl⟩ := check_accepted.1 h
  obtain ⟨-, -, hl, ha, -, -, he, -, -, hes⟩ := Ingress.accepted_validates hc
  subst hes
  refine ⟨hc, rfl, by simpa [Request.plain] using hl, fun s hs => ?_⟩
  have hm : s.member ∈ q.plain.rungs := List.mem_map.2 ⟨s, hs, rfl⟩
  exact ⟨ha _ hm, he _ hm⟩

/-- Dropping the ladder from an accepted Escape gives `Ingress.check`'s acceptance of the plain request. -/
theorem check_strip {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    Ingress.check ctx fits q.plain = .accepted sp { es with above := [], baseSig := 0 } := by
  obtain ⟨hc, rfl, -, -⟩ := accepted_validates h
  exact hc

/-- A request with no rung and the base hash 0 is checked exactly as `Ingress.check` checks it. -/
theorem check_ofPlain (ctx : Ctx) (fits : Bool) (q : Ingress.Request) (h : q.rungs = []) :
    check ctx fits (Request.ofPlain q) = Ingress.check ctx fits q := by
  have hp : (Request.ofPlain q).plain = q := by
    cases q; simp_all [Request.ofPlain, Request.plain]
  by_cases ha : ∃ sp es, Ingress.check ctx fits q = .accepted sp es
  · obtain ⟨sp, es, hc⟩ := ha
    have hc' : Ingress.check ctx fits (Request.ofPlain q).plain = .accepted sp es := by rw [hp]; exact hc
    obtain ⟨-, -, -, -, -, -, -, -, -, hes⟩ := Ingress.accepted_validates hc'
    have hw : withLadder ctx (Request.ofPlain q) es = es := by
      subst hes; simp [withLadder, Request.ofPlain, h, Ingress.cand]
    rw [check_accepted.2 ⟨es, hc', hw.symm⟩, hc]
  · rw [check_other (fun sp es he => ha ⟨sp, es, by rw [← hp]; exact he⟩), hp]

/-- A member that passed gate 25 is escape-class. -/
theorem escape_class {ctx : Ctx} {m : Member} (he : escapeFault ctx m = none) :
    classOf ctx m = some .escape := by
  unfold escapeFault at he
  obtain ⟨-, he⟩ := Ingress.orElse_none he
  obtain ⟨-, he⟩ := Ingress.orElse_none he
  obtain ⟨hc, -⟩ := Ingress.orElse_none he
  generalize classOf ctx m = k at hc ⊢
  rcases k with _ | ⟨_ | _ | _⟩ <;> simp_all

/-- Every rung a candidate retains is the transaction of an admissible escape-class member. -/
def RungsClassed (ctx : Ctx) (c : Cand) : Prop :=
  ∀ g ∈ c.above, ∃ m : Member, m.frame.WF ∧ g.tx = tx ctx m ∧ classOf ctx m = some .escape

/-- The ladder an acceptance registers: the Escape's rungs are the request's, in its order, each the
transaction of an admissible escape-class member, and the spend retains none. -/
@[req "SPN-32"]
theorem accepted_rungs {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    es.above = q.rungs.map (rung ctx) ∧ es.baseSig = q.escape.userSig ∧ sp.above = [] ∧
      RungsClassed ctx sp ∧ RungsClassed ctx es := by
  obtain ⟨hc, rfl, -, hr⟩ := accepted_validates h
  obtain ⟨-, -, -, -, -, -, -, -, hsp, -⟩ := Ingress.accepted_validates hc
  subst hsp
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro g hg
    simp [Ingress.cand] at hg
  intro g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨ha, he⟩ := hr s hs
  exact ⟨s.member, Ingress.frame_wf ha, rfl, escape_class he⟩

theorem accepted_classed {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) :
    (Classed ctx sp ∧ RungsClassed ctx sp) ∧ Classed ctx es ∧ RungsClassed ctx es := by
  obtain ⟨hc, rfl, -, -⟩ := accepted_validates h
  obtain ⟨-, -, -, hrs, hre⟩ := accepted_rungs h
  obtain ⟨csp, ces⟩ := Ingress.accepted_classed hc
  exact ⟨⟨csp, hrs⟩, ces, hre⟩

/-! ## Over a federation -/

/-- `Ingress.CheckedTrace` with this check: every honest acceptance is the event this check produced for some
request, and every claw-back `Ingress.checkClawback`'s candidate. -/
def CheckedTrace (ctx : Ctx) (t : Federation.Trace) : Prop :=
  (∀ y ∈ t, ∀ i env cid d E sp es, y.2 = .process i env (.accept cid d E sp es) →
    ∃ q, check ctx true q = .accepted sp es) ∧
  ∀ y ∈ t, ∀ i env c, y.2 = .process i env (.clawback c) →
    ∃ q, checkClawback ctx Classification.current q = some c

/-- A fixture's trace is checked when each acceptance is some request's verdict and each claw-back some
ClawbackRequest's candidate. -/
theorem checkedTrace_of (ctx : Ctx) (t : Federation.Trace) (qs : List Request)
    (qcs : List Ingress.ClawbackRequest)
    (h : (Ingress.acceptPairs t).all (fun p => qs.any fun q => check ctx true q == .accepted p.1 p.2) = true)
    (hcl : (Ingress.clawCands t).all
      (fun c => qcs.any fun q => checkClawback ctx Classification.current q == some c) = true) :
    CheckedTrace ctx t := by
  refine ⟨fun y hy i env cid d E sp es hs => ?_, fun y hy i env c hs => ?_⟩
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ (Ingress.mem_acceptPairs hy hs))
    exact ⟨q, by simpa using hq⟩
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcl _ (Ingress.mem_clawCands hy hs))
    exact ⟨q, by simpa using hq⟩

/-- One step keeps every resident candidate classed with classed rungs, when the step's acceptance and
claw-back are checked. -/
theorem step_classed (r : Rules) (env : Env) (w : World) (e : Event) {ctx : Ctx}
    (hw : ∀ c ∈ w.node.cands, Classed ctx c ∧ RungsClassed ctx c)
    (hacc : ∀ cid d E sp es, e = .accept cid d E sp es → ∃ q, check ctx true q = .accepted sp es)
    (hcl : ∀ x, e = .clawback x → ∃ q, checkClawback ctx Classification.current q = some x)
    {c : Cand} (hc : c ∈ (step r env w e).1.node.cands) : Classed ctx c ∧ RungsClassed ctx c := by
  refine ⟨?_, ?_⟩
  · rcases Federation.cand_origin r env w e hc with
      ⟨d, hd, dh, dt, -⟩ | ⟨cid, dd, E, sp, es, rfl, -, hse⟩ | ⟨x, rfl, -, hxt, hxh⟩
    · obtain ⟨m, hm, htx, hcl'⟩ := (hw d hd).1
      exact ⟨m, hm, dt ▸ htx, dh ▸ hcl'⟩
    · obtain ⟨q, hq⟩ := hacc cid dd E sp es rfl
      obtain ⟨⟨csp, -⟩, ces, -⟩ := accepted_classed hq
      rcases hse with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · obtain ⟨m, hm, htx, hcl'⟩ := csp
        exact ⟨m, hm, ht ▸ htx, hh ▸ hcl'⟩
      · obtain ⟨m, hm, htx, hcl'⟩ := ces
        exact ⟨m, hm, ht ▸ htx, hh ▸ hcl'⟩
    · obtain ⟨q, hq⟩ := hcl x rfl
      obtain ⟨hm, htx, -, hcl'⟩ := Ingress.checkClawback_classed hq
      exact ⟨q.member, hm, hxt.trans htx, by rw [hxh]; exact hcl'⟩
  · intro g hg
    rcases Ingress.cand_above_origin r env w e hc with
      ⟨d, hd, hda⟩ | ⟨cid, dd, E, sp, es, rfl, hse⟩ | ⟨x, rfl, hxa⟩
    · exact (hw d hd).2 g (hda ▸ hg)
    · obtain ⟨q, hq⟩ := hacc cid dd E sp es rfl
      obtain ⟨⟨-, hrs⟩, -, hre⟩ := accepted_classed hq
      rcases hse with h | h
      · exact hrs g (h ▸ hg)
      · exact hre g (h ▸ hg)
    · obtain ⟨q, hq⟩ := hcl x rfl
      rw [hxa, Ingress.checkClawback_above hq] at hg
      cases hg

/-- Every candidate resident at an honest node, at every state of an execution checked by this ingress, is
classed, and every rung it retains is the transaction of an admissible escape-class member. -/
theorem resident_classed {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t) :
    (∀ i ∈ honest, ∀ c ∈ (f.worlds i).node.cands, Classed ctx c ∧ RungsClassed ctx c) ∧
    ∀ y ∈ t, ∀ i ∈ honest, ∀ c ∈ (y.1.worlds i).node.cands, Classed ctx c ∧ RungsClassed ctx c := by
  induction hx with
  | init f h =>
    refine ⟨fun i hi c hc => ?_, fun y hy => by cases hy⟩
    rw [(h.2.2 i hi).2.2.2.1] at hc; cases hc
  | @next t f s ha hx ih =>
    have hct : CheckedTrace ctx t :=
      ⟨fun y hy => hc.1 y (List.mem_cons_of_mem _ hy), fun y hy => hc.2 y (List.mem_cons_of_mem _ hy)⟩
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
          refine step_classed r env (f.worlds j) e (now j hi) (fun cid d E sp es he => ?_)
            (fun x he => ?_) hcm
          · subst he
            have hs : s = .process j env (.accept cid d E sp es) := by
              cases s <;> simp_all [Federation.actor]
            exact hc.1 (f, s) List.mem_cons_self j env cid d E sp es hs
          · subst he
            have hs : s = .process j env (.clawback x) := by
              cases s <;> simp_all [Federation.actor]
            exact hc.2 (f, s) List.mem_cons_self j env x hs
        · exact now i hi c hcm
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact now
      · exact past y hy

/-- `Federation.HotBinding` derived over an execution checked by this ingress, with the transaction identity
collision-free: no partial of a signer outside the extracted set, queued under a non-hot candidate, shares a
hot-class transaction's input-0 message. A row on a candidate's base is an escape-class member's, as in
`Ingress.hot_binding`; a row on a rung above the base is the rung's, whose transaction is an escape-class
member's (`RungIngress.resident_classed`); one identity is one transaction, so one class. -/
@[req "DUR-8"]
theorem hot_binding {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t)
    (hid : ∀ a b, ctx.txId a = ctx.txId b → a = b) {m : Member} (hw : m.frame.WF)
    (hhot : classOf ctx m = some .hot) :
    Federation.HotBinding f (sighash (tx ctx m) 0) := by
  intro x hxm hext hmsg h0
  rcases Federation.part_origin hx hxm with he | ⟨hs, g, env, e, hm, hq⟩
  · exact absurd he hext
  obtain ⟨c, hcm, hcase⟩ := Ingress.queued_cand hq h0
  obtain ⟨hcl, hrc⟩ := (resident_classed hx hc).2 _ hm x.signer hs c hcm
  have same (m' : Member) (hw' : m'.frame.WF) (hcmsg : x.msg = sighash (tx ctx m') 0) :
      classOf ctx m' = some .hot := by
    rw [hmsg] at hcmsg
    simp only [sighash, Ingress.tx, Prod.mk.injEq, and_true] at hcmsg
    have hf := Encode.encode_injective _ _ hw hw' (hid _ _ hcmsg)
    have ho : m.psbt.txOutputs = m'.psbt.txOutputs := by
      simp only [Ingress.Member.frame, Encode.Commitment.mk.injEq] at hf
      exact hf.2.2.2.2.1
    rw [← hhot]; simp only [classOf, Ingress.outputs, Evaluate.outputs, ho]
  rcases hcase with ⟨hcmsg, hch⟩ | ⟨g', hg', hgmsg, -⟩
  · obtain ⟨m', hw', htx, hcl'⟩ := hcl
    have := same m' hw' (by rw [← htx]; exact hcmsg)
    rw [hch]
    cases hh : c.hot
    · rw [hh] at hcl'; rw [hcl'] at this; cases this
    · rfl
  · obtain ⟨m', hw', htx, hcl'⟩ := hrc g' hg'
    have := same m' hw' (by rw [← htx]; exact hgmsg)
    rw [hcl'] at this; cases this

/-- `DUR-8`'s "never a signing quorum" over an execution checked by this ingress, for a target it accepted:
`Federation.no_exposed_quorum` with its message binding replaced by two premises, every honest acceptance
checked and a collision-free transaction identity. What stays: `hr`, `noNormal`, `bound`. -/
@[req "DUR-8"]
theorem no_exposed_quorum {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : CheckedTrace ctx t)
    (hid : ∀ a b, ctx.txId a = ctx.txId b → a = b) (n : Node) {fits : Bool} {q : Request} {sp es : Cand}
    (hq : check ctx fits q = .accepted sp es)
    (noNormal : NoHonestNormalDecision r (fun j => Federation.project j t) f.extracted
      (sighash sp.tx 0))
    (bound : f.extracted.eraseDups.length < n.t) :
    exposedQuorum { node := n, exposure := f.parts } sp = false := by
  obtain ⟨hc0, -, -, -⟩ := accepted_validates hq
  obtain ⟨ha, -, -, -, -, -, -, -, hsp, -⟩ := Ingress.accepted_validates hc0
  have hb : Federation.HotBinding f (sighash sp.tx 0) := by
    rw [hsp]; exact hot_binding hx hc hid (Ingress.frame_wf ha) (Ingress.accepted_spend hc0).1
  exact Federation.no_exposed_quorum hr hx n sp hb noNormal bound

/-! ## Possession over the ladder -/

/-- The signatures this node made at ingress and still holds: its own signature on every input of every rung,
the base first, of every resident candidate. `SPN-32`: "The node MUST sign the spend, the Escape and every rung
at ingress". -/
@[req "SPN-32"]
def ownSigs (n : Node) : List Authority.Sig :=
  n.cands.flatMap fun c => c.ladder.flatMap fun g =>
    (List.range g.tx.inputs.length).map fun k => { msg := sighash g.tx k, input := k, signer := n.id }

/-- `NCH-24`'s store test on one partial, per input, over the ladder, as far as `Federation.storable` keeps it: a
resident candidate with this commitment id retaining a rung, the base or one above it, whose transaction has this
message at this input ("the rung is found by txid", and the input in range). The signer's range and the
candidate's expiry are not tested, as there, and the user-signature hash is not compared: the row carries none. -/
@[req "NCH-24"]
def storable (n : Node) (m : Sighash) (k cid : Nat) : Bool :=
  n.cands.any fun c => c.id == cid &&
    c.ladder.any fun g => m == sighash g.tx k && decide (k < g.tx.inputs.length)

/-- One frame's delivery, with its commitment id, if this store test passed when it arrived. -/
def arrival (a : World × Env × Event) : List (Nat × Authority.Sig) :=
  match a.2.2 with
  | .receivePartial m k s cid =>
    if storable a.1.node m k cid then [(cid, { msg := m, input := k, signer := s })] else []
  | _ => []

/-- `Federation.kept` with this store test: the partials delivered over the history that the store took, kept
while their commitment's candidate stays resident. -/
def kept : History → Node → List (Nat × Authority.Sig)
  | [], _ => []
  | a :: h, n => (kept h a.1.node ++ arrival a).filter fun p => n.cands.any (·.id == p.1)

theorem mem_kept : ∀ {h : History} {n : Node} {p : Nat × Authority.Sig}, p ∈ kept h n →
    ∃ a ∈ h, a.2.2 = .receivePartial p.2.msg p.2.input p.2.signer p.1
  | [], _, _, hp => by cases hp
  | a :: h, n, p, hp => by
    simp only [kept, List.mem_filter, List.mem_append] at hp
    rcases hp.1 with hp | hp
    · obtain ⟨b, hb, he⟩ := mem_kept hp
      exact ⟨b, List.mem_cons_of_mem a hb, he⟩
    · refine ⟨a, List.mem_cons_self, ?_⟩
      obtain ⟨w, env, e⟩ := a
      cases e with
      | receivePartial m k s cid =>
        simp only [arrival] at hp
        split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          rfl
        · cases hp
      | _ => simp [arrival] at hp

def received (n : Node) (h : History) : List Authority.Sig := (kept h n).map Prod.snd

/-- Node `i`'s possession over the ladder at the end of a composed trace: `Federation.held` with the node's own
signatures and its store over every rung it retains. -/
@[req "DUR-28"]
def held (i : Nat) (t : Federation.Trace) (f : Fed) : List Authority.Sig :=
  ownSigs (f.worlds i).node ++ received (f.worlds i).node (Federation.project i t)

/-- Possession comes from delivery: each signature an honest node holds over its ladder is its own or a partial
of the inventory, with the same message, input and signer. -/
@[req "DUR-28"]
theorem held_origin {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} (hi : i ∈ honest) {x : Authority.Sig}
    (hm : x ∈ held i t f) : x.signer = i ∨ ∃ y ∈ f.parts, Authority.sig y = x := by
  rcases List.mem_append.1 hm with hm | hm
  · left
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.1 hm
    obtain ⟨g, _, hg⟩ := List.mem_flatMap.1 hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
    exact Federation.node_id hx hi
  · right
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨⟨w, env, e⟩, ha, he⟩ := mem_kept hp
    simp only at he
    subst he
    obtain ⟨y, hy, h1, h2, h3, _⟩ := Federation.partial_receipt_origin hx ha
    exact ⟨y, hy, by simp [Authority.sig, h1, h2, h3]⟩

theorem ownSigs_sub (n : Node) {x : Authority.Sig} (h : x ∈ Federation.ownSigs n) : x ∈ ownSigs n := by
  obtain ⟨c, hc, hx⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨c, hc, List.mem_flatMap.2 ⟨⟨c.tx, c.baseSig⟩, List.mem_cons_self, hx⟩⟩

theorem storable_of {n : Node} {m : Sighash} {k cid : Nat} (h : Federation.storable n m k cid = true) :
    storable n m k cid = true := by
  obtain ⟨c, hc, h⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨c, hc, ?_⟩
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, List.any_eq_true.2 ⟨⟨c.tx, c.baseSig⟩, List.mem_cons_self, by simp only [Bool.and_eq_true]; exact ⟨h.1.2, h.2⟩⟩⟩

theorem kept_sub : ∀ {h : History} {n : Node} {p : Nat × Authority.Sig}, p ∈ Federation.kept h n → p ∈ kept h n
  | [], _, _, hp => by cases hp
  | a :: h, n, p, hp => by
    simp only [Federation.kept, kept, List.mem_filter, List.mem_append] at hp ⊢
    refine ⟨?_, hp.2⟩
    rcases hp.1 with hp | hp
    · exact .inl (kept_sub hp)
    · right
      obtain ⟨w, env, e⟩ := a
      cases e with
      | receivePartial m k s cid =>
        simp only [Federation.arrival, arrival] at hp ⊢
        split at hp
        · rename_i hs; rw [storable_of hs]; exact hp
        · cases hp
      | _ => simp [Federation.arrival] at hp

/-- Possession over the ladder contains `Federation.held`. -/
@[req "DUR-28"]
theorem held_sub (i : Nat) (t : Federation.Trace) (f : Fed) {x : Authority.Sig}
    (h : x ∈ Federation.held i t f) : x ∈ held i t f := by
  rcases List.mem_append.1 h with h | h
  · exact List.mem_append.2 (.inl (ownSigs_sub _ h))
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact List.mem_append.2 (.inr (List.mem_map.2 ⟨p, kept_sub hp, rfl⟩))

theorem flatMap_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem any_congr {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a List.mem_cons_self, any_congr (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem ownSigs_bare (n : Node) (h : ∀ c ∈ n.cands, c.above = []) : ownSigs n = Federation.ownSigs n := by
  unfold ownSigs Federation.ownSigs
  apply flatMap_congr
  intro c hc
  simp [Cand.ladder, h c hc]

theorem storable_bare (n : Node) (h : ∀ c ∈ n.cands, c.above = []) (m : Sighash) (k cid : Nat) :
    storable n m k cid = Federation.storable n m k cid := by
  unfold storable Federation.storable
  apply any_congr
  intro c hc
  simp [Cand.ladder, h c hc, Bool.and_assoc]

theorem kept_bare : ∀ {h : History} (n : Node), (∀ a ∈ h, ∀ c ∈ a.1.node.cands, c.above = []) →
    kept h n = Federation.kept h n
  | [], _, _ => rfl
  | a :: h, n, hb => by
    simp only [kept, Federation.kept]
    rw [kept_bare a.1.node (fun b hb' => hb b (List.mem_cons_of_mem a hb'))]
    congr 2
    obtain ⟨w, env, e⟩ := a
    cases e with
    | receivePartial m k s cid =>
      simp only [arrival, Federation.arrival]
      rw [storable_bare w.node (hb _ List.mem_cons_self)]
    | _ => rfl

/-- Where no candidate retains a rung, at the end and at every frame of the node's history, possession over the
ladder is `Federation.held`. -/
@[req "DUR-28"]
theorem held_bare (i : Nat) (t : Federation.Trace) (f : Fed)
    (hn : ∀ c ∈ (f.worlds i).node.cands, c.above = [])
    (hh : ∀ a ∈ Federation.project i t, ∀ c ∈ a.1.node.cands, c.above = []) :
    held i t f = Federation.held i t f := by
  simp only [held, Federation.held, received, Federation.received, ownSigs_bare _ hn, kept_bare _ hh]

theorem project_world {i : Nat} : ∀ {t : Federation.Trace} {a : World × Env × Event},
    a ∈ Federation.project i t → ∃ y ∈ t, a.1 = y.1.worlds i
  | [], _, h => by cases h
  | (g, s) :: t, a, h => by
    simp only [Federation.project] at h
    split at h
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨(g, s), List.mem_cons_self, rfl⟩
        · obtain ⟨y, hy, he⟩ := project_world h
          exact ⟨y, List.mem_cons_of_mem _ hy, he⟩
      · obtain ⟨y, hy, he⟩ := project_world h
        exact ⟨y, List.mem_cons_of_mem _ hy, he⟩
    · obtain ⟨y, hy, he⟩ := project_world h
      exact ⟨y, List.mem_cons_of_mem _ hy, he⟩

/-- On every execution checked by `Ingress.check` possession over the ladder is `Federation.held` at every
honest node: no candidate there retains a rung (`Ingress.resident_no_rungs`). -/
@[req "DUR-28"]
theorem held_plain {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ctx} (hc : Ingress.CheckedTrace ctx t) {i : Nat}
    (hi : i ∈ honest) : held i t f = Federation.held i t f := by
  obtain ⟨now, past⟩ := Ingress.resident_no_rungs hx hc
  refine held_bare i t f (now i hi) (fun a ha => ?_)
  obtain ⟨y, hy, he⟩ := project_world ha
  rw [he]
  exact past y hy i hi

end BtcPolicy.RungIngress
