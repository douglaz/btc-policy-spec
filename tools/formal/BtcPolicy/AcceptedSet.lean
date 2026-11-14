import BtcPolicy.ClassAssembly
import BtcPolicy.LadderShape
/-! `SPN-33`'s vault-authorized set with every rung, derived from the node's accepted registrations
(`bps-keml.5`).

**The set.** `Sweep.authorized` collects, for every candidate in a node's registry now or before one of its own
steps, the txid of the base and of every rung the candidate retains above it (`Kernel.Cand.ladder`).
`SPN-33`: "On acceptance the node MUST add the spend's, the Escape's and every rung's txid to its
**vault-authorized set**"; `WTC-18`: "The authorized set is the txids of every spend, Escape, rung, refresh and
claw-back this node accepted". Its earlier body, the base txids alone, is kept verbatim as `Sweep.authorizedPre`.

**The earlier set on its own domain.** With no rung retained anywhere in the registry's history the two are equal
as lists (`Sweep.authorized_bare`), and the earlier set is always contained in this one
(`Sweep.authorizedPre_sub`). On an execution whose acceptances and claw-backs are checked by `Ingress.check`, at
an honest node, they are equal (`AcceptedSet.authorized_checked`, `AcceptedSet.authorizedAt_checked`):
`Ingress.resident_no_rungs` holds at honest nodes only, and a node outside the honest list may start with any
registry. Each definition that reads the set agrees there with its value at the earlier set:
`AcceptedSet.check_pre` (`Sweep.check`), `readsAt_pre`, `failing_pre` (`PreRelease.failing`), `readOf_pre`
(`Ladder.readOf`), `readAt_pre` (`RungRelease.readAt`), `refuses_pre` (`LadderRelease.refuses`), `checkOf_pre`
(`Assembly.checkOf`) and `candOk_pre` (`ClassAssembly.candOk`). Inclusion gives no monotone verdict: a larger
set admits more replacement targets and parents, and it can also add outputs to a pass's protected value.

**What changes, and where.** The set is read by four functions: `Package.residentRead` (a replacement's resident,
`WTC-25`), `Package.ancestryVerdict` (each unconfirmed ancestor, `WTC-24`), `Sweep.additions` and
`Sweep.unconfirmedExternal` (`WTC-10`, `DUR-22`: a resident's pending vault-script outputs join the snapshot when
its creator is in the set and are counted as external deposits otherwise). Through `Sweep.snapshot` the
additions also reach `Package.missingPrevout`, so a prevout created by a resident rung is shown. Each differs
only where a candidate of the node's registry history retains a rung and the backend's mempool or pending outputs
name that rung's txid.

**The protected value.** `DUR-22` adds the unconfirmed outputs whose parent is in the set, "less the outputs of
every selected Escape and of every resident rung". Here `Sweep.additions` adds each pending vault-script output
whose creator is in the set and that no other resident spends. `Sweep.passAt` subtracts the outputs of a selected
Escape whose base is resident and none of a resident rung, so on the paths that read it (`Sweep.check`,
`PreRelease.failing`, the pass of `Ladder.readOf`, which leaves the rungs empty) such an output of a resident rung
is now added and not subtracted. `Ladder.passAt` over `RungRelease.readAt` subtracts the outputs of the resident
rungs of each selected Escape the registry holds, and not those of a rung whose candidate was pruned or is not
selected, which the set still holds: there too such an output is now added and not subtracted. Before, these
outputs were left out of the snapshot and counted as unconfirmed external deposits. The effect is empty when no
rung txid has a pending vault-script output, which is the case when every Escape and rung pays every output to the
escape descriptor (`CHN-14`); the backend here does not enforce that. `AcceptedSet.passAt_pre` states it for
`Sweep.passAt`: when no pending output has a creator the set holds and the earlier set does not, the pass is the
one the earlier set gives.

**Accepted means accepted.** On an execution, at an honest node, every id in the set is the txid of a member of
a ladder that an `accept` or `clawback` step of that node registered: a step whose payload carries that
transaction and ladder, after which the registry holds a candidate with them that no candidate before the step
had (`AcceptedSet.Registers`, `AcceptedSet.authorized_origin`). A step that refuses leaves the registry as it was
and adds no new member (`AcceptedSet.authorized_same`; `AcceptedSet.accept_refused` for an acceptance whose
`Kernel.pairAdmits` fails, which is how a repeat with other rung txids is refused under
`Kernel.Registration.preserve`). The statement is about membership: a step that adds nothing can repeat ids
already present in the list. On a run checked by `RungIngress.check`, the registering step's payload is a
checked request's pair, whose rungs are the request's in its order, or a checked claw-back, which carries no rung
(`AcceptedSet.checked_origin`); `LadderShape.CheckedTrace` runs are such runs (`LadderShape.to_rung`). Every
member of a registered ladder enters the set and stays at every later state (`AcceptedSet.registered_authorized`),
and no step removes an id (`AcceptedSet.authorized_step`, `AcceptedSet.authorizedAt_mono`): pruning, expiry and
settlement are kernel steps, and a reorganization is `Sweep.Step.chain`. The history is the node's own
(`Federation.project`): an id another node accepted is not read here.

**The replacement reads it.** A ladder's selected rung and a rung's assembly read the set through
`Ladder.readOf`'s `A` (`Ladder.ancestryTx`, `Assembly.rungCheck`). An admitted validation naming a resident as
the one replaced has that resident in the set (`AcceptedSet.replaced_authorized`), so, at an honest node of an
execution, a member of a ladder some `accept` or `clawback` step of that node registered
(`AcceptedSet.replaced_origin`).

**Not here.** Refresh txids (`WTC-18` lists them): refresh is not modelled. The watchtower's record
(`Alerts.Record`) stays a supplied parameter and does not read this set. `Sweep.passAt` and `Ladder.passAt` are
unchanged (above). -/

namespace BtcPolicy.AcceptedSet
open BtcPolicy.Kernel BtcPolicy.Federation
open BtcPolicy.Sweep (authorized authorizedPre authorizedAt mem_authorized)

/-! ## The earlier set on its own domain -/

/-- On an execution checked by `Ingress.check`, at an honest node, the set is the earlier one: no candidate
there retains a rung, now or at any earlier state (`Ingress.resident_no_rungs`). -/
@[req "SPN-33"]
theorem authorized_checked {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ingress.Ctx} (hc : Ingress.CheckedTrace ctx t) {i : Nat}
    (hi : i ∈ honest) :
    authorized (project i t) (f.worlds i).node = authorizedPre (project i t) (f.worlds i).node := by
  obtain ⟨h1, h2⟩ := Ingress.resident_no_rungs hx hc
  refine Sweep.authorized_bare _ _ (h1 i hi) fun a ha c hc' => ?_
  obtain ⟨y, hy, he⟩ := RungIngress.project_world ha
  rw [he] at hc'
  exact h2 y hy i hi c hc'

/-- The earlier set node `i` reads in state `st` after history `T`. -/
def authorizedPreAt (st : Sweep.State) (T : Sweep.Trace) (i : Nat) : List Nat :=
  authorizedPre (project i (Sweep.fedTrace T)) (st.fed.worlds i).node

/-- The same on a composed sweep execution. -/
@[req "SPN-33"]
theorem authorizedAt_checked {cfg : Sweep.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : Sweep.State} (hx : Sweep.Execution cfg r honest T st) {ctx : Ingress.Ctx}
    (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T)) {i : Nat} (hi : i ∈ honest) :
    authorizedAt st T i = authorizedPreAt st T i :=
  authorized_checked (Sweep.fed_execution hx) hc hi

/-! ## Each reader agrees there with the earlier set -/

section Readers
variable {cfg : Sweep.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
  {ctx : Ingress.Ctx} {i : Nat}

/-- `Sweep.check` agrees with its value at the earlier set. -/
@[req "SPN-33"]
theorem check_pre (hx : Sweep.Execution cfg r honest T st) (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T))
    (hi : i ∈ honest) (c : Cand) :
    Sweep.check cfg st T i c = match st.obs i with
      | none => false
      | some b =>
        Sweep.covered cfg (authorizedPreAt st T i) (st.fed.worlds i).node b c &&
          Sweep.ancestryOk cfg (authorizedPreAt st T i) b c &&
          Sweep.possessed cfg (st.fed.worlds i).node.t (held i (Sweep.fedTrace T) st.fed) c := by
  unfold Sweep.check
  rw [authorizedAt_checked hx hc hi]
  cases st.obs i <;> rfl

/-- `Sweep.readsAt` agrees with its value at the earlier set. -/
theorem readsAt_pre (hx : Sweep.Execution cfg r honest T st) (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T))
    (hi : i ∈ honest) (b : Sweep.Backend) :
    Sweep.readsAt cfg st T i b = Sweep.passAt cfg (authorizedPreAt st T i) (st.fed.worlds i).node b := by
  unfold Sweep.readsAt
  rw [authorizedAt_checked hx hc hi]

/-- `PreRelease.failing` agrees with its value at the earlier set. -/
@[req "DUR-21"]
theorem failing_pre (pc : PreRelease.Cfg) (hx : Sweep.Execution cfg r honest T st)
    (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T)) (hi : i ∈ honest) :
    PreRelease.failing pc st T i =
      PreRelease.failingAt pc (authorizedPreAt st T i) (st.fed.worlds i).node (st.obs i) := by
  rw [PreRelease.failing_eq, authorizedAt_checked hx hc hi]

/-- `Ladder.readOf` agrees with its value at the earlier set. -/
@[req "DUR-21"]
theorem readOf_pre (hx : Sweep.Execution cfg r honest T st) (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T))
    (hi : i ∈ honest) (m : Option Nat) :
    Ladder.readOf st T i m =
      { A := authorizedPreAt st T i, reg := (st.fed.worlds i).node, ob := st.obs i, median := m } := by
  unfold Ladder.readOf
  rw [authorizedAt_checked hx hc hi]

/-- `RungRelease.readAt` reads the earlier set there. -/
@[req "DUR-21"]
theorem readAt_pre (hx : Sweep.Execution cfg r honest T st) (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T))
    (hi : i ∈ honest) (c : Cand) : (RungRelease.readAt st T i c).A = authorizedPreAt st T i :=
  authorizedAt_checked hx hc hi

/-- `LadderRelease.refuses` agrees with its value at the earlier set; the ladder's own part reads it through
`RungRelease.readAt` (`readAt_pre`). -/
@[req "DUR-21"]
theorem refuses_pre (lc : Ladder.Cfg) (hx : Sweep.Execution cfg r honest T st)
    (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T)) (hi : i ∈ honest) (c : Cand) :
    LadderRelease.refuses lc st T i c = (c.isEscape &&
      (!(PreRelease.verdict lc.pre (authorizedPreAt st T i) (st.fed.worlds i).node (st.obs i) c).ok ||
        (!c.above.isEmpty && !LadderRelease.baseOk lc st T i c))) := by
  unfold LadderRelease.refuses
  rw [authorizedAt_checked hx hc hi]

/-- `Assembly.checkOf` agrees with its value at the earlier set. -/
@[req "SPN-39"]
theorem checkOf_pre (acfg : Assembly.Cfg) (hx : Sweep.Execution cfg r honest T st)
    (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace T)) (hi : i ∈ honest) (c : Cand) :
    Assembly.checkOf acfg st T i c = match st.obs i with
      | none => false
      | some b => Assembly.checkAt acfg (authorizedPreAt st T i) (Assembly.clawTxsAt st T i)
          (st.fed.worlds i).node (held i (Sweep.fedTrace T) st.fed) b c := by
  unfold Assembly.checkOf
  rw [authorizedAt_checked hx hc hi]
  cases st.obs i <;> rfl

/-- `ClassAssembly.candOk` agrees with its value at the earlier set, on both branches. -/
@[req "SPN-39"]
theorem candOk_pre (ccfg : RungAssembly.Cfg) {st : RungAssembly.State} {T : ClassAssembly.LTrace}
    (hx : Sweep.Execution cfg r honest (ClassAssembly.sweepT T) st.sw)
    (hc : Ingress.CheckedTrace ctx (Sweep.fedTrace (ClassAssembly.sweepT T))) (hi : i ∈ honest) (c : Cand) :
    ClassAssembly.candOk ccfg st T i c = match st.sw.obs i with
      | none => false
      | some b =>
        if c.isEscape then
          ClassAssembly.finalAt ccfg st T i c == some 0 &&
            Assembly.rungCheck ccfg.asm
              { ClassAssembly.readAt st T i c with A := authorizedPreAt st.sw (ClassAssembly.sweepT T) i } b c
              (ClassAssembly.heldAt ccfg st T i) 0
        else
          Assembly.checkAt ccfg.asm (authorizedPreAt st.sw (ClassAssembly.sweepT T) i)
            (Assembly.clawTxsAt st.sw (ClassAssembly.sweepT T) i) (st.sw.fed.worlds i).node
            (ClassAssembly.heldAt ccfg st T i) b c := by
  have hA := authorizedAt_checked hx hc hi
  have hrd : ClassAssembly.readAt st T i c =
      { ClassAssembly.readAt st T i c with A := authorizedPreAt st.sw (ClassAssembly.sweepT T) i } := by
    rw [← hA]
    rfl
  unfold ClassAssembly.candOk
  rw [← hrd, hA]
  cases st.sw.obs i <;> rfl

end Readers

/-! ## The base path's protected value -/

theorem additions_congr {A A' : List Nat} {b : Sweep.Backend}
    (h : ∀ p ∈ b.pending, A.contains p.1 = A'.contains p.1) : Sweep.additions A b = Sweep.additions A' b := by
  unfold Sweep.additions
  congr 1
  exact List.filter_congr fun p hp => by rw [h p hp]

theorem external_congr {A A' : List Nat} {b : Sweep.Backend}
    (h : ∀ p ∈ b.pending, A.contains p.1 = A'.contains p.1) :
    Sweep.unconfirmedExternal A b = Sweep.unconfirmedExternal A' b := by
  unfold Sweep.unconfirmedExternal
  congr 1
  exact List.filter_congr fun p hp => by rw [h p hp]

/-- Two sets that agree on every pending output's creator give the same snapshot. -/
theorem snapshot_congr {A A' : List Nat} {b : Sweep.Backend}
    (h : ∀ p ∈ b.pending, A.contains p.1 = A'.contains p.1) : Sweep.snapshot A b = Sweep.snapshot A' b := by
  unfold Sweep.snapshot
  rw [additions_congr h]

/-- `DUR-22`'s pass on the base path, when no pending vault-script output has a creator the set holds and the
earlier set does not (a rung's txid that is no base's): the pass the earlier set gives. Where a resident rung has
such an output, the set adds it to the snapshot and `Sweep.passAt` does not subtract it. -/
@[req "DUR-22"]
theorem passAt_pre (cfg : Sweep.Cfg) (h : History) (n n' : Node) (b : Sweep.Backend)
    (hp : ∀ p ∈ b.pending, p.1 ∈ authorized h n → p.1 ∈ authorizedPre h n) :
    Sweep.passAt cfg (authorized h n) n' b = Sweep.passAt cfg (authorizedPre h n) n' b := by
  have hc : ∀ p ∈ b.pending, (authorized h n).contains p.1 = (authorizedPre h n).contains p.1 := by
    intro p hpm
    have := hp p hpm
    have := Sweep.authorizedPre_sub h n (x := p.1)
    cases h1 : (authorized h n).contains p.1 <;> cases h2 : (authorizedPre h n).contains p.1 <;>
      simp_all
  unfold Sweep.passAt
  rw [snapshot_congr hc, external_congr hc]

/-! ## Accepted means accepted -/

/-- A candidate's identity as the set reads it: its base transaction and the rungs it retains above it. -/
def key (c : Cand) : Tx × List Rung := (c.tx, c.above)

/-- The ids of an identity: the base's txid, then each rung's. -/
def ids (k : Tx × List Rung) : List Nat := k.1.id :: k.2.map (·.tx.id)

theorem ids_key (c : Cand) : ids (key c) = c.ladder.map (·.tx.id) := by simp [ids, key, Cand.ladder]

/-- Where a candidate's identity comes from: a candidate after a step has the identity of one before it, or of a
member of the pair or the claw-back the step registers. -/
theorem key_origin (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) :
    (∃ d ∈ w.node.cands, key d = key c) ∨
    (∃ cid dd E sp es, e = .accept cid dd E sp es ∧ (key c = key sp ∨ key c = key es)) ∨
    ∃ x, e = .clawback x ∧ key c = key x := by
  have keep (hc : c ∈ w.node.cands) : ∃ d ∈ w.node.cands, key d = key c := ⟨c, hc, rfl⟩
  have frame (f : Cand → Cand) (hf : ∀ d, key (f d) = key d) (hc : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, key d = key c := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact ⟨d, hd, (hf d).symm⟩
  have ww : ∀ r sel T slack (d : Cand), key (withWindow r sel T slack d) = key d := by
    intro r sel T slack d; unfold withWindow; split <;> rfl
  cases e with
  | accept cid dd E sp es =>
    simp only [step, accept] at hc
    split at hc
    · refine .inl (keep ?_)
      simp only [refuse] at hc
      split at hc
      · exact hc
      · split at hc
        · exact hc
        · exact hc
    · split at hc
      · exact .inl (keep hc)
      · have base (x : Cand) (hx : x ∈ register r w.node env sp es) :
            (∃ d ∈ w.node.cands, key d = key x) ∨ (key x = key sp ∨ key x = key es) := by
          rcases List.mem_cons.1 (mem_register hx) with rfl | hx
          · exact .inr (.inl rfl)
          rcases List.mem_cons.1 hx with rfl | hx
          · exact .inr (.inr rfl)
          · exact .inl ⟨x, hx, rfl⟩
        split at hc
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
          rw [ww]
          rcases base x hx with h | h
          · exact .inl h
          · exact .inr (.inl ⟨cid, dd, E, sp, es, rfl, h⟩)
        · rcases base c hc with h | h
          · exact .inl h
          · exact .inr (.inl ⟨cid, dd, E, sp, es, rfl, h⟩)
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => by apply ww) hc
        · exact keep hc
  | refuse cid d E pair code =>
    refine .inl (keep ?_)
    simp only [step, refuse] at hc
    split at hc
    · exact hc
    · split at hc
      · exact hc
      · exact hc
  | firePass =>
    refine .inl ?_
    simp only [step, firePass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> rfl) hc
  | ladderPass =>
    refine .inl ?_
    simp only [step, ladderPass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by rfl) hc
  | packageAccepted cid =>
    exact .inl (frame _ (fun d => by split <;> rfl) hc)
  | send cid =>
    refine .inl ?_
    simp only [step, send] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> rfl) hc
  | settle tx =>
    refine .inl ?_
    simp only [step, settle] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> rfl) hc
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> rfl) hc)
  | clawback x =>
    rcases mem_clawback (by simpa [step] using hc) with hc | ⟨rfl, -⟩
    · exact .inl (keep hc)
    · exact .inr (.inr ⟨x, rfl, rfl⟩)

/-- Step `y` of a federation history registers identity `k` at node `i`: it is node `i`'s `accept` whose pair
carries `k`, or its `clawback` of a candidate with `k`, and after it the registry holds a candidate with `k` that
no candidate before it had. -/
def Registers (r : Rules) (i : Nat) (y : Fed × Federation.Step) (k : Tx × List Rung) : Prop :=
  ∃ env e, actor y.2 = some (i, env, e) ∧
    ((∃ cid dd E sp es, e = .accept cid dd E sp es ∧ (k = key sp ∨ k = key es)) ∨
      ∃ x, e = .clawback x ∧ k = key x) ∧
    (∃ c ∈ (step r env (y.1.worlds i) e).1.node.cands, key c = k) ∧
    ∀ d ∈ (y.1.worlds i).node.cands, key d ≠ k

/-- Every candidate at an honest node, now and at every earlier state of an execution, has the identity some step
of the history registered there. -/
theorem registry_origin {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} (hi : i ∈ honest) :
    (∀ c ∈ (f.worlds i).node.cands, ∃ y ∈ t, Registers r i y (key c)) ∧
    ∀ y ∈ t, ∀ c ∈ (y.1.worlds i).node.cands, ∃ y' ∈ t, Registers r i y' (key c) := by
  induction hx with
  | init f h =>
    refine ⟨fun c hc => ?_, fun y hy => by cases hy⟩
    rw [(h.2.2 i hi).2.2.2.1] at hc; cases hc
  | @next t f s ha hx ih =>
    obtain ⟨now, past⟩ := ih
    have lift {k : Tx × List Rung} (h : ∃ y ∈ t, Registers r i y k) : ∃ y ∈ (f, s) :: t, Registers r i y k := by
      obtain ⟨y, hy, hr⟩ := h
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩
    refine ⟨fun c hc => ?_, fun y hy c hc => ?_⟩
    · cases hact : actor s with
      | none =>
        rw [apply_no_actor r f s hact i] at hc
        exact lift (now c hc)
      | some a =>
        obtain ⟨j, env, e⟩ := a
        rw [apply_of_actor r f s hact i] at hc
        split at hc
        · subst i
          by_cases hold : ∃ d ∈ (f.worlds j).node.cands, key d = key c
          · obtain ⟨d, hd, hk⟩ := hold
            rw [← hk]; exact lift (now d hd)
          · have hnew : ∀ d ∈ (f.worlds j).node.cands, key d ≠ key c := fun d hd hk => hold ⟨d, hd, hk⟩
            rcases key_origin r env (f.worlds j) e hc with h | h | h
            · exact absurd h hold
            · obtain ⟨cid, dd, E, sp, es, rfl, hk⟩ := h
              exact ⟨(f, s), List.mem_cons_self, env, _, hact,
                .inl ⟨cid, dd, E, sp, es, rfl, hk⟩, ⟨c, hc, rfl⟩, hnew⟩
            · obtain ⟨x, rfl, hk⟩ := h
              exact ⟨(f, s), List.mem_cons_self, env, _, hact, .inr ⟨x, rfl, hk⟩, ⟨c, hc, rfl⟩, hnew⟩
        · exact lift (now c hc)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact lift (now c hc)
      · exact lift (past y hy c hc)

/-- **Each id in the set has an accepted origin** (`SPN-33`, `WTC-18`). At an honest node of an execution, every
id the node's set holds is the txid of the base or of a rung of an identity some `accept` or `clawback` step of
that node registered. -/
@[req "SPN-33"]
theorem authorized_origin {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} (hi : i ∈ honest) {x : Nat}
    (h : x ∈ authorized (project i t) (f.worlds i).node) :
    ∃ y ∈ t, ∃ k, x ∈ ids k ∧ Registers r i y k := by
  obtain ⟨now, past⟩ := registry_origin hx hi
  rcases mem_authorized.1 h with ⟨c, hc, hxc⟩ | ⟨a, ha, c, hc, hxc⟩
  · obtain ⟨y, hy, hr⟩ := now c hc
    exact ⟨y, hy, key c, by rw [ids_key]; exact hxc, hr⟩
  · obtain ⟨y, hy, he⟩ := RungIngress.project_world ha
    rw [he] at hc
    obtain ⟨y', hy', hr⟩ := past y hy c hc
    exact ⟨y', hy', key c, by rw [ids_key]; exact hxc, hr⟩

/-- The same on a composed sweep execution, at the set node `i` reads. -/
@[req "SPN-33"]
theorem authorizedAt_origin {cfg : Sweep.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : Sweep.State} (hx : Sweep.Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) {x : Nat}
    (h : x ∈ authorizedAt st T i) : ∃ y ∈ Sweep.fedTrace T, ∃ k, x ∈ ids k ∧ Registers r i y k :=
  authorized_origin (Sweep.fed_execution hx) hi h

/-- **On a run checked by `RungIngress.check`, the origin is a checked request.** At an honest node `i` of an
execution whose acceptances and claw-backs that check gave, the step that registered an id is node `i`'s
acceptance of a pair the check accepted for some request, and the id is the spend's txid, the Escape's, or the
txid of one of the request's rungs, in its order; or it is node `i`'s claw-back of a candidate
`Ingress.checkClawback` built, and the id is that candidate's own txid: a checked claw-back carries no rung. -/
@[req "SPN-33"]
theorem checked_origin {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {ctx : Ingress.Ctx} (hc : RungIngress.CheckedTrace ctx t) {i : Nat}
    (hi : i ∈ honest) {x : Nat} (h : x ∈ authorized (project i t) (f.worlds i).node) :
    ∃ y ∈ t, ∃ k, Registers r i y k ∧
      ((∃ env cid dd E sp es q, y.2 = .process i env (.accept cid dd E sp es) ∧
          RungIngress.check ctx true q = .accepted sp es ∧
          (x = sp.tx.id ∨ x = es.tx.id ∨ x ∈ (q.rungs.map (RungIngress.rung ctx)).map (·.tx.id))) ∨
        ∃ env c q, y.2 = .process i env (.clawback c) ∧
          Ingress.checkClawback ctx Classification.current q = some c ∧ x = c.tx.id) := by
  obtain ⟨y, hy, k, hxk, hr⟩ := authorized_origin hx hi h
  refine ⟨y, hy, k, hr, ?_⟩
  obtain ⟨env, e, hact, he, -⟩ := hr
  rcases he with ⟨cid, dd, E, sp, es, rfl, hk⟩ | ⟨cl, rfl, hk⟩
  · have hs : y.2 = .process i env (.accept cid dd E sp es) := by
      generalize y.2 = s at hact; cases s <;> simp_all [Federation.actor]
    obtain ⟨q, hq⟩ := hc.1 y hy i env cid dd E sp es hs
    obtain ⟨hesa, -, hspa, -, -⟩ := RungIngress.accepted_rungs hq
    refine .inl ⟨env, cid, dd, E, sp, es, q, hs, hq, ?_⟩
    rcases hk with rfl | rfl
    · simp [ids, key, hspa] at hxk; exact .inl hxk
    · simp only [ids, key, hesa, List.mem_cons] at hxk
      rcases hxk with hxk | hxk
      · exact .inr (.inl hxk)
      · exact .inr (.inr hxk)
  · have hs : y.2 = .process i env (.clawback cl) := by
      generalize y.2 = s at hact; cases s <;> simp_all [Federation.actor]
    obtain ⟨q, hq⟩ := hc.2 y hy i env cl hs
    refine .inr ⟨env, cl, q, hs, hq, ?_⟩
    subst hk
    simpa [ids, key, Ingress.checkClawback_above hq] using hxk

/-! ## Nothing removes an id, and a refusal adds none -/

/-- One federation step keeps every id of node `i`'s set: the registry it leaves is the pre-state the step
records, or the step is another node's and leaves node `i` as it was. -/
@[req "SPN-33"]
theorem authorized_step (r : Rules) (f : Fed) (s : Federation.Step) (t : Federation.Trace) (i : Nat) {x : Nat}
    (h : x ∈ authorized (project i t) (f.worlds i).node) :
    x ∈ authorized (project i ((f, s) :: t)) ((Federation.apply r f s).worlds i).node := by
  cases hact : actor s with
  | none =>
    rw [apply_no_actor r f s hact i]
    simpa [project, hact] using h
  | some a =>
    obtain ⟨j, env, e⟩ := a
    rw [apply_of_actor r f s hact i]
    by_cases hij : j = i
    · subst hij
      rcases mem_authorized.1 h with ⟨c, hc, hxc⟩ | ⟨a, ha, c, hc, hxc⟩
      · exact mem_authorized.2 (.inr ⟨(f.worlds j, env, e), by simp [project, hact], c, hc, hxc⟩)
      · exact mem_authorized.2 (.inr ⟨a, by simp [project, hact, ha], c, hc, hxc⟩)
    · have hji : i ≠ j := fun h => hij h.symm
      simpa [project, hact, hij, hji] using h

/-- On a composed sweep run, no step removes an id from node `i`'s set: pruning, expiry and settlement are kernel
steps, and a reorganization, a deposit or an eviction is `Sweep.Step.chain`, which leaves the federation as it
was. -/
@[req "SPN-33"]
theorem authorizedAt_mono (r : Rules) (st : Sweep.State) (T : Sweep.Trace) (s : Sweep.Step) (i : Nat) {x : Nat}
    (h : x ∈ authorizedAt st T i) : x ∈ authorizedAt (Sweep.apply r st s) ((st, s) :: T) i := by
  cases s with
  | fed s => exact authorized_step r st.fed s (Sweep.fedTrace T) i h
  | chain b => exact h
  | observe j b => exact h

/-- A step after which every candidate at node `i` has the identity of one before it adds no new member to node
`i`'s set. The list itself can grow: the recorded pre-state repeats ids already present. -/
@[req "SPN-33"]
theorem authorized_same (r : Rules) (f : Fed) (s : Federation.Step) (t : Federation.Trace) (i : Nat)
    (hs : ∀ c ∈ ((Federation.apply r f s).worlds i).node.cands, ∃ d ∈ (f.worlds i).node.cands, key d = key c)
    {x : Nat} :
    x ∈ authorized (project i ((f, s) :: t)) ((Federation.apply r f s).worlds i).node ↔
      x ∈ authorized (project i t) (f.worlds i).node := by
  refine ⟨fun h => ?_, authorized_step r f s t i⟩
  have now (c : Cand) (hc : c ∈ ((Federation.apply r f s).worlds i).node.cands)
      (hxc : x ∈ c.ladder.map (·.tx.id)) : x ∈ authorized (project i t) (f.worlds i).node := by
    obtain ⟨d, hd, hk⟩ := hs c hc
    exact mem_authorized.2 (.inl ⟨d, hd, by rw [← ids_key, hk, ids_key]; exact hxc⟩)
  rcases mem_authorized.1 h with ⟨c, hc, hxc⟩ | ⟨a, ha, c, hc, hxc⟩
  · exact now c hc hxc
  · cases hact : actor s with
    | none =>
      simp only [project, hact] at ha
      exact mem_authorized.2 (.inr ⟨a, ha, c, hc, hxc⟩)
    | some p =>
      obtain ⟨j, env, e⟩ := p
      simp only [project, hact] at ha
      split at ha
      · rename_i hji
        rcases List.mem_cons.1 ha with rfl | ha
        · subst hji; exact mem_authorized.2 (.inl ⟨c, hc, hxc⟩)
        · exact mem_authorized.2 (.inr ⟨a, ha, c, hc, hxc⟩)
      · exact mem_authorized.2 (.inr ⟨a, ha, c, hc, hxc⟩)

/-- An acceptance whose pair `Kernel.pairAdmits` refuses leaves the registry as it was: under
`Kernel.Registration.preserve` that includes a repeat whose Escape's ordered rung txids differ from the resident's
(`SPN-32`), so the rungs it proposes enter no set (`authorized_same`). -/
@[req "SPN-32"]
theorem accept_refused (r : Rules) (env : Env) (w : World) {cid : Nat} {dd : Bool} {E : Clocks.Wall}
    {sp es : Cand} (h : pairAdmits r w.node sp es = false) :
    (step r env w (.accept cid dd E sp es)).1.node.cands = w.node.cands := by
  simp [step, accept, h, refuse_cands]

/-- **Every member of a registered ladder enters the set and stays** (`SPN-33`). For a step of node `i` in the
history of an execution, every txid of the ladder of a candidate its registry holds after the step is in node
`i`'s set at the end: the pruning, expiry or settlement of the candidate later does not remove it. -/
@[req "SPN-33"]
theorem registered_authorized {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} {y : Fed × Federation.Step} (hy : y ∈ t) {env : Env}
    {e : Event} (ha : actor y.2 = some (i, env, e)) {c : Cand} (hc : c ∈ (step r env (y.1.worlds i) e).1.node.cands)
    {x : Nat} (hxc : x ∈ c.ladder.map (·.tx.id)) : x ∈ authorized (project i t) (f.worlds i).node := by
  induction hx with
  | init f h => cases hy
  | @next t f s hadm hx ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · refine mem_authorized.2 (.inl ⟨c, ?_, hxc⟩)
      rw [apply_of_actor r _ _ ha i]
      simpa using hc
    · exact authorized_step r f s t i (ih hy)

/-! ## The replacement reads it -/

/-- An admitted validation that names a resident as the one replaced has that resident in the set it reads
(`WTC-25`: "The resident MUST be in this node's vault-authorized set"). -/
@[req "WTC-25"]
theorem replaced_authorized {g : Package.ReplacementAncestry} {creator : Package.Creator}
    {snap : VaultUnspent.Snapshot} {mem : Package.MempoolRead} {A : List Nat} {c : Package.Candidate} {rr : Nat}
    {anc : List Nat} (h : Package.validate g creator snap mem A c (some rr) = .admitted anc) : rr ∈ A := by
  refine (Classical.em (rr ∈ A)).elim id fun hn => ?_
  have := Package.resident_unauthorized_refused g creator snap mem A c rr hn
  rw [h] at this
  cases this

/-- **On a run, a replaced resident was registered by this node** (`WTC-25`, `SPN-33`). When an honest node
`i`'s read of a composed sweep execution admits a validation that names a resident as the one replaced, as a
rung's selection and a rung's assembly do (`Ladder.ancestryTx`, `Assembly.rungCheck`), that resident's txid is
the base's or a rung's of an identity some `accept` or `clawback` step of node `i` registered. -/
@[req "WTC-25"]
theorem replaced_origin {cfg : Sweep.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : Sweep.Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) {m : Option Nat}
    {g : Package.ReplacementAncestry} {creator : Package.Creator} {snap : VaultUnspent.Snapshot}
    {mem : Package.MempoolRead} {c : Package.Candidate} {rr : Nat} {anc : List Nat}
    (h : Package.validate g creator snap mem (Ladder.readOf st T i m).A c (some rr) = .admitted anc) :
    ∃ y ∈ Sweep.fedTrace T, ∃ k, rr ∈ ids k ∧ Registers r i y k :=
  authorizedAt_origin hx hi (replaced_authorized h)

end BtcPolicy.AcceptedSet
