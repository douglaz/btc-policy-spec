import BtcPolicy.FedSilence
import BtcPolicy.Ingress
/-! `POL-20`'s admission bound over a ledgered federation run. `Ledger.bridge` takes its cuts as
given: `hnd`, `hamt`, `hinv` and `hcohort`, with no execution behind them. Here the cuts are the
honest nodes' Hot ledgers at the end of one schedule run through `FedSilence.lapply`, which is
`Federation.apply` with each kernel event taken through `Ledger.sysStep`
(`FedSilence.lrun_execution`: forgetting the ledgers of a legal schedule, from a state a
`Federation.Execution` reaches, leaves a `Federation.Execution`). Each node's cut is its ledger there and its own HotClock sample `now i`.

**What is derived.** Node `i`'s ledger is `Ledger.sysRun` over node `i`'s own events
(`Admission.lrun_sys`, `Admission.nodeTrace`), so `Ledger.liveSum_le_cap` gives `hinv` from empty
ledgers (`Admission.led_le_cap`). From an empty ledger, every row of an honest ledger is the
reservation an admitted, fresh hot acceptance at that node placed, with that spend's commitment id, `POL-11` outflow,
HotClock sample and signed expiry (`Admission.row_origin`); over a run whose acceptances are all
checked (`Ingress.CheckedTrace`), with the commitment id collision-free, that is `hamt` at every cut
(`Admission.one_amount`). `hcohort` follows for `POL-20`'s cohort, read off the run: a spend counts
at node `i` when node `i` accepted it at a reservation time inside its own interval and no prune
pass refunded that reservation by the cut (`Admission.Counted`); every such node counts it at its
cut (`Admission.counts_at_cut`), and `q` distinct honest such nodes give `q` counted cuts
(`Admission.cohort_count`). `Admission.fed_bridge` is `Ledger.bridge` with `hamt`, `hinv` and
`hcohort` discharged that way.

**What stays given.** `hnd`, that the caller's cohort list names each spend once; that each cohort
amount is a checked spend's outflow under its id (`hval`); the two ledger guard values
`Ledger.Settlement.retainOnMempool` and `Ledger.Release.acceptedAdmission`; that every HotClock
sample node `i` takes in the schedule is at or before its cut sample (`hclock`, which
`Ledger.MonotoneHotClock` gives at the node's last sample, `Admission.clock_of_monotone`); the collision-free commitment id; and
that the honest list is the honest nodes, of length `n − c`, with `q` for `t − c`.

**What is not claimed.** The cohort is admission: a reservation placed at acceptance and still
standing at the cut. The conclusion bounds admitted outflow and says nothing of exposure or
completion: no premise asks for a release, and `POL-20` says the bound "MUST NOT be presented as a
bound on funds completing or lost in an arbitrary rolling window". Which nodes are honest is not derived. -/

namespace BtcPolicy.Admission
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence

/-! ## One node's ledger in a ledgered federation run -/

/-- Node `i`'s events in a schedule, in order, as `Ledger.sysStep` takes them: each step whose
`Federation.actor` is node `i`. -/
def nodeTrace (i : Nat) : List Federation.Step → List (Env × Event)
  | [] => []
  | s :: ss =>
    match Federation.actor s with
    | some (j, env, e) => if j = i then (env, e) :: nodeTrace i ss else nodeTrace i ss
    | none => nodeTrace i ss

theorem nodeTrace_append (i : Nat) (a b : List Federation.Step) :
    nodeTrace i (a ++ b) = nodeTrace i a ++ nodeTrace i b := by
  induction a with
  | nil => rfl
  | cons s a ih =>
    simp only [List.cons_append, nodeTrace]
    split
    · split <;> simp [ih]
    · exact ih

theorem lrun_append (g : Guards) (cfg : Config) (r : Rules) (a b : List Federation.Step) :
    ∀ F : LFed, lrun g cfg r F (a ++ b) = lrun g cfg r (lrun g cfg r F a) b := by
  induction a with
  | nil => intro F; rfl
  | cons s a ih => intro F; exact ih _

theorem lapply_sys_self (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (s : Federation.Step)
    {i : Nat} {env : Env} {e : Event} (hs : Federation.actor s = some (i, env, e)) :
    (lapply g cfg r F s).sys i = (sysStep g cfg r env (F.sys i) e).1 := by
  cases s <;> simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := hs
    simp [lapply, LFed.sys, LFed.advance]

theorem lapply_sys_other (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (s : Federation.Step)
    {i : Nat} (hs : ∀ env e, Federation.actor s ≠ some (i, env, e)) :
    (lapply g cfg r F s).sys i = F.sys i := by
  cases s with
  | process j env e =>
    have hji : j ≠ i := fun h => hs env e (by simp [Federation.actor, h])
    simp [lapply, LFed.sys, LFed.advance, Ne.symm hji]
  | deliver j env m =>
    have hji : j ≠ i := fun h => hs env (.receipt m.cid m.sender) (by simp [Federation.actor, h])
    simp [lapply, LFed.sys, LFed.advance, Ne.symm hji]
  | deliverPartial j env x =>
    have hji : j ≠ i := fun h =>
      hs env (.receivePartial x.msg x.input x.signer x.cid) (by simp [Federation.actor, h])
    simp [lapply, LFed.sys, LFed.advance, Ne.symm hji]
  | _ => rfl

/-- Node `i`'s world and ledger at the end of a ledgered run are `Ledger.sysRun` over node `i`'s own
events from where it started: no other node's step and no inventory step moves them. -/
theorem lrun_sys (g : Guards) (cfg : Config) (r : Rules) (i : Nat) :
    ∀ (ss : List Federation.Step) (F : LFed),
      (lrun g cfg r F ss).sys i = (sysRun g cfg r (F.sys i) (nodeTrace i ss)).1 := by
  intro ss
  induction ss with
  | nil => intro F; rfl
  | cons s ss ih =>
    intro F
    show (lrun g cfg r (lapply g cfg r F s) ss).sys i = _
    rw [ih]
    cases hact : Federation.actor s with
    | none =>
      rw [lapply_sys_other g cfg r F s (fun env e h => by rw [hact] at h; cases h)]
      simp only [nodeTrace, hact]
    | some x =>
      obtain ⟨j, env, e⟩ := x
      by_cases hji : j = i
      · subst hji
        rw [lapply_sys_self g cfg r F s hact]
        simp only [nodeTrace, hact, if_true]
        rfl
      · rw [lapply_sys_other g cfg r F s (fun env' e' h => by
          rw [hact] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact hji h.1)]
        simp only [nodeTrace, hact, hji, if_false]

/-- `hinv`. Every honest ledger is within the cap at the end of every schedule, from a ledger within
the cap: `Ledger.liveSum_le_cap` over the node's own events. -/
@[req "POL-20"]
theorem led_le_cap (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (ss : List Federation.Step)
    (i : Nat) (h : liveSum (F.leds i) ≤ cfg.cap) : liveSum ((lrun g cfg r F ss).leds i) ≤ cfg.cap := by
  have hs := congrArg Sys.led (lrun_sys g cfg r i ss F)
  simp only [LFed.sys] at hs
  rw [hs]
  exact liveSum_le_cap g cfg r _ _ h

/-! ## Where a row comes from -/

/-- Two rows with one commitment, amount, reservation time and signed expiry: what a release, a
refund and the exposure bit leave of a row. -/
def Kin (a b : Res) : Prop :=
  a.cid = b.cid ∧ a.amount = b.amount ∧ a.reservedAt = b.reservedAt ∧ a.expiry = b.expiry

theorem Kin.trans {a b c : Res} (h₁ : Kin a b) (h₂ : Kin b c) : Kin a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

theorem kin_markExposed {n : Node} {l : Ledger} {row : Res} (h : row ∈ markExposed n l) :
    ∃ x ∈ l, Kin x row := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  refine ⟨x, hx, ?_⟩
  unfold Kin
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem mem_checked {g : Release} {env : Env} {w : Secs} {l : Ledger} {e : Event} {x : Res}
    (h : x ∈ checked g env w l e) : x ∈ l := by
  cases g with
  | everyStep => exact (List.mem_filter.1 h).1
  | acceptedAdmission =>
    simp only [checked] at h
    split at h
    · exact (List.mem_filter.1 h).1
    · exact h

theorem mem_kept {g : Release} {env : Env} {w : Secs} {l : Ledger} {e : Event} {a : Bool} {x : Res}
    (h : x ∈ kept g (checked g env w l e) l a) : x ∈ l := by
  cases g with
  | everyStep => simp only [kept] at h; exact mem_checked h
  | acceptedAdmission =>
    simp only [kept] at h
    split at h
    · exact mem_checked h
    · exact h

/-- One composed step's rows, for every value of every guard parameter: each comes from a row
before the step, or is the reservation this step's admitted hot acceptance placed, over a check
ledger that did not hold its commitment (`POL-18`'s "placed at acceptance, idempotently per
commitment"). -/
@[req "POL-18"]
theorem sysStep_row_origin (g : Guards) (cfg : Config) (r : Rules) (env : Env) (sys : Sys)
    (e : Event) {row : Res} (h : row ∈ (sysStep g cfg r env sys e).1.led) :
    (∃ x ∈ sys.led, Kin x row) ∨
      ∃ cid d E sp es, e = .accept cid d E sp es ∧
        admitted sys.world (sysStep g cfg r env sys e).1.world e = true ∧
        holds (checked g.release env cfg.window sys.led e) sp.id = false ∧
        sp.id = row.cid ∧ sp.tx.outflow = row.amount ∧ env.mono = row.reservedAt ∧
        sp.expiry = row.expiry := by
  by_cases hb : refusedByBudget cfg (checked g.release env cfg.window sys.led e) e = true
  · simp only [sysStep, hb, if_true] at h
    obtain ⟨x, hx, hk⟩ := kin_markExposed h
    exact .inl ⟨x, mem_kept hx, hk⟩
  · have hw : (sysStep g cfg r env sys e).1.world = (step r env sys.world e).1 := by
      simp only [sysStep, hb, Bool.false_eq_true, if_false]
    simp only [sysStep, hb, Bool.false_eq_true, if_false] at h
    obtain ⟨x, hx, hk⟩ := kin_markExposed h
    rw [hw]
    cases e with
    | accept cid d E sp es =>
      simp only [afterEvent] at hx
      split at hx
      · rename_i hadm
        rw [hadm, kept_of_admitted] at hx
        unfold reserve at hx
        split at hx
        · exact .inl ⟨x, mem_checked hx, hk⟩
        · rename_i hnot
          rcases List.mem_append.1 hx with hx | hx
          · exact .inl ⟨x, mem_checked hx, hk⟩
          · rw [List.mem_singleton] at hx
            subst hx
            obtain ⟨h1, h2, h3, h4⟩ := hk
            exact .inr ⟨cid, d, E, sp, es, rfl, hadm, by simpa using hnot, h1, h2, h3, h4⟩
      · exact .inl ⟨x, mem_kept hx, hk⟩
    | prune =>
      simp only [afterEvent, refundAtPrune] at hx
      exact .inl ⟨x, mem_kept (List.mem_filter.1 hx).1, hk⟩
    | settle tx =>
      simp only [afterEvent] at hx
      split at hx
      · exact .inl ⟨x, mem_kept hx, hk⟩
      · exact .inl ⟨x, mem_kept (List.mem_filter.1 hx).1, hk⟩
    | refuse cid d E pair code | receipt cid s | firePass | packageAccepted c | send c | tick | panic
    | adversaryExposes m i s c | receivePartial m i s c | clawback _ =>
      simp only [afterEvent] at hx
      exact .inl ⟨x, mem_kept hx, hk⟩

theorem actor_accept {s : Federation.Step} {i : Nat} {env : Env} {cid : Nat} {d : Bool} {E : Wall}
    {sp es : Cand} (h : Federation.actor s = some (i, env, .accept cid d E sp es)) :
    s = .process i env (.accept cid d E sp es) := by
  cases s with
  | process j env' e' =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | _ => simp [Federation.actor] at h

/-- Node `i` accepted a hot spend at this step of the schedule, after the prefix `a`: the composed
step admitted it (`Ledger.admitted`) over a check ledger that did not hold its commitment, so the
step placed its reservation at its own HotClock sample. -/
def Reserves (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (a : List Federation.Step) (i : Nat)
    (envR : Env) (cid : Nat) (d : Bool) (E : Wall) (sp es : Cand) : Prop :=
  admitted ((lrun g cfg r F a).sys i).world
      (sysStep g cfg r envR ((lrun g cfg r F a).sys i) (.accept cid d E sp es)).1.world
      (.accept cid d E sp es) = true ∧
    holds (checked g.release envR cfg.window ((lrun g cfg r F a).sys i).led (.accept cid d E sp es))
      sp.id = false

/-- **Every row has an acceptance behind it.** For every value of every guard parameter, a row of
node `i`'s ledger at the end of a schedule is a row it started with, up to `Kin`, or the
reservation a step of the schedule placed: node `i`'s admitted, fresh acceptance of a hot spend
with the row's commitment id, `POL-11` outflow, signed expiry and, as reservation time, that
step's HotClock sample. -/
@[req "POL-18"]
theorem row_origin (g : Guards) (cfg : Config) (r : Rules) (i : Nat) :
    ∀ (ss : List Federation.Step) (F : LFed) (row : Res), row ∈ (lrun g cfg r F ss).leds i →
      (∃ x ∈ F.leds i, Kin x row) ∨
        ∃ a b envR cid d E sp es, ss = a ++ .process i envR (.accept cid d E sp es) :: b ∧
          Reserves g cfg r F a i envR cid d E sp es ∧
          sp.id = row.cid ∧ sp.tx.outflow = row.amount ∧ envR.mono = row.reservedAt ∧
          sp.expiry = row.expiry := by
  intro ss
  induction ss with
  | nil => intro F row h; exact .inl ⟨row, h, rfl, rfl, rfl, rfl⟩
  | cons s ss ih =>
    intro F row h
    rcases ih (lapply g cfg r F s) row h with ⟨x, hx, hk⟩ | ⟨a, b, envR, cid, d, E, sp, es, hss, hres⟩
    · cases hact : Federation.actor s with
      | none =>
        have hl := congrArg Sys.led
          (lapply_sys_other g cfg r F s (i := i) (fun env e h => by rw [hact] at h; cases h))
        simp only [LFed.sys] at hl
        rw [hl] at hx
        exact .inl ⟨x, hx, hk⟩
      | some y =>
        obtain ⟨j, env, e⟩ := y
        by_cases hji : j = i
        · subst hji
          have hl := congrArg Sys.led (lapply_sys_self g cfg r F s hact)
          simp only [LFed.sys] at hl
          rw [hl] at hx
          rcases sysStep_row_origin g cfg r env (F.sys j) e hx with
            ⟨x', hx', hk'⟩ | ⟨cid, d, E, sp, es, rfl, hadm, hfresh, h1, h2, h3, h4⟩
          · exact .inl ⟨x', hx', hk'.trans hk⟩
          · refine .inr ⟨[], ss, env, cid, d, E, sp, es, ?_, ⟨hadm, hfresh⟩,
              h1.trans hk.1, h2.trans hk.2.1, h3.trans hk.2.2.1, h4.trans hk.2.2.2⟩
            rw [actor_accept hact]
            rfl
        · have hl := congrArg Sys.led (lapply_sys_other g cfg r F s (i := i) (fun env' e' h => by
            rw [hact] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact hji h.1))
          simp only [LFed.sys] at hl
          rw [hl] at hx
          exact .inl ⟨x, hx, hk⟩
    · exact .inr ⟨s :: a, b, envR, cid, d, E, sp, es, by rw [hss]; rfl, hres⟩

/-! ## The checked acceptance behind a row -/

theorem mem_ltrace_of_mem (g : Guards) (cfg : Config) (r : Rules) :
    ∀ (ss : List Federation.Step) (t : Federation.Trace) (F : LFed) {y : Federation.Fed × Federation.Step},
      y ∈ t → y ∈ ltrace g cfg r t F ss := by
  intro ss
  induction ss with
  | nil => intro t F y h; exact h
  | cons s ss ih => intro t F y h; exact ih _ _ (List.mem_cons_of_mem _ h)

theorem mem_ltrace (g : Guards) (cfg : Config) (r : Rules) (s : Federation.Step)
    (b : List Federation.Step) :
    ∀ (a : List Federation.Step) (t : Federation.Trace) (F : LFed),
      ((lrun g cfg r F a).fed, kernelStep g cfg (lrun g cfg r F a) s) ∈ ltrace g cfg r t F (a ++ s :: b) := by
  intro a
  induction a with
  | nil => intro t F; exact mem_ltrace_of_mem g cfg r b _ _ List.mem_cons_self
  | cons s' a ih => intro t F; exact ih _ _

/-- An admitted acceptance is the event the forgotten run carries: the budget check did not turn
it into a staged refusal. -/
theorem kernelStep_admitted {g : Guards} {cfg : Config} {r : Rules} {F : LFed} {a : List Federation.Step}
    {i : Nat} {envR : Env} {cid : Nat} {d : Bool} {E : Wall} {sp es : Cand}
    (h : Reserves g cfg r F a i envR cid d E sp es) :
    kernelStep g cfg (lrun g cfg r F a) (.process i envR (.accept cid d E sp es)) =
      .process i envR (.accept cid d E sp es) := by
  have hb := admitted_not_budget_refused g cfg r envR ((lrun g cfg r F a).sys i) cid d E sp es h.1
  simp only [LFed.sys] at hb
  simp only [kernelStep, kernelEvent, hb, Bool.false_eq_true, if_false]

/-- Every row of an honest ledger, from empty ledgers, is the reservation of a checked spend: one
`Ingress.check` accepted, with the row's commitment id, outflow and signed expiry. -/
@[req "POL-18"]
theorem row_checked {g : Guards} {cfg : Config} {r : Rules} {F : LFed} {ss : List Federation.Step}
    {t : Federation.Trace} {ctx : Ingress.Ctx} (hc : Ingress.CheckedTrace ctx (ltrace g cfg r t F ss))
    {i : Nat} (h0 : F.leds i = []) {row : Res} (hrow : row ∈ (lrun g cfg r F ss).leds i) :
    ∃ q sp es, Ingress.check ctx true q = .accepted sp es ∧ sp.id = row.cid ∧
      sp.tx.outflow = row.amount ∧ sp.expiry = row.expiry := by
  rcases row_origin g cfg r i ss F row hrow with ⟨x, hx, -⟩ | ⟨a, b, envR, cid, d, E, sp, es, hss, hres, h1, h2, -, h4⟩
  · rw [h0] at hx; cases hx
  · have hm := mem_ltrace g cfg r (.process i envR (.accept cid d E sp es)) b a t F
    rw [← hss, kernelStep_admitted hres] at hm
    obtain ⟨q, hq⟩ := hc.1 _ hm i envR cid d E sp es rfl
    exact ⟨q, sp, es, hq, h1, h2, h4⟩

/-- The honest nodes' cuts at the end of a ledgered run: each ledger, at that node's own HotClock
sample. -/
def cuts (F : LFed) (honest : List Nat) (now : Nat → Mono) : List NodeCut :=
  honest.map fun i => { led := F.leds i, now := now i }

/-- `hamt`, at every honest cut. From empty ledgers, over a run whose acceptances are all checked
and with the commitment id collision-free, a row under a cohort spend's id has that spend's amount,
when the cohort amount is a checked spend's outflow under that id (`hval`). -/
@[req "POL-20"]
theorem one_amount {g : Guards} {cfg : Config} {r : Rules} {F : LFed} {ss : List Federation.Step}
    {t : Federation.Trace} {ctx : Ingress.Ctx} (hc : Ingress.CheckedTrace ctx (ltrace g cfg r t F ss))
    (hid : ∀ a b, ctx.commitId a = ctx.commitId b → a = b) {honest : List Nat}
    (h0 : ∀ i ∈ honest, F.leds i = []) (now : Nat → Mono) {cohort : List Ledgers.Spend}
    (hval : ∀ s ∈ cohort, ∃ fits q sp es, Ingress.check ctx fits q = .accepted sp es ∧
      sp.id = s.1 ∧ sp.tx.outflow = s.2) :
    ∀ k ∈ cuts (lrun g cfg r F ss) honest now, ∀ s ∈ cohort, ∀ row ∈ k.led,
      row.cid = s.1 → row.amount = s.2 := by
  intro k hk s hs row hrow hcid
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
  obtain ⟨q', sp', es', hq', h1, h2, -⟩ := row_checked hc (h0 i hi) hrow
  obtain ⟨fits, q, sp, es, hq, hid1, hout⟩ := hval s hs
  have htx := (Ingress.one_amount_per_commitment hid hq hq' (by rw [hid1, ← hcid, h1])).1
  rw [← h2, ← htx, hout]

/-! ## `POL-20`'s cohort, read off the run -/

/-- `POL-20`'s count at node `i`, read off the run: node `i` "accepted at a reservation time inside
that node's own interval" — an admitted, fresh acceptance of a spend with this id (`Reserves`), at a
HotClock sample inside the interval ending at the cut sample `now` — "counting only reservations
not refunded while unexposed by the cut": every prune pass node `i` takes after it keeps that
reservation (`Ledger.pruneKeeps`). `Mono.withinWindow` reads the interval's lower end only; that the
sample is at or before `now` is `hclock`'s, in the theorems that read this. -/
@[req "POL-20"]
def Counted (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (ss : List Federation.Step)
    (i id : Nat) (now : Mono) : Prop :=
  ∃ a b envR cid d E sp es, ss = a ++ .process i envR (.accept cid d E sp es) :: b ∧ sp.id = id ∧
    Reserves g cfg r F a i envR cid d E sp es ∧
    Mono.withinWindow envR.mono now cfg.window = true ∧
    pruneKeeps g cfg r sp.id envR.mono
      (sysStep g cfg r envR ((lrun g cfg r F a).sys i) (.accept cid d E sp es)).1 (nodeTrace i b) = true

/-- **A counted spend is charged at the cut.** Under the current settlement and release values,
when every HotClock sample node `i` takes is at or before its cut sample, a spend `Counted` at node
`i` is counted there by `Ledger.countsAt`: no release in between takes the reservation
(`Ledger.hasReservation_sysRun`). -/
@[req "POL-20"]
theorem counts_at_cut {g : Guards} (hs : g.settlement = .retainOnMempool)
    (hr : g.release = .acceptedAdmission) {cfg : Config} {r : Rules} {F : LFed}
    {ss : List Federation.Step} {i id : Nat} {now : Mono}
    (hclock : ∀ x ∈ nodeTrace i ss, x.1.mono.notAfter now = true)
    (h : Counted g cfg r F ss i id now) :
    countsAt cfg.window id { led := (lrun g cfg r F ss).leds i, now := now } = true := by
  obtain ⟨a, b, envR, cid, d, E, sp, es, rfl, rfl, ⟨ha, hfresh⟩, hwin, hprune⟩ := h
  have hreserved := admitted_reserves g cfg r envR ((lrun g cfg r F a).sys i) cid d E sp es ha hfresh
  have htrace : nodeTrace i (a ++ .process i envR (.accept cid d E sp es) :: b) =
      nodeTrace i a ++ (envR, .accept cid d E sp es) :: nodeTrace i b := by
    rw [nodeTrace_append]; simp [nodeTrace, Federation.actor]
  have hsamples : ∀ x ∈ nodeTrace i b, x.1.mono.notAfter now = true :=
    fun x hx => hclock x (by rw [htrace]; simp [hx])
  have hfinal := hasReservation_sysRun g hs hr cfg r sp.id envR.mono now hwin (nodeTrace i b) _
    hsamples hprune hreserved
  have hl : (lrun g cfg r F (a ++ .process i envR (.accept cid d E sp es) :: b)).leds i =
      (sysRun g cfg r (sysStep g cfg r envR ((lrun g cfg r F a).sys i) (.accept cid d E sp es)).1
        (nodeTrace i b)).1.led := by
    rw [lrun_append]
    have h1 := lrun_sys g cfg r i b
      (lapply g cfg r (lrun g cfg r F a) (.process i envR (.accept cid d E sp es)))
    rw [lapply_sys_self g cfg r _ (.process i envR (.accept cid d E sp es)) rfl] at h1
    exact congrArg Sys.led h1
  rw [hl]
  obtain ⟨row, hrow, hp⟩ := List.any_eq_true.1 hfinal
  have hp' : row.cid = sp.id ∧ row.reservedAt = envR.mono := by simpa using hp
  exact List.any_eq_true.2 ⟨row, hrow, by simp [hp'.1, hp'.2, hwin]⟩

theorem length_le_countP {p : Nat → Bool} :
    ∀ (acc honest : List Nat), acc.Nodup → (∀ i ∈ acc, i ∈ honest) → (∀ i ∈ acc, p i = true) →
      acc.length ≤ honest.countP p
  | [], _, _, _, _ => Nat.zero_le _
  | j :: rest, honest, hnd, hsub, hp => by
    obtain ⟨hj, hrest⟩ := List.nodup_cons.1 hnd
    have hjm := hsub j List.mem_cons_self
    rw [(List.perm_cons_erase hjm).countP_eq p, List.countP_cons, if_pos (hp j List.mem_cons_self),
      List.length_cons]
    have := length_le_countP rest (honest.erase j) hrest
      (fun i hi => (List.mem_erase_of_ne (fun (h : i = j) => hj (h ▸ hi))).2
        (hsub i (List.mem_cons_of_mem _ hi)))
      (fun i hi => hp i (List.mem_cons_of_mem _ hi))
    omega

/-- `hclock` from `Ledger.MonotoneHotClock`, at the last sample of the node's own events. -/
@[req "POL-19"]
theorem clock_of_monotone {i : Nat} {ss : List Federation.Step} {pre : List (Env × Event)}
    {last : Env × Event} (htr : nodeTrace i ss = pre ++ [last])
    (hm : MonotoneHotClock (pre ++ [last])) :
    ∀ x ∈ nodeTrace i ss, x.1.mono.notAfter last.1.mono = true := by
  rw [htr]
  exact mono_le_last pre last hm

/-- **The cross-node count.** `q` distinct honest nodes at which a spend is `Counted` give `q`
honest cuts that count it: `hcohort`'s count for that spend. -/
@[req "POL-20"]
theorem cohort_count {g : Guards} (hs : g.settlement = .retainOnMempool)
    (hr : g.release = .acceptedAdmission) {cfg : Config} {r : Rules} {F : LFed}
    {ss : List Federation.Step} {honest : List Nat} {now : Nat → Mono}
    (hclock : ∀ i ∈ honest, ∀ x ∈ nodeTrace i ss, x.1.mono.notAfter (now i) = true)
    {id : Nat} {acc : List Nat} (hnd : acc.Nodup) (hsub : ∀ i ∈ acc, i ∈ honest)
    (hc : ∀ i ∈ acc, Counted g cfg r F ss i id (now i)) :
    acc.length ≤ cohortCount cfg.window (cuts (lrun g cfg r F ss) honest now) id := by
  unfold cohortCount cuts
  rw [List.countP_map]
  exact length_le_countP acc honest hnd hsub fun i hi =>
    counts_at_cut hs hr (hclock i (hsub i hi)) (hc i hi)

/-- **`POL-20`'s bound over a ledgered federation run.** `Ledger.bridge` at the honest nodes' cuts
at the end of one schedule, from empty ledgers, with `hinv` (`led_le_cap`), `hamt` (`one_amount`)
and `hcohort` (`cohort_count`) derived. Given: `hs`, `hr`, the checked acceptances `hc`, the
collision-free commitment id `hid`, `hnd`, `hval`, `hclock`, and for each cohort spend `q` distinct
honest nodes at which it is `Counted`. Which nodes are honest, and `q` and `honest.length` as
`t − c` and `n − c`, remain the caller's. -/
@[req "POL-20"]
theorem fed_bridge {g : Guards} (hs : g.settlement = .retainOnMempool)
    (hr : g.release = .acceptedAdmission) {cfg : Config} {r : Rules} {F : LFed}
    {ss : List Federation.Step} {t : Federation.Trace} {honest : List Nat}
    (h0 : ∀ i ∈ honest, F.leds i = []) {ctx : Ingress.Ctx}
    (hc : Ingress.CheckedTrace ctx (ltrace g cfg r t F ss))
    (hid : ∀ a b, ctx.commitId a = ctx.commitId b → a = b) (q : Nat) (cohort : List Ledgers.Spend)
    (hnd : (cohort.map (·.1)).Nodup)
    (hval : ∀ s ∈ cohort, ∃ fits qr sp es, Ingress.check ctx fits qr = .accepted sp es ∧
      sp.id = s.1 ∧ sp.tx.outflow = s.2)
    (now : Nat → Mono) (hclock : ∀ i ∈ honest, ∀ x ∈ nodeTrace i ss, x.1.mono.notAfter (now i) = true)
    (hcount : ∀ s ∈ cohort, ∃ acc : List Nat, acc.Nodup ∧ q ≤ acc.length ∧
      ∀ i ∈ acc, i ∈ honest ∧ Counted g cfg r F ss i s.1 (now i)) :
    q * Ledgers.outflow cohort ≤ honest.length * cfg.cap := by
  have h := bridge cfg q cohort (cuts (lrun g cfg r F ss) honest now) hnd
    (one_amount hc hid h0 now hval)
    (by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      exact led_le_cap g cfg r F ss i (by rw [h0 i hi]; exact Nat.zero_le _))
    (by
      intro s hs'
      obtain ⟨acc, hnd', hq, hacc⟩ := hcount s hs'
      exact Nat.le_trans hq (cohort_count hs hr hclock hnd' (fun i hi => (hacc i hi).1)
        (fun i hi => (hacc i hi).2)))
  simpa [cuts] using h

end BtcPolicy.Admission
