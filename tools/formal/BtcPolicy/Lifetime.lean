import BtcPolicy.Ingress
import BtcPolicy.Ledger
/-! Ingress lifetime seams: `SPN-31`'s in-flight marker, `SPN-45`'s refresh subordination, and
`SPN-29`'s unwind of a refused registration, over checked ingress (`Ingress.check`) and the composed
node and Hot ledger (`Ledger.sysStep`).

**The abstract atomicity.** `Section` names the transitions, and `Section.frame` says which of the
three state components each one writes; `step_frame` proves that no step writes outside its frame.
The registration hold is ONE transition from gate 15 to gate 30 of `SPN-5`: gate 24's placement,
the Escape's checks, gate 27, signing, registration, the unwind `SPN-29` requires when registration
refuses, the Carrier's staging, the pending log's entry (`SPN-30`) and the marker's release. In it
the ledger places a row only where registration accepts, so `SPN-29`'s "only a reservation placed by
this request MUST be unwound in the same step" has no intermediate state to be visible in. A finer
model that splits the hold must show that no other section writes the ledger, the registry, the
pending log or the marker set between its parts. `SPN-20`'s three lock sections are not modelled as
locks, and no fairness is assumed.

**What is proved.** Under `SPN-45`'s predicate (`Subordination.pendingAndMarker`), no refresh
registers while a spend's marker is held, whatever else interleaves
(`refresh_subordinated_in_preflight`, `no_refresh_after_claim`). Every exit, including a panic
unwind, releases the marker it claimed (`exit_releases`, `claim_exit_restores`). The hold that
releases the marker and accepts a fresh pair writes the spend's pending entry in the same
transition, so subordination passes from the marker to the pending log with no gap
(`hold_logs_spend`). Under the current release point, a hold that does not accept leaves every
ledger row as it was apart from the exposure bit (`hold_refusal_keeps_rows`): a refused retry of a
commitment leaves the earlier acceptance's row unchanged and places none of its own, and every row
its check found releasable stays charged (`hold_refusal_keeps_charges`). A hold that accepts
charges the spend (`hold_admitted_charges`).

**The marker is needed.** Under `DEF-7`'s reading, `Subordination.pendingOnly`, a refresh over the
Escape's input registers during the spend's preflight and both stay registered
(`Exhibits.Lifetime.preflight_race_without_marker`).

**What is not modelled.** A refresh's own gates other than Lockdown and subordination are one
supplied verdict (`Op.refresh`'s `ok`), and a registered refresh is kept beside the registry
(`St.refreshes`): its broadcast, settlement and replacement are not modelled. The ingress and commit
holds' writes (the nonce log, `D`, the PIN budget, `DUR-4`'s intent) are outside; the kernel writes
the Carrier at the registration hold. An exit before the registration hold that stages a refusal is
its own `Op.kernel` refusal followed by `Op.exit`. `Op.kernel` admits any kernel event, an unchecked
`accept` included, and the theorems hold over it. -/

namespace BtcPolicy.Lifetime
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## The guard parameter -/

/-- What refresh subordination consults. `SPN-45`: "A refresh MUST be refused
`REFRESH_SUBORDINATED` / `refresh_subordination` while ANY spend is pending on this node — the
pending log has any live entry, or a spend's in-flight marker (`SPN-31`) is held."

`pendingOnly` is the reading of `DEF-7`, which says "Refresh subordination required the spend to be
registered". -/
inductive Subordination
  | pendingAndMarker | pendingOnly
  deriving DecidableEq, Repr

def current : Subordination := .pendingAndMarker

/-! ## State and operations -/

/-- One node's lifetime state: the composed node and Hot ledger, `SPN-31`'s in-flight markers by
request, and the refreshes this node registered. -/
structure St where
  sys : Ledger.Sys
  /-- `SPN-31`'s markers: one entry per spend request from its claim to its exit. -/
  inFlight : List Nat := []
  /-- The refresh transactions this node registered (`SPN-43`), newest first. -/
  refreshes : List Tx := []
  deriving DecidableEq, Repr

/-- How a spend request leaves before its registration hold: a refusal, or a panic unwind. -/
inductive Exit
  | refused | panic
  deriving DecidableEq, Repr

/-- One transition. `k` names a spend request. -/
inductive Op
  /-- The end of the commit hold: `SPN-31`, "Before its chain preflight begins, a spend MUST claim
  an **in-flight marker**". -/
  | claim (k : Nat)
  /-- The registration hold of request `k`, checked by `Ingress.check`, ending its marker. -/
  | hold (k : Nat) (env : Env) (cid : Nat) (duress : Bool) (E : Wall) (q : Ingress.Request)
  /-- An exit of request `k` before its registration hold: `SPN-31`, "released on every exit
  including a panic unwind". -/
  | exit (k : Nat) (why : Exit)
  /-- A RefreshRequest at `SPN-43`'s second lock section; `ok` is its other gates' verdict. -/
  | refresh (env : Env) (tx : Tx) (ok : Bool)
  /-- Any other kernel event, through the composed step. -/
  | kernel (env : Env) (e : Event)
  deriving DecidableEq, Repr

/-- Whether an operation ends request `k`'s marker. -/
def Op.ends (k : Nat) : Op → Bool
  | .hold j .. => j == k
  | .exit j _ => j == k
  | _ => false

/-! ## The abstract atomicity -/

/-- The sections this model takes as one transition each. -/
@[req "SPN-20"]
inductive Section
  /-- The marker's claim at the end of the commit hold. -/
  | claim
  /-- Gates 15 to 30 of `SPN-5`, the marker's release with them. -/
  | registrationHold
  /-- The marker's release at an exit before the registration hold. -/
  | exit
  /-- `SPN-43`'s second lock section, from Lockdown through registration. -/
  | refreshHold
  /-- One kernel event other than ingress. -/
  | kernel
  deriving DecidableEq, Repr

def Op.section : Op → Section
  | .claim _ => .claim
  | .hold .. => .registrationHold
  | .exit .. => .exit
  | .refresh .. => .refreshHold
  | .kernel .. => .kernel

/-- The state components a section may write: the node with its ledger, the marker set, the
registered refreshes. -/
structure Frame where
  sys : Bool
  markers : Bool
  refreshes : Bool
  deriving DecidableEq, Repr

/-- The abstract atomicity: what each one-transition section writes. -/
@[req "SPN-20"]
def Section.frame : Section → Frame
  | .claim => ⟨false, true, false⟩
  | .registrationHold => ⟨true, true, false⟩
  | .exit => ⟨false, true, false⟩
  | .refreshHold => ⟨false, false, true⟩
  | .kernel => ⟨true, false, false⟩

/-! ## The step -/

/-- The fixed parameters of one node: the subordination value, the ledger's guards and sealed
parameters, the kernel's rules, the checking context. -/
structure Cfg where
  g : Subordination
  lg : Ledger.Guards
  cfg : Ledger.Config
  r : Rules
  ctx : Ingress.Ctx

/-- The candidates `Ingress.check` derives from a request. -/
def spendOf (ctx : Ingress.Ctx) (q : Ingress.Request) : Cand := Ingress.cand ctx q q.spend true q.fireAt
def escapeOf (ctx : Ingress.Ctx) (q : Ingress.Request) : Cand := Ingress.cand ctx q q.escape false none

/-- Gate 24's verdict, as `Ledger.sysStep` decides it on the `accept` event: `Ledger.admits` over the
ledger `Ledger.checked` leaves at this step. -/
@[req "POL-16"]
def fits (c : Cfg) (env : Env) (l : Ledger.Ledger) (cid : Nat) (d : Bool) (E : Wall)
    (q : Ingress.Request) : Bool :=
  let e := Event.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)
  !Ledger.refusedByBudget c.cfg (Ledger.checked c.lg.release env c.cfg.window l e) e

def verdict (c : Cfg) (env : Env) (l : Ledger.Ledger) (cid : Nat) (d : Bool) (E : Wall)
    (q : Ingress.Request) : Ingress.Verdict :=
  Ingress.check c.ctx (fits c env l cid d E q) q

/-- The registration hold: the checked verdict's kernel event through `Ledger.sysStep`, or no
transition, and the marker released. -/
@[req "SPN-29"]
def hold (c : Cfg) (st : St) (k : Nat) (env : Env) (cid : Nat) (d : Bool) (E : Wall)
    (q : Ingress.Request) : St :=
  { st with
    sys := match (verdict c env st.sys.led cid d E q).event cid d E with
      | some e => (Ledger.sysStep c.lg c.cfg c.r env st.sys e).1
      | none => st.sys
    inFlight := st.inFlight.erase k }

/-- `SPN-45`'s predicate at a refresh's sample: the pending log lists an entry (`Kernel.pending`), or,
under `pendingAndMarker`, a marker is held. -/
@[req "SPN-45"]
def subordinated (g : Subordination) (r : Rules) (env : Env) (st : St) : Bool :=
  !(pending r env st.sys.world.node).isEmpty || (g == .pendingAndMarker && !st.inFlight.isEmpty)

/-- A refresh registers when its other gates pass, the node is not locked down (`SPN-6`) and it is
not subordinated; otherwise it is refused and nothing moves. -/
@[req "SPN-45"]
def refreshHold (c : Cfg) (st : St) (env : Env) (tx : Tx) (ok : Bool) : St :=
  if ok && !st.sys.world.node.lockedDown && !subordinated c.g c.r env st then
    { st with refreshes := tx :: st.refreshes }
  else st

@[req "SPN-31"]
def step (c : Cfg) (st : St) : Op → St
  | .claim k => { st with inFlight := k :: st.inFlight }
  | .hold k env cid d E q => hold c st k env cid d E q
  | .exit k _ => { st with inFlight := st.inFlight.erase k }
  | .refresh env tx ok => refreshHold c st env tx ok
  | .kernel env e => { st with sys := (Ledger.sysStep c.lg c.cfg c.r env st.sys e).1 }

def run (c : Cfg) : St → List Op → St
  | st, [] => st
  | st, o :: os => run c (step c st o) os

/-- No step writes outside its section's frame. -/
@[req "SPN-20"]
theorem step_frame (c : Cfg) (st : St) (o : Op) :
    (o.section.frame.sys = false → (step c st o).sys = st.sys) ∧
    (o.section.frame.markers = false → (step c st o).inFlight = st.inFlight) ∧
    (o.section.frame.refreshes = false → (step c st o).refreshes = st.refreshes) := by
  have no : ∀ {p : Prop}, true = false → p := fun h => absurd h (by decide)
  cases o with
  | claim k => exact ⟨fun _ => rfl, fun h => no h, fun _ => rfl⟩
  | hold k env cid d E q => exact ⟨fun h => no h, fun h => no h, fun _ => rfl⟩
  | exit k w => exact ⟨fun _ => rfl, fun h => no h, fun _ => rfl⟩
  | refresh env tx ok =>
    refine ⟨fun _ => ?_, fun _ => ?_, fun h => no h⟩ <;>
      simp only [step, refreshHold] <;> split <;> rfl
  | kernel env e => exact ⟨fun h => no h, fun _ => rfl, fun _ => rfl⟩

/-! ## The marker -/

theorem step_keeps_marker (c : Cfg) (st : St) (o : Op) (k : Nat) (hk : k ∈ st.inFlight)
    (ho : o.ends k = false) : k ∈ (step c st o).inFlight := by
  cases o with
  | claim j => exact List.mem_cons_of_mem _ hk
  | hold j env cid d E q =>
    have hne : k ≠ j := fun h => by simp [Op.ends, h] at ho
    exact (List.mem_erase_of_ne hne).2 hk
  | exit j w =>
    have hne : k ≠ j := fun h => by simp [Op.ends, h] at ho
    exact (List.mem_erase_of_ne hne).2 hk
  | refresh env tx ok =>
    simp only [step, refreshHold]; split <;> exact hk
  | kernel env e => exact hk

theorem step_refreshes_of_marker (c : Cfg) (hg : c.g = .pendingAndMarker) (st : St) (o : Op)
    (k : Nat) (hk : k ∈ st.inFlight) : (step c st o).refreshes = st.refreshes := by
  cases o with
  | refresh env tx ok =>
    have hs : subordinated c.g c.r env st = true := by
      have : st.inFlight.isEmpty = false := by
        cases h : st.inFlight with
        | nil => rw [h] at hk; cases hk
        | cons _ _ => rfl
      simp [subordinated, hg, this]
    simp [step, refreshHold, hs]
  | _ => rfl

/-- `SPN-31` and `SPN-45`: while a spend's marker is held, no refresh registers, whatever other
requests, refreshes and kernel events interleave, and the marker stays held, until an operation that
ends it. -/
@[req "SPN-31"]
theorem refresh_subordinated_in_preflight (c : Cfg) (hg : c.g = .pendingAndMarker) (k : Nat) :
    ∀ (ops : List Op) (st : St), k ∈ st.inFlight → (∀ o ∈ ops, o.ends k = false) →
      (run c st ops).refreshes = st.refreshes ∧ k ∈ (run c st ops).inFlight
  | [], _, hk, _ => ⟨rfl, hk⟩
  | o :: os, st, hk, hops => by
    have ho := hops o List.mem_cons_self
    obtain ⟨h1, h2⟩ := refresh_subordinated_in_preflight c hg k os (step c st o)
      (step_keeps_marker c st o k hk ho) (fun x hx => hops x (List.mem_cons_of_mem _ hx))
    exact ⟨h1.trans (step_refreshes_of_marker c hg st o k hk), h2⟩

/-- From a spend's claim to the operation that ends it, no refresh registers. -/
@[req "SPN-45"]
theorem no_refresh_after_claim (c : Cfg) (hg : c.g = .pendingAndMarker) (k : Nat) (st : St)
    (ops : List Op) (hops : ∀ o ∈ ops, o.ends k = false) :
    (run c st (.claim k :: ops)).refreshes = st.refreshes :=
  (refresh_subordinated_in_preflight c hg k ops _ List.mem_cons_self hops).1

/-- Every operation that ends a marker releases it, a panic unwind included. -/
@[req "SPN-31"]
theorem exit_releases (c : Cfg) (st : St) (o : Op) (k : Nat) (ho : o.ends k = true) :
    (step c st o).inFlight = st.inFlight.erase k := by
  cases o with
  | hold j env cid d E q =>
    have : j = k := by simpa [Op.ends] using ho
    subst this; rfl
  | exit j w =>
    have : j = k := by simpa [Op.ends] using ho
    subst this; rfl
  | _ => simp [Op.ends] at ho

/-- A claim and the exit that ends it leave the marker set as it was before the claim. -/
@[req "SPN-31"]
theorem claim_exit_restores (c : Cfg) (st : St) (o : Op) (k : Nat) (ho : o.ends k = true) :
    (step c (step c st (.claim k)) o).inFlight = st.inFlight := by
  rw [exit_releases c _ o k ho]
  exact List.erase_cons_head k st.inFlight

/-! ## The registration hold -/

/-- The kernel event a hold runs: none, a staged refusal, or the checked pair. -/
theorem hold_event (c : Cfg) (env : Env) (l : Ledger.Ledger) (cid : Nat) (d : Bool) (E : Wall)
    (q : Ingress.Request) :
    (verdict c env l cid d E q).event cid d E = none ∨
    (∃ code pair, (verdict c env l cid d E q).event cid d E = some (.refuse cid d E (some pair) code)) ∨
    (verdict c env l cid d E q).event cid d E =
      some (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) := by
  generalize hv : verdict c env l cid d E q = v
  cases v with
  | malformed => exact .inl rfl
  | refused code => exact .inl rfl
  | staged code pair => exact .inr (.inl ⟨code, pair, rfl⟩)
  | accepted sp es =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl, rfl⟩ := Ingress.accepted_validates hv
    exact .inr (.inr rfl)

/-- A ledger's rows without the exposure bit. -/
def rows (l : Ledger.Ledger) : List (Nat × Nat × Mono × Wall) :=
  l.map fun x => (x.cid, x.amount, x.reservedAt, x.expiry)

theorem rows_markExposed (n : Node) (l : Ledger.Ledger) : rows (Ledger.markExposed n l) = rows l := by
  unfold rows Ledger.markExposed
  rw [List.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  split <;> rfl

theorem holds_of_rows {l l' : Ledger.Ledger} (h : rows l = rows l') (cm : Nat) :
    Ledger.holds l cm = Ledger.holds l' cm := by
  have e : ∀ m : Ledger.Ledger, Ledger.holds m cm = (rows m).any (·.1 == cm) := by
    intro m; simp only [Ledger.holds, rows, List.any_map]; rfl
  rw [e, e, h]

/-- `SPN-29` on the checked path: a registration hold that does not leave an accepted Carrier for
its pair — any refusal, a refused registration included — leaves every ledger row as it was apart
from the exposure bit. Under the current release point, the value the statement names. -/
@[req "SPN-29"]
theorem hold_refusal_keeps_rows (c : Cfg) (hrel : c.lg.release = .acceptedAdmission) (st : St)
    (k : Nat) (env : Env) (cid : Nat) (d : Bool) (E : Wall) (q : Ingress.Request)
    (hno : Ledger.admitted st.sys.world (hold c st k env cid d E q).sys.world
      (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) = false) :
    rows (hold c st k env cid d E q).sys.led = rows st.sys.led := by
  rcases hold_event c env st.sys.led cid d E q with he | ⟨code, pair, he⟩ | he
  · simp only [hold, he]
  · simp only [hold, he, Ledger.sysStep, Ledger.refusedByBudget, Bool.false_eq_true, if_false,
      rows_markExposed, Ledger.afterEvent, Ledger.admitted, Ledger.kept, hrel]
  · simp only [hold, he] at hno ⊢
    simp only [Ledger.sysStep] at hno ⊢
    split
    · rw [rows_markExposed, hrel]; rfl
    · rename_i hb
      rw [if_neg hb] at hno
      simp only [rows_markExposed, Ledger.afterEvent, hno, Ledger.kept, hrel, Bool.false_eq_true,
        if_false]

/-- `SPN-29`, `POL-18` and `POL-19` on the checked path: a hold that does not accept leaves every
commitment charged exactly where it was, so a refused retry of a commitment leaves the earlier
acceptance's row with its amount, reservation time and expiry, and places none of its own; and
every row the request's admission check found releasable stays charged. -/
@[req "POL-18"]
theorem hold_refusal_keeps_charges (c : Cfg) (hrel : c.lg.release = .acceptedAdmission) (st : St)
    (k : Nat) (env : Env) (cid : Nat) (d : Bool) (E : Wall) (q : Ingress.Request)
    (hno : Ledger.admitted st.sys.world (hold c st k env cid d E q).sys.world
      (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) = false) :
    (∀ cm, Ledger.holds (hold c st k env cid d E q).sys.led cm = Ledger.holds st.sys.led cm) ∧
    ∀ row ∈ st.sys.led, ∃ row' ∈ (hold c st k env cid d E q).sys.led,
      row'.cid = row.cid ∧ row'.amount = row.amount ∧ row'.reservedAt = row.reservedAt ∧
        row'.expiry = row.expiry := by
  have h := hold_refusal_keeps_rows c hrel st k env cid d E q hno
  refine ⟨holds_of_rows h, fun row hrow => ?_⟩
  have hm : (row.cid, row.amount, row.reservedAt, row.expiry) ∈
      rows (hold c st k env cid d E q).sys.led := by
    rw [h]; exact List.mem_map.2 ⟨row, hrow, rfl⟩
  obtain ⟨row', hrow', he⟩ := List.mem_map.1 hm
  simp only [Prod.mk.injEq] at he
  exact ⟨row', hrow', he.1, he.2.1, he.2.2.1, he.2.2.2⟩

/-- The world a hold leaves: unchanged, a staged refusal's, or the kernel's acceptance of the checked
pair. -/
theorem hold_world (c : Cfg) (st : St) (k : Nat) (env : Env) (cid : Nat) (d : Bool) (E : Wall)
    (q : Ingress.Request) :
    (hold c st k env cid d E q).sys.world = st.sys.world ∨
    (∃ pair, (hold c st k env cid d E q).sys.world =
      { st.sys.world with node := refuse c.r env st.sys.world.node cid d E pair }) ∨
    (hold c st k env cid d E q).sys.world =
      { st.sys.world with node := accept c.r env st.sys.world.node cid d E (spendOf c.ctx q)
                                    (escapeOf c.ctx q) } := by
  rcases hold_event c env st.sys.led cid d E q with he | ⟨code, pair, he⟩ | he
  · exact .inl (by simp only [hold, he])
  · exact .inr (.inl ⟨some pair, by simp only [hold, he, Ledger.sysStep, Ledger.refusedByBudget,
      Bool.false_eq_true, if_false, Kernel.step]⟩)
  · simp only [hold, he, Ledger.sysStep]
    split
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inr (.inr rfl)

/-- An acceptance that leaves an accepted Carrier the node did not have took the registration
branch, so it wrote `Kernel.logRegistration`. -/
theorem accept_log_of_admitted {r : Rules} {env : Env} {n : Node} {cid : Nat} {d : Bool}
    {E : Wall} {sp es : Cand}
    (hacc : (accept r env n cid d E sp es).carriers.any (fun k => k.cid == cid && k.accepted) = true)
    (hnew : n.carriers.any (·.cid == cid) = false) :
    (accept r env n cid d E sp es).pendingLog = logRegistration r n sp es := by
  unfold accept at hacc ⊢
  split
  · rename_i hg
    rw [if_pos hg] at hacc
    exact absurd (Ledger.refuse_accepted hacc) (by simp [hnew])
  · rename_i hg
    rw [if_neg hg] at hacc
    split
    · rename_i hD
      rw [hD] at hacc
      obtain ⟨k, hk, hp⟩ := List.any_eq_true.1 hacc
      have : n.carriers.any (·.cid == cid) = true :=
        List.any_eq_true.2 ⟨k, hk, by simp only [Bool.and_eq_true] at hp; exact hp.1⟩
      rw [hnew] at this; cases this
    · rfl

/-- A hold that leaves an accepted Carrier the node did not have ran the checked pair's
acceptance. -/
theorem hold_admitted_accept (c : Cfg) (st : St) (k : Nat) (env : Env) (cid : Nat) (d : Bool)
    (E : Wall) (q : Ingress.Request)
    (ha : Ledger.admitted st.sys.world (hold c st k env cid d E q).sys.world
      (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) = true) :
    (hold c st k env cid d E q).sys.world =
      { st.sys.world with node := accept c.r env st.sys.world.node cid d E (spendOf c.ctx q)
                                    (escapeOf c.ctx q) } ∧
    st.sys.world.node.carriers.any (·.cid == cid) = false := by
  simp only [Ledger.admitted, Bool.and_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨-, hacc⟩, hnew⟩ := ha
  rcases hold_world c st k env cid d E q with hw | ⟨pair, hw⟩ | hw
  · rw [hw] at hacc
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.1 hacc
    have : st.sys.world.node.carriers.any (·.cid == cid) = true :=
      List.any_eq_true.2 ⟨x, hx, by simp only [Bool.and_eq_true] at hp; exact hp.1⟩
    rw [hnew] at this; cases this
  · rw [hw] at hacc
    exact absurd (Ledger.refuse_accepted hacc) (by simp [hnew])
  · exact ⟨hw, hnew⟩

/-- `SPN-30` and `SPN-31`, the handoff: the hold that releases a spend's marker and accepts a fresh
pair writes the spend's pending entry in the same transition, so at every sample through the
spend's expiry the pending log lists it and every refresh is subordinated, under either reading of
`SPN-45`. Fresh: the spend is not resident, and the log neither holds it nor has seen a settlement
clear it. Under `Rules.pendingSource = .record`, the value the statement names. -/
@[req "SPN-30"]
theorem hold_logs_spend (c : Cfg) (hpr : c.r.pendingSource = .record) (st : St) (k : Nat)
    (env : Env) (cid : Nat) (d : Bool) (E : Wall) (q : Ingress.Request)
    (ha : Ledger.admitted st.sys.world (hold c st k env cid d E q).sys.world
      (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) = true)
    (hres : st.sys.world.node.cands.any (·.id == (spendOf c.ctx q).id) = false)
    (hlog : st.sys.world.node.pendingLog.entries.any (·.id == (spendOf c.ctx q).id) = false)
    (hcl : st.sys.world.node.pendingLog.cleared.contains (spendOf c.ctx q).id = false)
    (env' : Env) (hin : env'.eff.atOrBefore (spendOf c.ctx q).expiry = true) :
    (spendOf c.ctx q).id ∈ pending c.r env' (hold c st k env cid d E q).sys.world.node ∧
    ∀ g, subordinated g c.r env' (hold c st k env cid d E q) = true := by
  obtain ⟨hw, hnew⟩ := hold_admitted_accept c st k env cid d E q ha
  have hacc : (accept c.r env st.sys.world.node cid d E (spendOf c.ctx q)
      (escapeOf c.ctx q)).carriers.any (fun x => x.cid == cid && x.accepted) = true := by
    have h := ha
    simp only [Ledger.admitted, Bool.and_eq_true] at h
    rw [hw] at h
    exact h.1.2
  have hlogw : (hold c st k env cid d E q).sys.world.node.pendingLog =
      logRegistration c.r st.sys.world.node (spendOf c.ctx q) (escapeOf c.ctx q) := by
    rw [hw]; exact accept_log_of_admitted hacc hnew
  have hmem : (spendOf c.ctx q).id ∈
      pending c.r env' (hold c st k env cid d E q).sys.world.node := by
    simp only [pending, hpr, hlogw, logRegistration, hres, Bool.and_false, Bool.false_eq_true,
      if_false]
    apply List.mem_map.2
    refine ⟨{ id := (spendOf c.ctx q).id, tx := (spendOf c.ctx q).tx,
              siblingTx := (escapeOf c.ctx q).tx.id, expiry := (spendOf c.ctx q).expiry }, ?_, rfl⟩
    apply List.mem_filter.2
    refine ⟨?_, hin⟩
    have hhot : (spendOf c.ctx q).hot = true := rfl
    have hcl' : (spendOf c.ctx q).id ∉ st.sys.world.node.pendingLog.cleared := by simpa using hcl
    simp [hhot, hlog, hcl']
  refine ⟨hmem, fun g => ?_⟩
  have : (pending c.r env' (hold c st k env cid d E q).sys.world.node).isEmpty = false := by
    cases h : pending c.r env' (hold c st k env cid d E q).sys.world.node with
    | nil => rw [h] at hmem; cases hmem
    | cons _ _ => rfl
  simp [subordinated, this]

/-- `POL-18` on the checked path: a hold that leaves an accepted Carrier for its pair charges the
spend's commitment, by a new row or by the one an earlier acceptance placed. -/
@[req "POL-18"]
theorem hold_admitted_charges (c : Cfg) (st : St) (k : Nat) (env : Env) (cid : Nat) (d : Bool)
    (E : Wall) (q : Ingress.Request)
    (ha : Ledger.admitted st.sys.world (hold c st k env cid d E q).sys.world
      (.accept cid d E (spendOf c.ctx q) (escapeOf c.ctx q)) = true) :
    Ledger.holds (hold c st k env cid d E q).sys.led (spendOf c.ctx q).id = true := by
  have hreserve : ∀ (l : Ledger.Ledger) (now : Mono),
      Ledger.holds (Ledger.reserve l (spendOf c.ctx q) now) (spendOf c.ctx q).id = true := by
    intro l now
    unfold Ledger.reserve
    split
    · assumption
    · simp [Ledger.holds, List.any_append]
  rcases hold_event c env st.sys.led cid d E q with he | ⟨code, pair, he⟩ | he
  · have hw : (hold c st k env cid d E q).sys.world = st.sys.world := by simp only [hold, he]
    simp only [Ledger.admitted, Bool.and_eq_true, Bool.not_eq_true', hw] at ha
    obtain ⟨⟨-, hacc⟩, hnew⟩ := ha
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.1 hacc
    have : st.sys.world.node.carriers.any (·.cid == cid) = true :=
      List.any_eq_true.2 ⟨x, hx, by simp only [Bool.and_eq_true] at hp; exact hp.1⟩
    rw [hnew] at this; cases this
  · obtain ⟨-, hnew⟩ := hold_admitted_accept c st k env cid d E q ha
    have hw' : (hold c st k env cid d E q).sys.world =
        { st.sys.world with node := refuse c.r env st.sys.world.node cid d E (some pair) } := by
      simp only [hold, he, Ledger.sysStep, Ledger.refusedByBudget, Bool.false_eq_true, if_false,
        Kernel.step]
    have hacc := ha
    simp only [Ledger.admitted, Bool.and_eq_true, hw'] at hacc
    exact absurd (Ledger.refuse_accepted hacc.1.2) (by simp [hnew])
  · simp only [hold, he] at ha ⊢
    simp only [Ledger.sysStep] at ha ⊢
    split
    · rename_i hb
      rw [if_pos hb] at ha
      simp only [Ledger.admitted, Bool.and_eq_true, Bool.not_eq_true'] at ha
      exact absurd (Ledger.refuse_accepted ha.1.2) (by simp [ha.2])
    · rename_i hb
      rw [if_neg hb] at ha
      simp only [Ledger.holds_markExposed, Ledger.afterEvent, ha, if_true]
      exact hreserve _ _

end BtcPolicy.Lifetime
