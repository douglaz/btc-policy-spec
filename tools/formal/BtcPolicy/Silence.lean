import BtcPolicy.Ledger
import BtcPolicy.Policy
/-! SILENCE as a two-run relation (`ADR-0023` decision 14). `DUR-1`: "Every observable a
node emits MUST be identical between a normal-PIN and a duress-PIN request".

**The two worlds.** One request body, two enrolment tables. The bytes, the delivery schedule, the
chain view and every clock sample are the same in both runs; what differs is which class the
node's enrolment gives the presented PIN, and the table is the secret. Two different PIN bodies
would differ in a public input — `SEC-10` scopes silence to "a coordinator that turns hostile at
the wrench", and that coordinator knows what it relayed. The conformance item that drives one
request under each PIN and asserts everything but the PIN equal is the experiment that
approximates this relation; it is not its statement. Applying the relation to SILENCE is also
conditional on `SEC-10`'s "release-history premise": "no node has run a compromised release
while the current PINs were in use". These proofs concern the specified honest transitions;
they do not establish absence of a compromised release or model PIN history retained on a
coordinator by such a release.

**The relation is a coupling invariant, not a commuting projection.** `observe ∘ step = stepObs ∘
observe` is the wrong shape twice over: identical observations do not determine the next output,
and exposing the hidden fields that would make a projection commute is what `DUR-1` forbids. What
is proved here is that two runs coupled by `Coupled` — equal on everything but the fields the arm
writes — emit equal observations at each step and stay coupled. `SPN-41`'s exemption reads an
Escape's window, which closes at its own run's `T`: inside each run's horizon that close is read
off `Node.unarmedT`, which the coupling keeps, so both runs keep the same Escapes. `SPN-41`'s
removal of every selected Escape and its pair reads the arm bit, and inside each run's horizon it
is false (`removal_false_preHorizon`): an unarmed run never removes, and an armed one is strictly
before its `T`, so effective time has not passed `T + combine_slack_secs`. `SPN-30`'s pending log
is node state of its own, written from the request, the registry's ids, the log itself, the chain
view and the effective sample, so the coupling carries it as it is (`PubNode`), and no premise names
it.

**The horizon is a guard on the state ENTERING a step**: unarmed, or the driver's sample strictly
below that state's own current `T` (`DUR-7`'s "`armed ∧ max(ratchet, effective) ≥ T`"), where the
time ratchet is node state, advanced at every holder decision and every accepted hot spend. So the
arming receipt is always inside the prefix — the node enters it unarmed — and its own effects are
the last shared observable, which is where `DEF-12`'s twin lives. Stickiness is the prefix
quantification of `obsPair` and not a property of the clock: `SPN-13`'s effective time is not
monotone, and neither is its maximum with the ratchet. What a backward step cannot do (`F60`)
is un-reach a `T` at or below the effective time of a holder decision or a hot acceptance while
that `T` is unchanged, or reopen a hot window whose close is below that effective time, because
both of the ratchet's readers compare at or above it. The horizon may be zero: `DUR-14` says "a hot spend pending at arm time whose `fire_at −
epsilon_secs` has already passed collapses the window to now", and then the prefix ends at the receipt that armed.

**`Obs`.** `DUR-1`'s list, as far as this model carries it: the response — `SPN-34`'s `Accepted {
commitment_id, first_seen, remaining_secs }` by the two instants a rendered `remaining_secs` is a
function of, or `API-13`'s refusal code, which is every capacity and budget twin's channel — the
`/pending` listing of the pending log (`SPN-30`, `API-21`), `/healthz`'s `locked_down` (`API-19`), `DEF-12`'s confirmation
marker, the ordered effects (`SPN-38`'s queued partial with its message, input, class and
commitment, and `DUR-29`'s broadcast), and the ordered work trace of `DUR-1`'s "candidate visits"
and `DUR-10`'s set insertion.

**What `Obs` omits, and what is therefore not claimed.** Response timing class, allocation counts,
lock counts and store-lock hold time — four of the items `DUR-1` lists: counts are not durations,
`SEC-47` says "End-to-end timing has no hard gate" and `F22` records why, and a unit-cost model
must not be advertised as constant time. A peer effect carries its message, its input, its class
and its commitment, which is its shape; `DUR-1`'s "peer message shapes and sizes" also asks for
the size, and serialized size belongs to the encoders and is not in this model, so equal shapes
here are not equal bytes on the wire. Destinations are not carried either: a partial is queued for
transport to every peer (`SPN-38`: "queued for transport, not that a peer received it"), and this
kernel is one node, so there is no per-destination trace to compare.
`/events`: the kernel emits no alert, and the alert queue is `Alerts.lean`'s (`WTC-20`), whose
module docstring states the same argument as this one. The queue adds no observable divergence
between the two PINs before the horizon because it is a function of two inputs only: the chain
scan, an environment input equal in both runs, and the authorized set, which under `current` is
`SPN-33`'s accepted txids. Under `Coupled` the accepted candidates' transactions are equal
(`pubCand_tx`: the projection the coupling equates keeps a candidate's `tx`) and a refusal is
the same refusal in both runs (`Obs.resp`, equal at every step by `silence`), so the accepted
sets are equal, the two snapshots are equal, and the two queues after a pass are equal. Not
claimed: anything at or past the horizon, a compromised node or failure of `SEC-10`'s
"release-history premise", and `NCH-16`'s freshness diagnostic, which is not a watchtower alert.
`API-19`'s `last_deadline_tick`, which is "published by the deadline driver alone": `DUR-7`'s driver is not an event of this kernel — its
`tick` is `NCH-40`'s store prune driver — so neither the bucket nor the Lockdown latch at `T` is
modelled, and the first post-horizon divergence this model does exhibit is the Escape partial
whose window opens at `T`.

**What is not claimed at all.** Machine timing (above); a compromised node or a coordinator
compromised before the wrench, which `SEC-10` excludes ("a compromised node sees the PIN in
plaintext"), or failure of its "release-history premise" even with an honest coordinator before
the wrench; any Lockdown latency (`DUR-15`, `SEC-48`, `F13`: "The DELAY before Lockdown lands has
no finite bound"); the plausibility of the cover story; and anything at or past `T`. `F3`, `F4`
and `F13` stay traces with no repair chosen. `F60`'s backward step is closed by the time ratchet,
so `silence` takes no premise on the trace's samples; `BtcPolicy.Exhibits.TwoRun` runs each of
its routes on the effective sample alone and under the ratchet.

**Scope: one node.** `DUR-1` is per node — "Every observable a node emits" — and a peer's relays
are inputs held equal across the two runs. A federation's horizon is the first node's crossing,
by events rather than by a minimum over incomparable clocks; that is a corollary, and no
federation claim is made here.

The Hot ledger is not in `Obs` and is part of the coupling: a refund that happened only under
duress would surface later as a `HOT_VELOCITY_EXCEEDED` on a request the other run admits, which
is `POL-21`'s "a refund that happened only under duress would be the timing signal `DUR-1`
forbids", and the composed step of `Ledger.lean` is what carries it. -/

namespace BtcPolicy.Silence

open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger

/-! ## One request, two enrolments -/

/-- The PIN as it arrives: bytes the coordinator chose and knows (`SEC-10`). -/
abbrev Pin := Nat

/-- `DUR-4`'s enrolment: which class this node's table gives a presented PIN. The secret of the
two worlds; nothing below reads it except through a request's class. -/
abbrev Enrolment := Pin → Bool

/-- One environment input. A `request` or staged `refusal` carries the PIN it presented;
the remaining events carry no PIN — `DUR-36`'s claw-back "records no intent and reads no arm state", and a relay, a fire pass, a
settlement and a tick are the environment's. -/
inductive Input
  | request (cid : Nat) (pin : Pin) (E : Wall) (sp es : Cand)
  | refusal (cid : Nat) (pin : Pin) (E : Wall) (pair : Option (Nat × Nat))
      (code : Policy.Code := .BAD_PIN)
  | pinless (e : Event)
  deriving DecidableEq, Repr

/-- The kernel event one enrolment makes of an input. -/
def Input.event (tbl : Enrolment) : Input → Event
  | .request cid pin E sp es => .accept cid (tbl pin) E sp es
  | .refusal cid pin E pair code => .refuse cid (tbl pin) E pair code
  | .pinless e => e

/-- What an acceptance may look like, read off the event so that it is plainly pin-uniform.
`DUR-11` says the freeze "applies to every candidate with `hot = true`" and that "Refreshes,
claw-backs and Escape candidates are unaffected", so a pair's second member is not hot. `SPN-37`
says "The Escape member of a pair is registered with **no** fire window". `DUR-20` says the
window, and so its close, is "installed at that Escape's holder decision". So neither member
arrives carrying one. This shape boundary does not constrain selected membership: `SPN-23`
says an accepted repeat "re-applies its schedule, records its own intent (`DUR-4`), and re-stages".
Resident identity is carried by `NodeInv` and preserved by registration, not an ingress exclusion. -/
def wfEvent (_n : Node) : Event → Bool
  | .accept _ _ _ sp es => !es.hot && sp.windowClose == none && es.windowClose == none
  | _ => true

/-! ## The observer projection -/

/-- `API-12`'s two bodies, plus the answers that are not a body. `SPN-34`: "The response to an
accepted spend is `Accepted { commitment_id, first_seen, remaining_secs }` with … `remaining_secs
= fire_at − first_seen`", so carrying the two instants carries the rendered figure. -/
inductive Resp
  | accepted (cid : Nat) (firstSeen : Effective) (fireAt : Option Wall)
  | refused (code : Policy.Code)
  /-- `DUR-6`: "one whose `expiry ≤ now` MUST answer the fixed 30-second retry (`NCH-36`) and
  change nothing". -/
  | retry
  /-- `DUR-6`'s idempotent no-op, and a relay counted. -/
  | ack
  /-- An internal transition answers nobody. -/
  | silent
  deriving DecidableEq, Repr

/-- The answer the request got. Each arm names the check that decides it and adds none. `DUR-7`:
a locked-down node answers so that "every subsequent spend, refresh and claw-back answers
`FRAUD_SUSPECTED` / `lockdown` / `funds quarantined by policy`". `NCH-30`: "One resident Carrier
owns one coordinator nonce and one slot in the ordinary nonce log", and a second body on that
nonce is `API-13`'s "nonce already seen". `POL-16`: a spend over the budget "is refused
`HOT_VELOCITY_EXCEEDED` / `hot_budget_velocity` before signing", and "a full ledger refuses with
the same code and a detail naming the capacity rather than the window", which is why one arm
carries both. `NCH-33`: `D` is computed "in checked arithmetic that fails closed", and on `Nat`
the case that fails is a signed expiry already behind this decision's effective time, which is
`API-13`'s "expiry outside the freshness window". -/
@[req "API-12"]
def respond (r : Rules) (cfg : Config) (env : Env) (sys : Sys) : Event → Resp
  | e@(.accept cid _ E sp es) =>
    if sys.world.node.lockedDown then .refused .FRAUD_SUSPECTED
    else if sys.world.node.carriers.any (·.cid == cid) ||
        sys.world.node.tombstones.any (·.cid == cid) then .refused .NONCE_REPLAYED
    else if refusedByBudget cfg (ageOut env cfg.window sys.led) e then
      .refused .HOT_VELOCITY_EXCEEDED
    else if (Mono.deadline env.mono E env.eff).isNone then .refused .COMMITMENT_EXPIRED
    else if !pairAdmits r sys.world.node sp es then .refused .PSBT_INCONSISTENT
    else .accepted cid env.eff sp.fireAt
  | .refuse _ _ _ _ code => .refused code
  | .receipt cid _ =>
    match sys.world.node.carriers.find? (·.cid == cid) with
    | none => .ack
    | some k => if env.eff.before k.E then .ack else .retry
  | .receivePartial _ _ _ _ => .silent  -- internal post-response transition; see Event.receivePartial
  | _ => .silent

/-! ## `DEF-12`'s marker: the guard parameter this module owns -/

/-- `DEF-12`: "A harness-only marker fired on holder confirmation only when the confirmation
ARMED, which is present under duress and absent under normal — a duress oracle hanging off an
ordinary log." `committed` is the prohibition as it stands: "every artifact derived from a holder
confirmation MUST key on pin-uniform state, never on the arm bit". -/
inductive Marker
  | committed | armBit
  deriving DecidableEq, Repr

def current : Marker := .committed

/-- The marker this step leaves on a surface, keyed on `Kernel.commits` — the pin-uniform
condition `receipt` itself branches on — or, under the withdrawn value, on the intent's arm
bit. -/
@[req "DEF-12"]
def markerOf (g : Marker) (env : Env) (n : Node) : Event → Bool
  | .receipt cid s =>
    commits env n cid s &&
      (match g with
       | .committed => true
       | .armBit => (n.carriers.find? (·.cid == cid)).elim false (·.duress))
  | _ => false

/-! ## `DUR-1`'s work trace -/

/-- The two operations a request's own step performs on the overlay, in order. `DUR-1` lists
"candidate visits" among the observables and `SEC-47` names "ordered handler operations"; an
allocation count and a lock-hold time are durations of a machine and are not here. -/
inductive Op
  /-- `DUR-10`: the Escape id added to `selected_escapes`. -/
  | select (id : Nat)
  /-- `DUR-20`: one entry visited and its window written. -/
  | visit (id : Nat)
  deriving DecidableEq, Repr

/-- The ordered work of one step. The acceptance's traversal is `Kernel.traverses`, the same
condition `accept` branches on, and whether the acceptance registered at all is read from the
Carrier's local acceptance status — the test `Ledger.afterEvent` uses for the reservation (`SPN-29`: "only a
reservation placed by this request MUST be unwound in the same step"). The holder decision's is
`Kernel.commits`. Nothing here re-decides a rule. -/
@[req "DUR-1"]
def work (r : Rules) (env : Env) (before after : Sys) : Event → List Op
  | .accept cid _ _ sp es =>
    if after.world.node.carriers.any (fun k => k.cid == cid && k.accepted) &&
        !before.world.node.carriers.any (·.cid == cid) &&
        traverses r env before.world.node sp then
      (register r before.world.node env.mono sp es).map (fun c => Op.visit c.id)
    else []
  | .receipt cid s =>
    if commits env before.world.node cid s then
      match before.world.node.carriers.find? (·.cid == cid) with
      | none => []
      | some k => (k.pair.toList.map fun p => Op.select p.2) ++ before.world.node.cands.map (fun c => Op.visit c.id)
    else []
  | _ => []

/-- `DUR-10` requires the insertion "under either PIN, in identical work". A commit that inserted
only under duress is the break that clause exists to prevent; it is not a guard parameter, because
no dated amendment ever made it — the set has always required the inert entry (`DUR-10`: "An
entry whose duress bit remains clear therefore sits in the set present and never released"). The visit trace of the
holder decision differs at once, and `SPN-41`'s exemption — "the exemption is granted to the normal
PIN's inert slot too, so probing `CANDIDATE_CAPACITY` before `T` reveals nothing" — is the surface
it would open later. -/
def workDuressOnly (env : Env) (n : Node) : Event → List Op
  | .receipt cid s =>
    if commits env n cid s then
      match n.carriers.find? (·.cid == cid) with
      | none => []
      | some k =>
        (if k.duress then (k.pair.toList.map fun p => Op.select p.2) else []) ++ n.cands.map (fun c => Op.visit c.id)
    else []
  | _ => []

/-- One step's observation. -/
structure Obs where
  resp : Resp
  pending : List Nat
  lockedDown : Bool
  marker : Bool
  effects : List Effect
  ops : List Op
  deriving DecidableEq, Repr

def obsOf (g : Marker) (cfg : Config) (r : Rules) (env : Env) (before after : Sys)
    (effs : List Effect) (e : Event) : Obs :=
  { resp := respond r cfg env before e,
    pending := pending r env after.world.node,
    lockedDown := after.world.node.lockedDown,
    marker := markerOf g env before.world.node e,
    effects := effs,
    ops := work r env before after e }

/-! ## The concealment horizon and the two runs walked together -/

/-- `DUR-7`'s comparison as a guard on the state entering a step: unarmed, or the driver's sample
strictly below that state's current `T`. The kernel has no deadline-driver event, so this guard is
where the driver's read lives: `max(ratchet, effective)` under `ratchet`, the value of `driverTime`
as it stands, and the effective sample alone under the withdrawn value `effective`. -/
@[req "DUR-7"]
def preHorizon (r : Rules) (env : Env) (n : Node) : Bool :=
  !n.armed || !(match r.driverTime with
    | .ratchet => n.ratchet.latest env.eff
    | .effective => env.eff).deadlineReached n.T

/-- The two runs walked together over one trace of inputs, emitting one pair of observations per
step while BOTH entering states are inside the horizon and `wfEvent` admits the request shape.
Fresh-nonce repeats remain in the walk even after selection. The list ends at the first step
where either has crossed: the horizon of the pair is the earlier of the two, because a coordinator holding both worlds' surfaces is the
adversary `SEC-10` names. Sticky by this quantification and not by a property of the sample
`preHorizon` reads, which can still step back to the ratchet after a fire pass read a later
one. -/
def obsPair (g : Marker) (gs : Guards) (cfg : Config) (r : Rules) (tbl₀ tbl₁ : Enrolment) :
    Sys → Sys → List (Env × Input) → List (Obs × Obs)
  | _, _, [] => []
  | a, b, (env, i) :: rest =>
    if preHorizon r env a.world.node && preHorizon r env b.world.node &&
        wfEvent a.world.node (i.event tbl₀) then
      (obsOf g cfg r env a (sysStep gs cfg r env a (i.event tbl₀)).1
          (sysStep gs cfg r env a (i.event tbl₀)).2 (i.event tbl₀),
        obsOf g cfg r env b (sysStep gs cfg r env b (i.event tbl₁)).1
          (sysStep gs cfg r env b (i.event tbl₁)).2 (i.event tbl₁)) ::
        obsPair g gs cfg r tbl₀ tbl₁ (sysStep gs cfg r env a (i.event tbl₀)).1
          (sysStep gs cfg r env b (i.event tbl₁)).1 rest
    else []

/-! ## The coupling -/

/-- The ids of `selected_escapes`, which every holder decision writes under both PINs
(`DUR-10`: "Every holder decision whose intent names a pair"); only the entries' bits are the arm's. -/
def selIds (n : Node) : List Nat := n.selected.map (·.1)

def inSel (sel : List Nat) (i : Nat) : Bool := sel.any (· == i)

theorem inSel_selIds (n : Node) (i : Nat) : inSel (selIds n) i = n.selected.any (·.1 == i) := by
  simp [inSel, selIds, List.any_map, Function.comp_def]

/-- A candidate with the overlay's writes erased: `DUR-11`'s freeze bit, and on a selected Escape
the window `DUR-20` writes from `T`. Whether a window is installed is kept: the writes that install
one run under both PINs (`DUR-20`), and `SPN-41`'s exemption reads it. Everything else on a
candidate is pin-uniform. -/
def pubCand (sel : List Nat) (c : Cand) : Cand :=
  if inSel sel c.id then
    { c with frozen := false, fireAt := none, windowClose := c.windowClose.map fun _ => Wall.sample 0 }
  else { c with frozen := false }

/-- `DUR-4`'s intent with its duress bit erased: the bit is the secret, the rest is the request. -/
def pubCarrier (k : Carrier) : Carrier := { k with duress := false }

def pubTombstone (k : Tombstone) : Tombstone := { k with duress := false }

/-- Everything about a node that is not the Armed overlay's to write. `armed`, `sweep_active` and
`T` are absent because they are the overlay (`DUR-10`); the selected set keeps its ids and loses
its bits. The time ratchet is present: `DUR-7` advances it at the same events under both PINs. So
is `Node.unarmedT`, the `T` an unarmed node holds: every holder decision writes it, under both PINs,
from what the projection keeps, and no arm-only write moves it. So is `SPN-30`'s pending log, whole:
an acceptance, a settlement and a prune pass write it from the request, the registry's ids, the
log itself, the chain view and the effective sample, and `SPN-41`'s removal, the one write that reads the arm bit,
leaves it. Carrying it here is the coupling covering pin-uniform state, not a premise of
`silence`. -/
structure PubNode where
  id : Nat
  t : Nat
  poisoned : Bool
  lockedDown : Bool
  carriers : List Carrier
  cands : List Cand
  sel : List Nat
  duressDelay : Secs
  epsilon : Secs
  combineSlack : Secs
  holdSecs : Secs
  tombstones : List Tombstone
  ratchet : Effective
  unarmedT : Wall
  pendingLog : PendingLog
  deriving DecidableEq, Repr

def pubNode (n : Node) : PubNode :=
  { id := n.id, t := n.t, poisoned := n.poisoned, lockedDown := n.lockedDown,
    carriers := n.carriers.map pubCarrier, cands := n.cands.map (pubCand (selIds n)),
    sel := selIds n, duressDelay := n.duressDelay, epsilon := n.epsilon,
    combineSlack := n.combineSlack, holdSecs := n.holdSecs, tombstones := n.tombstones.map pubTombstone,
    ratchet := n.ratchet, unarmedT := n.unarmedT, pendingLog := n.pendingLog }

/-- Two runs differing only in what the arm wrote, with one Hot ledger and one exposure history
between them. -/
structure Coupled (a b : Sys) : Prop where
  node : pubNode a.world.node = pubNode b.world.node
  exposure : a.world.exposure = b.world.exposure
  led : a.led = b.led

/-! ## The per-run invariant the coupling rests on -/

/-- `DUR-13` and `DUR-14`'s live bound on one hot candidate, carried at a sample: it is broadcast,
or its window has already closed at that sample, or `T` is at or before its fire time less
`epsilon_secs` or that sample. Carried at the time ratchet, it reads `expiry < L ∨ T ≤ max(fire_at
− ε, L)` for an unbroadcast candidate, with `SPN-30`'s close in place of `expiry`. -/
def hotBoundAt (n : Node) (now : Effective) (c : Cand) : Prop :=
  ∀ f, c.fireAt = some f →
    c.broadcast = true ∨ windowOpen now n.combineSlack c = false ∨
    Wall.belowFire n.T f n.epsilon now = true

/-- What one run carries. `sweep` is `DUR-10`'s two overlay flags written by one writer; `frozen`
is `DUR-11` in both directions; `windows` carries `DUR-20`'s "all selected windows share one `T`"
for selected candidates with opening authority. A refused holder decision can select an absent
pair; later registration creates closed candidates, and `due` refuses them until a holder
decision opens them and writes their windows. Selection implies neither residency nor opening.
`idsUnique` carries registration's duplicate-free ids: `SPN-32` requires "both distinct ids
together when both are absent". `hotBound` is the freeze-invisible invariant — the reason no
hot candidate becomes due before
`T` in EITHER run, which is what makes `DUR-11`'s freeze unobservable rather than merely
frozen. -/
structure NodeInv (n : Node) (now : Effective) : Prop where
  sweep : n.sweepActive = n.armed
  unfrozen : n.armed = false → ∀ c ∈ n.cands, c.frozen = false
  frozen : n.armed = true → ∀ c ∈ n.cands, c.hot = true → c.frozen = true
  windows : ∀ c ∈ n.cands, inSel (selIds n) c.id = true → c.quorum = true →
    c.fireAt = some n.T
  noWindow : ∀ c ∈ n.cands, inSel (selIds n) c.id = false → c.windowClose = none
  hotBound : n.armed = true → ∀ c ∈ n.cands, c.hot = true → inSel (selIds n) c.id = false →
    hotBoundAt n now c
  idsUnique : (n.cands.map Cand.id).Nodup
  /-- `DUR-20`'s windows on the selected set, whatever the quorum: an installed window closes at
  `T + combine_slack_secs`, and a hot entry's fire time is `T`, because every write of `T` writes
  every selected window with it. -/
  selWin : ∀ c ∈ n.cands, inSel (selIds n) c.id = true →
    (c.windowClose = none ∨ c.windowClose = some (n.T.plus n.combineSlack)) ∧
    (c.hot = true → c.fireAt = some n.T)
  /-- `Node.unarmedT` is the `T` an unarmed node holds, and an armed node's `T` is at or below it:
  `DUR-14`'s shrink and `DUR-13`'s clamp only ever write at or below the computed value. -/
  unarmed : (n.armed = false → n.T = n.unarmedT) ∧
    (n.armed = true → Wall.atOrBefore n.T n.unarmedT = true)

/-- Every clause of it is stable under a later sample, which is why it can be carried at one
sample, the time ratchet, and read at the step's own sample or the ratchet's maximum with it. -/
theorem NodeInv.weaken {n : Node} {a b : Effective} (h : NodeInv n a) (hab : a.notAfter b = true) :
    NodeInv n b :=
  { sweep := h.sweep, unfrozen := h.unfrozen, frozen := h.frozen, windows := h.windows,
    noWindow := h.noWindow, idsUnique := h.idsUnique, selWin := h.selWin, unarmed := h.unarmed,
    hotBound := by
      intro ha c hc hhot hsel f hf
      rcases h.hotBound ha c hc hhot hsel f hf with hb | hx | hw
      · exact .inl hb
      · exact .inr (.inl (windowOpen_weaken hx hab))
      · exact .inr (.inr (Wall.belowFire_weaken hw hab)) }

/-- `NodeInv` at the kernel's initial boundary: a node that holds no candidate, is not armed, has
its sweep flag clear and holds `T` as its `unarmedT` satisfies it at every sample, `selWin` and
`unarmed` included. `inv_sysStep` carries it from there. `hu` narrows no state `silence` covers
at `Kernel.Reachable.init`: no transition reads `unarmedT` except through
`Kernel.unarmedDeadline`, to compute the next `unarmedT`, and `silence_initial` gives an admitted
node with its sweep flag clear its `T` there without changing an observation
(`obsPair_unarmedT`). `hs` is the `sweep` clause's, which predates `selWin` and `unarmed`. -/
theorem nodeInv_initial (n : Node) (now : Effective) (hc : n.cands = []) (ha : n.armed = false)
    (hs : n.sweepActive = false) (hu : n.T = n.unarmedT) : NodeInv n now :=
  { sweep := (by rw [hs, ha]), unfrozen := fun _ c h => (by simp [hc] at h),
    frozen := fun h => (by rw [ha] at h; cases h), windows := fun c h => (by simp [hc] at h),
    noWindow := fun c h => (by simp [hc] at h), hotBound := fun h => (by rw [ha] at h; cases h),
    idsUnique := (by simp [hc]), selWin := fun c h => (by simp [hc] at h),
    unarmed := ⟨fun _ => hu, fun h => (by rw [ha] at h; cases h)⟩ }

theorem coupled_refl (a : Sys) : Coupled a a := ⟨rfl, rfl, rfl⟩

/-! ## Reading a step through the projection

Every list operation a step performs is a `map`, a `filter`, an `any` or a `find?` whose function
reads only public fields. Each commutes with the projection, so a step's update on one run and the
other's factor through one common function of the projected state — which is how the coupling is
carried without a projection that commutes with `step` itself. -/

theorem pubCand_id (sel : List Nat) (c : Cand) : (pubCand sel c).id = c.id := by
  unfold pubCand; split <;> rfl
theorem pubCand_hot (sel : List Nat) (c : Cand) : (pubCand sel c).hot = c.hot := by
  unfold pubCand; split <;> rfl
theorem pubCand_tx (sel : List Nat) (c : Cand) : (pubCand sel c).tx = c.tx := by
  unfold pubCand; split <;> rfl
theorem pubCand_quorum (sel : List Nat) (c : Cand) : (pubCand sel c).quorum = c.quorum := by
  unfold pubCand; split <;> rfl
theorem pubCand_terminal (sel : List Nat) (c : Cand) : (pubCand sel c).terminal = c.terminal := by
  unfold pubCand; split <;> rfl
theorem pubCand_settled (sel : List Nat) (c : Cand) : (pubCand sel c).settled = c.settled := by
  unfold pubCand; split <;> rfl
theorem pubCand_broadcast (sel : List Nat) (c : Cand) : (pubCand sel c).broadcast = c.broadcast := by
  unfold pubCand; split <;> rfl
theorem pubCand_released (sel : List Nat) (c : Cand) : (pubCand sel c).released = c.released := by
  unfold pubCand; split <;> rfl
theorem pubCand_packageOk (sel : List Nat) (c : Cand) : (pubCand sel c).packageOk = c.packageOk := by
  unfold pubCand; split <;> rfl
theorem pubCand_expiry (sel : List Nat) (c : Cand) : (pubCand sel c).expiry = c.expiry := by
  unfold pubCand; split <;> rfl
theorem pubCand_acceptedAt (sel : List Nat) (c : Cand) : (pubCand sel c).acceptedAt = c.acceptedAt := by
  unfold pubCand; split <;> rfl
theorem pubCand_pair (sel : List Nat) (c : Cand) : (pubCand sel c).pair = c.pair := by
  unfold pubCand; split <;> rfl
/-- Possession is pin-uniform: the arm freezes a candidate and moves its window, and writes
nothing to the partials this node holds. Erasing it here would make the two runs' counts differ
and put any later statement over them out of reach. -/
theorem pubCand_held (sel : List Nat) (c : Cand) :
    (pubCand sel c).heldSigners = c.heldSigners := by
  unfold pubCand; split <;> rfl
theorem pubCand_frozen (sel : List Nat) (c : Cand) : (pubCand sel c).frozen = false := by
  unfold pubCand; split <;> rfl
/-- Off the selected set the window is the projection's: `DUR-20` writes it only on an entry. -/
theorem pubCand_fireAt_of_not_sel (sel : List Nat) (c : Cand) (h : inSel sel c.id = false) :
    (pubCand sel c).fireAt = c.fireAt := by simp [pubCand, h]
theorem pubCand_windowClose_of_not_sel (sel : List Nat) (c : Cand) (h : inSel sel c.id = false) :
    (pubCand sel c).windowClose = c.windowClose := by simp [pubCand, h]

theorem pubCarrier_cid (k : Carrier) : (pubCarrier k).cid = k.cid := rfl

/-! ### The four commutations, each by induction on one list

They are stated for any projection, because the node projects its candidates and its Carriers
the same way: a list operation whose function reads only what the projection keeps commutes
with it. -/

theorem map_comm {α β γ : Type} (pub : α → β) (G : β → γ) :
    ∀ (l : List α) (F : α → γ), (∀ c ∈ l, F c = G (pub c)) → l.map F = (l.map pub).map G := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons c cs ih =>
    intro F hF
    simp only [List.map_cons, hF c (by simp), ih F fun x hx => hF x (by simp [hx])]

theorem filter_comm {α β : Type} (pub : α → β) (q : β → Bool) :
    ∀ (l : List α) (p : α → Bool), (∀ c ∈ l, p c = q (pub c)) →
      (l.filter p).map pub = (l.map pub).filter q := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons c cs ih =>
    intro p hp
    have hrest := ih p fun x hx => hp x (by simp [hx])
    rw [List.filter_cons, List.map_cons, List.filter_cons, hp c (by simp)]
    split <;> simp [hrest]

theorem any_comm {α β : Type} (pub : α → β) (q : β → Bool) :
    ∀ (l : List α) (p : α → Bool), (∀ c ∈ l, p c = q (pub c)) →
      l.any p = (l.map pub).any q := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons c cs ih =>
    intro p hp
    simp only [List.any_cons, List.map_cons, hp c (by simp),
      ih p fun x hx => hp x (by simp [hx])]

theorem find?_comm {α β : Type} (pub : α → β) (q : β → Bool) :
    ∀ (l : List α) (p : α → Bool), (∀ c ∈ l, p c = q (pub c)) →
      (l.find? p).map pub = (l.map pub).find? q := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons c cs ih =>
    intro p hp
    rw [List.find?_cons, List.map_cons, List.find?_cons, hp c (by simp)]
    split
    · rfl
    · exact ih p fun x hx => hp x (by simp [hx])

/-! ## The release decision is the same in both runs

`SPN-38`'s `due` with `DUR-10`'s authorization, as a function of the projected candidate alone.
This is where the horizon does its work, and where `DUR-11`'s freeze stops being observable: a
selected entry's window opens at its own run's `T`, and a hot candidate is broadcast, closed at the
time ratchet, or has a fire time at or after `T` (`DUR-13`, `DUR-14`), so before the horizon
neither releases — in the armed run because it is frozen, in the other because its window has not
opened at the effective sample or has closed at `max(ratchet, effective)`. -/

/-- The decision as the projection sees it, given whether either run is armed. `n` supplies the
public fields `due` reads off the node, the ones `due_congr` lists. -/
def releaseErased (r : Rules) (env : Env) (n : Node) (sel : List Nat) (anyArmed : Bool)
    (ec : Cand) : Bool :=
  if inSel sel ec.id then false
  else if anyArmed && ec.hot then false
  else due r env n ec

/-- The fields of the node `due` reads, each a hypothesis here, and all public. -/
theorem due_congr {r : Rules} {env : Env} {x y : Node} (hr : x.ratchet = y.ratchet)
    (hs : x.combineSlack = y.combineSlack) (hh : x.holdSecs = y.holdSecs) (c : Cand) :
    due r env x c = due r env y c := by
  simp only [due, closeSample, holdMatured, hr, hs, hh]

theorem releaseErased_congr {r : Rules} {env : Env} {x y : Node} (hr : x.ratchet = y.ratchet)
    (hs : x.combineSlack = y.combineSlack) (hh : x.holdSecs = y.holdSecs) :
    releaseErased r env x = releaseErased r env y := by
  funext sel anyArmed ec
  simp only [releaseErased, due_congr hr hs hh]

theorem find?_sel_none (n : Node) (c : Cand) (h : inSel (selIds n) c.id = false) :
    n.selected.find? (·.1 == c.id) = none := by
  rw [inSel_selIds] at h
  refine List.find?_eq_none.2 fun x hx hp => ?_
  rw [List.any_eq_false] at h
  exact h x hx hp

theorem releaseAuthorized_not_sel (n : Node) (c : Cand) (h : inSel (selIds n) c.id = false) :
    releaseAuthorized n c = true := by
  simp [releaseAuthorized, find?_sel_none n c h]

theorem releaseAuthorized_sel_unarmed (n : Node) (c : Cand) (hs : inSel (selIds n) c.id = true)
    (hsweep : n.sweepActive = n.armed) (ha : n.armed = false) : releaseAuthorized n c = false := by
  simp only [releaseAuthorized]
  cases hf : n.selected.find? (·.1 == c.id) with
  | none =>
    rw [inSel_selIds, List.any_eq_true] at hs
    obtain ⟨x, hx, hp⟩ := hs
    exact absurd (List.find?_eq_none.1 hf x hx) (by simp [hp])
  | some e => simp [hsweep, ha]

/-- The freeze bit is the only field `due` reads that the projection erases, and it decides
nothing on a candidate that is not a frozen hot one (`SPN-38`). -/
theorem due_pub (r : Rules) (env : Env) (n : Node) (sel : List Nat) (c : Cand)
    (hs : inSel sel c.id = false) (h : c.hot = false ∨ c.frozen = false) :
    due r env n (pubCand sel c) = due r env n c := by
  simp only [due, closeSample, holdMatured, windowOpen, residentConflict, conflicts, pubCand_broadcast,
    pubCand_settled, pubCand_terminal, pubCand_hot, pubCand_frozen, pubCand_quorum, pubCand_expiry,
    pubCand_tx, pubCand_acceptedAt,
    pubCand_fireAt_of_not_sel sel c hs, pubCand_windowClose_of_not_sel sel c hs]
  rcases h with h | h <;> simp [h]

/-- A candidate of one run has a partner in the other with the same projection. -/
theorem partner {n m : Node}
    (hmap : n.cands.map (pubCand (selIds n)) = m.cands.map (pubCand (selIds m)))
    {c : Cand} (hc : c ∈ n.cands) :
    ∃ c' ∈ m.cands, pubCand (selIds m) c' = pubCand (selIds n) c := by
  have : pubCand (selIds n) c ∈ m.cands.map (pubCand (selIds m)) := by
    rw [← hmap]; exact List.mem_map_of_mem hc
  obtain ⟨c', hc', he⟩ := List.mem_map.1 this
  exact ⟨c', hc', he⟩

/-- `SPN-38`'s two window conjuncts, each on its own: a candidate whose fire window has not opened
or has closed is not due. -/
theorem not_due_of_fire (r : Rules) (env : Env) (n : Node) (c : Cand) (f : Wall)
    (hf : c.fireAt = some f) (h : env.eff.atOrAfter f = false) : due r env n c = false := by
  simp [due, hf, h]

theorem not_due_of_window (r : Rules) (env : Env) (n : Node) (c : Cand)
    (h : windowOpen (closeSample r env n c) n.combineSlack c = false) : due r env n c = false := by
  simp [due, h]

theorem windowOpen_pub (sel : List Nat) (c : Cand) (hs : inSel sel c.id = false) :
    windowOpen now slack (pubCand sel c) = windowOpen now slack c := by
  simp [windowOpen, pubCand_windowClose_of_not_sel sel c hs, pubCand_fireAt_of_not_sel sel c hs,
    pubCand_expiry, pubCand_hot]

/-- `DUR-7`'s driver inside the horizon, read off the guard: an armed node's ratchet and the step's
effective sample are both strictly below its `T`. -/
theorem preHorizon_below {r : Rules} (hdr : r.driverTime = .ratchet) {env : Env} {n : Node}
    (hp : preHorizon r env n = true) (ha : n.armed = true) :
    (n.ratchet.latest env.eff).deadlineReached n.T = false := by
  simp only [preHorizon, ha, hdr, Bool.not_true, Bool.false_or] at hp
  simpa using hp

/-- On an armed node inside its horizon, no hot candidate off the selected set is due EVEN WITH
THE FREEZE ERASED: its fire window has not opened at the effective sample, or it is broadcast, or
its window had already closed at the time ratchet, and so at `max(ratchet, effective)`. That is
the statement `DUR-14` exists for — reading the freeze bit instead would make the argument
circular, since the freeze is what the relation must show is invisible. The bound is carried at
the ratchet, and each read takes one half: the close is read at or above it (`hcl`) and the
driver sees both readings below `T` (`hdr`), so an effective sample that stepped back below the
ratchet makes none of these candidates due. -/
theorem not_due_pub_of_armed {r : Rules} (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {env : Env} {n : Node} (hi : NodeInv n n.ratchet)
    (hp : preHorizon r env n = true) (ha : n.armed = true) {c : Cand} (hc : c ∈ n.cands)
    (hhot : c.hot = true) (hs : inSel (selIds n) c.id = false) :
    due r env n (pubCand (selIds n) c) = false := by
  have hT := preHorizon_below hdr hp ha
  cases hf : c.fireAt with
  | none =>
    have : (pubCand (selIds n) c).fireAt = none := by
      rw [pubCand_fireAt_of_not_sel _ c hs, hf]
    simp [due, this]
  | some f =>
    have hfp : (pubCand (selIds n) c).fireAt = some f := by
      rw [pubCand_fireAt_of_not_sel _ c hs, hf]
    rcases hi.hotBound ha c hc hhot hs f hf with hb | hx | hw
    · simp [due, pubCand_broadcast, hb]
    · apply not_due_of_window
      have hcs : closeSample r env n (pubCand (selIds n) c) = n.ratchet.latest env.eff := by
        simp [closeSample, hcl, pubCand_hot, hhot]
      rw [hcs, windowOpen_pub _ c hs]
      exact windowOpen_weaken hx (Effective.notAfter_latest_left _ _)
    · exact not_due_of_fire r env n _ f hfp (Effective.not_atOrAfter_of_belowFire_latest hw hT)

/-- The release decision factors through the projection, for a pair of runs coupled on the
candidate list and each inside its own horizon. -/
theorem release_factor {r : Rules} (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    (env : Env) (n m : Node) (hsel : selIds n = selIds m)
    (hmap : n.cands.map (pubCand (selIds n)) = m.cands.map (pubCand (selIds m)))
    (hrt : n.ratchet = m.ratchet) (hcs : n.combineSlack = m.combineSlack)
    (hhs : n.holdSecs = m.holdSecs) (hin : NodeInv n n.ratchet) (him : NodeInv m m.ratchet)
    (hpn : preHorizon r env n = true) (hpm : preHorizon r env m = true) :
    ∀ c ∈ n.cands, (due r env n c && releaseAuthorized n c)
      = releaseErased r env n (selIds n) (n.armed || m.armed) (pubCand (selIds n) c) := by
  intro c hc
  simp only [releaseErased, pubCand_id, pubCand_hot]
  by_cases hs : inSel (selIds n) c.id = true
  · -- a selected entry: its window opens at its own run's `T`, and an unarmed run never
    -- authorizes it (`DUR-10`)
    simp only [hs, if_true]
    cases ha : n.armed with
    | false => simp [releaseAuthorized_sel_unarmed n c hs hin.sweep ha]
    | true =>
      have hT : env.eff.deadlineReached n.T = false :=
        (Effective.deadlineReached_latest (preHorizon_below hdr hpn ha)).2
      cases hq : c.quorum with
      | false => simp [due, hq]
      | true =>
        rw [not_due_of_fire r env n c n.T (hin.windows c hc hs hq)
          (by rw [Effective.atOrAfter_eq_deadlineReached]; exact hT)]
        rfl
  · -- off the set: `DUR-10` authorizes it, and what remains is `due` on public fields
    simp only [Bool.not_eq_true] at hs
    rw [releaseAuthorized_not_sel n c hs, Bool.and_true]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hhot : c.hot with
    | false =>
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact (due_pub r env n _ c hs (.inl hhot)).symm
    | true =>
      cases ha : (n.armed || m.armed) with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        refine (due_pub r env n _ c hs (.inr ?_)).symm
        exact hin.unfrozen (by simpa using (Bool.or_eq_false_iff.1 ha).1) c hc
      | true =>
        simp only [Bool.true_and, ↓reduceIte]
        cases han : n.armed with
        | true =>
          -- frozen on its own node (`DUR-11`), so it is not due there
          simp [due, hhot, hin.frozen han c hc hhot]
        | false =>
          -- the other run is armed: its own deadline bound refuses the same fire time, and the
          -- freeze is not what does it
          have ham : m.armed = true := by
            rcases Bool.or_eq_true_iff.1 ha with h | h
            · exact absurd h (by simp [han])
            · exact h
          obtain ⟨c', hc', he⟩ := partner hmap hc
          have hid : c'.id = c.id := by
            have : (pubCand (selIds m) c').id = (pubCand (selIds n) c).id := by rw [he]
            rwa [pubCand_id, pubCand_id] at this
          have hs' : inSel (selIds m) c'.id = false := by rw [hid, ← hsel]; exact hs
          have hhot' : c'.hot = true := by
            have : (pubCand (selIds m) c').hot = (pubCand (selIds n) c).hot := by rw [he]
            rw [pubCand_hot, pubCand_hot] at this; rw [this]; exact hhot
          have h2 : due r env n (pubCand (selIds n) c) = due r env n c :=
            due_pub r env n _ c hs (.inr (hin.unfrozen han c hc))
          rw [← h2, ← he, due_congr hrt hcs hhs]
          exact not_due_pub_of_armed hcl hdr him hpm ham hc' hhot' hs'

/-! ## The coupling is preserved, event by event -/

theorem pub_id {x y : Node} (h : pubNode x = pubNode y) : x.id = y.id := congrArg PubNode.id h
theorem pub_t {x y : Node} (h : pubNode x = pubNode y) : x.t = y.t := congrArg PubNode.t h
theorem pub_poisoned {x y : Node} (h : pubNode x = pubNode y) : x.poisoned = y.poisoned :=
  congrArg PubNode.poisoned h
theorem pub_lockedDown {x y : Node} (h : pubNode x = pubNode y) : x.lockedDown = y.lockedDown :=
  congrArg PubNode.lockedDown h
theorem pub_carriers {x y : Node} (h : pubNode x = pubNode y) :
    x.carriers.map pubCarrier = y.carriers.map pubCarrier := congrArg PubNode.carriers h
theorem pub_cands {x y : Node} (h : pubNode x = pubNode y) :
    x.cands.map (pubCand (selIds x)) = y.cands.map (pubCand (selIds y)) := congrArg PubNode.cands h
theorem pub_sel {x y : Node} (h : pubNode x = pubNode y) : selIds x = selIds y :=
  congrArg PubNode.sel h
theorem pub_duressDelay {x y : Node} (h : pubNode x = pubNode y) : x.duressDelay = y.duressDelay :=
  congrArg PubNode.duressDelay h
theorem pub_epsilon {x y : Node} (h : pubNode x = pubNode y) : x.epsilon = y.epsilon :=
  congrArg PubNode.epsilon h
theorem pub_combineSlack {x y : Node} (h : pubNode x = pubNode y) : x.combineSlack = y.combineSlack :=
  congrArg PubNode.combineSlack h
theorem pub_holdSecs {x y : Node} (h : pubNode x = pubNode y) : x.holdSecs = y.holdSecs :=
  congrArg PubNode.holdSecs h

theorem pub_tombstones {x y : Node} (h : pubNode x = pubNode y) :
    x.tombstones.map pubTombstone = y.tombstones.map pubTombstone := congrArg PubNode.tombstones h

theorem pub_ratchet {x y : Node} (h : pubNode x = pubNode y) : x.ratchet = y.ratchet :=
  congrArg PubNode.ratchet h

theorem pub_unarmedT {x y : Node} (h : pubNode x = pubNode y) : x.unarmedT = y.unarmedT :=
  congrArg PubNode.unarmedT h

theorem pub_pendingLog {x y : Node} (h : pubNode x = pubNode y) : x.pendingLog = y.pendingLog :=
  congrArg PubNode.pendingLog h

theorem pubNode_ext {x y : Node} (hid : x.id = y.id) (ht : x.t = y.t)
    (hp : x.poisoned = y.poisoned) (hl : x.lockedDown = y.lockedDown)
    (hk : x.carriers.map pubCarrier = y.carriers.map pubCarrier)
    (hc : x.cands.map (pubCand (selIds x)) = y.cands.map (pubCand (selIds y)))
    (hs : selIds x = selIds y) (hd : x.duressDelay = y.duressDelay) (he : x.epsilon = y.epsilon)
    (hcs : x.combineSlack = y.combineSlack) (hh : x.holdSecs = y.holdSecs)
    (hm : x.tombstones.map pubTombstone = y.tombstones.map pubTombstone)
    (hrt : x.ratchet = y.ratchet) (hu : x.unarmedT = y.unarmedT)
    (hpl : x.pendingLog = y.pendingLog) : pubNode x = pubNode y := by
  simp only [pubNode, PubNode.mk.injEq]
  exact ⟨hid, ht, hp, hl, hk, hc, hs, hd, he, hcs, hh, hm, hrt, hu, hpl⟩

/-- What `DUR-20`'s window write leaves visible on a projected candidate: that an entry's window
is installed, and not the `T` it was written from. -/
def winMark (ids : List Nat) (ec : Cand) : Cand :=
  if inSel ids ec.id then { ec with windowClose := some (Wall.sample 0) } else ec

/-- `DUR-20`'s window write through the projection: the value vanishes, because it is written
from `T`, and only the installation remains. -/
theorem pubCand_withWindow (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    pubCand (sel.map (·.1)) (withWindow sel T slack c)
      = winMark (sel.map (·.1)) (pubCand (sel.map (·.1)) c) := by
  by_cases h : sel.any (·.1 == c.id) = true
  · have h' : inSel (sel.map (·.1)) c.id = true := by
      simp only [inSel, List.any_map, Function.comp_def]; exact h
    simp [pubCand, withWindow, winMark, h, h', withWindow_id]
  · simp only [Bool.not_eq_true] at h
    have h' : inSel (sel.map (·.1)) c.id = false := by
      simp only [inSel, List.any_map, Function.comp_def]; exact h
    simp [pubCand, withWindow, winMark, h, h']

theorem pubCand_writeWindows (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (l : List Cand) :
    (writeWindows sel T slack l).map (pubCand (sel.map (·.1)))
      = (l.map (pubCand (sel.map (·.1)))).map (winMark (sel.map (·.1))) := by
  simp only [writeWindows, List.map_map, Function.comp_def, pubCand_withWindow]

/-- `DUR-11`'s freeze bit is the only thing an arm writes at a candidate's birth. The node id
`born` seeds the held set with is the same in both runs — `pubNode` keeps it — so possession at
birth is pin-uniform too. -/
theorem pubCand_born (sel : List Nat) (self : Nat) (x y : Bool) (now : Mono) (c : Cand) :
    pubCand sel (born self x now c) = pubCand sel (born self y now c) := by
  by_cases h : inSel sel (born self x now c).id = true
  · have h2 : inSel sel (born self y now c).id = true := by simpa [born] using h
    simp [pubCand, born, h, h2]
  · simp only [Bool.not_eq_true] at h
    have h2 : inSel sel (born self y now c).id = false := by simpa [born] using h
    simp [pubCand, born, h, h2]

theorem traverses_always {r : Rules} (ht : r.traversal = .always) (env : Env) (n : Node)
    (sp : Cand) : traverses r env n sp = sp.hot := by simp [traverses, ht]

/-- A predicate on Carriers that `pubCarrier` does not change answers the same `any` on two nodes
with one public projection. -/
theorem carriers_any_pub {x y : Node} (h : pubNode x = pubNode y) (p : Carrier → Bool)
    (hp : ∀ k, p k = p (pubCarrier k)) : x.carriers.any p = y.carriers.any p := by
  rw [any_comm pubCarrier p x.carriers p (fun k _ => hp k),
      any_comm pubCarrier p y.carriers p (fun k _ => hp k), pub_carriers h]

theorem cands_any_pub' {x y : Node} (h : pubNode x = pubNode y) (p : Cand → Bool)
    (hp : ∀ sel c, p c = p (pubCand sel c)) : x.cands.any p = y.cands.any p := by
  rw [any_comm (pubCand (selIds x)) p x.cands p (fun c _ => hp _ c),
      any_comm (pubCand (selIds y)) p y.cands p (fun c _ => hp _ c), pub_cands h]

theorem pairAdmits_pub (r : Rules) {x y : Node} (h : pubNode x = pubNode y) (sp es : Cand) :
    pairAdmits r x sp es = pairAdmits r y sp es := by
  simp only [pairAdmits]
  rw [cands_any_pub' h _ (fun sel c => by simp [pubCand_id]),
    cands_any_pub' h (fun c => c.id == es.id) (fun sel c => by simp [pubCand_id]),
    cands_any_pub' h _ (fun sel c => by simp [pubCand_id, pubCand_tx, pubCand_hot, pubCand_expiry,
      pubCand_pair])]

theorem register_pub (r : Rules) {x y : Node} (h : pubNode x = pubNode y) (now : Mono) (sp es : Cand) :
    (register r x now sp es).map (pubCand (selIds x))
      = (register r y now sp es).map (pubCand (selIds y)) := by
  have hsel : selIds x = selIds y := pub_sel h
  have hid : x.id = y.id := pub_id h
  have hc := pub_cands h
  unfold register
  rw [cands_any_pub' h (fun c => c.id == sp.id) (fun sel c => by simp [pubCand_id])]
  split
  · exact hc
  · simp only [List.map_cons]
    rw [hsel] at hc ⊢
    rw [pubCand_born (selIds y) x.id x.armed y.armed now { sp with pair := some (sp.id, es.id) },
      pubCand_born (selIds y) x.id x.armed y.armed now { es with pair := some (sp.id, es.id) }, hid, hc]

theorem tombstones_any_pub {x y : Node} (h : pubNode x = pubNode y) (p : Tombstone → Bool)
    (hp : ∀ k, p k = p (pubTombstone k)) : x.tombstones.any p = y.tombstones.any p := by
  rw [any_comm pubTombstone p x.tombstones p (fun k _ => hp k),
      any_comm pubTombstone p y.tombstones p (fun k _ => hp k), pub_tombstones h]

theorem refuse_pub {r : Rules} (env : Env) {na nb : Node}
    (hn : pubNode na = pubNode nb) (cid : Nat) (da db : Bool) (E : Wall)
    (pair : Option (Nat × Nat)) :
    pubNode (refuse r env na cid da E pair) = pubNode (refuse r env nb cid db E pair) := by
  simp only [refuse, pub_lockedDown hn, carriers_any_pub hn (fun k => k.cid == cid) (fun _ => rfl),
    tombstones_any_pub hn (fun k => k.cid == cid) (fun _ => rfl)]
  split
  · exact hn
  · cases hd : Mono.deadline env.mono E env.eff with
    | none => exact hn
    | some D =>
      apply pubNode_ext
      · exact pub_id (x := na) (y := nb) hn
      · exact pub_t (x := na) (y := nb) hn
      · exact pub_poisoned (x := na) (y := nb) hn
      · rfl
      · simp [pubCarrier, pub_carriers hn]
      · exact pub_cands (x := na) (y := nb) hn
      · exact pub_sel (x := na) (y := nb) hn
      · exact pub_duressDelay (x := na) (y := nb) hn
      · exact pub_epsilon (x := na) (y := nb) hn
      · exact pub_combineSlack (x := na) (y := nb) hn
      · exact pub_holdSecs (x := na) (y := nb) hn
      · exact pub_tombstones (x := na) (y := nb) hn
      · exact pub_ratchet (x := na) (y := nb) hn
      · exact pub_unarmedT (x := na) (y := nb) hn
      · exact pub_pendingLog (x := na) (y := nb) hn

/-- `SPN-30`'s write at an acceptance reads the request, the registry's ids and the log itself,
and the projection keeps all three. -/
theorem logRegistration_pub (r : Rules) {x y : Node} (h : pubNode x = pubNode y) (sp es : Cand) :
    logRegistration r x sp es = logRegistration r y sp es := by
  simp only [logRegistration, pub_pendingLog h,
    cands_any_pub' h (fun c => c.id == sp.id) (fun sel c => by simp [pubCand_id])]

/-- An acceptance (`SPN-32`, `DUR-4`), under the unconditional traversal (`ht`). The intent's duress
bit is the only field of it the projection erases, and `DUR-11`'s birth freeze is the only field of
the pair's. -/
theorem accept_pub {r : Rules} (ht : r.traversal = .always) (env : Env) {na nb : Node}
    (hn : pubNode na = pubNode nb) (cid : Nat) (da db : Bool) (E : Wall) (sp es : Cand) :
    pubNode (accept r env na cid da E sp es) = pubNode (accept r env nb cid db E sp es) := by
  have hguard : (na.lockedDown || na.carriers.any (·.cid == cid) || na.tombstones.any (·.cid == cid) || !pairAdmits r na sp es)
      = (nb.lockedDown || nb.carriers.any (·.cid == cid) || nb.tombstones.any (·.cid == cid) || !pairAdmits r nb sp es) := by
    rw [pub_lockedDown hn, carriers_any_pub hn _ (fun _ => rfl), tombstones_any_pub hn _ (fun _ => rfl), pairAdmits_pub r hn]
  simp only [accept, hguard]
  split
  · exact refuse_pub env hn cid da db E _
  · cases hd : Mono.deadline env.mono E env.eff with
    | none => simp only [hd]; exact hn
    | some D =>
      simp only [hd, traverses_always ht]
      refine pubNode_ext (by show na.id = nb.id; exact pub_id hn)
        (by show na.t = nb.t; exact pub_t hn)
        (by show na.poisoned = nb.poisoned; exact pub_poisoned hn)
        (by show na.lockedDown = nb.lockedDown; exact pub_lockedDown hn) ?_ ?_
        (by show selIds na = selIds nb; exact pub_sel hn)
        (by show na.duressDelay = nb.duressDelay; exact pub_duressDelay hn)
        (by show na.epsilon = nb.epsilon; exact pub_epsilon hn)
        (by show na.combineSlack = nb.combineSlack; exact pub_combineSlack hn)
        (by show na.holdSecs = nb.holdSecs; exact pub_holdSecs hn)
        (by show na.tombstones.map pubTombstone = nb.tombstones.map pubTombstone; exact pub_tombstones hn)
        (by dsimp only; simp only [advanceRatchet, pub_ratchet hn])
        (by show na.unarmedT = nb.unarmedT; exact pub_unarmedT hn)
        (by show logRegistration r na sp es = logRegistration r nb sp es
            exact logRegistration_pub r hn sp es)
      · simp [pubCarrier, pub_carriers hn]
      · have hbase :
            (register r na env.mono sp es).map (pubCand (selIds na))
              = (register r nb env.mono sp es).map (pubCand (selIds nb)) := register_pub r hn env.mono sp es
        simp only [selIds] at hbase ⊢
        by_cases hh : sp.hot = true
        · rw [if_pos hh, if_pos hh, pubCand_writeWindows na.selected, pubCand_writeWindows nb.selected,
            hbase, show na.selected.map (·.1) = nb.selected.map (·.1) from pub_sel hn]
        · rw [if_neg hh, if_neg hh]
          exact hbase

/-! ### The updates a step writes, through the projection -/

theorem pubCand_set_released (sel : List Nat) (c : Cand) :
    pubCand sel { c with released := true } = { pubCand sel c with released := true } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

/-- A write to the held set commutes with the projection: an update of possession is the same
update on the projected candidate, whichever run performed it. -/
theorem pubCand_set_held (sel : List Nat) (c : Cand) (held : List Nat) :
    pubCand sel { c with heldSigners := held }
      = { pubCand sel c with heldSigners := held } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

theorem pubCand_set_packageOk (sel : List Nat) (c : Cand) :
    pubCand sel { c with packageOk := true } = { pubCand sel c with packageOk := true } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

theorem pubCand_set_send (sel : List Nat) (c : Cand) (go : Bool) :
    pubCand sel { c with packageOk := false, broadcast := c.broadcast || go }
      = { pubCand sel c with packageOk := false, broadcast := (pubCand sel c).broadcast || go } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

theorem pubCand_set_settled (sel : List Nat) (c : Cand) :
    pubCand sel { c with settled := true } = { pubCand sel c with settled := true } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

theorem pubCand_set_terminal (sel : List Nat) (c : Cand) :
    pubCand sel { c with terminal := true } = { pubCand sel c with terminal := true } := by
  by_cases h : inSel sel c.id <;> simp [pubCand, h]

theorem pubCarrier_cid_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') : k.cid = k'.cid := by
  have := congrArg Carrier.cid h; exact this
theorem pubCarrier_relaySenders_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') :
    k.relaySenders = k'.relaySenders := by
  have := congrArg Carrier.relaySenders h; exact this
theorem pubCarrier_E_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') : k.E = k'.E := by
  have := congrArg Carrier.E h; exact this
theorem pubCarrier_D_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') : k.D = k'.D := by
  have := congrArg Carrier.D h; exact this
theorem pubCarrier_pair_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') :
    k.pair = k'.pair := by have := congrArg Carrier.pair h; exact this

theorem pubCarrier_opens_eq {k k' : Carrier} (h : pubCarrier k = pubCarrier k') :
    opens k = opens k' := by
  have hp := pubCarrier_pair_eq h
  have ho : k.mayOpen = k'.mayOpen := by have := congrArg Carrier.mayOpen h; exact this
  funext id
  simp [opens, hp, ho]

theorem find?_pub {x y : Node} (h : pubNode x = pubNode y) (cid : Nat) :
    (x.carriers.find? (·.cid == cid)).map pubCarrier
      = (y.carriers.find? (·.cid == cid)).map pubCarrier := by
  rw [find?_comm pubCarrier (fun k => k.cid == cid) x.carriers (fun k => k.cid == cid)
        (fun k _ => rfl),
      find?_comm pubCarrier (fun k => k.cid == cid) y.carriers (fun k => k.cid == cid)
        (fun k _ => rfl), pub_carriers h]

/-- `DUR-5`'s condition is pin-uniform, which is what `DEF-12` requires of everything keyed on
it. -/
@[req "DEF-12"]
theorem commits_pub {x y : Node} (h : pubNode x = pubNode y) (env : Env) (cid sender : Nat) :
    commits env x cid sender = commits env y cid sender := by
  have hf := find?_pub h cid
  simp only [commits, pub_t h, pub_id h]
  cases hx : x.carriers.find? (·.cid == cid) with
  | none =>
    cases hy : y.carriers.find? (·.cid == cid) with
    | none => rfl
    | some k' => rw [hx, hy] at hf; simp at hf
  | some k =>
    cases hy : y.carriers.find? (·.cid == cid) with
    | none => rw [hx, hy] at hf; simp at hf
    | some k' =>
      rw [hx, hy] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      show (env.mono.before k.D && env.eff.before k.E &&
          decide (y.t ≤ holderCount (addSender y.id k.relaySenders sender)))
        = (env.mono.before k'.D && env.eff.before k'.E &&
          decide (y.t ≤ holderCount (addSender y.id k'.relaySenders sender)))
      rw [pubCarrier_D_eq hf, pubCarrier_E_eq hf, pubCarrier_relaySenders_eq hf]

/-! ### `DUR-10`'s set insertion keeps the ids pin-uniform -/

theorem selIds_insertSelected (sel : List (Nat × Bool)) (id : Nat) (d : Bool) :
    (insertSelected sel id d).map (·.1)
      = if sel.any (·.1 == id) then sel.map (·.1) else sel.map (·.1) ++ [id] := by
  unfold insertSelected
  split
  · rename_i h
    simp only [List.map_map, Function.comp_def]
    refine List.map_congr_left fun e _ => ?_
    split <;> rfl
  · rename_i h
    simp [h]

theorem inSel_append (sel : List Nat) (id i : Nat) :
    inSel (sel ++ [id]) i = (inSel sel i || (id == i)) := by
  simp [inSel, List.any_append]

/-- An id in the set before a holder decision is in it after: "nothing is ever displaced". -/
@[req "DUR-10"]
theorem inSel_insert_of_inSel (sel : List (Nat × Bool)) (id : Nat) (d : Bool) (i : Nat)
    (h : inSel (sel.map (·.1)) i = true) :
    inSel ((insertSelected sel id d).map (·.1)) i = true := by
  rw [selIds_insertSelected]
  split
  · exact h
  · rw [inSel_append, h, Bool.true_or]

theorem inSel_selectIntent_of_inSel (sel : List (Nat × Bool)) (k : Carrier) (d : Bool) (i : Nat)
    (h : inSel (sel.map (·.1)) i = true) :
    inSel ((selectIntent sel k d).map (·.1)) i = true := by
  unfold selectIntent
  split
  · exact h
  · exact inSel_insert_of_inSel _ _ _ _ h

theorem selectIntent_ids {a b : Node} (h : selIds a = selIds b) {ka kb : Carrier}
    (hk : ka.pair = kb.pair) (da db : Bool) :
    (selectIntent a.selected ka da).map (·.1) = (selectIntent b.selected kb db).map (·.1) := by
  unfold selectIntent
  rw [hk]
  cases hp : kb.pair with
  | none => exact h
  | some p =>
    have hany : a.selected.any (·.1 == p.2) = b.selected.any (·.1 == p.2) := by
      rw [← inSel_selIds, ← inSel_selIds, h]
    simp only [selIds_insertSelected, hany]
    change (if _ then selIds a else selIds a ++ [p.2]) = _
    rw [h]
    rfl

/-! ### `DUR-13`'s computed value, through the projection and beside `T` -/

theorem foldl_pub {α β : Type} (pub : α → α) (f : β → α → β) (hf : ∀ b a, f b (pub a) = f b a) :
    ∀ (l : List α) (init : β), l.foldl f init = (l.map pub).foldl f init
  | [], _ => rfl
  | a :: l, init => by
    simp only [List.foldl_cons, List.map_cons, hf]
    exact foldl_pub pub f hf l _

theorem intentRecords_pub (r : Rules) {x y : Node} (h : pubNode x = pubNode y) :
    (intentRecords r x).map pubTombstone = (intentRecords r y).map pubTombstone := by
  have hc : (x.carriers.map Carrier.tombstone).map pubTombstone =
      (y.carriers.map Carrier.tombstone).map pubTombstone := by
    have := congrArg (List.map Carrier.tombstone) (pub_carriers h)
    simpa [List.map_map, Function.comp_def, pubTombstone, pubCarrier, Carrier.tombstone] using this
  simp only [intentRecords, List.map_append, hc]
  split <;> simp [pub_tombstones h]

/-- `DUR-13`'s ingress start reads the intents' samples and bindings, never a duress bit. -/
theorem pairFirstSeen_pub {r : Rules} {x y : Node} (h : pubNode x = pubNode y) {kx ky : Carrier}
    (hk : pubCarrier kx = pubCarrier ky) : pairFirstSeen r x kx = pairFirstSeen r y ky := by
  have hfs : kx.firstSeen = ky.firstSeen := by have := congrArg Carrier.firstSeen hk; exact this
  have hp := pubCarrier_pair_eq hk
  unfold pairFirstSeen
  rw [foldl_pub pubTombstone _ (fun _ _ => rfl) (intentRecords r x),
    foldl_pub pubTombstone _ (fun _ _ => rfl) (intentRecords r y), intentRecords_pub r h, hfs, hp]

/-- `Node.unarmedT`'s write reads only what the projection keeps: the scan's filter, the fire
time off the selected set, and `unarmedT` itself on it. -/
theorem unarmedDeadline_pub {r : Rules} {env : Env} {x y : Node} (h : pubNode x = pubNode y)
    {kx ky : Carrier} (hk : pubCarrier kx = pubCarrier ky) :
    unarmedDeadline r env x kx = unarmedDeadline r env y ky := by
  let G : Cand → Option Wall := fun ec =>
    if pendingHot env ec then
      (if inSel (selIds x) ec.id then some x.unarmedT else ec.fireAt) else none
  have hfac : ∀ (n : Node), selIds n = selIds x → n.unarmedT = x.unarmedT →
      (n.cands.filterMap fun c =>
        if pendingHot env c then
          (if n.selected.any (·.1 == c.id) then some n.unarmedT else c.fireAt) else none)
        = (n.cands.map (pubCand (selIds n))).filterMap G := by
    intro n hs hu
    rw [List.filterMap_map]
    congr 1
    funext c
    simp only [Function.comp_apply, G, pendingHot, pubCand_hot, pubCand_broadcast, pubCand_expiry,
      pubCand_id, ← hs, ← inSel_selIds, hu]
    by_cases hsel : inSel (selIds n) c.id = true
    · simp [hsel]
    · simp only [Bool.not_eq_true] at hsel
      simp [hsel, pubCand_fireAt_of_not_sel _ c hsel]
  unfold unarmedDeadline newDeadline earliestHotFire
  rw [hfac x rfl rfl, hfac y (pub_sel h).symm (pub_unarmedT h).symm, pub_cands h,
    pairFirstSeen_pub h hk, pub_duressDelay h, pub_epsilon h]

/-- Two lists of instants, pairwise in order. -/
def PairwiseLe : List Wall → List Wall → Prop
  | [], [] => True
  | x :: xs, y :: ys => Wall.atOrBefore x y = true ∧ PairwiseLe xs ys
  | _, _ => False

theorem filterMap_pairwiseLe (f g : Cand → Option Wall) :
    ∀ (l : List Cand), (∀ c ∈ l, (f c = none ∧ g c = none) ∨
        ∃ x y, f c = some x ∧ g c = some y ∧ Wall.atOrBefore x y = true) →
      PairwiseLe (l.filterMap f) (l.filterMap g)
  | [], _ => trivial
  | c :: l, h => by
    have ih := filterMap_pairwiseLe f g l (fun d hd => h d (by simp [hd]))
    rcases h c (by simp) with ⟨hf, hg⟩ | ⟨x, y, hf, hg, hxy⟩
    · simp only [List.filterMap_cons, hf, hg]; exact ih
    · simp only [List.filterMap_cons, hf, hg]; exact ⟨hxy, ih⟩

theorem foldEarliest_cons (w : Wall) (l : List Wall) (acc : Option Wall) :
    foldEarliest (w :: l) acc =
      foldEarliest l (some (match acc with | none => w | some a => Wall.earlier a w)) := rfl

theorem foldEarliest_mono : ∀ (la lb : List Wall) (aa ab : Option Wall),
    PairwiseLe la lb → Wall.optAtOrBefore aa ab = true →
      Wall.optAtOrBefore (foldEarliest la aa) (foldEarliest lb ab) = true
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, hp, _ => absurd hp id
  | _ :: _, [], _, _, hp, _ => absurd hp id
  | x :: xs, y :: ys, aa, ab, ⟨hxy, hrest⟩, h => by
    rw [foldEarliest_cons, foldEarliest_cons]
    apply foldEarliest_mono xs ys _ _ hrest
    cases aa <;> cases ab <;> simp_all [Wall.optAtOrBefore]
    exact Wall.earlier_mono h hxy

/-- `DUR-13`'s computed value and `unarmedT`'s write, in order whichever way `T` and `unarmedT`
stand: the two scans differ only at a selected hot candidate, whose fire time is `T`
(`NodeInv.selWin`) in the one and `unarmedT` in the other. -/
theorem newDeadline_unarmed_le {r : Rules} {env : Env} {n : Node} {L : Effective} (hi : NodeInv n L)
    (k : Carrier) :
    (Wall.atOrBefore n.T n.unarmedT = true →
      Wall.atOrBefore (newDeadline r env n k) (unarmedDeadline r env n k) = true) ∧
    (Wall.atOrBefore n.unarmedT n.T = true →
      Wall.atOrBefore (unarmedDeadline r env n k) (newDeadline r env n k) = true) := by
  let F : Cand → Option Wall := fun c =>
    if pendingHot env c then c.fireAt else none
  let Gh : Cand → Option Wall := fun c =>
    if pendingHot env c then
      (if n.selected.any (·.1 == c.id) then some n.unarmedT else c.fireAt) else none
  have pw : ∀ (f g : Cand → Option Wall) (A B : Wall), Wall.atOrBefore A B = true →
      (∀ c ∈ n.cands, f c = F c ∨ f c = Gh c) → (∀ c ∈ n.cands, g c = F c ∨ g c = Gh c) →
      (∀ c ∈ n.cands, (n.selected.any (·.1 == c.id) = true → c.hot = true →
        pendingHot env c = true →
          f c = some A ∧ g c = some B) ∧
        ((n.selected.any (·.1 == c.id) = true → c.hot = false ∨
          pendingHot env c = false) → f c = g c)) →
      PairwiseLe (n.cands.filterMap f) (n.cands.filterMap g) := by
    intro f g A B hAB _ _ hc
    refine filterMap_pairwiseLe f g n.cands (fun c hcm => ?_)
    obtain ⟨hsel, hoff⟩ := hc c hcm
    by_cases hs : n.selected.any (·.1 == c.id) = true
    · by_cases hh : c.hot = true
      · by_cases hcond : pendingHot env c = true
        · obtain ⟨h1, h2⟩ := hsel hs hh hcond
          exact .inr ⟨A, B, h1, h2, hAB⟩
        · rw [hoff (fun _ => .inr (by simpa using hcond))]
          cases g c with
          | none => exact .inl ⟨rfl, rfl⟩
          | some y => exact .inr ⟨y, y, rfl, rfl, Wall.atOrBefore_refl y⟩
      · rw [hoff (fun _ => .inl (by simpa using hh))]
        cases g c with
        | none => exact .inl ⟨rfl, rfl⟩
        | some y => exact .inr ⟨y, y, rfl, rfl, Wall.atOrBefore_refl y⟩
    · rw [hoff (fun h => absurd h hs)]
      cases g c with
      | none => exact .inl ⟨rfl, rfl⟩
      | some y => exact .inr ⟨y, y, rfl, rfl, Wall.atOrBefore_refl y⟩
  have hfire : ∀ c ∈ n.cands, n.selected.any (·.1 == c.id) = true → c.hot = true →
      c.fireAt = some n.T :=
    fun c hc hs hh => (hi.selWin c hc (by rw [inSel_selIds]; exact hs)).2 hh
  have shape : ∀ c ∈ n.cands,
      (n.selected.any (·.1 == c.id) = true → c.hot = true →
        pendingHot env c = true →
          F c = some n.T ∧ Gh c = some n.unarmedT) ∧
      ((n.selected.any (·.1 == c.id) = true → c.hot = false ∨
        pendingHot env c = false) → F c = Gh c) := by
    intro c hc
    refine ⟨fun hs hh hcond => ?_, fun hoff => ?_⟩
    · simp only [F, Gh, hcond, if_true, hs, hfire c hc hs hh, and_self]
    · simp only [F, Gh]
      by_cases hs : n.selected.any (·.1 == c.id) = true
      · rcases hoff hs with h | h
        · simp [h]
        · rw [if_neg (by simp only [h, Bool.false_eq_true, not_false_eq_true]),
            if_neg (by simp only [h, Bool.false_eq_true, not_false_eq_true])]
      · simp only [Bool.not_eq_true] at hs
        simp [hs]
  have dead : ∀ (ea eb : Option Wall), Wall.optAtOrBefore ea eb = true →
      Wall.atOrBefore (Wall.initialDeadline (pairFirstSeen r n k) n.duressDelay env.eff ea n.epsilon)
        (Wall.initialDeadline (pairFirstSeen r n k) n.duressDelay env.eff eb n.epsilon) = true :=
    fun ea eb h => Wall.initialDeadline_mono _ _ _ _ h
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · refine dead _ _ (foldEarliest_mono _ _ none none ?_ rfl)
    exact pw F Gh n.T n.unarmedT hT (fun _ _ => .inl rfl) (fun _ _ => .inr rfl)
      (fun c hc => ⟨(shape c hc).1, (shape c hc).2⟩)
  · refine dead _ _ (foldEarliest_mono _ _ none none ?_ rfl)
    exact pw Gh F n.unarmedT n.T hT (fun _ _ => .inr rfl) (fun _ _ => .inl rfl)
      (fun c hc => ⟨fun a b d => ((shape c hc).1 a b d).symm, fun h => ((shape c hc).2 h).symm⟩)

/-- The written `T` is at most the computed one, under every value of `Rules.clampOn`. -/
theorem writtenDeadline_le (r : Rules) (env : Env) (n : Node) (k : Carrier) :
    Wall.atOrBefore (writtenDeadline r env n k) (newDeadline r env n k) = true := by
  unfold writtenDeadline
  split
  · exact Wall.clamp_le_initial _ _ _ _ _ _
  · exact Wall.atOrBefore_refl _

/-- A decision that leaves its node unarmed writes the computed value, under every value of
`Rules.clampOn`: no selector picks the clamp on a node unarmed before and after. -/
theorem writtenDeadline_eq_of_unarmed {r : Rules} {env : Env} {n : Node} {k : Carrier}
    (ha : n.armed = false) (hp : pairDuress r n k = false) :
    writtenDeadline r env n k = newDeadline r env n k := by
  unfold writtenDeadline clampSelected
  cases r.clampOn <;> simp [ha, hp]

/-! ### Each event through the projection -/

/-- What a holder decision does to a projected candidate: `DUR-5`'s pin-uniform quorum write,
and the window of an entry the same decision selected — installed, its value erased because it
is written from `T`. -/
def holderG (newIds : List Nat) (opening : Nat → Bool) (ec : Cand) : Cand :=
  if inSel newIds ec.id then
    { ec with quorum := ec.quorum || opening ec.id, frozen := false,
              fireAt := none, windowClose := some (Wall.sample 0) }
  else { ec with quorum := ec.quorum || opening ec.id, frozen := false }

theorem pubCand_holder (selPairs : List (Nat × Bool)) (T : Wall) (slack : Secs)
    (opening : Nat → Bool) (d : Bool) (oldIds : List Nat) (c : Cand)
    (hsub : ∀ i, inSel oldIds i = true → inSel (selPairs.map (·.1)) i = true) :
    pubCand (selPairs.map (·.1))
        (withWindow selPairs T slack
          { c with quorum := c.quorum || opening c.id,
                   frozen := c.frozen || (c.hot && d) })
      = holderG (selPairs.map (·.1)) opening (pubCand oldIds c) := by
  rw [pubCand_withWindow]
  by_cases hnew : inSel (selPairs.map (·.1)) c.id = true
  · by_cases hold : inSel oldIds c.id = true <;> simp [pubCand, holderG, winMark, hnew, hold]
  · simp only [Bool.not_eq_true] at hnew
    have hold : inSel oldIds c.id = false := by
      cases hh : inSel oldIds c.id with
      | false => rfl
      | true => exact absurd (hsub c.id hh) (by rw [hnew]; simp)
    simp [pubCand, holderG, winMark, hnew, hold]

/-- `DUR-5`'s holder decision: one write, and every field of it that differs between the two runs
is one the projection erases — the arm bit, the entry's duress bit, `T`, and every window `T`
writes. -/
theorem holderDecision_pub {r : Rules} {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb)
    {ka kb : Carrier} (hk : pubCarrier ka = pubCarrier kb) :
    pubNode (holderDecision r env na ka) = pubNode (holderDecision r env nb kb) := by
  have hsel : selIds na = selIds nb := pub_sel hn
  have hopen := pubCarrier_opens_eq hk
  have hcid : ka.cid = kb.cid := pubCarrier_cid_eq hk
  have hids := selectIntent_ids hsel (pubCarrier_pair_eq hk) (pairDuress r na ka) (pairDuress r nb kb)
  refine pubNode_ext (by show na.id = nb.id; exact pub_id hn)
    (by show na.t = nb.t; exact pub_t hn)
    (by show na.poisoned = nb.poisoned; exact pub_poisoned hn)
    (by show na.lockedDown = nb.lockedDown; exact pub_lockedDown hn) ?_ ?_
    (by show (selectIntent na.selected ka (pairDuress r na ka)).map (·.1)
          = (selectIntent nb.selected kb (pairDuress r nb kb)).map (·.1); exact hids)
    (by show na.duressDelay = nb.duressDelay; exact pub_duressDelay hn)
    (by show na.epsilon = nb.epsilon; exact pub_epsilon hn)
    (by show na.combineSlack = nb.combineSlack; exact pub_combineSlack hn)
    (by show na.holdSecs = nb.holdSecs; exact pub_holdSecs hn)
    (by
      have hm := congrArg (fun k => pubTombstone k.tombstone) hk
      simpa [holderDecision, pubTombstone, Carrier.tombstone, pubCarrier, pub_tombstones hn] using hm)
    (by
      have hmo : ka.mayOpen = kb.mayOpen := by simpa [pubCarrier] using congrArg Carrier.mayOpen hk
      dsimp only [holderDecision]
      first
        | (simp only [advanceRatchet, pub_ratchet hn]; done)
        | simp only [advanceRatchet, pub_ratchet hn, hmo])
    (by show unarmedDeadline r env na ka = unarmedDeadline r env nb kb
        exact unarmedDeadline_pub hn hk)
    (by show na.pendingLog = nb.pendingLog; exact pub_pendingLog hn)
  · show (na.carriers.filter (·.cid != ka.cid)).map pubCarrier
      = (nb.carriers.filter (·.cid != kb.cid)).map pubCarrier
    rw [hcid,
      filter_comm pubCarrier (fun k => k.cid != kb.cid) na.carriers (fun k => k.cid != kb.cid)
        (fun k _ => rfl),
      filter_comm pubCarrier (fun k => k.cid != kb.cid) nb.carriers (fun k => k.cid != kb.cid)
        (fun k _ => rfl),
      pub_carriers hn]
  · have hGa : ∀ c ∈ na.cands,
        (pubCand ((selectIntent na.selected ka (pairDuress r na ka)).map (·.1))
          (withWindow (selectIntent na.selected ka (pairDuress r na ka)) (writtenDeadline r env na ka)
            na.combineSlack
            { c with quorum := c.quorum || opens ka c.id,
                     frozen := c.frozen || (c.hot && (pairDuress r na ka)) }))
          = holderG ((selectIntent na.selected ka (pairDuress r na ka)).map (·.1)) (opens ka)
              (pubCand (selIds na) c) := by
      intro c _
      exact pubCand_holder _ _ _ _ _ _ c
        (fun i hi => inSel_selectIntent_of_inSel na.selected ka (pairDuress r na ka) i hi)
    have hGb : ∀ c ∈ nb.cands,
        (pubCand ((selectIntent nb.selected kb (pairDuress r nb kb)).map (·.1))
          (withWindow (selectIntent nb.selected kb (pairDuress r nb kb)) (writtenDeadline r env nb kb)
            nb.combineSlack
            { c with quorum := c.quorum || opens kb c.id,
                     frozen := c.frozen || (c.hot && (pairDuress r nb kb)) }))
          = holderG ((selectIntent nb.selected kb (pairDuress r nb kb)).map (·.1)) (opens kb)
              (pubCand (selIds nb) c) := by
      intro c _
      exact pubCand_holder _ _ _ _ _ _ c
        (fun i hi => inSel_selectIntent_of_inSel nb.selected kb (pairDuress r nb kb) i hi)
    show (na.cands.map _).map (pubCand ((selectIntent na.selected ka (pairDuress r na ka)).map (·.1)))
      = (nb.cands.map _).map (pubCand ((selectIntent nb.selected kb (pairDuress r nb kb)).map (·.1)))
    simp only [List.map_map, Function.comp_def]
    rw [map_comm (pubCand (selIds na))
        (holderG ((selectIntent na.selected ka (pairDuress r na ka)).map (·.1)) (opens ka))
        na.cands _ hGa,
      map_comm (pubCand (selIds nb))
        (holderG ((selectIntent nb.selected kb (pairDuress r nb kb)).map (·.1)) (opens kb))
        nb.cands _ hGb,
      pub_cands hn, hids, hopen]

/-- A step that maps over the registry: both runs' updates factor through one function of the
projected candidate. -/
theorem map_pub {x y : Node} (h : pubNode x = pubNode y) {F₁ F₂ G : Cand → Cand}
    (h₁ : ∀ c ∈ x.cands, pubCand (selIds x) (F₁ c) = G (pubCand (selIds x) c))
    (h₂ : ∀ c ∈ y.cands, pubCand (selIds y) (F₂ c) = G (pubCand (selIds y) c)) :
    (x.cands.map F₁).map (pubCand (selIds x)) = (y.cands.map F₂).map (pubCand (selIds y)) := by
  simp only [List.map_map, Function.comp_def]
  rw [map_comm (pubCand (selIds x)) G x.cands _ h₁, map_comm (pubCand (selIds y)) G y.cands _ h₂,
    pub_cands h]

/-- A step that reads the registry: a filter and a map over it, both factoring. -/
theorem filter_map_pub {α : Type} {x y : Node} (h : pubNode x = pubNode y)
    {p₁ p₂ q : Cand → Bool} {f₁ f₂ : Cand → α} {g : Cand → α}
    (hp₁ : ∀ c ∈ x.cands, p₁ c = q (pubCand (selIds x) c))
    (hp₂ : ∀ c ∈ y.cands, p₂ c = q (pubCand (selIds y) c))
    (hf₁ : ∀ c, f₁ c = g (pubCand (selIds x) c)) (hf₂ : ∀ c, f₂ c = g (pubCand (selIds y) c)) :
    (x.cands.filter p₁).map f₁ = (y.cands.filter p₂).map f₂ := by
  rw [map_comm (pubCand (selIds x)) g (x.cands.filter p₁) f₁ (fun c _ => hf₁ c),
    map_comm (pubCand (selIds y)) g (y.cands.filter p₂) f₂ (fun c _ => hf₂ c),
    filter_comm (pubCand (selIds x)) q x.cands p₁ hp₁,
    filter_comm (pubCand (selIds y)) q y.cands p₂ hp₂, pub_cands h]

/-- Everything but the candidate list and the Carrier list is pin-uniform in one place. -/
theorem pubNode_ext_cands {x y : Node} (h : pubNode x = pubNode y) {cx cy : List Cand}
    (hc : cx.map (pubCand (selIds x)) = cy.map (pubCand (selIds y))) :
    pubNode { x with cands := cx } = pubNode { y with cands := cy } :=
  pubNode_ext (by show x.id = y.id; exact pub_id h) (by show x.t = y.t; exact pub_t h)
    (by show x.poisoned = y.poisoned; exact pub_poisoned h)
    (by show x.lockedDown = y.lockedDown; exact pub_lockedDown h)
    (by show x.carriers.map pubCarrier = y.carriers.map pubCarrier; exact pub_carriers h)
    (by show cx.map (pubCand (selIds x)) = cy.map (pubCand (selIds y)); exact hc)
    (by show selIds x = selIds y; exact pub_sel h)
    (by show x.duressDelay = y.duressDelay; exact pub_duressDelay h)
    (by show x.epsilon = y.epsilon; exact pub_epsilon h)
    (by show x.combineSlack = y.combineSlack; exact pub_combineSlack h)
    (by show x.holdSecs = y.holdSecs; exact pub_holdSecs h)
    (by show x.tombstones.map pubTombstone = y.tombstones.map pubTombstone; exact pub_tombstones h)
    (by show x.ratchet = y.ratchet; exact pub_ratchet h)
    (by show x.unarmedT = y.unarmedT; exact pub_unarmedT h)
    (by show x.pendingLog = y.pendingLog; exact pub_pendingLog h)

/-- The same, for a step that also writes the pending log, with one value in both runs. -/
theorem pubNode_ext_cands_log {x y : Node} (h : pubNode x = pubNode y) {cx cy : List Cand}
    (hc : cx.map (pubCand (selIds x)) = cy.map (pubCand (selIds y))) {lx ly : PendingLog}
    (hl : lx = ly) :
    pubNode { x with cands := cx, pendingLog := lx } = pubNode { y with cands := cy, pendingLog := ly } :=
  pubNode_ext (by show x.id = y.id; exact pub_id h) (by show x.t = y.t; exact pub_t h)
    (by show x.poisoned = y.poisoned; exact pub_poisoned h)
    (by show x.lockedDown = y.lockedDown; exact pub_lockedDown h)
    (by show x.carriers.map pubCarrier = y.carriers.map pubCarrier; exact pub_carriers h)
    (by show cx.map (pubCand (selIds x)) = cy.map (pubCand (selIds y)); exact hc)
    (by show selIds x = selIds y; exact pub_sel h)
    (by show x.duressDelay = y.duressDelay; exact pub_duressDelay h)
    (by show x.epsilon = y.epsilon; exact pub_epsilon h)
    (by show x.combineSlack = y.combineSlack; exact pub_combineSlack h)
    (by show x.holdSecs = y.holdSecs; exact pub_holdSecs h)
    (by show x.tombstones.map pubTombstone = y.tombstones.map pubTombstone; exact pub_tombstones h)
    (by show x.ratchet = y.ratchet; exact pub_ratchet h)
    (by show x.unarmedT = y.unarmedT; exact pub_unarmedT h)
    hl

/-- `DUR-5`'s holder set is pin-uniform: the relay's `sender_node_id` is one common input and
`pubCarrier` erases only the duress bit, so the set the two runs admit it into is the same set.
The two runs' own node ids are the other thing `addSender` reads, and `hs` is that they agree —
`pub_id` supplies it, since `PubNode` keeps `id`. -/
theorem pubCarrier_admit {k k' : Carrier} (h : pubCarrier k = pubCarrier k')
    {selfA selfB : Nat} (hs : selfA = selfB) (sender : Nat) :
    pubCarrier { k with relaySenders := addSender selfA k.relaySenders sender }
      = pubCarrier { k' with relaySenders := addSender selfB k'.relaySenders sender } := by
  subst hs
  simp only [pubCarrier] at h ⊢
  cases k; cases k'; simp_all

/-- A relay (`NCH-31`), and the holder decision it may run. -/
theorem receipt_pub {r : Rules} {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb)
    (cid sender : Nat) :
    pubNode (receipt r env na cid sender) = pubNode (receipt r env nb cid sender) := by
  have hf := find?_pub hn cid
  cases hx : na.carriers.find? (·.cid == cid) with
  | none =>
    cases hy : nb.carriers.find? (·.cid == cid) with
    | none => simp only [receipt, hx, hy]; exact hn
    | some k' => rw [hx, hy] at hf; simp at hf
  | some k =>
    cases hy : nb.carriers.find? (·.cid == cid) with
    | none => rw [hx, hy] at hf; simp at hf
    | some k' =>
      rw [hx, hy] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      have hguard : (!env.mono.before k.D || !env.eff.before k.E)
          = (!env.mono.before k'.D || !env.eff.before k'.E) := by
        rw [pubCarrier_D_eq hf, pubCarrier_E_eq hf]
      simp only [receipt, hx, hy, hguard]
      split
      · exact hn
      · rw [commits_pub hn env cid sender]
        split
        · exact holderDecision_pub hn (pubCarrier_admit hf (pub_id hn) sender)
        · refine pubNode_ext (by show na.id = nb.id; exact pub_id hn)
            (by show na.t = nb.t; exact pub_t hn)
            (by show na.poisoned = nb.poisoned; exact pub_poisoned hn)
            (by show na.lockedDown = nb.lockedDown; exact pub_lockedDown hn) ?_
            (by show na.cands.map (pubCand (selIds na)) = nb.cands.map (pubCand (selIds nb))
                exact pub_cands hn)
            (by show selIds na = selIds nb; exact pub_sel hn)
            (by show na.duressDelay = nb.duressDelay; exact pub_duressDelay hn)
            (by show na.epsilon = nb.epsilon; exact pub_epsilon hn)
            (by show na.combineSlack = nb.combineSlack; exact pub_combineSlack hn)
            (by show na.holdSecs = nb.holdSecs; exact pub_holdSecs hn)
            (by show na.tombstones.map pubTombstone = nb.tombstones.map pubTombstone; exact pub_tombstones hn)
            (by show na.ratchet = nb.ratchet; exact pub_ratchet hn)
            (by show na.unarmedT = nb.unarmedT; exact pub_unarmedT hn)
            (by show na.pendingLog = nb.pendingLog; exact pub_pendingLog hn)
          show (na.carriers.map _).map pubCarrier = (nb.carriers.map _).map pubCarrier
          simp only [List.map_map, Function.comp_def]
          rw [map_comm pubCarrier
              (fun ek => if ek.cid == cid then
                pubCarrier { k with relaySenders := addSender na.id k.relaySenders sender }
                else ek)
              na.carriers _ (fun x _ => by
                by_cases hb : (x.cid == cid) = true
                · simp only [pubCarrier_cid, hb, if_true]
                · simp only [Bool.not_eq_true] at hb
                  simp only [pubCarrier_cid, hb, Bool.false_eq_true, if_false]),
            map_comm pubCarrier
              (fun ek => if ek.cid == cid then
                pubCarrier { k with relaySenders := addSender na.id k.relaySenders sender }
                else ek)
              nb.carriers _ (fun x _ => by
                by_cases hb : (x.cid == cid) = true
                · simp only [pubCarrier_cid, hb, if_true]
                  exact (pubCarrier_admit hf (pub_id hn) sender).symm
                · simp only [Bool.not_eq_true] at hb
                  simp only [pubCarrier_cid, hb, Bool.false_eq_true, if_false]),
            pub_carriers hn]

/-- The fire pass (`DUR-8`, `SPN-38`): the release decision and the partial it queues. -/
theorem firePass_pub {r : Rules} (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb)
    (hia : NodeInv na na.ratchet) (hib : NodeInv nb nb.ratchet)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) :
    pubNode (firePass r env na).1 = pubNode (firePass r env nb).1 ∧
      (firePass r env na).2 = (firePass r env nb).2 := by
  have hsel : selIds na = selIds nb := pub_sel hn
  have hra := release_factor hcl hdr env na nb hsel (pub_cands hn) (pub_ratchet hn)
    (pub_combineSlack hn) (pub_holdSecs hn) hia hib hpa hpb
  have hrb := release_factor hcl hdr env nb na hsel.symm (pub_cands hn).symm (pub_ratchet hn).symm
    (pub_combineSlack hn).symm (pub_holdSecs hn).symm hib hia hpb hpa
  rw [releaseErased_congr (pub_ratchet hn).symm (pub_combineSlack hn).symm (pub_holdSecs hn).symm] at hrb
  have hguard : (r.poison == .asserted && na.poisoned) = (r.poison == .asserted && nb.poisoned) := by
    rw [pub_poisoned hn]
  simp only [firePass, hguard]
  split
  · refine ⟨?_, rfl⟩
    show pubNode { na with lockedDown := true } = pubNode { nb with lockedDown := true }
    exact pubNode_ext (by show na.id = nb.id; exact pub_id hn) (by show na.t = nb.t; exact pub_t hn)
      (by show na.poisoned = nb.poisoned; exact pub_poisoned hn) rfl
      (by show na.carriers.map pubCarrier = nb.carriers.map pubCarrier; exact pub_carriers hn)
      (by show na.cands.map (pubCand (selIds na)) = nb.cands.map (pubCand (selIds nb))
          exact pub_cands hn)
      (by show selIds na = selIds nb; exact pub_sel hn)
      (by show na.duressDelay = nb.duressDelay; exact pub_duressDelay hn)
      (by show na.epsilon = nb.epsilon; exact pub_epsilon hn)
      (by show na.combineSlack = nb.combineSlack; exact pub_combineSlack hn)
      (by show na.holdSecs = nb.holdSecs; exact pub_holdSecs hn)
      (by show na.tombstones.map pubTombstone = nb.tombstones.map pubTombstone; exact pub_tombstones hn)
      (by show na.ratchet = nb.ratchet; exact pub_ratchet hn)
      (by show na.unarmedT = nb.unarmedT; exact pub_unarmedT hn)
      (by show na.pendingLog = nb.pendingLog; exact pub_pendingLog hn)
  · constructor
    · show pubNode { na with cands := (na.cands.map fun c =>
            if due r env na c && releaseAuthorized na c then { c with released := true } else c) }
          = pubNode { nb with cands := (nb.cands.map fun c =>
            if due r env nb c && releaseAuthorized nb c then { c with released := true } else c) }
      refine pubNode_ext_cands hn (map_pub hn (G := fun ec =>
        if releaseErased r env na (selIds na) (na.armed || nb.armed) ec then
          { ec with released := true } else ec) ?_ ?_)
      · intro c hc
        simp only [hra c hc]
        by_cases hq : releaseErased r env na (selIds na) (na.armed || nb.armed)
            (pubCand (selIds na) c) = true
        · rw [if_pos hq, if_pos hq]; exact pubCand_set_released _ c
        · rw [if_neg hq, if_neg hq]
      · intro c hc
        simp only [hrb c hc, Bool.or_comm nb.armed na.armed, ← hsel]
        by_cases hq : releaseErased r env na (selIds na) (na.armed || nb.armed)
            (pubCand (selIds na) c) = true
        · rw [if_pos hq, if_pos hq]; exact pubCand_set_released _ c
        · rw [if_neg hq, if_neg hq]
    · show ((na.cands.filter fun c => due r env na c && releaseAuthorized na c && !c.released).map
            fun c => Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id)
          = ((nb.cands.filter fun c => due r env nb c && releaseAuthorized nb c && !c.released).map
            fun c => Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id)
      refine filter_map_pub hn (q := fun ec =>
        releaseErased r env na (selIds na) (na.armed || nb.armed) ec && !ec.released)
        (g := fun ec => Effect.queuePartial (sighash ec.tx 0) 0 ec.hot ec.id)
        (fun c hc => by simp [hra c hc, pubCand_released]) ?_
        (fun c => by simp [pubCand_tx, pubCand_hot, pubCand_id])
        (fun c => by simp [pubCand_tx, pubCand_hot, pubCand_id])
      intro c hc
      simp [hrb c hc, Bool.or_comm nb.armed na.armed, ← hsel, pubCand_released]

/-- `SPN-39`'s package test, with `DUR-29`'s Escape half of the re-authorization. The quorum it
reads is this node's possession — `released` and the held set, both of them pin-uniform
(`pubCand_released`, `pubCand_held`) — and not the world's exposure, so no hypothesis on the
exposure is needed. -/
theorem packageAccepted_pub {r : Rules} (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {env : Env} {wa wb : World}
    (hn : pubNode wa.node = pubNode wb.node)
    (hia : NodeInv wa.node wa.node.ratchet) (hib : NodeInv wb.node wb.node.ratchet)
    (hpa : preHorizon r env wa.node = true) (hpb : preHorizon r env wb.node = true) (cid : Nat) :
    pubNode (packageAccepted r env wa cid) = pubNode (packageAccepted r env wb cid) := by
  have hsel : selIds wa.node = selIds wb.node := pub_sel hn
  have hra := release_factor hcl hdr env wa.node wb.node hsel (pub_cands hn) (pub_ratchet hn)
    (pub_combineSlack hn) (pub_holdSecs hn) hia hib hpa hpb
  have hrb := release_factor hcl hdr env wb.node wa.node hsel.symm (pub_cands hn).symm
    (pub_ratchet hn).symm (pub_combineSlack hn).symm (pub_holdSecs hn).symm hib hia hpb hpa
  rw [releaseErased_congr (pub_ratchet hn).symm (pub_combineSlack hn).symm (pub_holdSecs hn).symm] at hrb
  refine pubNode_ext_cands hn (map_pub hn (G := fun ec =>
    if ec.id == cid && releaseErased r env wa.node (selIds wa.node) (wa.node.armed || wb.node.armed) ec
        && ec.released && heldQuorum wa.node.t ec then { ec with packageOk := true } else ec) ?_ ?_)
  · intro c hc
    have hp : (c.id == cid && due r env wa.node c && releaseAuthorized wa.node c && c.released
          && heldQuorum wa.node.t c)
        = ((pubCand (selIds wa.node) c).id == cid
            && releaseErased r env wa.node (selIds wa.node) (wa.node.armed || wb.node.armed)
              (pubCand (selIds wa.node) c)
            && (pubCand (selIds wa.node) c).released
            && heldQuorum wa.node.t (pubCand (selIds wa.node) c)) := by
      simp [Bool.and_assoc, hra c hc, pubCand_id, pubCand_released, heldQuorum, pubCand_held]
    simp only [hp]
    by_cases hq : ((pubCand (selIds wa.node) c).id == cid
        && releaseErased r env wa.node (selIds wa.node) (wa.node.armed || wb.node.armed)
          (pubCand (selIds wa.node) c)
        && (pubCand (selIds wa.node) c).released
        && heldQuorum wa.node.t (pubCand (selIds wa.node) c)) = true
    · rw [if_pos hq, if_pos hq]; exact pubCand_set_packageOk _ c
    · rw [if_neg hq, if_neg hq]
  · intro c hc
    have hp : (c.id == cid && due r env wb.node c && releaseAuthorized wb.node c && c.released
          && heldQuorum wb.node.t c)
        = ((pubCand (selIds wb.node) c).id == cid
            && releaseErased r env wa.node (selIds wa.node) (wa.node.armed || wb.node.armed)
              (pubCand (selIds wb.node) c)
            && (pubCand (selIds wb.node) c).released
            && heldQuorum wa.node.t (pubCand (selIds wb.node) c)) := by
      simp [Bool.and_assoc, hrb c hc, pubCand_id, pubCand_released, heldQuorum, pubCand_held,
        Bool.or_comm wb.node.armed wa.node.armed, ← hsel, pub_t hn]
    simp only [hp]
    by_cases hq : ((pubCand (selIds wb.node) c).id == cid
        && releaseErased r env wa.node (selIds wa.node) (wa.node.armed || wb.node.armed)
          (pubCand (selIds wb.node) c)
        && (pubCand (selIds wb.node) c).released
        && heldQuorum wa.node.t (pubCand (selIds wb.node) c)) = true
    · rw [if_pos hq, if_pos hq]; exact pubCand_set_packageOk _ c
    · rw [if_neg hq, if_neg hq]

/-- Candidate lookup, the input and message guard and held insertion all survive the projection.
The same `Input.pinless` partial is used in both runs. -/
theorem receivePartial_pub {na nb : Node} (hn : pubNode na = pubNode nb)
    (msg : Sighash) (input signer cid : Nat) :
    pubNode (receivePartial na msg input signer cid)
      = pubNode (receivePartial nb msg input signer cid) := by
  simp only [receivePartial]
  apply pubNode_ext_cands hn
  apply map_pub hn (G := fun c => if c.id == cid && input == 0 && msg == sighash c.tx 0 then
    { c with heldSigners := addHeld c.heldSigners signer } else c)
  all_goals
    intro c _
    simp only [pubCand_id, pubCand_tx, pubCand_held]
    split
    · simpa only [pubCand_id, pubCand_tx] using pubCand_set_held _ c (addHeld c.heldSigners signer)
    · rfl

theorem find?_cands_pub {x y : Node} (h : pubNode x = pubNode y) (cid : Nat) :
    (x.cands.find? (·.id == cid)).map (pubCand (selIds x))
      = (y.cands.find? (·.id == cid)).map (pubCand (selIds y)) := by
  rw [find?_comm (pubCand (selIds x)) (fun c => c.id == cid) x.cands (fun c => c.id == cid)
        (fun c _ => by simp [pubCand_id]),
      find?_comm (pubCand (selIds y)) (fun c => c.id == cid) y.cands (fun c => c.id == cid)
        (fun c _ => by simp [pubCand_id]), pub_cands h]

/-- `DUR-29`'s linearization point: the re-authorization immediately before the send, and the
broadcast it emits. -/
theorem send_pub {r : Rules} (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb)
    (hia : NodeInv na na.ratchet) (hib : NodeInv nb nb.ratchet)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (cid : Nat) :
    pubNode (send r env na cid).1 = pubNode (send r env nb cid).1 ∧
      (send r env na cid).2 = (send r env nb cid).2 := by
  have hsel : selIds na = selIds nb := pub_sel hn
  have hra := release_factor hcl hdr env na nb hsel (pub_cands hn) (pub_ratchet hn)
    (pub_combineSlack hn) (pub_holdSecs hn) hia hib hpa hpb
  have hrb := release_factor hcl hdr env nb na hsel.symm (pub_cands hn).symm (pub_ratchet hn).symm
    (pub_combineSlack hn).symm (pub_holdSecs hn).symm hib hia hpb hpa
  rw [releaseErased_congr (pub_ratchet hn).symm (pub_combineSlack hn).symm (pub_holdSecs hn).symm] at hrb
  have hf := find?_cands_pub hn cid
  cases hx : na.cands.find? (·.id == cid) with
  | none =>
    cases hy : nb.cands.find? (·.id == cid) with
    | none => simp only [send, hx, hy]; exact ⟨hn, trivial⟩
    | some c' => rw [hx, hy] at hf; simp at hf
  | some c =>
    cases hy : nb.cands.find? (·.id == cid) with
    | none => rw [hx, hy] at hf; simp at hf
    | some c' =>
      rw [hx, hy] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      have hca : c ∈ na.cands := List.mem_of_find?_eq_some hx
      have hcb : c' ∈ nb.cands := List.mem_of_find?_eq_some hy
      have hpk : c.packageOk = c'.packageOk := by
        rw [← pubCand_packageOk (selIds na) c, ← pubCand_packageOk (selIds nb) c', hf]
      have hrel : (due r env na c && releaseAuthorized na c)
          = (due r env nb c' && releaseAuthorized nb c') := by
        rw [hra c hca, hrb c' hcb, hf, hsel, Bool.or_comm nb.armed na.armed]
      have hgo : (c.packageOk && (r.reauth == .beforeAssembly || (due r env na c && releaseAuthorized na c)))
          = (c'.packageOk && (r.reauth == .beforeAssembly
              || (due r env nb c' && releaseAuthorized nb c'))) := by
        rw [hpk, hrel]
      have htx : c.tx = c'.tx := by
        rw [← pubCand_tx (selIds na) c, ← pubCand_tx (selIds nb) c', hf]
      simp only [send, hx, hy, hgo, htx]
      refine ⟨pubNode_ext_cands hn (map_pub hn (G := fun ec =>
        if ec.id == cid then
          { ec with packageOk := false, broadcast := ec.broadcast
            || (c'.packageOk && (r.reauth == .beforeAssembly
                || (due r env nb c' && releaseAuthorized nb c'))) } else ec) ?_ ?_), trivial⟩
      · intro d hd
        simp only []
        by_cases hb : (d.id == cid) = true
        · rw [if_pos hb, if_pos (by rw [pubCand_id]; exact hb)]
          exact pubCand_set_send _ d _
        · simp only [Bool.not_eq_true] at hb
          rw [if_neg (by simp [hb]), if_neg (by rw [pubCand_id]; simp [hb])]
      · intro d hd
        simp only []
        by_cases hb : (d.id == cid) = true
        · rw [if_pos hb, if_pos (by rw [pubCand_id]; exact hb)]
          exact pubCand_set_send _ d _
        · simp only [Bool.not_eq_true] at hb
          rw [if_neg (by simp [hb]), if_neg (by rw [pubCand_id]; simp [hb])]

theorem conflicts_pub (sel : List Nat) (tx : Tx) (c : Cand) :
    conflicts tx (pubCand sel c) = conflicts tx c := by simp [conflicts, pubCand_tx]

/-- `SPN-33`'s settlement: the chain view is an input held equal. -/
theorem settle_pub {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb) (tx : Tx) :
    pubNode (settle env na tx) = pubNode (settle env nb tx) := by
  simp only [settle]
  split
  · exact hn
  · refine pubNode_ext_cands_log hn (map_pub hn (G := fun ec =>
      if ec.tx.id == tx.id then { ec with settled := true }
      else if ec.hot && conflicts tx ec then { ec with terminal := true } else ec) ?_ ?_)
      (by rw [pub_pendingLog hn]) <;>
    · intro c hc
      simp only [pubCand_tx, pubCand_hot, conflicts_pub]
      by_cases h1 : (c.tx.id == tx.id) = true
      · simp only [h1, ↓reduceIte]
        rw [pubCand_set_settled]
        simp [pubCand_tx, pubCand_hot]
      · simp only [Bool.not_eq_true] at h1
        by_cases h2 : (c.hot && conflicts tx c) = true
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
          rw [pubCand_set_terminal]
          simp [pubCand_tx, pubCand_hot]
        · simp only [Bool.not_eq_true] at h2
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- `SPN-41`'s exemption through the projection. A selected Escape's installed window closes at
its own run's `T + combine_slack_secs` (`NodeInv.selWin`), which the projection erases; what it
keeps is that the window is installed, and `selOpen` stands for whether that close is still ahead.
Off the selected set the window is the projection's own. -/
def exemptPub (env : Env) (sel : List Nat) (selOpen : Bool) (ec : Cand) : Bool :=
  !ec.broadcast && ec.isEscape &&
    (match ec.windowClose with
     | some wc => if inSel sel ec.id then selOpen else env.eff.atOrBefore wc
     | none => false)

/-- On one run inside its horizon, whether a selected Escape's installed window is still open is
read off `unarmedT`, which the projection keeps: an unarmed node's `T` is `unarmedT`, and an armed
node inside its horizon is strictly before its `T`, which is at or below `unarmedT`, so every
installed window is open on both readings. -/
theorem exemptEscape_factor {r : Rules} (hdr : r.driverTime = .ratchet) {env : Env} {n : Node}
    {L : Effective} (hi : NodeInv n L) (hp : preHorizon r env n = true) :
    ∀ e ∈ n.cands, exemptEscape env e =
      exemptPub env (selIds n) (env.eff.atOrBefore (n.unarmedT.plus n.combineSlack))
        (pubCand (selIds n) e) := by
  have hclose : env.eff.atOrBefore (n.T.plus n.combineSlack) =
      env.eff.atOrBefore (n.unarmedT.plus n.combineSlack) := by
    cases ha : n.armed with
    | false => rw [hi.unarmed.1 ha]
    | true =>
      have hT := (Effective.deadlineReached_latest (preHorizon_below hdr hp ha)).2
      rw [Effective.atOrBefore_plus_of_not_reached _ hT,
        Effective.atOrBefore_plus_of_not_reached _
          (Effective.not_reached_of_atOrBefore hT (hi.unarmed.2 ha))]
  intro e he
  by_cases hs : inSel (selIds n) e.id = true
  · obtain ⟨hw, _⟩ := hi.selWin e he hs
    rcases hw with hw | hw
    · simp [exemptEscape, exemptPub, pubCand, Cand.isEscape, hs, hw]
    · simp [exemptEscape, exemptPub, pubCand, Cand.isEscape, hs, hw, hclose]
  · simp only [Bool.not_eq_true] at hs
    simp only [exemptEscape, exemptPub, pubCand, Cand.isEscape, hs, Bool.false_eq_true, if_false]
    cases e.windowClose <;> rfl

/-- `SPN-41`'s removal of every selected Escape and its pair never runs inside the concealment
horizon, on either run: on a node whose `DUR-10` `active` bit is clear it is false outright, and
on an armed node the horizon puts `max(ratchet, effective)` strictly below `T`, so effective time
is at or before `T + combine_slack_secs`. It reads the selected set nowhere, so the condition is
false before the candidate it would remove is consulted. -/
@[req "SPN-41"]
theorem removal_false_preHorizon {r : Rules} (hdr : r.driverTime = .ratchet) {env : Env}
    {n : Node} (hp : preHorizon r env n = true) :
    (n.armed && !env.eff.atOrBefore (n.T.plus n.combineSlack)) = false := by
  cases ha : n.armed with
  | false => rfl
  | true =>
    have hT := (Effective.deadlineReached_latest (preHorizon_below hdr hp ha)).2
    simp [Effective.atOrBefore_plus_of_not_reached _ hT]

/-- `SPN-41`'s pruning: a comparison against a candidate's own expiry, and the exemption of an
Escape whose window has not closed, with its pair. The exemption reads the window `T` wrote, which
inside each run's horizon is read off `unarmedT`, so it is pin-uniform where the walk uses it:
`SPN-41`'s "the exemption is granted to the normal PIN's inert slot too". `SPN-41`'s removal of
every selected Escape and its pair, the conjunct that reads the arm bit, is false on both runs
inside the horizon (`removal_false_preHorizon`), so on both the keep test is the expiry-or-exemption
test alone: a candidate stays if its expiry has not passed or if an exempt Escape shares its pair.
The pass also prunes the pending log at expiry, reading only the log and the effective sample, and
the projection carries the log whole. -/
theorem prune_pub {r : Rules} (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node}
    (hn : pubNode na = pubNode nb) {La Lb : Effective} (hia : NodeInv na La) (hib : NodeInv nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) :
    pubNode (prune env na) = pubNode (prune env nb) := by
  have hsel := pub_sel hn
  let Q : Cand → Bool := fun ec => env.eff.atOrBefore ec.expiry ||
    (na.cands.map (pubCand (selIds na))).any fun ee =>
      ee.pair == ec.pair &&
        exemptPub env (selIds na) (env.eff.atOrBefore (na.unarmedT.plus na.combineSlack)) ee
  have keep : ∀ (n : Node) (L : Effective), NodeInv n L → preHorizon r env n = true →
      selIds n = selIds na →
      n.cands.map (pubCand (selIds n)) = na.cands.map (pubCand (selIds na)) →
      n.unarmedT = na.unarmedT → n.combineSlack = na.combineSlack →
      ∀ c ∈ n.cands, (env.eff.atOrBefore c.expiry ||
        n.cands.any fun e => e.pair == c.pair && exemptEscape env e) = Q (pubCand (selIds n) c) := by
    intro n L hi hp hs hm hu hcs c _
    simp only [Q, pubCand_expiry]
    congr 1
    rw [any_comm (pubCand (selIds n))
        (fun ee => ee.pair == (pubCand (selIds n) c).pair &&
          exemptPub env (selIds n) (env.eff.atOrBefore (n.unarmedT.plus n.combineSlack)) ee)
        n.cands _ (fun e he => by simp only [exemptEscape_factor hdr hi hp e he, pubCand_pair]),
      hm, hs, hu, hcs]
  refine pubNode_ext_cands_log hn ?_ (by rw [pub_pendingLog hn])
  show (na.cands.filter _).map (pubCand (selIds na)) = (nb.cands.filter _).map (pubCand (selIds nb))
  simp only [removal_false_preHorizon hdr hpa, removal_false_preHorizon hdr hpb, Bool.false_and,
    Bool.not_false, Bool.and_true]
  rw [filter_comm (pubCand (selIds na)) Q na.cands _ (keep na La hia hpa rfl rfl rfl rfl),
    filter_comm (pubCand (selIds nb)) Q nb.cands _
      (keep nb Lb hib hpb hsel.symm (pub_cands hn).symm (pub_unarmedT hn).symm
        (pub_combineSlack hn).symm),
    pub_cands hn]

/-- `NCH-40` (3)'s retirement driver. -/
theorem tick_pub {r : Rules} {env : Env} {na nb : Node} (hn : pubNode na = pubNode nb) :
    pubNode (tick r env na) = pubNode (tick r env nb) := by
  have live : (na.carriers.filter (carrierRetained r env)).map pubCarrier =
      (nb.carriers.filter (carrierRetained r env)).map pubCarrier := by
    rw [filter_comm pubCarrier (carrierRetained r env) na.carriers (carrierRetained r env)
        (fun _ _ => rfl),
      filter_comm pubCarrier (carrierRetained r env) nb.carriers (carrierRetained r env)
        (fun _ _ => rfl), pub_carriers hn]
  have dead : ((na.carriers.filter fun k => !carrierRetained r env k).map Carrier.tombstone).map pubTombstone =
      ((nb.carriers.filter fun k => !carrierRetained r env k).map Carrier.tombstone).map pubTombstone := by
    have hfilter : (na.carriers.filter fun k => !carrierRetained r env k).map pubCarrier =
        (nb.carriers.filter fun k => !carrierRetained r env k).map pubCarrier := by
      rw [filter_comm pubCarrier (fun k => !carrierRetained r env k) na.carriers
          (fun k => !carrierRetained r env k) (fun _ _ => rfl),
        filter_comm pubCarrier (fun k => !carrierRetained r env k) nb.carriers
          (fun k => !carrierRetained r env k) (fun _ _ => rfl), pub_carriers hn]
    simpa [List.map_map, Function.comp_def, pubTombstone, pubCarrier, Carrier.tombstone]
      using congrArg (List.map Carrier.tombstone) hfilter
  apply pubNode_ext (x := tick r env na) (y := tick r env nb)
    (pub_id (x := na) (y := nb) hn) (pub_t (x := na) (y := nb) hn) (pub_poisoned (x := na) (y := nb) hn) (pub_lockedDown (x := na) (y := nb) hn)
    live (pub_cands (x := na) (y := nb) hn) (pub_sel (x := na) (y := nb) hn) (pub_duressDelay (x := na) (y := nb) hn) (pub_epsilon (x := na) (y := nb) hn) (pub_combineSlack (x := na) (y := nb) hn)
    (pub_holdSecs (x := na) (y := nb) hn) _ (pub_ratchet (x := na) (y := nb) hn) (pub_unarmedT (x := na) (y := nb) hn)
    (pub_pendingLog (x := na) (y := nb) hn)
  change ((na.tombstones ++ _).filter (Tombstone.retained env)).map pubTombstone =
    ((nb.tombstones ++ _).filter (Tombstone.retained env)).map pubTombstone
  rw [filter_comm pubTombstone (Tombstone.retained env) _ (Tombstone.retained env) (fun _ _ => rfl),
    filter_comm pubTombstone (Tombstone.retained env) _ (Tombstone.retained env) (fun _ _ => rfl),
    List.map_append, List.map_append, pub_tombstones hn, dead]

/-- One kernel step of each run: the node projection, the exposure history and the effects. -/
theorem step_pub {r : Rules} (ht : r.traversal = .always) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {env : Env} {wa wb : World}
    (hn : pubNode wa.node = pubNode wb.node) (hx : wa.exposure = wb.exposure)
    (hia : NodeInv wa.node wa.node.ratchet) (hib : NodeInv wb.node wb.node.ratchet)
    (hpa : preHorizon r env wa.node = true) (hpb : preHorizon r env wb.node = true)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    pubNode (step r env wa (i.event tbl₀)).1.node = pubNode (step r env wb (i.event tbl₁)).1.node ∧
      (step r env wa (i.event tbl₀)).1.exposure = (step r env wb (i.event tbl₁)).1.exposure ∧
      (step r env wa (i.event tbl₀)).2 = (step r env wb (i.event tbl₁)).2 := by
  cases i with
  | request cid pin E sp es =>
    exact ⟨accept_pub ht env hn cid (tbl₀ pin) (tbl₁ pin) E sp es, hx, rfl⟩
  | refusal cid pin E pair code => exact ⟨refuse_pub env hn cid (tbl₀ pin) (tbl₁ pin) E pair, hx, rfl⟩
  | pinless e =>
    cases e with
    | accept cid d E sp es => exact ⟨accept_pub ht env hn cid d d E sp es, hx, rfl⟩
    | refuse cid d E pair code => exact ⟨refuse_pub env hn cid d d E pair, hx, rfl⟩
    | receipt cid s => exact ⟨receipt_pub hn cid s, hx, rfl⟩
    | firePass =>
      obtain ⟨h1, h2⟩ := firePass_pub (r := r) (env := env) hcl hdr hn hia hib hpa hpb
      refine ⟨h1, ?_, h2⟩
      simp only [Input.event, step]
      rw [hx, h2, pub_id hn]
    | packageAccepted c => exact ⟨packageAccepted_pub hcl hdr hn hia hib hpa hpb c, hx, rfl⟩
    | send c =>
      obtain ⟨h1, h2⟩ := send_pub hcl hdr hn hia hib hpa hpb c
      exact ⟨h1, hx, h2⟩
    | settle tx => exact ⟨settle_pub hn tx, hx, rfl⟩
    | prune => exact ⟨prune_pub hdr hn hia hib hpa hpb, hx, rfl⟩
    | tick => exact ⟨tick_pub hn, hx, rfl⟩
    | panic =>
      refine ⟨?_, hx, rfl⟩
      show pubNode { wa.node with poisoned := true } = pubNode { wb.node with poisoned := true }
      exact pubNode_ext (by show wa.node.id = wb.node.id; exact pub_id hn)
        (by show wa.node.t = wb.node.t; exact pub_t hn) rfl
        (by show wa.node.lockedDown = wb.node.lockedDown; exact pub_lockedDown hn)
        (by show wa.node.carriers.map pubCarrier = wb.node.carriers.map pubCarrier
            exact pub_carriers hn)
        (by show wa.node.cands.map (pubCand (selIds wa.node))
              = wb.node.cands.map (pubCand (selIds wb.node))
            exact pub_cands hn)
        (by show selIds wa.node = selIds wb.node; exact pub_sel hn)
        (by show wa.node.duressDelay = wb.node.duressDelay; exact pub_duressDelay hn)
        (by show wa.node.epsilon = wb.node.epsilon; exact pub_epsilon hn)
        (by show wa.node.combineSlack = wb.node.combineSlack; exact pub_combineSlack hn)
        (by show wa.node.holdSecs = wb.node.holdSecs; exact pub_holdSecs hn)
        (by show wa.node.tombstones.map pubTombstone = wb.node.tombstones.map pubTombstone; exact pub_tombstones hn)
        (by show wa.node.ratchet = wb.node.ratchet; exact pub_ratchet hn)
        (by show wa.node.unarmedT = wb.node.unarmedT; exact pub_unarmedT hn)
        (by show wa.node.pendingLog = wb.node.pendingLog; exact pub_pendingLog hn)
    | receivePartial m j sg c =>
      refine ⟨receivePartial_pub hn m j sg c, ?_, rfl⟩
      simp only [Input.event, step]
      rw [hx]
    | adversaryExposes m j sg c =>
      refine ⟨hn, ?_, rfl⟩
      simp only [Input.event, step]
      rw [hx]

/-! ## The Hot ledger is one ledger between the two runs

`POL-21`: "The duress freeze MUST NOT touch the ledger: a refund that happened only under duress
would be the timing signal `DUR-1` forbids". Every ledger transition reads the candidate's
commitment id, its exposure flags and its settlement flags, and none of them is the overlay's. -/

theorem cands_any_pub {x y : Node} (h : pubNode x = pubNode y) (p : Cand → Bool)
    (hp : ∀ c, p c = p (pubCand (selIds x) c)) (hp' : ∀ c, p c = p (pubCand (selIds y) c)) :
    x.cands.any p = y.cands.any p := by
  rw [any_comm (pubCand (selIds x)) p x.cands p (fun c _ => hp c),
    any_comm (pubCand (selIds y)) p y.cands p (fun c _ => hp' c), pub_cands h]

@[req "POL-21"]
theorem markExposed_pub {x y : Node} (h : pubNode x = pubNode y) (l : Ledger) :
    markExposed x l = markExposed y l := by
  unfold markExposed
  refine congrArg (List.map · l) (funext fun row => ?_)
  rw [cands_any_pub h (fun c => c.id == row.cid && (c.released || c.broadcast))
    (fun c => by simp [pubCand_id, pubCand_released, pubCand_broadcast])
    (fun c => by simp [pubCand_id, pubCand_released, pubCand_broadcast])]

theorem refundOnSettlement_pub {x y : Node} (h : pubNode x = pubNode y) (l : Ledger) :
    refundOnSettlement x l = refundOnSettlement y l := by
  unfold refundOnSettlement
  refine congrArg (List.filter · l) (funext fun row => ?_)
  rw [cands_any_pub h (fun c => c.id == row.cid && (c.settled || c.terminal))
    (fun c => by simp [pubCand_id, pubCand_settled, pubCand_terminal])
    (fun c => by simp [pubCand_id, pubCand_settled, pubCand_terminal])]

/-- Whether the request was accepted is read off the Carriers' local acceptance status, which the
projection keeps: `POL-19`'s release persists, and `POL-18`'s reservation is placed, in both runs
or in neither. -/
theorem admitted_pub {ba bb aa ab : World}
    (hb : pubNode ba.node = pubNode bb.node) (ha : pubNode aa.node = pubNode ab.node)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    admitted ba aa (i.event tbl₀) = admitted bb ab (i.event tbl₁) := by
  have hcar : ∀ cid : Nat, ba.node.carriers.any (·.cid == cid) = bb.node.carriers.any (·.cid == cid) :=
    fun cid => carriers_any_pub hb _ (fun _ => rfl)
  have hac : ∀ cid, aa.node.carriers.any (fun k => k.cid == cid && k.accepted) =
      ab.node.carriers.any (fun k => k.cid == cid && k.accepted) :=
    fun cid => carriers_any_pub ha _ (fun _ => rfl)
  cases i with
  | request cid pin E sp es => simp only [Input.event, admitted, hac cid, hcar cid]
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | accept cid d E sp es => simp only [Input.event, admitted, hac cid, hcar cid]
    | _ => rfl

/-- `POL-19`'s release is evaluated at the same steps in both runs: a hot request's class is the
request's own. -/
theorem checked_pin (g : Release) (env : Env) (window : Secs) (l : Ledger) (i : Input)
    (tbl₀ tbl₁ : Enrolment) :
    checked g env window l (i.event tbl₀) = checked g env window l (i.event tbl₁) := by
  cases i <;> rfl

theorem afterEvent_pub (g : Guards) {env : Env} {ba bb aa ab : World}
    (hb : pubNode ba.node = pubNode bb.node) (ha : pubNode aa.node = pubNode ab.node)
    (i : Input) (tbl₀ tbl₁ : Enrolment) (l : Ledger) :
    afterEvent g env ba aa (i.event tbl₀) l = afterEvent g env bb ab (i.event tbl₁) l := by
  have hadm := admitted_pub hb ha i tbl₀ tbl₁
  have hres : ∀ (sp₀ sp₁ : Cand), sp₀ = sp₁ → ∀ (b : Bool) (b' : Bool), b = b' →
      (if b then reserve l sp₀ env.mono else l) = (if b' then reserve l sp₁ env.mono else l) := by
    intro _ _ h _ _ h'; subst h; subst h'; rfl
  cases i with
  | request cid pin E sp es => exact hres sp sp rfl _ _ hadm
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | accept cid d E sp es => exact hres sp sp rfl _ _ hadm
    | prune =>
      show refundAtPrune g.refund env aa.node l = refundAtPrune g.refund env ab.node l
      unfold refundAtPrune
      refine congrArg (List.filter · l) (funext fun row => ?_)
      rw [cands_any_pub ha (fun c => c.id == row.cid) (fun c => by simp [pubCand_id])
        (fun c => by simp [pubCand_id])]
    | settle tx =>
      show (match g.settlement with
          | .retainOnMempool => l | .refundOnAnySettlement => refundOnSettlement aa.node l) =
        (match g.settlement with
          | .retainOnMempool => l | .refundOnAnySettlement => refundOnSettlement ab.node l)
      cases g.settlement with
      | retainOnMempool => rfl
      | refundOnAnySettlement => exact refundOnSettlement_pub ha l
    | refuse cid d E pair code | receipt cid s | firePass | packageAccepted c | send c | tick | panic
    | adversaryExposes m j sg c | receivePartial m j sg c => rfl

/-- `POL-16`'s admission check reads the ledger as `POL-19`'s release leaves it at that check
(`Ledger.checked`) and the spend, and no overlay field. -/
@[req "POL-16"]
theorem refusedByBudget_pin (cfg : Config) (l : Ledger) (i : Input) (tbl₀ tbl₁ : Enrolment) :
    refusedByBudget cfg l (i.event tbl₀) = refusedByBudget cfg l (i.event tbl₁) := by
  cases i with
  | request cid pin E sp es => rfl
  | refusal cid pin E pair code => rfl
  | pinless e => rfl

/-- One composed step of each run (`Ledger.sysStep`): the coupling and the effects. -/
theorem sysStep_coupled {g : Guards} {cfg : Config} {r : Rules} (ht : r.traversal = .always)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    {env : Env} {a b : Sys} (hc : Coupled a b)
    (hia : NodeInv a.world.node a.world.node.ratchet) (hib : NodeInv b.world.node b.world.node.ratchet)
    (hpa : preHorizon r env a.world.node = true) (hpb : preHorizon r env b.world.node = true)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    Coupled (sysStep g cfg r env a (i.event tbl₀)).1 (sysStep g cfg r env b (i.event tbl₁)).1 ∧
      (sysStep g cfg r env a (i.event tbl₀)).2 = (sysStep g cfg r env b (i.event tbl₁)).2 := by
  obtain ⟨hnode, hexp, hled⟩ := hc
  obtain ⟨h1, h2, h3⟩ := step_pub ht hcl hdr hnode hexp hia hib hpa hpb i tbl₀ tbl₁
  simp only [sysStep, hled, checked_pin g.release env cfg.window b.led i tbl₀ tbl₁,
    refusedByBudget_pin cfg (checked g.release env cfg.window b.led (i.event tbl₁)) i tbl₀ tbl₁]
  split
  · refine ⟨⟨?_, hexp, markExposed_pub hnode _⟩, rfl⟩
    cases i with
    | request cid pin E sp es => exact refuse_pub env hnode cid (tbl₀ pin) (tbl₁ pin) E _
    | refusal cid pin E pair code => exact hnode
    | pinless e =>
      cases e <;> try exact hnode
      exact refuse_pub env hnode _ _ _ _ _
  · refine ⟨⟨h1, h2, ?_⟩, h3⟩
    rw [admitted_pub hnode h1 i tbl₀ tbl₁, afterEvent_pub g hnode h1 i tbl₀ tbl₁, markExposed_pub h1]

/-! ## The invariant is preserved, event by event

One run at a time: `NodeInv` is a property of a node and needs no coupling. `frozen` is the clause
`Kernel.Inv` states; the others are this module's own. -/

/-- A step that leaves the overlay alone and carries every candidate's identity, class, freeze
bit and window forward: `SPN-33`'s settlement marks, `SPN-38`'s release bookkeeping, `SPN-39`'s
package flag and `SPN-41`'s pruning are all of this shape, and a broadcast only ever turns on. -/
theorem inv_frame {n n' : Node} {now : Effective} (hi : NodeInv n now) (harm : n'.armed = n.armed)
    (hsw : n'.sweepActive = n.sweepActive) (hT : n'.T = n.T) (hsel : n'.selected = n.selected)
    (heps : n'.epsilon = n.epsilon) (hcs : n'.combineSlack = n.combineSlack)
    (hu : n'.unarmedT = n.unarmedT) (hn : (n'.cands.map Cand.id).Nodup)
    (hcands : ∀ c' ∈ n'.cands, ∃ c ∈ n.cands, c'.id = c.id ∧ c'.hot = c.hot ∧
      c'.frozen = c.frozen ∧ c'.fireAt = c.fireAt ∧ c'.windowClose = c.windowClose ∧
      c'.expiry = c.expiry ∧ (c.broadcast = true → c'.broadcast = true) ∧
      (c'.quorum = true → c.quorum = true)) :
    NodeInv n' now := by
  have hids : selIds n' = selIds n := by simp [selIds, hsel]
  refine ⟨by rw [hsw, harm, hi.sweep], ?_, ?_, ?_, ?_, ?_, hn, ?_,
    ⟨fun ha => by rw [hT, hu]; exact hi.unarmed.1 (by rw [← harm]; exact ha),
     fun ha => by rw [hT, hu]; exact hi.unarmed.2 (by rw [← harm]; exact ha)⟩⟩
  · intro ha c' hc'
    obtain ⟨c, hc, _, _, hfr, _⟩ := hcands c' hc'
    rw [hfr]; exact hi.unfrozen (by rw [← harm]; exact ha) c hc
  · intro ha c' hc' hhot
    obtain ⟨c, hc, _, hh, hfr, _⟩ := hcands c' hc'
    rw [hfr]; exact hi.frozen (by rw [← harm]; exact ha) c hc (by rw [← hh]; exact hhot)
  · intro c' hc' hs hq
    obtain ⟨c, hc, hid, _, _, hfa, _, _, _, hq'⟩ := hcands c' hc'
    rw [hfa, hT]; exact hi.windows c hc (by rw [hids, ← hid] at *; exact hs) (hq' hq)
  · intro c' hc' hs
    obtain ⟨c, hc, hid, _, _, _, hwc, _⟩ := hcands c' hc'
    rw [hwc]; exact hi.noWindow c hc (by rw [hids, ← hid] at *; exact hs)
  · intro ha c' hc' hhot hs f hf
    obtain ⟨c, hc, hid, hh, _, hfa, hwc, hexp, hbc, _⟩ := hcands c' hc'
    have hc0 := hi.hotBound (by rw [← harm]; exact ha) c hc (by rw [← hh]; exact hhot)
      (by rw [hids, ← hid] at *; exact hs) f (by rw [← hfa]; exact hf)
    have hwin : windowOpen now n'.combineSlack c' = windowOpen now n.combineSlack c := by
      simp only [windowOpen, hwc, hexp, hh, hfa, hcs]
    rcases hc0 with hb | hx | hw
    · exact .inl (hbc hb)
    · exact .inr (.inl (by rw [hwin]; exact hx))
    · exact .inr (.inr (by rw [hT, heps]; exact hw))
  · intro c' hc' hs
    obtain ⟨c, hc, hid, hh, _, hfa, hwc, _⟩ := hcands c' hc'
    obtain ⟨h1, h2⟩ := hi.selWin c hc (by rw [hids, ← hid] at *; exact hs)
    exact ⟨by rw [hwc, hT, hcs]; exact h1, fun hh' => by rw [hfa, hT]; exact h2 (by rw [← hh]; exact hh')⟩

theorem inv_refuse {r : Rules} {env : Env} {n : Node} {now : Effective} (hi : NodeInv n now)
    (cid : Nat) (d : Bool) (E : Wall) (pair : Option (Nat × Nat)) :
    NodeInv (refuse r env n cid d E pair) now := by
  apply inv_frame hi <;> try simp
  · exact hi.idsUnique
  intro c hc
  exact ⟨c, hc, rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩

theorem shrunk_eq_of_not_traverses {r : Rules} {env : Env} {n : Node} {sp : Cand}
    (h : traverses r env n sp = false) : shrunkDeadline r env n sp = n.T := by
  simp only [traverses, Bool.and_eq_false_iff, Bool.or_eq_false_iff, bne_iff_ne, ne_eq,
    Decidable.not_not] at h
  rcases h with hhot | ⟨_, heq⟩
  · simp [shrunkDeadline, hhot]
  · simpa using heq

/-- An acceptance retains a compatible resident pair or creates closed candidates.
`register_origin` distinguishes the cases; `ids_nodup_step`, using `register_nodup`, carries
resident uniqueness. A selected new candidate needs no window bound while closed.
`shrunkDeadline` supplies the hot-spend bound. This is where `dynamics` is load-bearing — under
the static value the spend
`DUR-14` exists for is accepted with a fire time before `T`, and the bound the whole relation
rests on is false at the next state. The bound is carried at a sample `L` at or above the
acceptance's own when the spend is hot (`hle`): `DUR-14`'s clamp writes `T` at most at
`max(T, now)`, so a shrink at a sample below the ratchet keeps every bound carried there. -/
theorem inv_accept_at {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) {env : Env} {n : Node} {L : Effective}
    (hi : NodeInv n L) (cid : Nat) (d : Bool) (E : Wall) (sp es : Cand)
    (hle : sp.hot = true → env.eff.notAfter L = true)
    (hlt : n.armed = true → env.eff.deadlineReached n.T = false)
    (hwf : wfEvent n (.accept cid d E sp es) = true) :
    NodeInv (accept r env n cid d E sp es) L := by
  simp only [wfEvent, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hwf
  obtain ⟨⟨hesh, hspw⟩, hesw⟩ := hwf
  have huniq := ids_nodup_step hr env { node := n, exposure := [] }
    (.accept cid d E sp es) hi.idsUnique
  unfold accept
  split
  · exact inv_refuse hi cid d E _
  · rename_i hg
    have hadmit : pairAdmits r n sp es = true := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true'] at hg
      simpa using hg.2
    split
    · exact hi
    · rename_i D hD
      have hT' : ∀ f, sp.fireAt = some f → n.armed = true → sp.hot = true →
          Wall.belowFire (shrunkDeadline r env n sp) f n.epsilon L = true := by
        intro f hf ha hh
        simp only [shrunkDeadline, hd, ha, hh, hf, beq_self_eq_true, Bool.and_self, if_true]
        exact Wall.belowFire_weaken (Wall.belowFire_shrink _ _ _ _) (hle hh)
      have hkeep : ∀ f, Wall.belowFire n.T f n.epsilon L = true →
          Wall.belowFire (shrunkDeadline r env n sp) f n.epsilon L = true := by
        intro f hb
        simp only [shrunkDeadline]
        split
        · rename_i hc
          have hh : sp.hot = true := by simp_all
          cases hsp : sp.fireAt with
          | none => exact hb
          | some g => exact Wall.belowFire_shrink_keeps_below hb (hle hh)
        · exact hb
      -- what the new registry carries
      have hmem : ∀ c ∈ (if traverses r env n sp then
            writeWindows n.selected (shrunkDeadline r env n sp) n.combineSlack
              (register r n env.mono sp es)
          else register r n env.mono sp es),
          (inSel (selIds n) c.id = true → c.quorum = true →
            c.fireAt = some (shrunkDeadline r env n sp)) ∧
          (inSel (selIds n) c.id = true →
            (c.windowClose = none ∨
              c.windowClose = some ((shrunkDeadline r env n sp).plus n.combineSlack)) ∧
            (c.hot = true → c.fireAt = some (shrunkDeadline r env n sp))) ∧
          ∃ x ∈ (born n.id n.armed env.mono { sp with pair := some (sp.id, es.id) } ::
              born n.id n.armed env.mono { es with pair := some (sp.id, es.id) } :: n.cands),
            c.frozen = x.frozen ∧ c.hot = x.hot ∧ (inSel (selIds n) c.id = false → c = x) := by
        intro c hc
        by_cases htr : traverses r env n sp = true
        · rw [if_pos htr] at hc
          simp only [writeWindows, List.mem_map] at hc
          obtain ⟨x, hx, rfl⟩ := hc
          have hx := mem_register hx
          refine ⟨?_, ?_, x, hx, withWindow_frozen _ _ _ x, withWindow_hot _ _ _ x, ?_⟩
          · intro hs _
            rw [withWindow_id] at hs
            rw [inSel_selIds] at hs
            simp [withWindow, hs]
          · intro hs
            rw [withWindow_id] at hs
            rw [inSel_selIds] at hs
            simp [withWindow, hs]
          · intro hs
            rw [withWindow_id] at hs
            rw [inSel_selIds] at hs
            simp [withWindow, hs]
        · simp only [Bool.not_eq_true] at htr
          rw [if_neg (by simp [htr])] at hc
          refine ⟨?_, ?_, c, mem_register hc, rfl, rfl, fun _ => rfl⟩
          · intro hs hq
            rw [shrunk_eq_of_not_traverses htr]
            rcases register_origin hr hadmit hc with hresident | habsent
            · exact hi.windows c hresident hs hq
            · have hc := mem_register hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | rfl | hc
              · cases hq
              · cases hq
              · exact False.elim (habsent c hc rfl)
          · -- no traversal: under `ht` the spend is not hot, so `T` stands and the pair is born
            -- with no window
            intro hs
            rw [shrunk_eq_of_not_traverses htr]
            have hsph : sp.hot = false := by simpa [traverses_always ht] using htr
            rcases register_origin hr hadmit hc with hresident | habsent
            · exact hi.selWin c hresident hs
            · have hc := mem_register hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | rfl | hc
              · exact ⟨.inl (by simpa [born] using hspw), fun h => absurd h (by simp [born, hsph])⟩
              · exact ⟨.inl (by simpa [born] using hesw), fun h => absurd h (by simp [born, hesh])⟩
              · exact False.elim (habsent c hc rfl)
      have hun : (n.armed = false → shrunkDeadline r env n sp = n.unarmedT) ∧
          (n.armed = true → Wall.atOrBefore (shrunkDeadline r env n sp) n.unarmedT = true) := by
        refine ⟨fun ha => by simp only [shrunkDeadline, ha]; simpa using hi.unarmed.1 ha,
          fun ha => Wall.atOrBefore_trans ?_ (hi.unarmed.2 ha)⟩
        unfold shrunkDeadline
        split
        · split
          · exact Wall.atOrBefore_refl _
          · exact Wall.shrinkDeadline_le_of_not_reached _ _ _ _ (hlt ha)
        · exact Wall.atOrBefore_refl _
      refine ⟨by exact hi.sweep, ?_, ?_, fun c hc => (hmem c hc).1, ?_, ?_, ?_,
        fun c hc => (hmem c hc).2.1, hun⟩
      · intro ha c hc
        have ha' : n.armed = false := ha
        obtain ⟨_, _, x, hx, hfr, _, _⟩ := hmem c hc
        rw [hfr]
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp [born, ha']
        · simp [born, ha']
        · exact hi.unfrozen ha' x hx
      · intro ha c hc hhot
        have ha' : n.armed = true := ha
        obtain ⟨_, _, x, hx, hfr, hh, _⟩ := hmem c hc
        rw [hh] at hhot
        rw [hfr]
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp only [born] at hhot ⊢; simp [ha', hhot]
        · simp only [born] at hhot ⊢; simp [ha', hhot]
        · exact hi.frozen ha' x hx hhot
      · intro c hc hs
        obtain ⟨_, _, x, hx, _, _, heq⟩ := hmem c hc
        rw [heq hs]
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simpa [born] using hspw
        · simpa [born] using hesw
        · refine hi.noWindow x hx ?_
          rw [← heq hs] at *
          exact hs
      · intro ha c hc hhot hs f hf
        have ha' : n.armed = true := ha
        obtain ⟨_, _, x, hx, _, _, heq⟩ := hmem c hc
        rw [heq hs] at hhot hf ⊢
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · refine .inr (.inr (hT' f ?_ ha' ?_))
          · simpa [born] using hf
          · simpa [born] using hhot
        · exact absurd (by simpa [born] using hhot) (by simp [hesh])
        · have hxs : inSel (selIds n) x.id = false := by rw [← heq hs] at *; exact hs
          rcases hi.hotBound ha' x hx hhot hxs f hf with hb | hw | hbf
          · exact .inl hb
          · exact .inr (.inl hw)
          · exact .inr (.inr (hkeep f hbf))
      · simpa only [step, accept, if_neg hg, hD] using huniq

/-- `DUR-5`'s holder decision: `DUR-13` computes `T` from the scan over the pending hot
candidates, so the computed value bounds every one of them at the moment of the decision — which
is why the scan's filter, `pendingHot`, and the invariant's disjuncts are the same conditions. Where the
clamp is selected the decision writes `max(min(T, T_computed), now)` instead,
which is at most `max(T_computed, now)`, and the bound is monotone downward in `T`
(`Wall.belowFire_clamp`), so the written value keeps it under every value of `Rules.clampOn`.
The bound is carried at a sample `L` at or above the decision's own (`hle`): a candidate the scan
drops as expired at the decision is closed at `L`, and one it counts is bounded by the computed
value. -/
theorem inv_holderDecision_at {r : Rules} {env : Env} {n : Node} {L : Effective}
    (hi : NodeInv n L) (hle : env.eff.notAfter L = true) (k : Carrier) :
    NodeInv (holderDecision r env n k) L := by
  have hsub : ∀ i, inSel (selIds (holderDecision r env n k)) i = false → inSel (selIds n) i = false := by
    intro i h
    have h' : inSel ((selectIntent n.selected k (pairDuress r n k)).map (·.1)) i = false := h
    cases hh : inSel (selIds n) i with
    | false => rfl
    | true =>
      rw [inSel_selectIntent_of_inSel n.selected k (pairDuress r n k) i (by simpa [selIds] using hh)] at h'
      exact absurd h' (by simp)
  have hcands : ∀ c' ∈ (holderDecision r env n k).cands, ∃ c ∈ n.cands, c'.id = c.id ∧
      c'.hot = c.hot ∧ c'.broadcast = c.broadcast ∧ c'.expiry = c.expiry ∧
      (c'.frozen = true → c.frozen = true ∨ c.hot = true) ∧
      (inSel (selIds (holderDecision r env n k)) c'.id = false →
        c'.fireAt = c.fireAt ∧ c'.windowClose = c.windowClose) := by
    intro c' hc'
    simp only [holderDecision, List.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    refine ⟨c, hc, by simp [withWindow_id], by simp [withWindow_hot], by simp [withWindow_broadcast],
      by simp [withWindow]; split <;> rfl, ?_, ?_⟩
    · intro hfr
      rw [withWindow_frozen] at hfr
      simp only [Bool.or_eq_true] at hfr
      rcases hfr with h | h
      · exact .inl h
      · exact .inr (by simpa using (Bool.and_eq_true .. ▸ h : c.hot = true ∧ (pairDuress r n k) = true).1)
    · intro hs
      rw [withWindow_id] at hs
      have : (selectIntent n.selected k (pairDuress r n k)).any (·.1 == c.id) = false := by
        simpa [selIds, inSel] using hs
      simp [withWindow, this]
  have hun : ((n.armed || pairDuress r n k) = false →
        writtenDeadline r env n k = unarmedDeadline r env n k) ∧
      ((n.armed || pairDuress r n k) = true →
        Wall.atOrBefore (writtenDeadline r env n k) (unarmedDeadline r env n k) = true) := by
    have hTU : Wall.atOrBefore n.T n.unarmedT = true := by
      cases ha : n.armed with
      | false => rw [hi.unarmed.1 ha]; exact Wall.atOrBefore_refl _
      | true => exact hi.unarmed.2 ha
    have hle := (newDeadline_unarmed_le (r := r) (env := env) hi k).1 hTU
    refine ⟨fun h => ?_, fun _ => Wall.atOrBefore_trans (writtenDeadline_le r env n k) hle⟩
    simp only [Bool.or_eq_false_iff] at h
    rw [writtenDeadline_eq_of_unarmed h.1 h.2]
    have hUT : Wall.atOrBefore n.unarmedT n.T = true := by
      rw [hi.unarmed.1 h.1]; exact Wall.atOrBefore_refl _
    exact Wall.atOrBefore_antisymm hle ((newDeadline_unarmed_le (r := r) (env := env) hi k).2 hUT)
  refine ⟨?_, ?_, inv_holderDecision r env n k hi.frozen, ?_, ?_, ?_, ?_, ?_, hun⟩
  · show (n.sweepActive || (pairDuress r n k)) = (n.armed || (pairDuress r n k))
    rw [hi.sweep]
  · intro ha c' hc'
    have ha' : (n.armed || (pairDuress r n k)) = false := ha
    simp only [Bool.or_eq_false_iff] at ha'
    obtain ⟨c, hc, _, _, _, _, hfr, _⟩ := hcands c' hc'
    cases hf : c'.frozen with
    | false => rfl
    | true =>
      rcases hfr hf with h | h
      · exact absurd (hi.unfrozen ha'.1 c hc) (by rw [h]; simp)
      · exact absurd hf (by
          simp only [holderDecision, List.mem_map] at hc'
          obtain ⟨x, hx, rfl⟩ := hc'
          rw [withWindow_frozen]
          simp [ha'.2, hi.unfrozen ha'.1 x hx])
  · intro c' hc' hs _
    exact (holderDecision_writes_every_window r env n k c' hc' (by simpa [selIds, inSel] using hs)).1
  · intro c' hc' hs
    obtain ⟨c, hc, hid, _, _, _, _, hw⟩ := hcands c' hc'
    rw [(hw hs).2]
    exact hi.noWindow c hc (by rw [← hid]; exact hsub c'.id hs)
  · intro ha c' hc' hhot hs f hf
    obtain ⟨c, hc, hid, hh, hb, hexp, _, hw⟩ := hcands c' hc'
    have hfc : c.fireAt = some f := by rw [← (hw hs).1]; exact hf
    have hnosel : inSel (selIds n) c.id = false := by rw [← hid]; exact hsub c'.id hs
    have hhotc : c.hot = true := by rw [← hh]; exact hhot
    cases hbc : c.broadcast with
    | true => exact .inl (by rw [hb]; exact hbc)
    | false =>
      cases hopen : windowOpen L n.combineSlack c' with
      | false => exact .inr (.inl hopen)
      | true =>
        refine .inr (.inr ?_)
        have hwin : windowOpen L n.combineSlack c = true := by
          rw [show windowOpen L n.combineSlack c' = windowOpen L n.combineSlack c from by
            simp only [windowOpen, (hw hs).2, (hw hs).1, hexp, hh]] at hopen
          exact hopen
        have hexpiryL : L.atOrBefore c.expiry = true := by
          simp only [windowOpen, hi.noWindow c hc hnosel, Bool.and_eq_true] at hwin
          exact hwin.1
        obtain ⟨e, he, hfe⟩ := earliestHotFire_le env n c hc hhotc hbc
          (Effective.atOrBefore_of_notAfter hle hexpiryL) f hfc
        have hb : Wall.belowFire (newDeadline r env n k) f n.epsilon L = true := by
          simp only [newDeadline, he]
          exact Wall.belowFire_weaken (Wall.belowFire_initial _ _ _ _ hfe) hle
        show Wall.belowFire (writtenDeadline r env n k) f n.epsilon L = true
        unfold writtenDeadline
        split
        · exact Wall.belowFire_clamp hb hle
        · exact hb
  · simp only [holderDecision]
    rw [ids_map _ _ (fun c => by rw [withWindow_id])]
    exact hi.idsUnique
  · intro c' hc' hs
    have hw := holderDecision_writes_every_window r env n k c' hc' (by simpa [selIds, inSel] using hs)
    exact ⟨.inr hw.2, fun _ => hw.1⟩

/-! ### Carried at the time ratchet

The invariant is carried at each state's own ratchet, not at a step's sample. `DUR-7`'s ratchet is
"the greatest effective time this node has read at a holder decision (`DUR-5`), a refused
Carrier's included, or at a hot acceptance", and those are the events that write `T` from a
sample, so each of them leaves a state whose ratchet is at or above the sample it wrote at.
`DUR-7`: "Nothing else moves it"; every other event touches no bound either, so it may run at any
sample, a backward one included. -/

/-- An acceptance at the ratchet it leaves: the advance, when the spend is hot and accepted, is
to `max(ratchet, effective)`; a refused or non-hot request leaves the ratchet as it was. -/
theorem inv_accept_ratchet {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) {env : Env} {n : Node}
    (hi : NodeInv n n.ratchet) (cid : Nat) (d : Bool) (E : Wall) (sp es : Cand)
    (hlt : n.armed = true → env.eff.deadlineReached n.T = false)
    (hwf : wfEvent n (.accept cid d E sp es) = true) :
    NodeInv (accept r env n cid d E sp es) (accept r env n cid d E sp es).ratchet := by
  have key : ∀ L, NodeInv n L → (sp.hot = true → env.eff.notAfter L = true) →
      NodeInv (accept r env n cid d E sp es) L :=
    fun L hL hle => inv_accept_at ht hd hr hL cid d E sp es hle hlt hwf
  unfold accept
  split
  · rw [refuse_ratchet]; exact inv_refuse hi cid d E _
  · rename_i hg
    split
    · exact hi
    · rename_i D hD
      have hL : n.ratchet.notAfter (accept r env n cid d E sp es).ratchet = true :=
        ratchet_never_lowered r env { node := n, exposure := [] } (.accept cid d E sp es)
      have hle : sp.hot = true → env.eff.notAfter (accept r env n cid d E sp es).ratchet = true := by
        intro hh
        simp only [accept, if_neg hg, hD]
        first
          | exact Effective.notAfter_latest_right _ _
          | (simp only [hh, if_true]; exact Effective.notAfter_latest_right _ _)
      simpa only [accept, if_neg hg, hD] using key _ (hi.weaken hL) hle

/-- A holder decision at the ratchet it leaves, `max(ratchet, effective)`. -/
theorem inv_holderDecision_ratchet {r : Rules} {env : Env} {n : Node} (hi : NodeInv n n.ratchet)
    (k : Carrier) : NodeInv (holderDecision r env n k) (holderDecision r env n k).ratchet := by
  refine inv_holderDecision_at (hi.weaken ?_) ?_ k
  · dsimp only [holderDecision]
    first
      | exact Effective.notAfter_latest_left _ _
      | (split <;> first | exact Effective.notAfter_latest_left _ _ | exact Effective.notAfter_refl _)
  · dsimp only [holderDecision]
    first
      | exact Effective.notAfter_latest_right _ _
      | (split <;> exact Effective.notAfter_latest_right _ _)

/-- Every event, one run: every clause of `NodeInv`, which the two-run relation consumes, carried
from the entering state's ratchet to the leaving state's, at any sample. -/
theorem inv_step {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) {env : Env} {w : World}
    (hi : NodeInv w.node w.node.ratchet) (e : Event) (hwf : wfEvent w.node e = true)
    (hlt : w.node.armed = true → env.eff.deadlineReached w.node.T = false) :
    NodeInv (step r env w e).1.node (step r env w e).1.node.ratchet := by
  have frame_map : ∀ (f : Cand → Cand) (pl : PendingLog), (∀ c, (f c).id = c.id ∧ (f c).hot = c.hot ∧
      (f c).frozen = c.frozen ∧ (f c).fireAt = c.fireAt ∧ (f c).windowClose = c.windowClose ∧
      (f c).expiry = c.expiry ∧ (c.broadcast = true → (f c).broadcast = true) ∧ (f c).quorum = c.quorum) →
      NodeInv { w.node with cands := w.node.cands.map f, pendingLog := pl } w.node.ratchet := by
    intro f pl hf
    refine inv_frame hi rfl rfl rfl rfl rfl rfl rfl ?_ ?_
    · simpa only [ids_map _ _ (fun c => (hf c).1)] using hi.idsUnique
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf c
      exact ⟨c, hc, h1, h2, h3, h4, h5, h6, h7, fun h => h8 ▸ h⟩
  cases e with
  | refuse cid d E pair code =>
    show NodeInv (refuse r env w.node cid d E pair) (refuse r env w.node cid d E pair).ratchet
    rw [refuse_ratchet]; exact inv_refuse hi cid d E pair
  | accept cid d E sp es => exact inv_accept_ratchet ht hd hr hi cid d E sp es hlt hwf
  | receipt cid s =>
    simp only [step, receipt]
    split
    · exact hi
    · split
      · exact hi
      · split
        · exact inv_holderDecision_ratchet hi _
        · exact inv_frame hi rfl rfl rfl rfl rfl rfl rfl hi.idsUnique
            (fun c' hc' => ⟨c', hc', rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩)
  | firePass =>
    simp only [step, firePass]
    split
    · exact inv_frame hi rfl rfl rfl rfl rfl rfl rfl hi.idsUnique
        (fun c' hc' => ⟨c', hc', rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩)
    · exact frame_map _ _ (fun c => by split <;> simp)
  | packageAccepted c =>
    simp only [step, packageAccepted]
    exact frame_map _ _ (fun c => by split <;> simp)
  | send c =>
    simp only [step, send]
    split
    · exact hi
    · exact frame_map _ _ (fun c => by split <;> simp <;> exact fun h => .inl h)
  | settle tx =>
    simp only [step, settle]
    split
    · exact hi
    · refine frame_map _ _ (fun c => ?_)
      split
      · simp
      · split <;> simp
  | prune =>
    simp only [step, prune]
    exact inv_frame hi rfl rfl rfl rfl rfl rfl rfl
      (List.Nodup.sublist (List.Sublist.map Cand.id List.filter_sublist) hi.idsUnique)
      (fun c' hc' => ⟨c', (List.mem_filter.1 hc').1, rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩)
  | tick =>
    simp only [step, tick]
    exact inv_frame hi rfl rfl rfl rfl rfl rfl rfl hi.idsUnique
      (fun c' hc' => ⟨c', hc', rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩)
  | panic =>
    exact inv_frame hi rfl rfl rfl rfl rfl rfl rfl hi.idsUnique
      (fun c' hc' => ⟨c', hc', rfl, rfl, rfl, rfl, rfl, rfl, (fun h => h), (fun h => h)⟩)
  | adversaryExposes m j sg c => exact hi
  | receivePartial m j sg c =>
    simp only [step, receivePartial]
    exact frame_map _ _ (fun c => by split <;> simp)

/-- And the composed step, which either refuses the spend before signing (`POL-16`) and leaves the
resident candidates unchanged while staging its Carrier, or takes the kernel's. -/
theorem inv_sysStep {g : Guards} {cfg : Config} {r : Rules} (ht : r.traversal = .always)
    (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve)
    {env : Env} {sys : Sys} (hi : NodeInv sys.world.node sys.world.node.ratchet) (e : Event)
    (hwf : wfEvent sys.world.node e = true)
    (hlt : sys.world.node.armed = true → env.eff.deadlineReached sys.world.node.T = false) :
    NodeInv (sysStep g cfg r env sys e).1.world.node (sysStep g cfg r env sys e).1.world.node.ratchet := by
  simp only [sysStep]
  split
  · cases e <;> try exact hi
    simp only [budgetRefusal, refuse_ratchet]
    exact inv_refuse hi _ _ _ _
  · exact inv_step ht hd hr hi e hwf hlt

/-! ## The observation is the same in both runs -/

theorem cands_ids_pub {x y : Node} (h : pubNode x = pubNode y) :
    x.cands.map (·.id) = y.cands.map (·.id) := by
  rw [map_comm (pubCand (selIds x)) (fun ec => ec.id) x.cands (fun c => c.id)
      (fun c _ => by simp [pubCand_id]),
    map_comm (pubCand (selIds y)) (fun ec => ec.id) y.cands (fun c => c.id)
      (fun c _ => by simp [pubCand_id]), pub_cands h]

theorem cands_map_id_pub {α : Type} {x y : Node} (h : pubNode x = pubNode y) (f : Nat → α) :
    x.cands.map (fun c => f c.id) = y.cands.map (fun c => f c.id) := by
  rw [map_comm (pubCand (selIds x)) (fun ec => f ec.id) x.cands (fun c => f c.id)
      (fun c _ => by simp [pubCand_id]),
    map_comm (pubCand (selIds y)) (fun ec => f ec.id) y.cands (fun c => f c.id)
      (fun c _ => by simp [pubCand_id]), pub_cands h]

/-- `/pending` is the same in both runs under either value of `Rules.pendingSource`, with no
hypothesis on it: `PubNode` carries the pending log, which every step writes from pin-uniform data
alone, and the registry projection reads only fields the projection keeps. -/
@[req "SPN-30"]
theorem pending_pub {r : Rules} {env : Env} {x y : Node} (h : pubNode x = pubNode y) :
    pending r env x = pending r env y := by
  unfold pending
  split
  · rw [pub_pendingLog h]
  refine filter_map_pub h (q := fun ec => ec.hot && !ec.settled && !ec.terminal && !ec.broadcast &&
      env.eff.atOrBefore ec.expiry) (g := fun ec => ec.id) ?_ ?_ ?_ ?_ <;>
  · intro c
    first
    | (intro _
       simp [pubCand_hot, pubCand_settled, pubCand_terminal, pubCand_broadcast, pubCand_expiry])
    | simp [pubCand_id]

@[req "DUR-1"]
theorem respond_pub {r : Rules} {cfg : Config} {env : Env} {a b : Sys} (hc : Coupled a b)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    respond r cfg env a (i.event tbl₀) = respond r cfg env b (i.event tbl₁) := by
  obtain ⟨hn, hx, hl⟩ := hc
  have hacc : ∀ (cid : Nat) (d₀ d₁ : Bool) (E : Wall) (sp es : Cand),
      respond r cfg env a (.accept cid d₀ E sp es) = respond r cfg env b (.accept cid d₁ E sp es) := by
    intro cid d₀ d₁ E sp es
    simp only [respond, pub_lockedDown hn, carriers_any_pub hn (fun k => k.cid == cid)
      (fun _ => rfl), tombstones_any_pub hn (fun k => k.cid == cid) (fun _ => rfl),
      hl, pairAdmits_pub r hn]
    rw [show refusedByBudget cfg (ageOut env cfg.window b.led) (.accept cid d₀ E sp es)
        = refusedByBudget cfg (ageOut env cfg.window b.led) (.accept cid d₁ E sp es) from rfl]
  cases i with
  | request cid pin E sp es => exact hacc cid (tbl₀ pin) (tbl₁ pin) E sp es
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | accept cid d E sp es => exact hacc cid d d E sp es
    | receipt cid s =>
      have hf := find?_pub hn cid
      simp only [Input.event, respond]
      cases hxx : a.world.node.carriers.find? (·.cid == cid) with
      | none =>
        cases hyy : b.world.node.carriers.find? (·.cid == cid) with
        | none => rfl
        | some k' => rw [hxx, hyy] at hf; simp at hf
      | some k =>
        cases hyy : b.world.node.carriers.find? (·.cid == cid) with
        | none => rw [hxx, hyy] at hf; simp at hf
        | some k' =>
          rw [hxx, hyy] at hf
          simp only [Option.map_some, Option.some.injEq] at hf
          show (if env.eff.before k.E then Resp.ack else Resp.retry)
            = (if env.eff.before k'.E then Resp.ack else Resp.retry)
          rw [pubCarrier_E_eq hf]
    | refuse _ _ _ _ _ | firePass | packageAccepted _ | send _ | settle _ | prune | tick | panic
    | adversaryExposes _ _ _ _ | receivePartial _ _ _ _ => rfl

@[req "DEF-12"]
theorem markerOf_pub {g : Marker} (hg : g = .committed) {env : Env} {x y : Node}
    (h : pubNode x = pubNode y) (i : Input) (tbl₀ tbl₁ : Enrolment) :
    markerOf g env x (i.event tbl₀) = markerOf g env y (i.event tbl₁) := by
  subst hg
  cases i with
  | request cid pin E sp es => rfl
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | receipt cid s => simp only [Input.event, markerOf, commits_pub h env cid s]
    | refuse _ _ _ _ _ | accept _ _ _ _ _ | firePass | packageAccepted _ | send _ | settle _ | prune | tick | panic
    | adversaryExposes _ _ _ _ | receivePartial _ _ _ _ => rfl

@[req "DUR-1"]
theorem work_pub {r : Rules} (ht : r.traversal = .always) {env : Env} {a b a' b' : Sys}
    (hn : pubNode a.world.node = pubNode b.world.node)
    (hn' : pubNode a'.world.node = pubNode b'.world.node) (i : Input) (tbl₀ tbl₁ : Enrolment) :
    work r env a a' (i.event tbl₀) = work r env b b' (i.event tbl₁) := by
  have hacc : ∀ (cid : Nat) (d₀ d₁ : Bool) (E : Wall) (sp es : Cand),
      work r env a a' (.accept cid d₀ E sp es) = work r env b b' (.accept cid d₁ E sp es) := by
    intro cid d₀ d₁ E sp es
    have hv := congrArg (List.map (fun c : Cand => Op.visit c.id)) (register_pub r hn env.mono sp es)
    simp only [List.map_map, Function.comp_def, pubCand_id] at hv
    simp only [work, carriers_any_pub hn' (fun k => k.cid == cid && k.accepted) (fun _ => rfl),
      carriers_any_pub hn (fun k => k.cid == cid) (fun _ => rfl), traverses_always ht]
    split
    · exact hv
    · rfl
  cases i with
  | request cid pin E sp es => exact hacc cid (tbl₀ pin) (tbl₁ pin) E sp es
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | accept cid d E sp es => exact hacc cid d d E sp es
    | receipt cid s =>
      have hf := find?_pub hn cid
      simp only [Input.event, work, commits_pub hn env cid s]
      split
      · cases hxx : a.world.node.carriers.find? (·.cid == cid) with
        | none =>
          cases hyy : b.world.node.carriers.find? (·.cid == cid) with
          | none => rfl
          | some k' => rw [hxx, hyy] at hf; simp at hf
        | some k =>
          cases hyy : b.world.node.carriers.find? (·.cid == cid) with
          | none => rw [hxx, hyy] at hf; simp at hf
          | some k' =>
            rw [hxx, hyy] at hf
            simp only [Option.map_some, Option.some.injEq] at hf
            show (k.pair.toList.map fun p => Op.select p.2) ++ _ =
              (k'.pair.toList.map fun p => Op.select p.2) ++ _
            rw [pubCarrier_pair_eq hf, cands_map_id_pub hn Op.visit]
      · rfl
    | refuse _ _ _ _ _ | firePass | packageAccepted _ | send _ | settle _ | prune | tick | panic
    | adversaryExposes _ _ _ _ | receivePartial _ _ _ _ => rfl

/-- One step's observation, in both runs. -/
theorem obsOf_eq {g : Marker} (hg : g = .committed) {gs : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    {env : Env} {a b : Sys} (hc : Coupled a b)
    (hia : NodeInv a.world.node a.world.node.ratchet) (hib : NodeInv b.world.node b.world.node.ratchet)
    (hpa : preHorizon r env a.world.node = true) (hpb : preHorizon r env b.world.node = true)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    obsOf g cfg r env a (sysStep gs cfg r env a (i.event tbl₀)).1
        (sysStep gs cfg r env a (i.event tbl₀)).2 (i.event tbl₀)
      = obsOf g cfg r env b (sysStep gs cfg r env b (i.event tbl₁)).1
        (sysStep gs cfg r env b (i.event tbl₁)).2 (i.event tbl₁) := by
  obtain ⟨hc', heff⟩ := sysStep_coupled ht hcl hdr hc hia hib hpa hpb i tbl₀ tbl₁
  simp only [obsOf, Obs.mk.injEq]
  exact ⟨respond_pub hc i tbl₀ tbl₁, pending_pub hc'.node, pub_lockedDown hc'.node,
    markerOf_pub hg hc.node i tbl₀ tbl₁, heff, work_pub ht hc.node hc'.node i tbl₀ tbl₁⟩

/-! ## The relation -/

theorem wfEvent_pub {x y : Node} (i : Input) (tbl₀ tbl₁ : Enrolment) :
    wfEvent x (i.event tbl₀) = wfEvent y (i.event tbl₁) := by
  cases i with
  | request cid pin E sp es => rfl
  | refusal cid pin E pair code => rfl
  | pinless e => cases e <;> rfl

/-- **SILENCE as a two-run relation.** `DUR-1`: "Every observable a node emits MUST be identical
between a normal-PIN and a duress-PIN request".

One trace of requests, two enrolment tables, one coupled pair of states: the two runs emit equal
observations at every step of the prefix on which both entering states are inside the concealment
horizon (`obsPair`). What carries the induction is that they stay coupled, which is
`sysStep_coupled`; this theorem concludes the equality alone. The walk also stops at the
request-shape boundary `wfEvent`: a non-hot Escape and no incoming window-close values.
There is no restriction on either incoming id's selected membership, nor a requirement that
selected ids be resident. Valid repeats after accepted or refused holder decisions remain covered.

The initial states are coupled and both satisfy `NodeInv` (including duplicate-free resident ids)
at their own time ratchet, assumed here and not derived from reachability; `inv_sysStep` carries it
from each state's ratchet to the next state's, at any sample. These premises narrow no state
`Kernel.Reachable.init` admits with its sweep flag clear: `silence_initial` concludes the relation
for every such state taken in both runs. Registration preserves residents;
`inv_sysStep` carries uniqueness and the opening-qualified window invariant through both kernel
ingress and budget refusal. The other rule premises are explicit: the marker keys on `DUR-5`'s
pin-uniform condition and not on the arm bit (`DEF-12`), `DUR-20`'s traversal is unconditional,
`DUR-14`'s `T` is dynamic, and `DUR-7`'s time ratchet is read at `max(ratchet, effective)` by a
hot window's close (`SPN-38`) and by the deadline driver. No premise is taken on
the trace's samples, which may step backward anywhere. With the close or the driver on the effective
sample alone, `F60`'s backward step opens a hot window below `T` in one world and not the other, and the
relation is false (`BtcPolicy.Exhibits.TwoRun.f60_ratcheted_close_alone_leaks`,
`BtcPolicy.Exhibits.TwoRun.f60_ratcheted_driver_alone_leaks`). -/
@[req "DUR-1"]
theorem silence {g : Marker} (hg : g = .committed) {gs : Guards} {cfg : Config} {r : Rules}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (tbl₀ tbl₁ : Enrolment) :
    ∀ (tr : List (Env × Input)) (a b : Sys), Coupled a b →
      NodeInv a.world.node a.world.node.ratchet → NodeInv b.world.node b.world.node.ratchet →
      ∀ y ∈ obsPair g gs cfg r tbl₀ tbl₁ a b tr, y.1 = y.2 := by
  intro tr
  induction tr with
  | nil => intro a b _ _ _ y hy; cases hy
  | cons x rest ih =>
    obtain ⟨env, i⟩ := x
    intro a b hc hia hib y hy
    simp only [obsPair] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨hpa, hpb⟩, hwf⟩ := hguard
      have hwfb : wfEvent b.world.node (i.event tbl₁) = true := by
        rw [← wfEvent_pub i tbl₀ tbl₁]; exact hwf
      rcases List.mem_cons.1 hy with rfl | hy
      · exact obsOf_eq hg ht hcl hdr hc hia hib hpa hpb i tbl₀ tbl₁
      · exact ih _ _ (sysStep_coupled ht hcl hdr hc hia hib hpa hpb i tbl₀ tbl₁).1
          (inv_sysStep ht hd hr hia (i.event tbl₀) hwf
            (fun ha => (Effective.deadlineReached_latest (preHorizon_below hdr hpa ha)).2))
          (inv_sysStep ht hd hr hib (i.event tbl₁) hwfb
            (fun ha => (Effective.deadlineReached_latest (preHorizon_below hdr hpb ha)).2)) y hy
    · cases hy

/-! ## The initial boundary: `unarmedT` is ghost state

`silence` takes `NodeInv` on its initial states, and `NodeInv.unarmed` asks an unarmed node to hold
its `T` as `Node.unarmedT`. `Kernel.Reachable.init` asks no such thing: it admits any node that is
not armed and holds no candidate and no Carrier, whatever its `unarmedT`. No transition reads the
field except a holder decision, through `Kernel.unarmedDeadline`, and only to compute the `unarmedT`
it leaves: no other field a step writes, no effect and no observation depends on it. The coupling
(`pubNode`) and `NodeInv.unarmed` read it as proof state. So a run's observations do not depend on
the `unarmedT` it starts from, and an initial state can be given its `T` there without changing a
single one. -/

/-- A composed state with its node's `unarmedT` replaced. -/
def withUnarmedT (s : Sys) (u : Wall) : Sys :=
  { s with world := { s.world with node := { s.world.node with unarmedT := u } } }

/-- One composed step from two states that differ only in `unarmedT` leaves two states that differ
only in `unarmedT`, and emits the same effects. -/
theorem sysStep_unarmedT (gs : Guards) (cfg : Config) (r : Rules) (env : Env) (s : Sys)
    (u v : Wall) (e : Event) :
    withUnarmedT (sysStep gs cfg r env (withUnarmedT s u) e).1 v =
        withUnarmedT (sysStep gs cfg r env s e).1 v ∧
      (sysStep gs cfg r env (withUnarmedT s u) e).2 = (sysStep gs cfg r env s e).2 := by
  obtain ⟨⟨n, x⟩, l⟩ := s
  cases e <;> dsimp only [sysStep, step, withUnarmedT, budgetRefusal, accept, refuse, receipt,
    firePass, packageAccepted, send, settle, prune, tick, receivePartial, holderDecision] <;>
    (repeat' split) <;> first | exact ⟨rfl, rfl⟩ | contradiction

/-- One step's observation reads no `unarmedT`, before the step or after it. -/
theorem obsOf_unarmedT (g : Marker) (cfg : Config) (r : Rules) (env : Env) (a b : Sys)
    (u v : Wall) (effs : List Effect) (e : Event) :
    obsOf g cfg r env (withUnarmedT a u) (withUnarmedT b v) effs e = obsOf g cfg r env a b effs e :=
  rfl

/-- The two runs walked together emit the same observations, and stop at the same step, whatever
`unarmedT` either starts from. -/
theorem obsPair_unarmedT (g : Marker) (gs : Guards) (cfg : Config) (r : Rules)
    (tbl₀ tbl₁ : Enrolment) :
    ∀ (tr : List (Env × Input)) (a b : Sys) (u v : Wall),
      obsPair g gs cfg r tbl₀ tbl₁ (withUnarmedT a u) (withUnarmedT b v) tr =
        obsPair g gs cfg r tbl₀ tbl₁ a b tr := by
  intro tr
  induction tr with
  | nil => intro _ _ _ _; rfl
  | cons x rest ih =>
    obtain ⟨env, i⟩ := x
    intro a b u v
    have step (s : Sys) (u : Wall) (e : Event) : ∃ u',
        (sysStep gs cfg r env (withUnarmedT s u) e).1 =
            withUnarmedT (sysStep gs cfg r env s e).1 u' ∧
          (sysStep gs cfg r env (withUnarmedT s u) e).2 = (sysStep gs cfg r env s e).2 :=
      ⟨_, (sysStep_unarmedT gs cfg r env s u _ e).1, (sysStep_unarmedT gs cfg r env s u u e).2⟩
    obtain ⟨u', ha, hea⟩ := step a u (i.event tbl₀)
    obtain ⟨v', hb, heb⟩ := step b v (i.event tbl₁)
    have hpa : preHorizon r env (withUnarmedT a u).world.node = preHorizon r env a.world.node := rfl
    have hpb : preHorizon r env (withUnarmedT b v).world.node = preHorizon r env b.world.node := rfl
    have hw : wfEvent (withUnarmedT a u).world.node (i.event tbl₀) =
        wfEvent a.world.node (i.event tbl₀) := rfl
    simp only [obsPair, hpa, hpb, hw, ha, hb, hea, heb, obsOf_unarmedT, ih]

/-- **`silence` at every initial state the kernel admits with its sweep flag clear.**
`Kernel.Reachable.init` admits a node that is not armed and holds no candidate and no Carrier
(`hi`, its conjunction as written); taken with its sweep flag clear (`hs`), any ledger and any
exposure history, and run under both enrolments, it emits equal observations at every step of
`obsPair`.

The premises `silence` grew with the clock family (`ADR-0026`) narrow none of these states.
`Coupled` carries `unarmedT`, which one state taken twice satisfies (`coupled_refl`).
`NodeInv.selWin` holds of a node with no candidate. `NodeInv.unarmed` holds once the state
carries its `T` as its `unarmedT`, and `obsPair_unarmedT` makes that a change no observation
sees. `hs` is the `sweep` clause's requirement on the initial node, and that clause predates the
clock family: `Reachable.init` does not clear the sweep flag, and no state that leaves it set is
covered here. -/
theorem silence_initial {g : Marker} (hg : g = .committed) {gs : Guards} {cfg : Config}
    {r : Rules} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (tbl₀ tbl₁ : Enrolment) (s : Sys)
    (hi : s.world.node.armed = false ∧ s.world.node.cands = [] ∧ s.world.node.carriers = [])
    (hs : s.world.node.sweepActive = false) :
    ∀ (tr : List (Env × Input)), ∀ y ∈ obsPair g gs cfg r tbl₀ tbl₁ s s tr, y.1 = y.2 := by
  intro tr y hy
  have hinv := nodeInv_initial (withUnarmedT s s.world.node.T).world.node
    (withUnarmedT s s.world.node.T).world.node.ratchet hi.2.1 hi.1 hs rfl
  rw [← obsPair_unarmedT g gs cfg r tbl₀ tbl₁ tr s s s.world.node.T s.world.node.T] at hy
  exact silence hg ht hd hr hcl hdr tbl₀ tbl₁ tr _ _ (coupled_refl _) hinv hinv y hy

namespace RegistrationCases
open Kernel.RegistrationCases

def observerChecks (r : Rules) : Bool :=
  let before := Ledger.RegistrationCases.accepted r
  let cfg := Ledger.RegistrationCases.cfg
  [false, true].all fun d =>
    let conflict := Event.accept 11 d (Wall.sample 200) c1 e2
    respond r cfg envBack before conflict == .refused .PSBT_INCONSISTENT &&
    respond r cfg envBack before (.accept 10 d (Wall.sample 200) c1 e2) ==
      .refused .NONCE_REPLAYED &&
    respond r cfg envBack { before with world := { before.world with node :=
      { before.world.node with lockedDown := true } } } conflict == .refused .FRAUD_SUSPECTED &&
    respond r { cfg with cap := 0 } envBack before
      (.accept 11 d (Wall.sample 200) c2 e1) == .refused .HOT_VELOCITY_EXCEEDED &&
    respond r cfg envBack before (.accept 11 d (Wall.sample 1) c1 e2) ==
      .refused .COMMITMENT_EXPIRED

/-- Actual traversal order for a compatible replay, after registration has retained residents.
Both a shrink and a non-shrink traverse the same resident ids once, under both PINs. -/
def workChecks (r : Rules) : Bool :=
  [false, true].all fun armed =>
    let n := if armed then scheduleBefore r else (lifecycle r).node
    let before : Sys := { world := { node := n, exposure := [] }, led := [] }
    [false, true].all fun d =>
      let ev := Event.accept 11 d (Wall.sample 200) c1 e1
      let after := (sysStep Ledger.current Ledger.RegistrationCases.cfg r env0 before ev).1
      work r env0 before after ev == [.visit 1, .visit 2]

end RegistrationCases

namespace RefusalCases
open Kernel.RegistrationCases

def cfg : Config := { cap := 1000, window := 120 }
def initial : Sys := { world := w0, led := [] }
def normal : Enrolment := fun _ => false
def duress : Enrolment := fun pin => pin == 1

/-- Both the refused ingress and its live holder decision precede the horizon; the fire pass
also lies before `T = 95`. Pin 0's initial registration is normal in both enrolments. -/
def trace (bound : Bool) : List (Env × Input) :=
  [(env0, .request 10 0 (Wall.sample 200) c1 e1),
   (env0, .refusal 11 1 (Wall.sample 200) (Kernel.RefusalCases.binding bound)
     (if bound then .EXPIRY_TOO_SHORT else .BAD_PIN)),
   (envBack, .pinless (.receipt 11 1)), (envAt 70 30, .pinless .firePass)]

def observations (g : Marker) (r : Rules) (bound : Bool) : List (Obs × Obs) :=
  obsPair g Ledger.current cfg r normal duress initial initial (trace bound)

def checks (g : Marker) (r : Rules) : Bool :=
  [false, true].all fun bound =>
    let os := observations g r bound
    os.length == (trace bound).length && os.all (fun o => o.1 == o.2) &&
    os.map (·.1.marker) == [false, false, true, false] &&
    os.map (·.1.ops) == [[.visit 1, .visit 2], [],
      (if bound then [.select 2, .visit 1, .visit 2] else [.visit 1, .visit 2]), []] &&
    os.map (·.1.resp) == [.accepted 10 env0.eff c1.fireAt,
      .refused (if bound then .EXPIRY_TOO_SHORT else .BAD_PIN), .ack, .silent]

end RefusalCases

end BtcPolicy.Silence
