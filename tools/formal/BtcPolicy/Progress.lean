import BtcPolicy.Freshness
import BtcPolicy.Lifetime
import BtcPolicy.FedSilence
/-! Progress under named scheduling profiles, the deadline driver as its own transition, and the
unbounded histories of `F3`, `F4` and `F13`. Newly formalized behaviour plus counterexamples. No
clock repair is chosen, no fairness is added to any safety theorem, and no deployment number is
assumed: every bound here is a parameter.

**Three profiles.** `Profile.Holds` says what the environment promises about one service (`Service`,
the instants at which it serves): `adversarial` promises nothing and is the profile of every safety
result, `eventual` promises service at some later instant from every instant, and `bounded B`
promises it within `B` slots of every instant. Service alone gives no progress: the transition must
be enabled when it is served (`served_eventually`, `served_within`), and the premise differs between
them. Under `eventual` enabling must be stable from some instant on, and under `bounded B` it must
hold across a usable window of `B` slots. Eventual service does not reach a finite expiry
(`eventual_misses_any_expiry`), and neither profile survives enabling that alternates with service
(`service_without_stable_enabling`).

**One run.** `pRun` plays a schedule (`Nat → Grant`) over `PSt`: the composed state of
`Lifetime.St`, `NCH-13`'s ingress guard (`Guard`) and the nonce log of `SPN-10` to `SPN-14`
(`NonceLog`). A grant is one critical section. `Grant.op` is exactly `Lifetime.step`, so
`Lifetime.Section.frame` stays the frame of every section it names (`op_is_lifetime`,
`Lifetime.step_frame`); this module adds sections beside them and replaces none (`driver_frame`,
`guard_frame`, `log_frame`). `SPN-20` says "`enter_lockdown` needs the same lock, and the lock is
unfair", and those two resource facts are all that is modelled: one grant per slot, and a schedule
free to pick any grant. No lock is implemented and no queue is ordered.

**The driver.** `DUR-7` says the driver "attempts it on every 1-second tick with no backend I/O, one
lock and one comparison". `driverDue` is that comparison, the same one `Silence.preHorizon` reads,
and `driverStep` writes the latch and nothing else (`driver_writes_latch_only`,
`driver_reads_no_chain`). `Kernel.tick` is `NCH-40`'s store prune driver and is a different
transition: it never writes the latch, and the deadline driver retires no Carrier
(`tick_keeps_latch`, `driver_retires_nothing`). A driver grant with the comparison true latches, on
every chain view: `driver_decides`, which is `DUR-15`'s "a statement about the decision, never about
its latency".

**Five goals, kept apart.** Local computation: the latch (`Local`). Message receipt: the guard takes
the envelope (`Received`). Arming: the node's arm bit (`Armed`). Escape submission: a candidate's
broadcast (`Submitted`). Chain inclusion, as far as a node can act on it: a settle pass whose chain
view shows the transaction (`Settled`); that a block holds it is `Sweep.Backend`'s, an environment
move no node step causes, and no theorem here concludes a confirmation. The record's progress table
lists, for each goal, its theorem under a named profile and its counterexample under a weaker one.

**`F13`.** A scheduler that never grants the driver leaves an armed node past `T` unlatched for every
horizon (`f13_starved`), while a fire pass on that node queues no hot partial
(`delayed_node_frozen`, over every schedule from a reachable world, no fairness premise). What gives a positive claim:
driver service within `B` slots and the comparison true at the driver's own sample
(`latch_within`), or the ratchet having read `T`, which then holds whatever the wall does
(`latch_within_of_read`).

**`F3`.** A forward excursion latches the guard's high-water; every honest envelope after the clock
is corrected is stale, delivered at every slot (`f3_blackhole`), and the outage lasts as long as the
excursion is large. The premise for a positive claim is `envelopeFits`: the high-water within
`NCH-12`'s past bound of the envelope's stamp (`received_within`).

**`F4`.** A wall-only entry pruned during an excursion latches the shared high-water
(`f4_latch_past_carrier`). A Carrier below the latch can no longer count a holder or arm
(`f4_no_arming`), for as many slots as the schedule delivers relays; `NCH-36` says "retries are bounded
by `E` and `D`, never unbounded". The log itself refuses every new request while
`raw + max_commitment_age_secs` is at or below the latch (`f4_every_request_refused`), and a latch
placed by an expiry a hostile coordinator signed against an excursion can be arbitrarily far ahead
of real time (`f4_log_outage`). The premise for a positive claim is a high-water below the expiry
(`window_open_below_latch`), which is the premise `NCH-37` already names.

**What is not modelled.** The guard's quota, the outer-stale path's answers (`NCH-37` answers a retry
and counts no holder, so it changes no history here), the alternate-signature work, `SPN-11`'s absent
monotonic sample, the log's length and capacity checks and `API-19`'s `last_deadline_tick`. Only the
envelope and driver grants read their `Env` from the log (`envOf`); `Grant.op` keeps `Lifetime`'s free
`Env`. A slot is not a second of real time, and nothing here bounds machine timing, service rates or
how long a block takes. -/

namespace BtcPolicy.Progress
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## The profiles -/

/-- The instants at which the environment serves one kind of progress. -/
abbrev Service := Nat → Bool

/-- The three environment profiles. -/
inductive Profile
  /-- Arbitrary adversarial scheduling, the profile of every safety result. -/
  | adversarial
  /-- From every instant, some later instant serves. -/
  | eventual
  /-- From every instant, an instant within `B` slots serves. `B` is a parameter, never a figure. -/
  | bounded (B : Nat)
  deriving DecidableEq, Repr

def Profile.Holds : Profile → Service → Prop
  | .adversarial, _ => True
  | .eventual, s => ∀ t, ∃ u, t ≤ u ∧ s u = true
  | .bounded B, s => ∀ t, ∃ u, t ≤ u ∧ u ≤ t + B ∧ s u = true

/-- The profiles only weaken in this order. -/
theorem bounded_eventual {B : Nat} {s : Service} (h : (Profile.bounded B).Holds s) :
    Profile.eventual.Holds s := fun t =>
  let ⟨u, hu, _, hs⟩ := h t; ⟨u, hu, hs⟩

/-- Eventual service reaches a stably enabled transition. -/
theorem served_eventually {s en : Service} {t0 : Nat} (hs : Profile.eventual.Holds s)
    (hen : ∀ u, t0 ≤ u → en u = true) : ∃ u, t0 ≤ u ∧ en u = true ∧ s u = true :=
  let ⟨u, hu, hsu⟩ := hs t0; ⟨u, hu, hen u hu, hsu⟩

/-- Bounded service reaches a transition enabled across a usable window of `B` slots. -/
theorem served_within {B t0 : Nat} {s en : Service} (hs : (Profile.bounded B).Holds s)
    (hen : ∀ u, t0 ≤ u → u ≤ t0 + B → en u = true) :
    ∃ u, t0 ≤ u ∧ u ≤ t0 + B ∧ en u = true ∧ s u = true :=
  let ⟨u, hu, hle, hsu⟩ := hs t0; ⟨u, hu, hle, hen u hu hle, hsu⟩

/-- Under `adversarial`, nothing need ever be served. -/
theorem adversarial_starves : ∃ s, Profile.adversarial.Holds s ∧ ∀ t, s t = false :=
  ⟨fun _ => false, trivial, fun _ => rfl⟩

/-- A bound `B` says nothing about a window narrower than `B`: service can come first at `B`. -/
theorem bounded_misses_narrower_window (B : Nat) :
    ∃ s, (Profile.bounded B).Holds s ∧ ∀ t, t < B → s t = false := by
  refine ⟨fun u => decide (B ≤ u), fun t => ⟨t + B, by omega, by omega, by simp⟩, fun t ht => ?_⟩
  simpa using ht

/-- Eventual service alone does not give service before a finite expiry, whatever the expiry. -/
theorem eventual_misses_any_expiry (E : Nat) :
    ∃ s, Profile.eventual.Holds s ∧ ∀ t, t < E → s t = false :=
  let ⟨s, hb, hs⟩ := bounded_misses_narrower_window E; ⟨s, bounded_eventual hb, hs⟩

/-- Service and enabling that alternate never meet, though each recurs within one slot. -/
theorem service_without_stable_enabling :
    ∃ s en : Service, (Profile.bounded 1).Holds s ∧ (Profile.bounded 1).Holds en ∧
      ∀ u, ¬(s u = true ∧ en u = true) := by
  refine ⟨fun u => u % 2 == 0, fun u => u % 2 == 1, fun t => ?_, fun t => ?_, fun u => ?_⟩
  · by_cases h : t % 2 = 0
    · exact ⟨t, by omega, by omega, by simp [h]⟩
    · exact ⟨t + 1, by omega, by omega, by simp; omega⟩
  · by_cases h : t % 2 = 1
    · exact ⟨t, by omega, by omega, by simp [h]⟩
    · exact ⟨t + 1, by omega, by omega, by simp; omega⟩
  · simp only [beq_iff_eq, not_and]
    omega

/-! ## The deadline driver -/

/-- `DUR-7`'s one comparison, `armed ∧ max(ratchet, effective) ≥ T`, read as `Silence.preHorizon`
reads it: the two are one predicate, so the driver and the concealment horizon cannot part. -/
@[req "DUR-7"]
def driverDue (r : Rules) (env : Env) (n : Node) : Bool := !Silence.preHorizon r env n

/-- `DUR-7`'s attempt, holding the lock: the comparison, then the latch. It stands apart from
`Kernel.tick`, `NCH-40`'s store prune driver. -/
@[req "DUR-7"]
def driverStep (r : Rules) (env : Env) (n : Node) : Node :=
  if driverDue r env n then { n with lockedDown := true } else n

/-- `DUR-15`'s "a statement about the decision, never about its latency": on any attempt that holds
the lock with the comparison true, the latch is set, on every chain view and every other field. -/
@[req "DUR-7"]
theorem driver_decides (r : Rules) (env : Env) (n : Node) (h : driverDue r env n = true) :
    (driverStep r env n).lockedDown = true := by
  simp [driverStep, h]

/-- `DUR-7`: "no backend I/O". The attempt reads no chain view. -/
@[req "DUR-7"]
theorem driver_reads_no_chain (r : Rules) (env : Env) (v : ChainView) (n : Node) :
    driverStep r { env with chain := v } n = driverStep r env n := rfl

/-- The attempt writes the latch and nothing else. -/
@[req "DUR-7"]
theorem driver_writes_latch_only (r : Rules) (env : Env) (n : Node) :
    { driverStep r env n with lockedDown := n.lockedDown } = n := by
  unfold driverStep
  split <;> rfl

/-- `NCH-40`'s store prune driver never writes the latch. -/
@[req "NCH-40"]
theorem tick_keeps_latch (r : Rules) (env : Env) (n : Node) :
    (tick r env n).lockedDown = n.lockedDown := rfl

/-- And the deadline driver retires nothing: `NCH-40` closes retirement to its own list. -/
@[req "NCH-40"]
theorem driver_retires_nothing (r : Rules) (env : Env) (n : Node) :
    (driverStep r env n).carriers = n.carriers ∧ (driverStep r env n).tombstones = n.tombstones := by
  unfold driverStep
  split <;> exact ⟨rfl, rfl⟩

/-- Under `driverTime = ratchet` the comparison holds at any raw sample at or past `T`. -/
theorem driverDue_of_wall {r : Rules} (hdr : r.driverTime = .ratchet) {w h : Nat} {mono : Mono}
    {chain : ChainView} {τ : Nat} {n : Node} (ha : n.armed = true) (hT : n.T = Wall.sample τ)
    (hw : τ ≤ w) :
    driverDue r { wall := Wall.sample w, hw := HighWater.sample h, mono := mono, chain := chain } n
      = true := by
  simp only [driverDue, Silence.preHorizon, hdr, ha, hT, Bool.not_true, Bool.false_or,
    Bool.not_not]
  exact Effective.deadlineReached_latest_right _ (Effective.ofWall_reached hw)

/-! ## `NCH-13`'s ingress guard -/

/-- The receiver's ingress state: the freshness high-water and the seen nonces, each with the
envelope's own timestamp. The quota of steps 2 and 5 is not modelled. -/
structure Guard where
  hw : Nat := 0
  seen : List (Nat × Nat × Nat) := []
  deriving DecidableEq, Repr

inductive GuardVerdict
  | accepted | stale | replayed
  deriving DecidableEq, Repr

/-- `NCH-12`: "An envelope is **fresh** iff `timestamp ∈ [now − 300, now + 60]`". -/
@[req "NCH-12"]
def fresh (ts now : Nat) : Bool := now ≤ ts + Freshness.past && ts ≤ now + Freshness.future

/-- `NCH-13`'s critical section, in its order: the high-water moves first and on every envelope,
freshness reads it, a stale envelope consumes no nonce, then prune, replay and insert. -/
@[req "NCH-13"]
def ingress (g : Guard) (raw sender nonce ts : Nat) : Guard × GuardVerdict :=
  let now := max g.hw raw
  if !fresh ts now then ({ g with hw := now }, .stale)
  else
    let kept := g.seen.filter fun e => now ≤ e.2.2 + Freshness.pruneOffset
    if kept.any (fun e => e.1 == sender && e.2.1 == nonce) then ({ hw := now, seen := kept }, .replayed)
    else ({ hw := now, seen := (sender, nonce, ts) :: kept }, .accepted)

/-- `NCH-13`: "the freshness high-water is forward-only and never lowered". -/
@[req "NCH-13"]
theorem ingress_hw (g : Guard) (raw sender nonce ts : Nat) :
    (ingress g raw sender nonce ts).1.hw = max g.hw raw := by
  simp only [ingress]
  split
  · rfl
  · split <;> rfl

/-- `F3`'s step: an envelope whose stamp is more than `NCH-12`'s past bound below the high-water is
stale whatever the raw sample below it, and it consumes no nonce. -/
@[req "NCH-38"]
theorem stale_below_latch (g : Guard) (raw sender nonce ts : Nat)
    (h : ts + Freshness.past < max g.hw raw) :
    ingress g raw sender nonce ts = ({ g with hw := max g.hw raw }, .stale) := by
  have hf : fresh ts (max g.hw raw) = false := by
    simp only [fresh, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact .inl (by omega)
  simp [ingress, hf]

/-- `NCH-38`'s recovery: "A stale sender recovers only when elapsed real time brings its timestamps
back inside the 300-second window". With the stamp inside the window of `max(high_water, raw)` and
an unseen nonce, the guard takes the envelope. -/
@[req "NCH-38"]
theorem ingress_accepts (g : Guard) (raw sender nonce ts : Nat)
    (hp : max g.hw raw ≤ ts + Freshness.past) (hf : ts ≤ max g.hw raw + Freshness.future)
    (hn : g.seen.any (fun e => e.1 == sender && e.2.1 == nonce) = false) :
    (ingress g raw sender nonce ts).2 = .accepted ∧
      (sender, nonce, ts) ∈ (ingress g raw sender nonce ts).1.seen := by
  have hfresh : fresh ts (max g.hw raw) = true := by simp [fresh, hp, hf]
  have hk : (g.seen.filter fun e => max g.hw raw ≤ e.2.2 + Freshness.pruneOffset).any
      (fun e => e.1 == sender && e.2.1 == nonce) = false := by
    simp only [List.any_eq_false, List.mem_filter] at hn ⊢
    exact fun e he => hn e he.1
  simp [ingress, hfresh, hk]

/-! ## The nonce log of `SPN-10` to `SPN-14` -/

/-- `SPN-11`: "its signed wall expiry and — for a channel-mode spend only — its monotonic Carrier
deadline `D`". -/
structure LogEntry where
  nonce : Nat
  expiry : Nat
  D : Option Nat := none
  deriving DecidableEq, Repr

/-- `SPN-12`'s one log with "one shared non-decreasing high-water mark", and the sealed
`max_commitment_age_secs`, a parameter. Length and capacity are not modelled. -/
structure NonceLog where
  maxAge : Nat := 0
  hw : Nat := 0
  entries : List LogEntry := []
  deriving DecidableEq, Repr

/-- `SPN-13`: "`effective_now = max(high_water, raw_now)`". -/
@[req "SPN-13"]
def NonceLog.eff (l : NonceLog) (raw : Nat) : Nat := max l.hw raw

/-- `SPN-11`: "An entry is **live** while `expiry > effective_now` OR `mono_now < D`". -/
@[req "SPN-11"]
def LogEntry.live (e : LogEntry) (eff mono : Nat) : Bool :=
  decide (eff < e.expiry) || match e.D with
    | some d => decide (mono < d)
    | none => false

/-- `SPN-10`'s two readings: "`expiry > effective_now`" and "`expiry ≤ raw_now +
max_commitment_age_secs` against the RAW wall clock". -/
@[req "SPN-10"]
def NonceLog.windowOk (l : NonceLog) (raw expiry : Nat) : Bool :=
  decide (l.eff raw < expiry) && decide (expiry ≤ raw + l.maxAge)

/-- The greatest expiry among the entries given, floored at `m`. -/
def maxExpiry (m : Nat) (es : List LogEntry) : Nat := es.foldl (fun a e => max a e.expiry) m

/-- `SPN-14`: "A refused request MUST mutate nothing", and "On accept, and only then, the log prunes
under both clocks", and `D` is computed there. `SPN-13`: "The high-water is advanced, on an accept
only, to the greatest expiry of every entry that accept pruned." `channel` is a channel-mode spend;
every other entry is wall-only. -/
@[req "SPN-14"]
def NonceLog.accept (l : NonceLog) (raw mono nonce expiry : Nat) (channel : Bool) : NonceLog :=
  let eff := l.eff raw
  let live := l.entries.filter (·.live eff mono)
  if !l.windowOk raw expiry || live.any (·.nonce == nonce) then l
  else
    { l with
      hw := maxExpiry l.hw (l.entries.filter (!·.live eff mono))
      entries := { nonce := nonce, expiry := expiry,
                   D := if channel then some (mono + (expiry - eff)) else none } :: live }

/-- `maxExpiry` is at or above its floor. -/
theorem le_maxExpiry (m : Nat) (es : List LogEntry) : m ≤ maxExpiry m es := by
  induction es generalizing m with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- And at or above every expiry it folds. -/
theorem expiry_le_maxExpiry (m : Nat) (es : List LogEntry) (e : LogEntry) (he : e ∈ es) :
    e.expiry ≤ maxExpiry m es := by
  induction es generalizing m with
  | nil => cases he
  | cons x es ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_maxExpiry _ _)
    · exact ih _ he

/-- `SPN-12`: the high-water is non-decreasing. -/
@[req "SPN-12"]
theorem accept_hw_mono (l : NonceLog) (raw mono nonce expiry : Nat) (channel : Bool) :
    l.hw ≤ (l.accept raw mono nonce expiry channel).hw := by
  simp only [NonceLog.accept]
  split
  · exact Nat.le_refl _
  · exact le_maxExpiry _ _

/-- `SPN-12`: "an accepted transition that prunes a Refresh whose expiry exceeds a live Carrier's
signed expiry advances the high-water past that Carrier". The entry pruned is any entry the accept
finds not live. -/
@[req "SPN-12"]
theorem accept_latches (l : NonceLog) (raw mono nonce expiry : Nat) (channel : Bool) (e : LogEntry)
    (he : e ∈ l.entries) (hdead : e.live (l.eff raw) mono = false)
    (hok : l.windowOk raw expiry = true)
    (hfresh : l.entries.any (fun x => x.live (l.eff raw) mono && x.nonce == nonce) = false) :
    e.expiry ≤ (l.accept raw mono nonce expiry channel).hw := by
  have hany : (l.entries.filter (·.live (l.eff raw) mono)).any (·.nonce == nonce) = false := by
    simp only [List.any_eq_false, List.mem_filter, Bool.and_eq_true, not_and] at hfresh ⊢
    exact fun x hx => hfresh x hx.1 hx.2
  simp only [NonceLog.accept, hok, Bool.not_true, Bool.false_or, hany, if_false]
  exact expiry_le_maxExpiry _ _ _ (List.mem_filter.2 ⟨he, by simp [hdead]⟩)

/-- `F4`'s reach: while `raw + max_commitment_age_secs` is at or below the high-water, `SPN-10`'s two
readings admit no expiry at all. One log serves Spend, Refresh and Clawback alike (`SPN-12`), so
this refuses all three. -/
@[req "SPN-12"]
theorem f4_every_request_refused (l : NonceLog) (raw expiry : Nat) (h : raw + l.maxAge ≤ l.hw) :
    l.windowOk raw expiry = false := by
  simp only [NonceLog.windowOk, NonceLog.eff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- `SPN-14`: a request the log refuses leaves it as it was, so a latch does not clear by being
asked. -/
@[req "SPN-14"]
theorem refused_keeps_log (l : NonceLog) (raw mono nonce expiry : Nat) (channel : Bool)
    (h : l.windowOk raw expiry = false) : l.accept raw mono nonce expiry channel = l := by
  simp [NonceLog.accept, h]

/-- The premise `NCH-37` names, "only if the nonce high-water is still below `E`", as a positive
result at the log: an expiry above the high-water and the raw sample and within the age bound passes
the window. -/
@[req "SPN-10"]
theorem window_open_below_latch (l : NonceLog) (raw expiry : Nat) (hw : l.hw < expiry)
    (hr : raw < expiry) (ha : expiry ≤ raw + l.maxAge) : l.windowOk raw expiry = true := by
  simp only [NonceLog.windowOk, NonceLog.eff, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `F4`'s unbounded form. Two excursions, each on an expiry `SPN-10`'s upper reading admits because
it reads the raw sample: an entry whose expiry sits `max_commitment_age_secs` above the first, and
an accept at that expiry that prunes it. Afterwards no expiry passes the window at any raw sample at
or below the first excursion, however long real time takes to get there, and each refusal leaves the
log as it is (`refused_keeps_log`). The first entry needs a coordinator signature on an expiry that
far ahead: `SPN-10` calls this "the horizon a hostile coordinator may claim". An honest coordinator
with a correct clock places a latch no further than real time plus the age bound. -/
@[req "SPN-12"]
theorem f4_log_outage (l : NonceLog) (J mono : Nat) (hage : 0 < l.maxAge) (hJ : l.hw < J)
    (hempty : l.entries = []) :
    let l1 := l.accept J mono 0 (J + l.maxAge) false
    let l2 := l1.accept (J + l.maxAge) mono 1 (J + l.maxAge + l.maxAge) false
    l2.hw = J + l.maxAge ∧ ∀ raw expiry, raw ≤ J → l2.windowOk raw expiry = false := by
  obtain ⟨maxAge, hw, entries⟩ := l
  simp only at hage hJ hempty
  subst hempty
  have hw1 : hw < J + maxAge := by omega
  have hmax : max hw (J + maxAge) = J + maxAge := by omega
  have hmaxJ : max hw J = J := by omega
  have hk : max (J + maxAge) (J + maxAge) = J + maxAge := by omega
  have key : (({ maxAge := maxAge, hw := hw, entries := [] } : NonceLog).accept J mono 0 (J + maxAge)
      false).accept (J + maxAge) mono 1 (J + maxAge + maxAge) false =
      { maxAge := maxAge, hw := J + maxAge,
        entries := [{ nonce := 1, expiry := J + maxAge + maxAge, D := none }] } := by
    simp [NonceLog.accept, NonceLog.windowOk, NonceLog.eff, LogEntry.live, maxExpiry, hmaxJ, hmax,
      hage, hJ]
  simp only [key]
  exact ⟨trivial, fun raw expiry hr => f4_every_request_refused _ _ _ (by simp only; omega)⟩

/-! ## The composed run -/

/-- The composed state a schedule plays over. -/
structure PSt where
  st : Lifetime.St
  guard : Guard := {}
  log : NonceLog := {}
  deriving DecidableEq, Repr

def PSt.node (s : PSt) : Node := s.st.sys.world.node

/-- The environment a grant that reads the log hands the kernel: the raw sample, this log's
high-water, the HotClock sample, the chain view. -/
def envOf (l : NonceLog) (raw mono : Nat) (chain : ChainView) : Env :=
  { wall := Wall.sample raw, hw := HighWater.sample l.hw, mono := Mono.sample mono, chain := chain }

/-- `DUR-7`: "no backend I/O". The driver's sample carries an empty chain view it does not read. -/
def driverEnv (l : NonceLog) (raw mono : Nat) : Env :=
  envOf l raw mono { mtp := Mtp.sample 0, seen := [] }

/-- One critical section. `SPN-20` says "`enter_lockdown` needs the same lock, and the lock is
unfair": one grant per slot, and nothing constrains which. -/
inductive Grant
  /-- `DUR-7`'s deadline driver holding the sign lock. -/
  | driver (raw mono : Nat)
  /-- A section `Lifetime` already names, exactly as it names it. -/
  | op (o : Lifetime.Op)
  /-- An authenticated envelope at `NCH-13`'s guard carrying a relay of `cid` from `sender`. -/
  | envelope (raw mono : Nat) (chain : ChainView) (cid sender nonce ts : Nat)
  /-- A request at the nonce log. -/
  | logAccept (raw mono nonce expiry : Nat) (channel : Bool)
  /-- The lock is free. -/
  | idle
  deriving DecidableEq, Repr

/-- One slot. An envelope grant reaches `Kernel.receipt` only when the guard accepts it. `Grant.op`
keeps `Lifetime`'s own route to that event, which passes no guard. -/
def pStep (c : Lifetime.Cfg) (s : PSt) : Grant → PSt
  | .driver raw mono =>
    { s with st := { s.st with sys := { s.st.sys with world := { s.st.sys.world with
        node := driverStep c.r (driverEnv s.log raw mono) s.st.sys.world.node } } } }
  | .op o => { s with st := Lifetime.step c s.st o }
  | .envelope raw mono chain cid sender nonce ts =>
    let v := ingress s.guard raw sender nonce ts
    if v.2 == .accepted then
      { s with guard := v.1,
               st := Lifetime.step c s.st (.kernel (envOf s.log raw mono chain) (.receipt cid sender)) }
    else { s with guard := v.1 }
  | .logAccept raw mono nonce expiry channel =>
    { s with log := s.log.accept raw mono nonce expiry channel }
  | .idle => s

/-- A schedule's run, at every slot. -/
def pRun (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant) : Nat → PSt
  | 0 => s0
  | t + 1 => pStep c (pRun c s0 sched t) (sched t)

/-! ### The frames: `Lifetime.Section.frame` stays, the new sections go beside it -/

/-- A section `Lifetime` names is exactly `Lifetime.step`, so `Lifetime.step_frame` is its frame, and
it touches neither the guard nor the log. -/
@[req "SPN-20"]
theorem op_is_lifetime (c : Lifetime.Cfg) (s : PSt) (o : Lifetime.Op) :
    (pStep c s (.op o)).st = Lifetime.step c s.st o ∧ (pStep c s (.op o)).guard = s.guard ∧
      (pStep c s (.op o)).log = s.log := ⟨rfl, rfl, rfl⟩

/-- The driver's section writes no marker, no refresh, no ledger row, no guard and no log. -/
@[req "DUR-7"]
theorem driver_frame (c : Lifetime.Cfg) (s : PSt) (raw mono : Nat) :
    (pStep c s (.driver raw mono)).st.inFlight = s.st.inFlight ∧
      (pStep c s (.driver raw mono)).st.refreshes = s.st.refreshes ∧
      (pStep c s (.driver raw mono)).st.sys.led = s.st.sys.led ∧
      (pStep c s (.driver raw mono)).st.sys.world.exposure = s.st.sys.world.exposure ∧
      (pStep c s (.driver raw mono)).guard = s.guard ∧ (pStep c s (.driver raw mono)).log = s.log :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A stale envelope moves only the guard's high-water. -/
@[req "NCH-13"]
theorem guard_frame (c : Lifetime.Cfg) (s : PSt) (raw mono : Nat) (chain : ChainView)
    (cid sender nonce ts : Nat) (h : (ingress s.guard raw sender nonce ts).2 ≠ .accepted) :
    (pStep c s (.envelope raw mono chain cid sender nonce ts)).st = s.st ∧
      (pStep c s (.envelope raw mono chain cid sender nonce ts)).log = s.log := by
  simp [pStep, h]

/-- A request at the log moves only the log. -/
@[req "SPN-14"]
theorem log_frame (c : Lifetime.Cfg) (s : PSt) (raw mono nonce expiry : Nat) (channel : Bool) :
    (pStep c s (.logAccept raw mono nonce expiry channel)).st = s.st ∧
      (pStep c s (.logAccept raw mono nonce expiry channel)).guard = s.guard := ⟨rfl, rfl⟩

/-! ### Every world a run holds is a kernel world, latched or not -/

/-- A world with the latch set. -/
def latW (w : World) : World := { w with node := { w.node with lockedDown := true } }

theorem latW_self {w : World} (h : w.node.lockedDown = true) : latW w = w := by
  obtain ⟨n, x⟩ := w
  cases n
  simp_all [latW]

/-- A latched node takes no new request: `accept` and `refuse` read the latch first. -/
theorem step_latW_request (r : Rules) (env : Env) (w : World) (e : Event)
    (he : (∃ cid d E sp es, e = .accept cid d E sp es) ∨ ∃ cid d E p code, e = .refuse cid d E p code) :
    (step r env (latW w) e).1 = latW w := by
  rcases he with ⟨cid, d, E, sp, es, rfl⟩ | ⟨cid, d, E, p, code, rfl⟩ <;>
    simp [step, accept, refuse, latW]

theorem receipt_latched (r : Rules) (env : Env) (n : Node) (cid s : Nat) :
    receipt r env { n with lockedDown := true } cid s = { receipt r env n cid s with lockedDown := true } := by
  have hf : ({ n with lockedDown := true } : Node).carriers = n.carriers := rfl
  unfold receipt
  rw [hf]
  cases hk : n.carriers.find? (·.cid == cid) with
  | none => rfl
  | some k =>
    simp only
    by_cases h1 : (!(env.mono.before k.D) || !(env.eff.before k.E)) = true
    · simp only [h1, if_true]
    · simp only [h1, if_false]
      have hc : commits env { n with lockedDown := true } cid s = commits env n cid s := rfl
      rw [hc]
      by_cases h2 : commits env n cid s = true
      · simp only [h2, if_true]; rfl
      · simp only [h2, if_false]; rfl

/-- Every other event reads no latch, so it does on a latched world what it does on the same world
unlatched. `DUR-7`: "Lockdown blocks NEW signing and MUST NOT block the in-flight Escape combine". -/
theorem step_latW_other (r : Rules) (env : Env) (w : World) (e : Event)
    (ha : ∀ cid d E sp es, e ≠ .accept cid d E sp es) (hf : ∀ cid d E p code, e ≠ .refuse cid d E p code) :
    step r env (latW w) e = (latW (step r env w e).1, (step r env w e).2) := by
  cases e with
  | accept cid d E sp es => exact absurd rfl (ha cid d E sp es)
  | refuse cid d E p code => exact absurd rfl (hf cid d E p code)
  | receipt cid s =>
    show ({ w with node := receipt r env { w.node with lockedDown := true } cid s }, []) = _
    rw [receipt_latched]
    rfl
  | firePass =>
    simp only [step, firePass, latW]
    split <;> rfl
  | packageAccepted c => rfl
  | send c =>
    simp only [step, send, latW]
    split <;> rfl
  | settle tx =>
    simp only [step, settle, latW]
    split <;> rfl
  | prune => rfl
  | tick => rfl
  | panic => rfl
  | adversaryExposes m i s c => rfl
  | receivePartial m i s c => rfl

/-- A composed section's world is the kernel's on some event, or unchanged. -/
theorem life_world_next (c : Lifetime.Cfg) (st : Lifetime.St) (o : Lifetime.Op) :
    (Lifetime.step c st o).sys.world = st.sys.world ∨
      ∃ env e, (Lifetime.step c st o).sys.world = (step c.r env st.sys.world e).1 := by
  cases o with
  | claim k => exact .inl rfl
  | exit k w => exact .inl rfl
  | hold k env cid d E q =>
    simp only [Lifetime.step, Lifetime.hold]
    split
    · exact .inr ⟨env, _, (FedSilence.sysStep_kernel _ _ _ _ _ _).1⟩
    · exact .inl rfl
  | refresh env tx ok =>
    simp only [Lifetime.step, Lifetime.refreshHold]
    split <;> exact .inl rfl
  | kernel env e => exact .inr ⟨env, _, (FedSilence.sysStep_kernel _ _ _ _ _ _).1⟩

/-- The world after one slot: the same, or the kernel's on some event, or the driver's latch. -/
theorem pStep_world (c : Lifetime.Cfg) (s : PSt) (g : Grant) :
    (pStep c s g).st.sys.world = s.st.sys.world ∨
      (∃ env e, (pStep c s g).st.sys.world = (step c.r env s.st.sys.world e).1) ∨
      (pStep c s g).st.sys.world = latW s.st.sys.world := by
  cases g with
  | driver raw mono =>
    simp only [pStep, driverStep]
    split
    · exact .inr (.inr rfl)
    · exact .inl rfl
  | op o =>
    rcases life_world_next c s.st o with h | ⟨env, e, h⟩
    · exact .inl h
    · exact .inr (.inl ⟨env, e, h⟩)
  | envelope raw mono chain cid sender nonce ts =>
    simp only [pStep]
    split
    · rcases life_world_next c s.st (.kernel (envOf s.log raw mono chain) (.receipt cid sender)) with
        h | ⟨env, e, h⟩
      · exact .inl h
      · exact .inr (.inl ⟨env, e, h⟩)
    · exact .inl rfl
  | logAccept raw mono nonce expiry channel => exact .inl rfl
  | idle => exact .inl rfl

/-- The latch never clears, on any kernel event. -/
theorem step_keeps_latch (r : Rules) (env : Env) (w : World) (e : Event)
    (h : w.node.lockedDown = true) : (step r env w e).1.node.lockedDown = true := by
  rw [← latW_self h]
  by_cases hreq : (∃ cid d E sp es, e = .accept cid d E sp es) ∨
      ∃ cid d E p code, e = .refuse cid d E p code
  · rw [step_latW_request r env w e hreq]; rfl
  · rw [step_latW_other r env w e
      (fun cid d E sp es he => hreq (.inl ⟨cid, d, E, sp, es, he⟩))
      (fun cid d E p code he => hreq (.inr ⟨cid, d, E, p, code, he⟩))]
    rfl

/-- `DUR-7`: "Lockdown is a latch that survives for the process lifetime with no reset". -/
@[req "DUR-7"]
theorem latch_sticky (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant) {t u : Nat} (htu : t ≤ u)
    (h : (pRun c s0 sched t).node.lockedDown = true) :
    (pRun c s0 sched u).node.lockedDown = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => exact h
  | succ d ih =>
    have ih := ih (Nat.le_add_right _ _)
    show (pStep c (pRun c s0 sched (t + d)) (sched (t + d))).st.sys.world.node.lockedDown = true
    rcases pStep_world c (pRun c s0 sched (t + d)) (sched (t + d)) with hw | ⟨env, e, hw⟩ | hw <;> rw [hw]
    · exact ih
    · exact step_keeps_latch _ _ _ _ ih
    · rfl

/-- The arm bit never clears, on any slot. -/
theorem armed_sticky_run (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant) {t u : Nat} (htu : t ≤ u)
    (h : (pRun c s0 sched t).node.armed = true) : (pRun c s0 sched u).node.armed = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => exact h
  | succ d ih =>
    have ih := ih (Nat.le_add_right _ _)
    show (pStep c (pRun c s0 sched (t + d)) (sched (t + d))).st.sys.world.node.armed = true
    rcases pStep_world c (pRun c s0 sched (t + d)) (sched (t + d)) with hw | ⟨env, e, hw⟩ | hw <;> rw [hw]
    · exact ih
    · exact armed_sticky _ _ _ _ ih
    · exact ih

/-- The world at every slot of every schedule is a reachable kernel world, or that world with the
driver's latch set. -/
def KernelWorld (r : Rules) (w : World) : Prop :=
  ∃ w', Reachable r w' ∧ (w = w' ∨ w = latW w')

theorem kernelWorld_run (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant)
    (h0 : Reachable c.r s0.st.sys.world) (t : Nat) :
    KernelWorld c.r (pRun c s0 sched t).st.sys.world := by
  induction t with
  | zero => exact ⟨_, h0, .inl rfl⟩
  | succ t ih =>
    obtain ⟨w', hr, hw⟩ := ih
    show KernelWorld c.r (pStep c (pRun c s0 sched t) (sched t)).st.sys.world
    rcases pStep_world c (pRun c s0 sched t) (sched t) with hn | ⟨env, e, hn⟩ | hn <;> rw [hn]
    · exact ⟨w', hr, hw⟩
    · rcases hw with hw | hw
      · rw [hw]; exact ⟨_, .next env e hr, .inl rfl⟩
      · rw [hw]
        by_cases hreq : (∃ cid d E sp es, e = .accept cid d E sp es) ∨
            ∃ cid d E p code, e = .refuse cid d E p code
        · rw [step_latW_request _ _ _ _ hreq]; exact ⟨w', hr, .inr rfl⟩
        · rw [step_latW_other _ _ _ _
            (fun cid d E sp es he => hreq (.inl ⟨cid, d, E, sp, es, he⟩))
            (fun cid d E p code he => hreq (.inr ⟨cid, d, E, p, code, he⟩))]
          exact ⟨_, .next env e hr, .inr rfl⟩
    · rcases hw with hw | hw <;> rw [hw]
      · exact ⟨w', hr, .inr rfl⟩
      · exact ⟨w', hr, .inr (latW_self rfl)⟩

/-- The part of `DUR-15`'s "a merely delayed node is still frozen and releases nothing" that the kernel
carries. Over every schedule from a reachable world, fair or not: at any slot, a fire pass on an armed
node queues no hot partial, whether the latch has landed or not. An Escape's partial is not covered:
it is the sweep's. `Kernel.no_hot_partial_while_armed` is reused unchanged, and no premise here says
anything about service. -/
@[req "DUR-15"]
theorem delayed_node_frozen (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant)
    (h0 : Reachable c.r s0.st.sys.world) (t : Nat) (env : Env)
    (ha : (pRun c s0 sched t).node.armed = true) :
    ∀ eff ∈ (step c.r env (pRun c s0 sched t).st.sys.world .firePass).2,
      ∀ m i cid, eff ≠ .queuePartial m i true cid := by
  obtain ⟨w', hr, hw⟩ := kernelWorld_run c s0 sched h0 t
  simp only [PSt.node] at ha
  rcases hw with hw | hw <;> rw [hw] at ha ⊢
  · exact no_hot_partial_while_armed c.r env w' hr ha
  · rw [step_latW_other _ _ _ .firePass (by intros; simp) (by intros; simp)]
    exact no_hot_partial_while_armed c.r env w' hr ha

/-! ## Local computation: the latch -/

/-- `DUR-7`'s comparison, once the time ratchet has read `T` on an armed node, no longer depends on
the wall: a backward step cannot un-reach it, and no later write of `T` escapes it. -/
@[req "DUR-7"]
def ReadPast (n : Node) : Prop := n.armed = true ∧ n.ratchet.deadlineReached n.T = true

instance (n : Node) : Decidable (ReadPast n) := by unfold ReadPast; infer_instance

theorem shrunk_bound (r : Rules) (env : Env) (n : Node) (sp es : Cand) :
    shrunkDeadline r env n sp es = n.T ∨
      (sp.hot = true ∧ (Wall.atOrBefore (shrunkDeadline r env n sp es) n.T = true ∨
        env.eff.deadlineReached (shrunkDeadline r env n sp es) = true)) := by
  unfold shrunkDeadline
  split
  · rename_i hc
    have hhot : sp.hot = true := by
      simp only [Bool.and_eq_true] at hc
      exact hc.2
    split
    · split
      · exact .inl rfl
      · exact .inr ⟨hhot, Wall.shrinkDeadline_le_max _ _ _ _⟩
    · split
      · split
        · exact .inl rfl
        · exact .inr ⟨hhot, Wall.shrinkDeadline_le_max _ _ _ _⟩
      · exact .inl rfl
  · exact .inl rfl

/-- The ratchet's reading survives every kernel event, at the clamp on the prior arm bit: a write of
`T` stays at or below the old `T` or at or below its own sample, and that sample then enters the
ratchet (`Kernel.holderDecision_bounds_T`, `Wall.shrinkDeadline_le_max`). -/
@[req "DUR-7"]
theorem step_keeps_read {r : Rules} (hc : r.clampOn = .priorArm) (env : Env) (w : World) (e : Event)
    (h : ReadPast w.node) : ReadPast (step r env w e).1.node := by
  obtain ⟨ha, ht⟩ := h
  have keepRefuse : ∀ cid d E p, ReadPast (refuse r env w.node cid d E p) := fun cid d E p => by
    refine ⟨by simpa using ha, ?_⟩
    rw [refuse_ratchet, refuse_T]
    exact ht
  cases e with
  | refuse cid d E p code => exact keepRefuse cid d E p
  | accept cid d E sp es =>
    show ReadPast (accept r env w.node cid d E sp es)
    unfold accept
    split
    · exact keepRefuse _ _ _ _
    · split
      · exact ⟨ha, ht⟩
      · refine ⟨ha, ?_⟩
        have hany : ∀ R : Effective, R = advanceRatchet env w.node ∨ (R = w.node.ratchet ∧ sp.hot = false) →
            R.deadlineReached (shrunkDeadline r env w.node sp es) = true := by
          intro R hR
          rcases shrunk_bound r env w.node sp es with hs | ⟨hhot, hb⟩
          · rw [hs]
            rcases hR with rfl | ⟨rfl, _⟩
            · exact Effective.deadlineReached_latest_left _ ht
            · exact ht
          · rcases hR with rfl | ⟨_, hcold⟩
            · exact Effective.deadlineReached_of_rewrite ht hb
            · rw [hhot] at hcold
              cases hcold
        refine hany _ ?_
        first
          | exact .inl rfl
          | (by_cases hhot : sp.hot = true
             · simp [hhot]
             · simp [hhot])
  | receipt cid s =>
    show ReadPast (receipt r env w.node cid s)
    unfold receipt
    split
    · exact ⟨ha, ht⟩
    · split
      · exact ⟨ha, ht⟩
      · split
        · rename_i k _ _ _
          refine ⟨by simp [holderDecision, ha], ?_⟩
          exact Effective.deadlineReached_of_rewrite ht ((holderDecision_bounds_T hc env w.node _).1 ha)
        · exact ⟨ha, ht⟩
  | firePass =>
    simp only [step, firePass]
    split <;> exact ⟨ha, ht⟩
  | packageAccepted c => exact ⟨ha, ht⟩
  | send c =>
    simp only [step, send]
    split <;> exact ⟨ha, ht⟩
  | settle tx =>
    simp only [step, settle]
    split <;> exact ⟨ha, ht⟩
  | prune => exact ⟨ha, ht⟩
  | tick => exact ⟨ha, ht⟩
  | panic => exact ⟨ha, ht⟩
  | adversaryExposes m i s c => exact ⟨ha, ht⟩
  | receivePartial m i s c => exact ⟨ha, ht⟩

/-- Once read, read at every later slot of every schedule. -/
theorem read_stable {c : Lifetime.Cfg} (hc : c.r.clampOn = .priorArm) (s0 : PSt) (sched : Nat → Grant)
    {t u : Nat} (htu : t ≤ u) (h : ReadPast (pRun c s0 sched t).node) :
    ReadPast (pRun c s0 sched u).node := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => exact h
  | succ d ih =>
    have ih := ih (Nat.le_add_right _ _)
    show ReadPast (pStep c (pRun c s0 sched (t + d)) (sched (t + d))).st.sys.world.node
    rcases pStep_world c (pRun c s0 sched (t + d)) (sched (t + d)) with hw | ⟨env, e, hw⟩ | hw <;> rw [hw]
    · exact ih
    · exact step_keeps_read hc _ _ _ ih
    · exact ih

/-- The comparison reads the arm bit, the ratchet and `T` of a node, and nothing else of it. -/
theorem driverDue_congr {r : Rules} {env : Env} {n m : Node} (ha : n.armed = m.armed)
    (hr : n.ratchet = m.ratchet) (hT : n.T = m.T) : driverDue r env n = driverDue r env m := by
  simp only [driverDue, Silence.preHorizon, ha, hr, hT]

theorem driverDue_of_read {r : Rules} (hdr : r.driverTime = .ratchet) (env : Env) {n : Node}
    (h : ReadPast n) : driverDue r env n = true := by
  simp only [driverDue, Silence.preHorizon, hdr, h.1, Bool.not_true, Bool.false_or, Bool.not_not]
  exact Effective.deadlineReached_latest_left _ h.2

/-- **Goal: local computation.** The Lockdown latch is set. -/
def Local (s : PSt) : Prop := s.node.lockedDown = true

/-- The driver's service. -/
def isDriver : Grant → Bool
  | .driver .. => true
  | _ => false

/-- The comparison at the driver's own sample, the premise a driver grant needs. -/
def driverSees (r : Rules) (s : PSt) : Grant → Bool
  | .driver raw mono => driverDue r (driverEnv s.log raw mono) s.node
  | _ => true

theorem latch_on_grant {c : Lifetime.Cfg} {s : PSt} {g : Grant} (hd : isDriver g = true)
    (hs : driverSees c.r s g = true) : (pStep c s g).node.lockedDown = true := by
  cases g with
  | driver raw mono => exact driver_decides c.r _ _ hs
  | _ => simp [isDriver] at hd

/-- **Bounded service, local computation.** Driver service within `B` slots of every instant, and the
comparison true at the driver's own sample across the window from `t0`: the latch is set by slot
`t0 + B + 1`. Both premises are needed (`Exhibits.Progress.f13_starved_run`,
`Exhibits.Progress.alternating_samples_never_latch`). -/
@[req "DUR-7"]
theorem latch_within {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 B : Nat}
    (hs : (Profile.bounded B).Holds fun u => isDriver (sched u))
    (hd : ∀ u, t0 ≤ u → u ≤ t0 + B → driverSees c.r (pRun c s0 sched u) (sched u) = true) :
    Local (pRun c s0 sched (t0 + B + 1)) := by
  obtain ⟨u, hu, hle, hsu⟩ := hs t0
  exact latch_sticky c s0 sched (t := u + 1) (by omega) (latch_on_grant hsu (hd u hu hle))

/-- **Eventual service, local computation.** Eventual driver service and stable enabling: the latch
is set at some later slot. Nothing says how much later (`f13_postponed`). -/
@[req "DUR-7"]
theorem latch_eventually {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 : Nat}
    (hs : Profile.eventual.Holds fun u => isDriver (sched u))
    (hd : ∀ u, t0 ≤ u → driverSees c.r (pRun c s0 sched u) (sched u) = true) :
    ∃ t, t0 < t ∧ Local (pRun c s0 sched t) := by
  obtain ⟨u, hu, hsu⟩ := hs t0
  exact ⟨u + 1, by omega, latch_on_grant hsu (hd u hu)⟩

/-- A driver grant's comparison holds whatever its sample, once the ratchet has read `T`. -/
theorem driverSees_of_read {r : Rules} (hdr : r.driverTime = .ratchet) {s : PSt} (g : Grant)
    (h : ReadPast s.node) : driverSees r s g = true := by
  cases g with
  | driver raw mono => exact driverDue_of_read hdr _ h
  | _ => rfl

/-- **Bounded service with the enabling discharged.** Once the time ratchet has read `T` on an armed
node, driver service within `B` slots latches by `t0 + B + 1`, whatever the wall does and whatever
else the schedule grants. The premises left are the clamp and the driver's sample as they stand, the
reading, and the service. -/
@[req "DUR-7"]
theorem latch_within_of_read {c : Lifetime.Cfg} (hc : c.r.clampOn = .priorArm)
    (hdr : c.r.driverTime = .ratchet) {s0 : PSt} {sched : Nat → Grant} {t0 B : Nat}
    (hs : (Profile.bounded B).Holds fun u => isDriver (sched u))
    (hr : ReadPast (pRun c s0 sched t0).node) :
    Local (pRun c s0 sched (t0 + B + 1)) :=
  latch_within hs fun u hu _ => driverSees_of_read hdr _ (read_stable hc s0 sched hu hr)

/-- Two schedules that agree below `t` play to one state at `t`. -/
theorem pRun_congr (c : Lifetime.Cfg) (s0 : PSt) {a b : Nat → Grant} (t : Nat)
    (h : ∀ u, u < t → a u = b u) : pRun c s0 a t = pRun c s0 b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show pStep c (pRun c s0 a t) (a t) = pStep c (pRun c s0 b t) (b t)
    rw [ih fun u hu => h u (by omega), h t (by omega)]

/-- A run from slot `k` on is a run from where the first `k` slots left it. -/
theorem pRun_shift (c : Lifetime.Cfg) (s0 : PSt) (sched : Nat → Grant) (k n : Nat) :
    pRun c s0 sched (k + n) = pRun c (pRun c s0 sched k) (fun u => sched (k + u)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show pStep c (pRun c s0 sched (k + n)) (sched (k + n)) = pStep c _ (sched (k + n))
    rw [ih]

/-! ### `F13` -/

/-- A post-wrench coordinator's stream: `DUR-15`'s "validly signed requests indefinitely", each
refused, each holding the lock for its slot. Every sample is free. -/
def mint (envs : Nat → Env) (cids : Nat → Nat) (E : Wall) : Nat → Grant := fun u =>
  .op (.kernel (envs u) (.refuse (cids u) false E none .BAD_PIN))

/-- **`F13`, under the adversarial profile.** `DUR-15`: "The DELAY before Lockdown lands has no finite
bound". Nothing the stream does touches the arm bit, `T`, the ratchet or the latch, and the driver
is never granted: at every slot of an unending run the node is armed and unlatched. Whether the
comparison is true at those samples is the caller's: `Exhibits.Progress.f13_starved_run` has it true
at every slot. `delayed_node_frozen` is the bounded consequence. -/
@[req "DUR-15"]
theorem f13_starved (c : Lifetime.Cfg) (s0 : PSt) (envs : Nat → Env) (cids : Nat → Nat) (E : Wall)
    (ha : s0.node.armed = true) (hl : s0.node.lockedDown = false) (u : Nat) :
    (∀ v, isDriver (mint envs cids E v) = false) ∧
      (pRun c s0 (mint envs cids E) u).node.armed = true ∧
      (pRun c s0 (mint envs cids E) u).node.lockedDown = false ∧
      (pRun c s0 (mint envs cids E) u).node.T = s0.node.T ∧
      (pRun c s0 (mint envs cids E) u).node.ratchet = s0.node.ratchet := by
  refine ⟨fun _ => rfl, ?_⟩
  induction u with
  | zero => exact ⟨ha, hl, rfl, rfl⟩
  | succ u ih =>
    obtain ⟨ha', hl', ht', hr'⟩ := ih
    have hw : (pRun c s0 (mint envs cids E) (u + 1)).node =
        refuse c.r (envs u) (pRun c s0 (mint envs cids E) u).node (cids u) false E none := by
      show ((Ledger.sysStep c.lg c.cfg c.r (envs u) (pRun c s0 (mint envs cids E) u).st.sys
        (.refuse (cids u) false E none .BAD_PIN)).1.world).node = _
      rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1]
      rfl
    rw [hw]
    refine ⟨by simpa using ha', ?_, ?_, ?_⟩
    · rw [refuse_lockedDown]; exact hl'
    · rw [refuse_T]; exact ht'
    · rw [refuse_ratchet]; exact hr'

/-- **`F13`, under the eventual and bounded profiles, for any postponement.** A driver served from
slot `L` on meets `bounded L`, so meets `eventual`, and still has not latched at `L`. `latch_within`'s
bound is therefore attained, and eventual service alone bounds nothing. -/
@[req "DUR-15"]
theorem f13_postponed (c : Lifetime.Cfg) (s0 : PSt) (envs : Nat → Env) (cids : Nat → Nat) (E : Wall)
    (ha : s0.node.armed = true) (hl : s0.node.lockedDown = false) (L raw mono : Nat) :
    let sched : Nat → Grant := fun u => if u < L then mint envs cids E u else .driver raw mono
    (Profile.bounded L).Holds (fun u => isDriver (sched u)) ∧
      Profile.eventual.Holds (fun u => isDriver (sched u)) ∧
      (pRun c s0 sched L).node.lockedDown = false := by
  intro sched
  have hb : (Profile.bounded L).Holds (fun u => isDriver (sched u)) := fun t =>
    ⟨t + L, by omega, by omega, by
      have h : ¬ t + L < L := by omega
      simp [sched, h, isDriver]⟩
  refine ⟨hb, bounded_eventual hb, ?_⟩
  rw [pRun_congr c s0 (b := mint envs cids E) L fun u hu => by simp [sched, hu]]
  exact (f13_starved c s0 envs cids E ha hl L).2.2.1

/-! ## Message receipt -/

/-- **Goal: message receipt.** The guard holds a nonce from this sender, which it writes only on
acceptance. -/
def Received (s : PSt) (sender : Nat) : Prop := ∃ nonce ts, (sender, nonce, ts) ∈ s.guard.seen

/-- The envelope service of one sender. -/
def carries (sender : Nat) : Grant → Bool
  | .envelope _ _ _ _ x _ _ => x == sender
  | _ => false

/-- The premise `F3` removes: the high-water within `NCH-12`'s past bound of the stamp, the stamp
within its future bound, and an unseen nonce. -/
def envelopeFits (s : PSt) : Grant → Bool
  | .envelope raw _ _ _ sender nonce ts =>
    decide (max s.guard.hw raw ≤ ts + Freshness.past) &&
      decide (ts ≤ max s.guard.hw raw + Freshness.future) &&
      !s.guard.seen.any (fun e => e.1 == sender && e.2.1 == nonce)
  | _ => true

theorem envelopeFits_parts {s : PSt} {raw mono cid sender nonce ts : Nat} {chain : ChainView}
    (h : envelopeFits s (.envelope raw mono chain cid sender nonce ts) = true) :
    max s.guard.hw raw ≤ ts + Freshness.past ∧ ts ≤ max s.guard.hw raw + Freshness.future ∧
      s.guard.seen.any (fun e => e.1 == sender && e.2.1 == nonce) = false := by
  simp only [envelopeFits, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Bounded service, message receipt.** Envelope delivery within `B` slots, and `envelopeFits`
across the window: the guard takes one. Delivery alone is not enough: `f3_blackhole` delivers at every
slot. -/
@[req "NCH-13"]
theorem received_within {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 B sender : Nat}
    (hs : (Profile.bounded B).Holds fun u => carries sender (sched u))
    (hf : ∀ u, t0 ≤ u → u ≤ t0 + B → envelopeFits (pRun c s0 sched u) (sched u) = true) :
    ∃ u, t0 ≤ u ∧ u ≤ t0 + B ∧ Received (pRun c s0 sched (u + 1)) sender := by
  obtain ⟨u, hu, hle, hsu⟩ := hs t0
  refine ⟨u, hu, hle, ?_⟩
  have hfit := hf u hu hle
  show Received (pStep c (pRun c s0 sched u) (sched u)) sender
  replace hsu : carries sender (sched u) = true := hsu
  generalize sched u = g at hsu hfit ⊢
  cases g with
  | envelope raw mono chain cid x nonce ts =>
    have hx : x = sender := by simpa [carries] using hsu
    subst hx
    obtain ⟨hp, hft, hn⟩ := envelopeFits_parts hfit
    obtain ⟨hacc, hmem⟩ := ingress_accepts _ raw x nonce ts hp hft hn
    refine ⟨nonce, ts, ?_⟩
    simp only [pStep, hacc]
    exact hmem
  | _ => simp [carries] at hsu

/-! ### `F3` -/

/-- An honest sender over a receiver whose clock read `J` once and was then corrected: slot `0`
carries the excursion, and from then on the slot stands for the real second, the raw sample and the
stamp both read it, and each envelope has its own nonce. -/
def honestStream (J : Nat) (mono : Nat → Nat) (chain : ChainView) (cid sender : Nat) : Nat → Grant
  | 0 => .envelope J (mono 0) chain cid sender 0 0
  | u + 1 => .envelope (u + 1) (mono (u + 1)) chain cid sender (u + 1) (u + 1)

/-- **`F3`, under bounded delivery.** `NCH-38`: "a larger excursion can make the authenticated channel
unavailable for unbounded real time". For every length `L`, an excursion past `L + 300` leaves every
honest envelope of the first `L` seconds stale, delivered at every slot (`bounded 0`, the strongest
delivery profile there is), and in the whole of it the kernel, the ledger and the seen nonces do not
move. No scheduling premise repairs this: the premise that does is `envelopeFits`. -/
@[req "NCH-38"]
theorem f3_blackhole (c : Lifetime.Cfg) (s0 : PSt) (mono : Nat → Nat) (chain : ChainView)
    (cid sender L J : Nat) (hJ : L + Freshness.past < J) :
    (Profile.bounded 0).Holds (fun u => carries sender (honestStream J mono chain cid sender u)) ∧
      ∀ u, u ≤ L + 1 →
        (pRun c s0 (honestStream J mono chain cid sender) u).st = s0.st ∧
        (pRun c s0 (honestStream J mono chain cid sender) u).guard.seen = s0.guard.seen ∧
        (1 ≤ u → J ≤ (pRun c s0 (honestStream J mono chain cid sender) u).guard.hw) := by
  refine ⟨fun t => ⟨t, by omega, by omega, ?_⟩, fun u => ?_⟩
  · cases t <;> simp [honestStream, carries]
  · induction u with
    | zero => exact fun _ => ⟨rfl, rfl, fun h => absurd h (by omega)⟩
    | succ u ih =>
      intro hu
      obtain ⟨hst, hseen, hhw⟩ := ih (by omega)
      have hstep : ∀ raw m ts nonce, ts ≤ L → (J ≤ raw ∨ 1 ≤ u) →
          let s := pRun c s0 (honestStream J mono chain cid sender) u
          pStep c s (.envelope raw m chain cid sender nonce ts) =
            { s with guard := { s.guard with hw := max s.guard.hw raw } } := by
        intro raw m ts nonce hts hr
        have hlt : ts + Freshness.past < max (pRun c s0 (honestStream J mono chain cid sender) u).guard.hw raw := by
          rcases hr with hr | hr
          · omega
          · have := hhw hr
            omega
        simp only [pStep, stale_below_latch _ raw sender nonce ts hlt]
        rfl
      have hnext : pRun c s0 (honestStream J mono chain cid sender) (u + 1) =
          pStep c (pRun c s0 (honestStream J mono chain cid sender) u)
            (honestStream J mono chain cid sender u) := rfl
      cases u with
      | zero =>
        rw [hnext]
        simp only [honestStream]
        rw [hstep J (mono 0) 0 0 (by omega) (.inl (Nat.le_refl _))]
        exact ⟨hst, hseen, fun _ => Nat.le_max_right _ _⟩
      | succ v =>
        rw [hnext]
        simp only [honestStream]
        rw [hstep (v + 1) (mono (v + 1)) (v + 1) (v + 1) (by omega) (.inr (by omega))]
        exact ⟨hst, hseen, fun _ => Nat.le_trans (hhw (by omega)) (Nat.le_max_left _ _)⟩

/-! ## Arming -/

/-- **Goal: arming.** The node's arm bit, which a holder decision on a duress pair writes. -/
def Armed (s : PSt) : Prop := s.node.armed = true

theorem any_some {α : Type} {p : α → Bool} {x : Option α} (h : x.any p = true) :
    ∃ a, x = some a ∧ p a = true := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

/-- The relay service of one Carrier. -/
def relaysFor (cid : Nat) : Grant → Bool
  | .envelope _ _ _ x _ _ _ => x == cid
  | _ => false

/-- What a relay of `cid` needs to arm: it passes the guard, the Carrier is resident with `D` and `E`
unexpired at this envelope's sample and the sender completes `t`, and the pair's duress bit is set. -/
def deciding (r : Rules) (s : PSt) : Grant → Bool
  | .envelope raw mono chain cid sender nonce ts =>
    envelopeFits s (.envelope raw mono chain cid sender nonce ts) &&
      commits (envOf s.log raw mono chain) s.node cid sender &&
      (s.node.carriers.find? (·.cid == cid)).any fun k =>
        pairDuress r s.node { k with relaySenders := addSender s.node.id k.relaySenders sender }
  | _ => true

/-- **Bounded service, arming.** Relay delivery within `B` slots, and across the window a relay that
`deciding` admits: the node is armed at `t0 + B + 1`. Delivery alone is not enough: `f4_no_arming`
delivers at every slot. -/
@[req "DUR-5"]
theorem armed_within {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 B cid : Nat}
    (hs : (Profile.bounded B).Holds fun u => relaysFor cid (sched u))
    (hd : ∀ u, t0 ≤ u → u ≤ t0 + B → deciding c.r (pRun c s0 sched u) (sched u) = true) :
    Armed (pRun c s0 sched (t0 + B + 1)) := by
  obtain ⟨u, hu, hle, hsu⟩ := hs t0
  have hdec := hd u hu hle
  refine armed_sticky_run c s0 sched (t := u + 1) (by omega) ?_
  show (pStep c (pRun c s0 sched u) (sched u)).st.sys.world.node.armed = true
  replace hsu : relaysFor cid (sched u) = true := hsu
  generalize sched u = g at hsu hdec ⊢
  cases g with
  | envelope raw mono chain x sender nonce ts =>
    have hx : x = cid := by simpa [relaysFor] using hsu
    subst hx
    simp only [deciding, Bool.and_eq_true] at hdec
    obtain ⟨⟨hfit, hc⟩, hany⟩ := hdec
    obtain ⟨hp, hft, hn⟩ := envelopeFits_parts hfit
    obtain ⟨k, hk, hdur⟩ := any_some hany
    obtain ⟨hacc, _⟩ := ingress_accepts _ raw sender nonce ts hp hft hn
    simp only [pStep, hacc, beq_self_eq_true, if_true, Lifetime.step]
    rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1]
    show (receipt c.r (envOf (pRun c s0 sched u).log raw mono chain)
      (pRun c s0 sched u).node x sender).armed = true
    have hbounds : (!((envOf (pRun c s0 sched u).log raw mono chain).mono.before k.D) ||
        !((envOf (pRun c s0 sched u).log raw mono chain).eff.before k.E)) = false := by
      simp only [commits, hk, Bool.and_eq_true] at hc
      simp [hc.1.1, hc.1.2]
    simp only [receipt, hk, hbounds, Bool.false_eq_true, if_false, hc, if_true]
    simp [holderDecision, hdur]
  | _ => simp [relaysFor] at hsu

/-! ### `F4` -/

/-- `SPN-12`'s composed consequence: an accept that prunes a wall-only entry whose expiry is at or
above a live Carrier's `E` leaves the high-water at or above `E`. -/
@[req "SPN-12"]
theorem f4_latch_past_carrier (l : NonceLog) (raw mono nonce expiry E : Nat) (channel : Bool)
    (e : LogEntry) (he : e ∈ l.entries) (hdead : e.live (l.eff raw) mono = false) (hE : E ≤ e.expiry)
    (hok : l.windowOk raw expiry = true)
    (hfresh : l.entries.any (fun x => x.live (l.eff raw) mono && x.nonce == nonce) = false) :
    E ≤ (l.accept raw mono nonce expiry channel).hw :=
  Nat.le_trans hE (accept_latches l raw mono nonce expiry channel e he hdead hok hfresh)

/-- Relays of one Carrier at every slot, each with its own nonce and an honest stamp. Every sample
is free. -/
def relayStream (raw mono : Nat → Nat) (chain : ChainView) (cid sender : Nat) : Nat → Grant := fun u =>
  .envelope (raw u) (mono u) chain cid sender u (raw u)

/-- **`F4`, under bounded delivery.** `SPN-12`: the high-water at or past a live Carrier's `E` makes
that Carrier's relays count for nothing: delivered at every slot (`bounded 0`), passing the guard or
not, at every raw and HotClock sample, and the kernel's world does not move, so the node never arms
from it. `NCH-36` says "retries are bounded by `E` and `D`, never unbounded": this is the Carrier's
whole life, and `D` ends the attempt rather than the refusal. No scheduling premise repairs it: the
premise that does is `NCH-37`'s high-water below `E`. -/
@[req "NCH-36"]
theorem f4_no_arming (c : Lifetime.Cfg) (s0 : PSt) (raw mono : Nat → Nat) (chain : ChainView)
    (cid sender E : Nat) (k : Carrier) (hk : s0.node.carriers.find? (·.cid == cid) = some k)
    (hE : k.E = Wall.sample E) (hlatch : E ≤ s0.log.hw) :
    (Profile.bounded 0).Holds (fun u => relaysFor cid (relayStream raw mono chain cid sender u)) ∧
      ∀ u, (pRun c s0 (relayStream raw mono chain cid sender) u).st.sys.world = s0.st.sys.world ∧
        (pRun c s0 (relayStream raw mono chain cid sender) u).log = s0.log := by
  refine ⟨fun t => ⟨t, by omega, by omega, by simp [relayStream, relaysFor]⟩, fun u => ?_⟩
  induction u with
  | zero => exact ⟨rfl, rfl⟩
  | succ u ih =>
    obtain ⟨hw, hl⟩ := ih
    show (pStep c (pRun c s0 (relayStream raw mono chain cid sender) u) _).st.sys.world = _ ∧
      (pStep c (pRun c s0 (relayStream raw mono chain cid sender) u) _).log = _
    simp only [relayStream, pStep]
    split
    · refine ⟨?_, hl⟩
      simp only [Lifetime.step]
      rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1, hw]
      have hb : (envOf (pRun c s0 (relayStream raw mono chain cid sender) u).log (raw u) (mono u)
          chain).eff.before k.E = false := by
        rw [hl, hE]
        exact Effective.ofWall_before_of_le (Nat.le_trans hlatch (Nat.le_max_left _ _))
      have hr := (receipt_at_bound c.r _ s0.st.sys.world.node cid sender k hk (.inr hb)).1
      show ({ s0.st.sys.world with node := receipt c.r _ s0.st.sys.world.node cid sender } : World) = _
      rw [hr]
    · exact ⟨hw, hl⟩

/-! ## Escape submission -/

/-- **Goal: Escape submission.** A candidate with this id has been broadcast. -/
def Submitted (s : PSt) (cid : Nat) : Prop :=
  ∃ d ∈ s.node.cands, d.id = cid ∧ d.broadcast = true

/-- The send service of one candidate. -/
def sendsFor (cid : Nat) : Grant → Bool
  | .op (.kernel _ (.send x)) => x == cid
  | _ => false

/-- What a send needs: the candidate is resident with `packageOk`, and `DUR-29`'s re-authorization
passes at this slot's sample, which is the usable window. -/
def sendable (r : Rules) (s : PSt) : Grant → Bool
  | .op (.kernel env (.send cid)) =>
    (s.node.cands.find? (·.id == cid)).any fun d =>
      d.packageOk && (r.reauth == .beforeAssembly || (due r env s.node d && releaseAuthorized r s.node d))
  | _ => true

/-- **Bounded service, Escape submission.** A send pass within `B` slots with `sendable` across the
window submits. A send served after the window closes does not
(`Exhibits.Progress.send_after_window_closes`). -/
@[req "DUR-29"]
theorem submitted_within {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 B cid : Nat}
    (hs : (Profile.bounded B).Holds fun u => sendsFor cid (sched u))
    (hd : ∀ u, t0 ≤ u → u ≤ t0 + B → sendable c.r (pRun c s0 sched u) (sched u) = true) :
    ∃ u, t0 ≤ u ∧ u ≤ t0 + B ∧ Submitted (pRun c s0 sched (u + 1)) cid := by
  obtain ⟨u, hu, hle, hsu⟩ := hs t0
  have hdec := hd u hu hle
  refine ⟨u, hu, hle, ?_⟩
  show Submitted (pStep c (pRun c s0 sched u) (sched u)) cid
  replace hsu : sendsFor cid (sched u) = true := hsu
  generalize sched u = g at hsu hdec ⊢
  cases g with
  | op o =>
    cases o with
    | kernel env e =>
      cases e with
      | send x =>
        have hx : x = cid := by simpa [sendsFor] using hsu
        subst hx
        obtain ⟨d, hf, hpg⟩ := any_some hdec
        simp only [Bool.and_eq_true] at hpg
        obtain ⟨hp, hgo⟩ := hpg
        have hmem := List.mem_of_find?_eq_some hf
        have hid : d.id = x := by simpa using List.find?_some hf
        have hworld : (pStep c (pRun c s0 sched u) (.op (.kernel env (.send x)))).node =
            (send c.r env (pRun c s0 sched u).node x).1 := by
          show ((Ledger.sysStep c.lg c.cfg c.r env (pRun c s0 sched u).st.sys (.send x)).1.world).node = _
          rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1]
          rfl
        simp only [Submitted]
        rw [hworld]
        simp only [send]
        rw [show (pRun c s0 sched u).node.cands.find? (·.id == x) = some d from hf]
        refine ⟨_, List.mem_map.2 ⟨d, hmem, rfl⟩, ?_, ?_⟩
        · simp [hid]
        · simp only [hid, beq_self_eq_true, if_true, hp, Bool.true_and, hgo, Bool.or_true]
      | _ => simp [sendsFor] at hsu
    | _ => simp [sendsFor] at hsu
  | _ => simp [sendsFor] at hsu

/-! ## Chain inclusion, as a node can act on it -/

/-- **Goal: chain inclusion, observed.** A resident candidate of this transaction is settled. The
block itself is `Sweep.Backend`'s. -/
def Settled (s : PSt) (tx : Tx) : Prop :=
  ∃ d ∈ s.node.cands, d.tx.id = tx.id ∧ d.settled = true

/-- The settle pass of one transaction. -/
def settlesFor (tx : Tx) : Grant → Bool
  | .op (.kernel _ (.settle x)) => x == tx
  | _ => false

/-- What a settle pass needs: the chain view it is handed shows the transaction, and a candidate of
that transaction is resident. Nothing the node does puts the transaction in the view. -/
def settleable (s : PSt) : Grant → Bool
  | .op (.kernel env (.settle tx)) =>
    env.chain.seen.contains tx && s.node.cands.any (·.tx.id == tx.id)
  | _ => true

/-- **Bounded service, chain inclusion.** A settle pass within `B` slots whose view shows the
transaction, with a candidate resident, settles it. The view's content is the premise: under the
same schedule with a view that never shows it the node sees nothing
(`Exhibits.Progress.submitted_is_not_included`). -/
@[req "SPN-33"]
theorem settled_within {c : Lifetime.Cfg} {s0 : PSt} {sched : Nat → Grant} {t0 B : Nat} {tx : Tx}
    (hs : (Profile.bounded B).Holds fun u => settlesFor tx (sched u))
    (hd : ∀ u, t0 ≤ u → u ≤ t0 + B → settleable (pRun c s0 sched u) (sched u) = true) :
    ∃ u, t0 ≤ u ∧ u ≤ t0 + B ∧ Settled (pRun c s0 sched (u + 1)) tx := by
  obtain ⟨u, hu, hle, hsu⟩ := hs t0
  have hdec := hd u hu hle
  refine ⟨u, hu, hle, ?_⟩
  show Settled (pStep c (pRun c s0 sched u) (sched u)) tx
  replace hsu : settlesFor tx (sched u) = true := hsu
  generalize sched u = g at hsu hdec ⊢
  cases g with
  | op o =>
    cases o with
    | kernel env e =>
      cases e with
      | settle x =>
        have hx : x = tx := by simpa [settlesFor] using hsu
        subst hx
        simp only [settleable, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hdec
        obtain ⟨hseen, d, hmem, hid⟩ := hdec
        have hworld : (pStep c (pRun c s0 sched u) (.op (.kernel env (.settle x)))).node =
            settle env (pRun c s0 sched u).node x := by
          show ((Ledger.sysStep c.lg c.cfg c.r env (pRun c s0 sched u).st.sys (.settle x)).1.world).node = _
          rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1]
          rfl
        simp only [Settled]
        rw [hworld]
        simp only [settle, hseen, Bool.not_true, Bool.false_eq_true, if_false]
        refine ⟨{ d with settled := true }, List.mem_map.2 ⟨d, hmem, by simp [hid]⟩, hid, rfl⟩
      | _ => simp [settlesFor] at hsu
    | _ => simp [settlesFor] at hsu
  | _ => simp [settlesFor] at hsu

end BtcPolicy.Progress
