import BtcPolicy.Settlement
import BtcPolicy.Progress
import BtcPolicy.RefreshAge
import BtcPolicy.Timelock
import BtcPolicy.Alerts
import BtcPolicy.PreRelease
/-! Recovery authority and the failure-state classification: the abstract custody and coin-lifetime
composition the vault's second branch needs, over the one backend world of `BtcPolicy.Sweep` and the
one run of `BtcPolicy.Settlement`. Newly formalized behaviour; no protocol change, no restartable
node and no anti-rollback hardware.

**Three things kept apart.** `Recovery.eligible` is what the script and consensus read: the Recovery
branch's selector (`Alerts.isRecovery`), `CHN-10`'s sealed `nSequence` on every input, and each input
confirmed, unspent and past its lock on this instant's chain. `Recovery.capable` is what a party
holds: 2 distinct recovery keys, the descriptor and its network (`OPS-23`); it is an input, moved only
by the environment's `Step.lose`, `Step.loseBackup`, `Step.copy` and `Step.learnBackup`, and no theorem
here decides how diligent an Operator is or how long hardware lasts. Inclusion is
`Settlement.confirmedAt`, an environment move, and no step of any party causes it.
`Recovery.publish_iff` joins the first two; `Recovery.included_origin` says what an inclusion
implies; only `Recovery.included_within` and `Recovery.included_eventually` conclude one, and each takes
its service premise.

**A coin's own history.** The lock is `Timelock`'s encoding read back (`Recovery.lockSecs`,
`Recovery.lockSecs_encoded`). `Recovery.clock` reads an instant as `RefreshAge.ChainView`, and
`Sweep.Backend.heights` keys it by creating transaction, so a coin's birth is its creating transaction's
block on that instant's chain and nothing else. `Recovery.lockAge` is BIP68's measure, for a spend in
the block after the tip: `MTP(tip) − MTP(confirming block's parent)`; `SPN-46`'s
`RefreshAge.age` reads the confirming block itself and is a different rule. No node state enters it:
every step but a chain move keeps every coin's age and verdict, a Lockdown latch included
(`Recovery.age_moves_only_by_chain`). A confirmed refresh is a new creating transaction, so its outputs
start their own count while its inputs are spent (`Recovery.refresh_spends_parents`,
`Recovery.successor_own_history`). A chain move is free but for one consensus guard
(`Recovery.lockRespected`), so a reorganization can make a mature coin young again, or unspend one
(`BtcPolicy.Exhibits.Recovery`).

**Death and history.** `Step.die` is terminal for that node instance: it takes no later step and no later
copy of its key (`Recovery.dead_takes_no_step`), and its earlier partials and any key extracted earlier stay in
the record (`Recovery.history_persists`). Nothing restarts a node. What a node submitted stays too
(`Recovery.sent_step`). Recovery keys a party copied stay copied and keys
the Operator lost stay lost (`Recovery.custody_step`), which is `SEC-54`'s reading of a loss as
permanent. `Recovery.to_settlement` forgets all of this and leaves a `Settlement.Execution`, so every
earlier result holds of these runs.

**The latch.** `Step.latch` is `DUR-7`'s attempt (`Progress.driverDue`), held beside the node in
`St.latched` so that each node still moves by `Kernel.step` alone: a latched node takes no `accept`, no
staged refusal and no claw-back, as `Kernel.accept`, `Kernel.refuse` and `Kernel.clawback` take none at
`lockedDown`, and in-flight candidates stay in flight (`Kernel.lockdown_preserves_in_flight`).

**The five classes.** `Recovery.failures` reads one coin in one composed state and lists, each from its
own part of the state, `Failure.normalBlocked`, `Failure.fastUnavailable`, `Failure.notMature`,
`Failure.missingCustody` and `Failure.awaitingInclusion`; `Recovery.mem_failures` is the exact reading of
each. A coin can stand in several at once. A coin a confirmed transaction has spent stands in none.
`BtcPolicy.Exhibits.Recovery` runs a reachable scenario standing in each class alone, so no two classes
are one.

**How far each class goes.** `Failure.normalBlocked` reads the present: fewer than `t` signers on some
input among those with a record in the inventory, those whose key is copied, and those still open
(`Recovery.openSigner`); or no user signature. `Recovery.normal_of_inventory` gives the direction that
follows from the inventory. That it stays blocked is not claimed. `Failure.fastUnavailable` reads the
Escapes registered and submitted on this run; whether any bounded request exists is `Feasibility`'s question
(`Feasibility.feasible_iff_best`), and `DUR-21` and the ladder stay outside as they do in `Sweep`. Each reads
one target and this run: another Normal-path transaction over the coin is another scenario. A claw-back is
such a transaction: `Recovery.openSigner` reads one as a non-hot target, and a run that takes
`Kernel.Event.clawback` signs one (`BtcPolicy.Exhibits.Clawback`).

**Not modelled.** A sealed lock of zero, whose Recovery spend BIP68 would let confirm in one block with its
unconfirmed parent: `CHN-4` says "There is no hard floor", and `Recovery.matured` reads confirmed coins alone. A
positive lock has no such case: the coin's own block never passes it. Keys, signatures and the witness's bytes beyond the selector: possession is a list. A
party's own read of the chain: `Step.publish` reads the truth. `CHN-4`'s block-time units beyond the lock's
seconds, and any fee or relay rule on a Recovery spend. An instant's fields stay independent, as in
`BtcPolicy.Settlement`, so an instant need not be a consistent chain and MTP need not grow;
`Recovery.lockRespected` constrains only spends a party has published, and any other transaction spending a
vault coin is external. `Recovery.moved` reads `mined`. -/

namespace BtcPolicy.Recovery
open BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Coverage (Outpoint)

/-! ## The lock -/

/-- `CHN-4`'s relative lock in seconds, read back from the sealed raw `nSequence` (`MAN-5`'s
`recovery_timelock`): its 16-bit units at 512 seconds each. -/
@[req "CHN-4"]
def lockSecs (nseq : Nat) : Nat := (nseq &&& 0xFFFF) * Timelock.secondsPerUnit

/-- Over the whole field, what `Timelock.bip68Time` encoded reads back. -/
@[req "CHN-4"]
theorem lockSecs_encoded (u : Nat) (h : u < 1 <<< Timelock.unitFieldWidth) :
    lockSecs (Timelock.bip68Time u) = u * Timelock.secondsPerUnit := by
  simp only [lockSecs, (Timelock.encode_roundtrip u h).1]

/-- On a default vault the lock is `CHN-4`'s day count, exactly. -/
@[req "CHN-4"]
theorem default_lock : lockSecs Timelock.defaultNSequence =
    Timelock.defaultDays * Timelock.secondsPerDay := by
  decide

/-! ## A coin's chain history -/

/-- An instant's chain as `RefreshAge` reads one: its tip's height, the block of each confirmed
transaction, each block's median-time-past. -/
@[req "CHN-4"]
def clock (b : Backend) : RefreshAge.ChainView :=
  { tip := b.tip.height, confirmed := b.heights, mtp := fun h => (b.mtps.lookup h).getD 0 }

/-- BIP68's elapsed time for a spend in the block after the tip, of a coin whose creating transaction
is `creator`: `MTP(tip)` less the MTP of the confirming block's parent. `none`: not confirmed on this
instant's chain. `SEC-54`: "until that coin's own timelock matures, counted from its confirmation". -/
@[req "CHN-4"]
def lockAge (cv : RefreshAge.ChainView) (creator : Nat) : Option Nat :=
  (cv.confirmed.lookup creator).map fun h => cv.mtp cv.tip - cv.mtp (h - 1)

/-- What the model fixes of a vault: the sweep's parameters, the federation's threshold, the three
recovery keys and the sealed lock. -/
structure Cfg where
  sweep : Sweep.Cfg
  t : Nat
  recKeys : List Nat
  sealedLock : Nat

/-- The coin is a confirmed output of the vault at this instant. -/
def unspentAt (b : Backend) (o : Outpoint) : Bool := b.confirmed.any (·.1 == o)

/-- The coin stands, unspent, past its own lock at this instant. -/
@[req "CHN-4"]
def matured (cfg : Cfg) (b : Backend) (o : Outpoint) : Bool :=
  unspentAt b o && match lockAge (clock b) (cfg.sweep.creator o) with
    | some a => decide (lockSecs cfg.sealedLock ≤ a)
    | none => false

/-- The age is what decides, with equality passing: BIP68's `MTP(tip) ≥ coin time + lock`. -/
@[req "CHN-4"]
theorem matured_iff (cfg : Cfg) (b : Backend) (o : Outpoint) :
    matured cfg b o = true ↔ unspentAt b o = true ∧
      ∃ a, lockAge (clock b) (cfg.sweep.creator o) = some a ∧ lockSecs cfg.sealedLock ≤ a := by
  unfold matured
  cases lockAge (clock b) (cfg.sweep.creator o) <;> simp

/-! ## The spend -/

/-- A Recovery-path transaction: the kernel's identity and ordered inputs, each input's `nSequence`,
and the witness. `CHN-10`: it "carries no user signature and no federation signature", and nothing
here has a field for one. -/
structure Spend where
  tx : Tx
  sequences : List Nat
  witness : List Encode.Bytes
  deriving DecidableEq, Repr

/-- The transaction's own form: the Recovery branch's selector (`WTC-19`), at least one input, and
`CHN-10`: "every input's `nSequence`" set to the sealed value. -/
@[req "CHN-10"]
def formOk (cfg : Cfg) (sp : Spend) : Bool :=
  Alerts.isRecovery sp.witness && !sp.tx.inputs.isEmpty &&
    sp.sequences.length == sp.tx.inputs.length && sp.sequences.all (· == cfg.sealedLock)

/-- Script-level eligibility at this instant, for the block after its tip. No key enters it. -/
@[req "OPS-26"]
def eligible (cfg : Cfg) (b : Backend) (sp : Spend) : Bool :=
  formOk cfg sp && sp.tx.inputs.all (matured cfg b)

@[req "OPS-26"]
theorem eligible_iff (cfg : Cfg) (b : Backend) (sp : Spend) :
    eligible cfg b sp = true ↔ formOk cfg sp = true ∧ ∀ o ∈ sp.tx.inputs, matured cfg b o = true := by
  simp [eligible]

/-- A spend the sealed sequence does not sit on is not eligible, however old the coins.
`CHN-10`: "`0xffffffff` disables relative locks and does not satisfy the recovery branch". -/
@[req "CHN-10"]
theorem wrong_sequence_ineligible (cfg : Cfg) (b : Backend) (sp : Spend) (q : Nat)
    (hq : q ∈ sp.sequences) (hne : q ≠ cfg.sealedLock) : eligible cfg b sp = false := by
  have : sp.sequences.all (· == cfg.sealedLock) = false := by
    rw [List.all_eq_false]
    exact ⟨q, hq, by simpa using hne⟩
  simp [eligible, formOk, this]

/-! ## Custody -/

/-- What one party holds of what a Recovery spend needs. `OPS-23`: "Without it even valid recovery
keys cannot locate the coins". Whether a key's holder can really use it is the caller's reading of
`keys`, as `SEC-54`'s "including access through usable backups" is for `E`. -/
structure Holder where
  keys : List Nat
  descriptor : Bool
  network : Bool
  deriving DecidableEq, Repr

/-- `CHN-1`'s `multi(2,REC_A,REC_B,REC_C)`. -/
@[req "CHN-1"]
def threshold : Nat := 2

/-- The distinct recovery keys a party holds. `SEC-54`: "copies of one key count once". -/
def heldKeys (cfg : Cfg) (h : Holder) : List Nat := (h.keys.filter cfg.recKeys.contains).eraseDups

/-- `OPS-26`: "It needs only the descriptor backup (`OPS-23`) and the recovery keys." -/
@[req "OPS-26"]
def capable (cfg : Cfg) (h : Holder) : Bool :=
  decide (threshold ≤ (heldKeys cfg h).length) && h.descriptor && h.network

/-! ## The composed state and steps -/

inductive Party
  | operator | attacker
  deriving DecidableEq, Repr

/-- The composed sweep and chain, what each party holds, the dead node instances, the driver latches
and the Recovery spends published. -/
structure St where
  sw : Sweep.State
  op : Holder
  att : Holder
  dead : List Nat := []
  latched : List Nat := []
  published : List (Party × Spend) := []
  /-- What nodes have submitted, each with whether it is an Escape. A candidate can be pruned; what
  left the node stays here. -/
  sent : List (Bool × Tx) := []

def St.holder (st : St) : Party → Holder
  | .operator => st.op
  | .attacker => st.att

inductive Step
  /-- A step of the composed sweep and chain. -/
  | base (s : Sweep.Step)
  /-- `DUR-7`'s deadline driver latches this node. -/
  | latch (i : Nat) (env : Env)
  /-- This node instance dies. `DUR-18`: it "contributes nothing further". -/
  | die (i : Nat)
  /-- The Operator permanently loses a recovery key. -/
  | lose (k : Nat)
  /-- The Operator permanently loses the descriptor backup. -/
  | loseBackup
  /-- The attacker copies a recovery key. -/
  | copy (k : Nat)
  /-- The attacker obtains the descriptor backup, which `OPS-23` calls "public data". -/
  | learnBackup
  /-- A party broadcasts a Recovery spend. -/
  | publish (who : Party) (sp : Spend)
  deriving DecidableEq, Repr

/-- The node a composed step runs on, or whose key it copies. `DUR-18`: a dead node "holds no schedule,
no partials and no key", so a key not copied before its death is not copied after. -/
def actingNode : Sweep.Step → Option Nat
  | .fed (.process i _ _) | .fed (.unstaged i _) | .fed (.emit i _) | .fed (.deliver i _ _)
  | .fed (.deliverPartial i _ _) | .fed (.extract i) | .observe i _ => some i
  | _ => none

/-- `CHN-4` and `CHN-10` as consensus enforces them on a transaction in a block: the block's parent's
MTP is past each input's coin time plus the lock. -/
@[req "CHN-10"]
def includedOk (cfg : Cfg) (b : Backend) (sp : Spend) : Bool :=
  match (clock b).confirmed.lookup sp.tx.id with
  | none => false
  | some h => sp.tx.inputs.all fun o =>
    match (clock b).confirmed.lookup (cfg.sweep.creator o) with
    | none => false
    | some c => decide (lockSecs cfg.sealedLock ≤ (clock b).mtp (h - 1) - (clock b).mtp (c - 1))

/-- The one consensus guard on a chain move: an instant showing a published Recovery spend confirmed
shows it where its lock allowed. -/
@[req "CHN-10"]
def lockRespected (cfg : Cfg) (published : List (Party × Spend)) (b : Backend) : Bool :=
  published.all fun p => !Settlement.confirmedAt b p.2.tx || includedOk cfg b p.2

/-- What this module adds to a composed step: a dead node takes none, a latched node registers
nothing new, and a chain move keeps the lock. -/
def baseOk (cfg : Cfg) (st : St) (s : Sweep.Step) : Bool :=
  (match actingNode s with
    | some i => !st.dead.contains i
    | none => true) &&
  match s with
  | .fed (.process i _ (.accept ..)) | .fed (.process i _ (.refuse ..))
  | .fed (.process i _ (.clawback ..)) => !st.latched.contains i
  | .chain b => lockRespected cfg st.published b
  | _ => true

/-- A composed history, newest first. -/
abbrev Trace := List (St × Step)

/-- The composed sweep's own steps in a history. -/
def sweepTrace : Trace → Sweep.Trace
  | [] => []
  | (st, .base s) :: T => (st.sw, s) :: sweepTrace T
  | _ :: T => sweepTrace T

/-- Which steps may be taken. The custody moves are the environment's and always may. -/
def admits (cfg : Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace) : Step → Bool
  | .base s => Settlement.admits cfg.sweep honest st.sw (sweepTrace T) s && baseOk cfg st s
  | .latch i env => honest.contains i && !st.dead.contains i &&
      Progress.driverDue r env (st.sw.fed.worlds i).node
  | .die i => honest.contains i
  | .lose _ | .loseBackup | .copy _ | .learnBackup => true
  | .publish who sp => eligible cfg st.sw.truth sp && capable cfg (st.holder who) &&
      !Settlement.confirmedAt st.sw.truth sp.tx

/-- The transaction a send submits, with the role of the candidate `Kernel.send` selects: by its id, as
the send does, since one transaction can stand under two commitments in two roles. -/
def sentBy (r : Rules) (st : Sweep.State) (s : Sweep.Step) : List (Bool × Tx) :=
  match s with
  | .fed (.process i _ (.send cid)) =>
    match (st.fed.worlds i).node.cands.find? (·.id == cid), Sweep.submits r st s with
    | some c, _ :: _ => [(c.isEscape, c.tx)]
    | _, _ => []
  | _ => []

def apply (r : Rules) (st : St) : Step → St
  | .base s => { st with sw := Sweep.apply r st.sw s, sent := sentBy r st.sw s ++ st.sent }
  | .latch i _ => { st with latched := i :: st.latched }
  | .die i => { st with dead := i :: st.dead }
  | .lose k => { st with op := { st.op with keys := st.op.keys.filter (· != k) } }
  | .loseBackup => { st with op := { st.op with descriptor := false, network := false } }
  | .copy k => { st with att := { st.att with keys := k :: st.att.keys } }
  | .learnBackup => { st with att := { st.att with descriptor := true, network := true } }
  | .publish who sp => { st with published := (who, sp) :: st.published }

/-- A fresh composed start: nothing dead, latched, published or sent. What each party holds, and the
chain's truth, are free. -/
def Fresh (honest : List Nat) (st : St) : Prop :=
  Sweep.Fresh honest st.sw ∧ st.dead = [] ∧ st.latched = [] ∧ st.published = [] ∧ st.sent = []

inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → St → Prop
  | init (st : St) (h : Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (ha : admits cfg r honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (apply r st s)

/-! ## What the run is underneath -/

/-- Forgetting custody, death, latches and publication leaves a `Settlement.Execution`. -/
theorem to_settlement {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) :
    Settlement.Execution cfg.sweep r honest (sweepTrace T) st.sw := by
  induction hx with
  | init st h => exact .init _ h.1
  | next s ha _ ih =>
    cases s with
    | base s =>
      simp only [admits, Bool.and_eq_true] at ha
      exact .next s ha.1 ih
    | _ => exact ih

/-! ## Eligibility and possibility -/

/-- A Recovery spend may be published exactly when it is eligible at the truth, the party is capable,
and it is not already confirmed. -/
@[req "OPS-26"]
theorem publish_iff (cfg : Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace) (who : Party)
    (sp : Spend) :
    admits cfg r honest st T (.publish who sp) = true ↔
      eligible cfg st.sw.truth sp = true ∧ capable cfg (st.holder who) = true ∧
        Settlement.confirmedAt st.sw.truth sp.tx = false := by
  simp [admits, and_assoc]

/-- `OPS-26`: "no user key, no node quorum, no coordinator, no PIN". The verdict reads the chain's
truth and what the party holds: no federation state, no node's life or latch, no earlier history. -/
@[req "OPS-26"]
theorem publish_reads_no_federation (cfg : Cfg) (r r' : Rules) (honest honest' : List Nat) (st : St)
    (T T' : Trace) (who : Party) (sp : Spend) (f : Federation.Fed) (obs : Nat → Option Backend)
    (dead latched : List Nat) :
    admits cfg r honest st T (.publish who sp) =
      admits cfg r' honest'
        { st with sw := { st.sw with fed := f, obs := obs }, dead := dead, latched := latched }
        T' (.publish who sp) := by
  cases who <;> rfl

/-- Before a coin's lock has passed, no party can publish over it, whichever keys it holds.
`OPS-27`: "a spend before maturity". -/
@[req "OPS-26"]
theorem immature_refused (cfg : Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace) (who : Party)
    (sp : Spend) {o : Outpoint} (ho : o ∈ sp.tx.inputs) (hm : matured cfg st.sw.truth o = false) :
    admits cfg r honest st T (.publish who sp) = false := by
  have : eligible cfg st.sw.truth sp = false := by
    have : sp.tx.inputs.all (matured cfg st.sw.truth) = false := by
      rw [List.all_eq_false]
      exact ⟨o, ho, by simp [hm]⟩
    simp [eligible, this]
  simp [admits, this]

/-- A party short of a recovery key, the descriptor or the network cannot publish, however old the
coin. -/
@[req "OPS-23"]
theorem incapable_refused (cfg : Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace) (who : Party)
    (sp : Spend) (hc : capable cfg (st.holder who) = false) :
    admits cfg r honest st T (.publish who sp) = false := by
  simp [admits, hc]

/-! ## Inclusion -/

/-- One step keeps the published list, adding at most the step's own spend. -/
theorem published_step (r : Rules) (st : St) (x : Step) {p : Party × Spend}
    (h : p ∈ (apply r st x).published) :
    p ∈ st.published ∨ x = .publish p.1 p.2 := by
  cases x with
  | publish who sp =>
    simp only [apply, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr rfl
    · exact .inl h
  | _ => exact .inl h

/-- An included published spend stands where its lock allowed: a chain move shows it there or it does
not move, and publication itself finds it unconfirmed. -/
@[req "CHN-10"]
theorem included_respects_lock {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) {p : Party × Spend} (hp : p ∈ st.published)
    (hc : Settlement.confirmedAt st.sw.truth p.2.tx = true) : includedOk cfg st.sw.truth p.2 = true := by
  induction hx with
  | init st h => rw [h.2.2.2.1] at hp; cases hp
  | @next T st x ha _ ih =>
    cases x with
    | base s =>
      cases s with
      | chain b =>
        simp only [admits, baseOk, actingNode, Bool.and_eq_true, Bool.true_and] at ha
        have hl := List.all_eq_true.1 ha.2 p hp
        simp only [apply, Sweep.apply] at hc ⊢
        simpa [hc] using hl
      | fed s =>
        simp only [apply, Sweep.apply] at hc ⊢
        exact ih hp hc
      | observe i b =>
        simp only [apply, Sweep.apply] at hc ⊢
        exact ih hp hc
    | publish who sp =>
      simp only [apply, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have := ((publish_iff _ _ _ _ _ _ _).1 ha).2.2
        simp only [apply] at hc
        simp [hc] at this
      · exact ih hp hc
    | latch i env => exact ih hp hc
    | die i => exact ih hp hc
    | lose k => exact ih hp hc
    | loseBackup => exact ih hp hc
    | copy k => exact ih hp hc
    | learnBackup => exact ih hp hc

/-- What an inclusion implies. A Recovery spend a party published and the chain now shows was
published at a state where it was eligible at the truth and that party was capable, and it sits where
its lock allowed. The converse is false: see `Recovery.no_inclusion_without_service`. -/
@[req "OPS-26"]
theorem included_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) {p : Party × Spend} (hp : p ∈ st.published)
    (hc : Settlement.confirmedAt st.sw.truth p.2.tx = true) :
    includedOk cfg st.sw.truth p.2 = true ∧
      ∃ st₀, (st₀, Step.publish p.1 p.2) ∈ T ∧ eligible cfg st₀.sw.truth p.2 = true ∧
        capable cfg (st₀.holder p.1) = true := by
  refine ⟨included_respects_lock hx hp hc, ?_⟩
  clear hc
  induction hx with
  | init st h => rw [h.2.2.2.1] at hp; cases hp
  | @next T st x ha _ ih =>
    rcases published_step r st x hp with h | h
    · obtain ⟨st₀, hm, he, hcap⟩ := ih h
      exact ⟨st₀, List.mem_cons_of_mem _ hm, he, hcap⟩
    · subst h
      obtain ⟨he, hcap, -⟩ := (publish_iff _ _ _ _ _ _ _).1 ha
      exact ⟨st, List.mem_cons_self, he, hcap⟩

/-- The environment's promise about a chain over slots: at a slot that serves, a spend eligible there
shows confirmed at the next. It says nothing about how often a slot serves. -/
def Serves (cfg : Cfg) (hist : Nat → Backend) (serve : Progress.Service) (sp : Spend) : Prop :=
  ∀ u, serve u = true → eligible cfg (hist u) sp = true →
    Settlement.confirmedAt (hist (u + 1)) sp.tx = true

/-- Inclusion under bounded service, given that across a window of `B` slots the spend is eligible or
already confirmed (its inputs are spent once it confirms): `Progress.served_within`, with `Serves` as the
promise. -/
@[req "OPS-26"]
theorem included_within {cfg : Cfg} {hist : Nat → Backend} {serve : Progress.Service} {sp : Spend}
    {B t0 : Nat} (hs : (Progress.Profile.bounded B).Holds serve) (hv : Serves cfg hist serve sp)
    (hen : ∀ u, t0 ≤ u → u ≤ t0 + B →
      (eligible cfg (hist u) sp || Settlement.confirmedAt (hist u) sp.tx) = true) :
    ∃ u, t0 ≤ u ∧ u ≤ t0 + B + 1 ∧ Settlement.confirmedAt (hist u) sp.tx = true := by
  obtain ⟨u, h0, h1, he, hsv⟩ := Progress.served_within
    (en := fun u => eligible cfg (hist u) sp || Settlement.confirmedAt (hist u) sp.tx) hs hen
  rcases (Bool.or_eq_true _ _).mp he with he | hc
  · exact ⟨u + 1, by omega, by omega, hv u hsv he⟩
  · exact ⟨u, h0, by omega, hc⟩

/-- Inclusion under eventual service, given that from some slot on the spend is eligible or already
confirmed. -/
@[req "OPS-26"]
theorem included_eventually {cfg : Cfg} {hist : Nat → Backend} {serve : Progress.Service} {sp : Spend}
    {t0 : Nat} (hs : Progress.Profile.eventual.Holds serve) (hv : Serves cfg hist serve sp)
    (hen : ∀ u, t0 ≤ u → (eligible cfg (hist u) sp || Settlement.confirmedAt (hist u) sp.tx) = true) :
    ∃ u, t0 ≤ u ∧ Settlement.confirmedAt (hist u) sp.tx = true := by
  obtain ⟨u, h0, he, hsv⟩ := Progress.served_eventually
    (en := fun u => eligible cfg (hist u) sp || Settlement.confirmedAt (hist u) sp.tx) hs hen
  rcases (Bool.or_eq_true _ _).mp he with he | hc
  · exact ⟨u + 1, by omega, hv u hsv he⟩
  · exact ⟨u, h0, hc⟩

/-- `SEC-54`: "A possible spend, including Recovery, guarantees neither broadcast nor confirmation".
Under `adversarial`, a spend eligible at every slot of a chain that never moves is confirmed at none,
and the promise `Serves` holds. -/
@[req "SEC-54"]
theorem no_inclusion_without_service (cfg : Cfg) (b : Backend) (sp : Spend)
    (hc : Settlement.confirmedAt b sp.tx = false) :
    ∃ (hist : Nat → Backend) (serve : Progress.Service), Progress.Profile.adversarial.Holds serve ∧
      Serves cfg hist serve sp ∧ ∀ u, Settlement.confirmedAt (hist u) sp.tx = false :=
  ⟨fun _ => b, fun _ => false, trivial, fun _ h => (by cases h), fun _ => hc⟩

/-! ## A coin's history is the chain's -/

/-- A step that is not a chain move leaves the truth where it was. -/
theorem truth_kept (r : Rules) (st : St) (x : Step) (hx : ∀ b, x ≠ .base (.chain b)) :
    (apply r st x).sw.truth = st.sw.truth := by
  cases x with
  | base s =>
    cases s with
    | chain b => exact absurd rfl (hx b)
    | fed s => rfl
    | observe i b => rfl
  | _ => rfl

/-- Maturity belongs to the chain. Every step but a chain move keeps every coin's age and its verdict,
a driver latch, a node's death, a duress arming and a custody move included: Lockdown does not restart
it. `SEC-54`: "until that coin's own timelock matures, counted from its confirmation". -/
@[req "CHN-4"]
theorem age_moves_only_by_chain (cfg : Cfg) (r : Rules) (st : St) (x : Step)
    (hx : ∀ b, x ≠ .base (.chain b)) (creator : Nat) (o : Outpoint) :
    lockAge (clock (apply r st x).sw.truth) creator = lockAge (clock st.sw.truth) creator ∧
      matured cfg (apply r st x).sw.truth o = matured cfg st.sw.truth o := by
  rw [truth_kept r st x hx]
  exact ⟨rfl, rfl⟩

/-- A refresh confirming in a new block: its inputs leave the vault's unspent outputs, its outputs
join them, and its own block is recorded. -/
def confirmRefresh (b : Backend) (tx : Tx) (outs : List Coverage.Coin) (h hash m : Nat) : Backend :=
  { b with
    tip := ⟨h, hash⟩, sequence := b.sequence + 1,
    confirmed := b.confirmed.filter (fun c => !tx.inputs.contains c.1) ++ outs,
    mined := (tx.id, tx.inputs) :: b.mined,
    heights := (tx.id, h) :: b.heights,
    mtps := (h, m) :: b.mtps }

/-- A confirmed refresh spends its inputs, however mature they were, unless one of its outputs names
the same outpoint. -/
@[req "SPN-46"]
theorem refresh_spends_parents (cfg : Cfg) (b : Backend) (tx : Tx) (outs : List Coverage.Coin)
    (h hash m : Nat) {o : Outpoint} (ho : o ∈ tx.inputs) (hout : ∀ c ∈ outs, c.1 ≠ o) :
    matured cfg (confirmRefresh b tx outs h hash m) o = false := by
  have : unspentAt (confirmRefresh b tx outs h hash m) o = false := by
    simp only [unspentAt, confirmRefresh, List.any_append, Bool.or_eq_false_iff, List.any_eq_false,
      List.mem_filter, beq_iff_eq]
    refine ⟨?_, fun c hc => hout c hc⟩
    rintro c ⟨-, hn⟩ rfl
    simp [ho] at hn
  simp [matured, this]

/-- A confirmed refresh's output has its own relative-lock history: in the block that confirms it its
age is the one the block's own parent gives, and nothing about the coins it spent enters. Its verdict
is that age against the lock, for any parents of any age. -/
@[req "CHN-4"]
theorem successor_own_history (cfg : Cfg) (b : Backend) (tx : Tx) (outs : List Coverage.Coin)
    (h hash m : Nat) (hh : 0 < h) {o : Outpoint} (hc : cfg.sweep.creator o = tx.id) (ho : o ∈ outs.map (·.1)) :
    lockAge (clock (confirmRefresh b tx outs h hash m)) tx.id =
        some (m - (b.mtps.lookup (h - 1)).getD 0) ∧
      (matured cfg (confirmRefresh b tx outs h hash m) o = true ↔
        lockSecs cfg.sealedLock ≤ m - (b.mtps.lookup (h - 1)).getD 0) := by
  have hne : (h - 1 == h) = false := by simp; omega
  have hage : lockAge (clock (confirmRefresh b tx outs h hash m)) tx.id =
      some (m - (b.mtps.lookup (h - 1)).getD 0) := by
    simp [lockAge, clock, confirmRefresh, List.lookup, hne]
  have hun : unspentAt (confirmRefresh b tx outs h hash m) o = true := by
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 ho
    simp only [unspentAt, confirmRefresh, List.any_append, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inr ⟨c, hcm, rfl⟩
  refine ⟨hage, ?_⟩
  rw [matured_iff, hc, hage]
  simp [hun]

/-! ## Death and history -/

/-- Death is terminal for the instance: it stays on the list. -/
@[req "DUR-18"]
theorem dead_sticky (r : Rules) (st : St) (x : Step) {i : Nat} (h : i ∈ st.dead) :
    i ∈ (apply r st x).dead := by
  cases x with
  | die j => exact List.mem_cons_of_mem _ h
  | _ => exact h

/-- And a dead instance takes no later step, and its key is not copied after its death. `DUR-18`: it
"contributes nothing further". -/
@[req "DUR-18"]
theorem dead_takes_no_step (cfg : Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace)
    (s : Sweep.Step) {i : Nat} (hs : actingNode s = some i) (h : i ∈ st.dead) :
    admits cfg r honest st T (.base s) = false := by
  have hc : st.dead.contains i = true := List.contains_iff_mem.2 h
  have hb : baseOk cfg st s = false := by simp only [baseOk, hs, hc, Bool.not_true, Bool.false_and]
  simp [admits, hb]

/-- What a node submitted stays on the record, a pruned candidate included. -/
@[req "SEC-54"]
theorem sent_step (r : Rules) (st : St) (x : Step) {p : Bool × Tx} (h : p ∈ st.sent) :
    p ∈ (apply r st x).sent := by
  cases x with
  | base s => exact List.mem_append_right _ h
  | _ => exact h

/-- What a party holds moves one way, across every step: the Operator's keys and backup only leave and
the attacker's only arrive. `SEC-54` treats "the stated key losses as permanent". -/
@[req "SEC-54"]
theorem custody_step (r : Rules) (st : St) (x : Step) :
    (∀ k ∈ (apply r st x).op.keys, k ∈ st.op.keys) ∧
      ((apply r st x).op.descriptor = true → st.op.descriptor = true) ∧
      ((apply r st x).op.network = true → st.op.network = true) ∧
      (∀ k ∈ st.att.keys, k ∈ (apply r st x).att.keys) ∧
      (st.att.descriptor = true → (apply r st x).att.descriptor = true) ∧
      (st.att.network = true → (apply r st x).att.network = true) := by
  cases x with
  | lose k =>
    simp only [apply, List.mem_filter]
    exact ⟨fun _ h => h.1, id, id, fun _ h => h, id, id⟩
  | copy k =>
    simp only [apply, List.mem_cons]
    exact ⟨fun _ h => h, id, id, fun _ h => .inr h, id, id⟩
  | loseBackup =>
    simp only [apply]
    exact ⟨fun _ h => h, by simp, by simp, fun _ h => h, id, id⟩
  | learnBackup =>
    simp only [apply]
    exact ⟨fun _ h => h, id, id, fun _ h => h, by simp, by simp⟩
  | _ => exact ⟨fun _ h => h, id, id, fun _ h => h, id, id⟩

/-- A key copied and a signature exposed stay historical facts, across death, latch, loss and every
chain move: what any earlier state of a run held in the partial inventory, the extracted set or any
node's exposure rows, the final state holds (`Settlement.exposure_persists`). A recovery key a party
copied also stays. -/
@[req "POL-18"]
theorem history_persists {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) {st₀ : St} {x : Step} (hm : (st₀, x) ∈ T) :
    (∀ p ∈ st₀.sw.fed.parts, p ∈ st.sw.fed.parts) ∧
      (∀ j ∈ st₀.sw.fed.extracted, j ∈ st.sw.fed.extracted) ∧
      (∀ i, ∀ p ∈ (st₀.sw.fed.worlds i).exposure, p ∈ (st.sw.fed.worlds i).exposure) ∧
      (∀ k ∈ st₀.att.keys, k ∈ st.att.keys) := by
  induction hx with
  | init st h => cases hm
  | @next T st' s' _ _ ih =>
    have stepK := fun k hk => (custody_step r st' s').2.2.2.1 k hk
    have stepS : (∀ p ∈ st'.sw.fed.parts, p ∈ (apply r st' s').sw.fed.parts) ∧
        (∀ j ∈ st'.sw.fed.extracted, j ∈ (apply r st' s').sw.fed.extracted) ∧
        ∀ i, ∀ p ∈ (st'.sw.fed.worlds i).exposure, p ∈ ((apply r st' s').sw.fed.worlds i).exposure := by
      cases s' with
      | base s => exact Settlement.step_keeps_exposure r st'.sw s
      | _ => exact ⟨fun _ h => h, fun _ h => h, fun _ _ h => h⟩
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨stepS.1, stepS.2.1, stepS.2.2, stepK⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih hm
      exact ⟨fun p hp => stepS.1 p (h1 p hp), fun j hj => stepS.2.1 j (h2 j hj),
        fun i p hp => stepS.2.2 i p (h3 i p hp), fun k hk => stepK k (h4 k hk)⟩

/-! ## The five classes -/

/-- The ways an exit from the vault fails. They are not interchangeable: each reads its own part of the
state, and `BtcPolicy.Exhibits.Recovery` runs a scenario standing in each alone. -/
inductive Failure
  /-- The Normal path cannot complete this target: no user signature, or too few signers. -/
  | normalBlocked
  /-- No Escape over this coin stands submitted, and none is assembled or assemblable at a living node. -/
  | fastUnavailable
  /-- This coin is not past its own lock. -/
  | notMature
  /-- The Operator is short of a recovery key, the descriptor or the network. -/
  | missingCustody
  /-- A transaction spending this coin is out, and the chain does not show it confirmed. -/
  | awaitingInclusion
  deriving DecidableEq, Repr

/-- One coin, and the Normal-path transaction asked about it with its user signatures and class. -/
structure Scenario where
  coin : Outpoint
  target : Tx
  userSigs : List Authority.UserSig
  hot : Bool

def nodeOf (st : St) (i : Nat) : Node := (st.sw.fed.worlds i).node

/-- A resident candidate on the target that can still release: not terminal, not frozen, and either
opened already or named by a live Carrier that may open it (`Kernel.opens`; `Kernel.due` reads the quorum
bit). -/
def inFlight (n : Node) (X : Tx) : Bool :=
  n.cands.any fun c => c.tx == X && !c.terminal && !c.frozen &&
    (c.quorum || n.carriers.any fun k => opens k c.id)

/-- This node could still add a partial on the target. `DUR-11` freezes hot candidates alone, a node
at `lockedDown` takes no new acceptance (`Kernel.accept`), a poisoned node releases nothing (`DUR-9`), and
a candidate in flight stays so through a latch. -/
def openSigner (st : St) (honest : List Nat) (X : Tx) (hot : Bool) (i : Nat) : Bool :=
  honest.contains i && !st.dead.contains i && !(nodeOf st i).poisoned &&
    ((!st.latched.contains i && !(nodeOf st i).lockedDown && (!hot || !(nodeOf st i).armed)) ||
      inFlight (nodeOf st i) X)

/-- The records in the partial inventory, as `Authority` counts them. -/
def inventory (st : St) : List Authority.Sig := st.sw.fed.parts.map Authority.sig

/-- The signers on input `k` of the target: those with a record, whatever became of them since, those
whose key has been copied, and those still open. -/
def reachSigners (cfg : Cfg) (st : St) (honest : List Nat) (X : Tx) (hot : Bool) (k : Nat) : List Nat :=
  (Authority.signers cfg.sweep.keys X k (inventory st) ++
    cfg.sweep.keys.filter fun i => st.sw.fed.extracted.contains i || openSigner st honest X hot i).eraseDups

/-- The Normal path is not blocked: the user's signature on every input and `t` reachable signers on
every input (`DUR-28`, `CHN-9`). -/
@[req "DUR-28"]
def normalOpen (cfg : Cfg) (st : St) (honest : List Nat) (sc : Scenario) : Bool :=
  Authority.userSigned sc.target sc.userSigs && !sc.target.inputs.isEmpty &&
    (List.range sc.target.inputs.length).all fun k =>
      decide (cfg.t ≤ (reachSigners cfg st honest sc.target sc.hot k).length)

/-- A confirmed transaction other than this one spends one of its inputs, so on this instant's chain it
cannot confirm. A reorganization can lift it. -/
def conflicted (b : Backend) (tx : Tx) : Bool :=
  b.mined.any fun m => m.1 != tx.id && m.2.any tx.inputs.contains

/-- An Escape over this coin stands submitted, whichever node sent it and whatever became of that node;
or a living honest node holds one that is assembled or passes `Sweep.check` at its read. Any of them
conflicted at the truth does not count. An assembled Escape counts until it is pruned: whether its send's
re-authorization still passes depends on the sample (`Exhibits.Sweep.stale_assembly_not_sent`). -/
@[req "DUR-29"]
def fastAvailable (cfg : Cfg) (st : St) (T : Trace) (honest : List Nat) (coin : Outpoint) : Bool :=
  st.sent.any (fun p => p.1 && p.2.inputs.contains coin && !conflicted st.sw.truth p.2) ||
    honest.any fun i => !st.dead.contains i && (nodeOf st i).cands.any fun c =>
      c.isEscape && c.tx.inputs.contains coin && !conflicted st.sw.truth c.tx &&
        (c.packageOk || Sweep.check cfg.sweep st.sw (sweepTrace T) i c)

/-- A transaction spending this coin is out, not confirmed, and not conflicted at the truth: a published
Recovery spend, or anything a node has submitted. -/
@[req "SEC-54"]
def awaiting (st : St) (coin : Outpoint) : Bool :=
  st.published.any (fun p => p.2.tx.inputs.contains coin && !Settlement.confirmedAt st.sw.truth p.2.tx &&
      !conflicted st.sw.truth p.2.tx) ||
    st.sent.any fun p => p.2.inputs.contains coin && !Settlement.confirmedAt st.sw.truth p.2 &&
      !conflicted st.sw.truth p.2

/-- A confirmed transaction at the truth spends this coin. -/
def moved (b : Backend) (coin : Outpoint) : Bool := b.mined.any (·.2.contains coin)

/-- The classes this coin stands in. A coin that has moved stands in none. -/
@[req "SEC-54"]
def failures (cfg : Cfg) (st : St) (T : Trace) (honest : List Nat) (sc : Scenario) : List Failure :=
  if moved st.sw.truth sc.coin then [] else
    (if normalOpen cfg st honest sc then [] else [.normalBlocked]) ++
    (if fastAvailable cfg st T honest sc.coin then [] else [.fastUnavailable]) ++
    (if matured cfg st.sw.truth sc.coin then [] else [.notMature]) ++
    (if capable cfg st.op then [] else [.missingCustody]) ++
    (if awaiting st sc.coin then [.awaitingInclusion] else [])

/-- Each class is exactly its own reading of the state, on a coin that has not moved. -/
@[req "SEC-54"]
theorem mem_failures (cfg : Cfg) (st : St) (T : Trace) (honest : List Nat) (sc : Scenario)
    (hm : moved st.sw.truth sc.coin = false) :
    (.normalBlocked ∈ failures cfg st T honest sc ↔ normalOpen cfg st honest sc = false) ∧
      (.fastUnavailable ∈ failures cfg st T honest sc ↔ fastAvailable cfg st T honest sc.coin = false) ∧
      (.notMature ∈ failures cfg st T honest sc ↔ matured cfg st.sw.truth sc.coin = false) ∧
      (.missingCustody ∈ failures cfg st T honest sc ↔ capable cfg st.op = false) ∧
      (.awaitingInclusion ∈ failures cfg st T honest sc ↔ awaiting st sc.coin = true) := by
  simp only [failures, hm, Bool.false_eq_true, ↓reduceIte]
  cases normalOpen cfg st honest sc <;> cases fastAvailable cfg st T honest sc.coin <;>
    cases matured cfg st.sw.truth sc.coin <;> cases capable cfg st.op <;>
    cases awaiting st sc.coin <;> simp

/-- A coin that has moved stands in no class. -/
theorem moved_no_failures (cfg : Cfg) (st : St) (T : Trace) (honest : List Nat) (sc : Scenario)
    (hm : moved st.sw.truth sc.coin = true) : failures cfg st T honest sc = [] := by
  simp [failures, hm]

/-- The class and the route. On a coin outside `notMature` and `missingCustody`, a Recovery spend of that
coin alone, of the right form and not yet confirmed, may be published by the Operator. -/
@[req "OPS-26"]
theorem publish_of_clear (cfg : Cfg) (r : Rules) (st : St) (T : Trace) (honest honest' : List Nat)
    (sc : Scenario) (sp : Spend) (hm : moved st.sw.truth sc.coin = false)
    (hform : formOk cfg sp = true) (hin : sp.tx.inputs = [sc.coin])
    (hc : Settlement.confirmedAt st.sw.truth sp.tx = false)
    (hmat : .notMature ∉ failures cfg st T honest sc) (hcap : .missingCustody ∉ failures cfg st T honest sc) :
    admits cfg r honest' st T (.publish .operator sp) = true := by
  obtain ⟨-, -, h3, h4, -⟩ := mem_failures cfg st T honest sc hm
  have hmat' : matured cfg st.sw.truth sc.coin = true := by
    cases h : matured cfg st.sw.truth sc.coin with
    | true => rfl
    | false => exact absurd (h3.2 h) hmat
  have hcap' : capable cfg st.op = true := by
    cases h : capable cfg st.op with
    | true => rfl
    | false => exact absurd (h4.2 h) hcap
  rw [publish_iff]
  refine ⟨?_, hcap', hc⟩
  simp [eligible, hform, hin, hmat']

/-- `Failure.normalBlocked`'s direction from the record: a Normal authorization standing in the
inventory leaves the target unblocked, at any state, with no premise on any node. -/
@[req "DUR-28"]
theorem normal_of_inventory (cfg : Cfg) (st : St) (honest : List Nat) (sc : Scenario)
    (h : Authority.normal cfg.sweep.keys cfg.t sc.target sc.userSigs (inventory st) = true) :
    normalOpen cfg st honest sc = true := by
  simp only [Authority.normal, Authority.quorum, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨hu, hne, hq⟩ := h
  simp only [normalOpen, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range]
  refine ⟨⟨hu, hne⟩, fun k hk => Nat.le_trans (hq k (by simpa using hk)) ?_⟩
  apply length_le_of_nodup_subset (nodup_eraseDups _)
  intro z hz
  simp only [reachSigners, List.mem_eraseDups, List.mem_append]
  exact .inl (List.mem_eraseDups.2 (List.mem_eraseDups.1 hz))

/-! ## Running a schedule -/

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → St → List Step → Bool
  | _, _, [] => true
  | T, st, x :: xs => admits cfg r honest st T x && legal cfg r honest ((st, x) :: T) (apply r st x) xs

def record (r : Rules) : Trace → St → List Step → Trace × St
  | T, st, [] => (T, st)
  | T, st, x :: xs => record r ((st, x) :: T) (apply r st x) xs

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) {xs : List Step} (hl : legal cfg r honest T st xs = true) :
    Execution cfg r honest (record r T st xs).1 (record r T st xs).2 := by
  induction xs generalizing T st with
  | nil => exact hx
  | cons x xs ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next x hl.1 hx) hl.2

/-! ## The federation steps of a composed schedule -/

/-- The federation steps of a composed schedule, in order. -/
def fedSteps : List Step → List Federation.Step
  | [] => []
  | .base (.fed s) :: xs => s :: fedSteps xs
  | _ :: xs => fedSteps xs

/-- What a composed schedule does to the federation is `Federation.run` over its federation steps,
and the federation trace it leaves is `Federation.runTrace`'s: no backend, custody or latch step
moves the federation. -/
theorem fed_record (r : Rules) :
    ∀ (xs : List Step) (T : Trace) (st : St),
      Sweep.fedTrace (sweepTrace (record r T st xs).1) =
          Federation.runTrace r (Sweep.fedTrace (sweepTrace T)) st.sw.fed (fedSteps xs) ∧
        (record r T st xs).2.sw.fed = Federation.run r st.sw.fed (fedSteps xs) := by
  intro xs
  induction xs with
  | nil => intro T st; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro T st
    obtain ⟨h1, h2⟩ := ih ((st, x) :: T) (apply r st x)
    simp only [record]
    rw [h1, h2]
    cases x with
    | base s =>
      cases s with
      | fed s => exact ⟨rfl, rfl⟩
      | chain b => exact ⟨rfl, rfl⟩
      | observe i b => exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

/-! ## `DUR-21`'s check on the composed run

`PreRelease.Execution` refines `Sweep.Execution` by one conjunct on a fire pass and a ladder pass. A
composed run is a `Settlement.Execution` underneath (`Recovery.to_settlement`), so when each of its fire passes
carries the computed verdict and each ladder pass lists no release (`PreRelease.Checked`), its sweep part is a
refined run, and every result of `BtcPolicy.PreRelease` holds of it, with custody, death, latches and Recovery
publication beside it. -/

/-- A composed run whose fire passes carry `DUR-21`'s verdict, computed from the acting node's latest
observation and history, and whose ladder passes list no release, is a refined run underneath: its sweep trace and state are a
`PreRelease.Execution`. -/
@[req "DUR-21"]
theorem to_prerelease {cfg : Cfg} {pc : PreRelease.Cfg} (hpc : pc.sweep = cfg.sweep) {r : Rules}
    {honest : List Nat} {T : Trace} {st : St} (hx : Execution cfg r honest T st)
    (hc : PreRelease.Checked pc (sweepTrace T)) : PreRelease.Execution pc r honest (sweepTrace T) st.sw := by
  have hs := Settlement.to_sweep (to_settlement hx)
  rw [← hpc] at hs
  exact PreRelease.execution_iff.2 ⟨hs, hc⟩

/-- **No premature exposure on the composed run.** On a composed run whose fire passes carry the
computed verdict and whose ladder passes list no release, every row of the partial inventory whose signer's key is not in the cumulative
extracted set was emitted by that signer's honest node at a fire pass of the run, and, for an
Escape-role candidate, only past that node's verdict there (`PreRelease.Emitted`). -/
@[req "DUR-21"]
theorem no_premature_exposure {cfg : Cfg} {pc : PreRelease.Cfg} (hpc : pc.sweep = cfg.sweep) {r : Rules}
    {honest : List Nat} {T : Trace} {st : St} (hx : Execution cfg r honest T st)
    (hc : PreRelease.Checked pc (sweepTrace T)) {x : Exp} (hm : x ∈ st.sw.fed.parts)
    (hs : x.signer ∉ st.sw.fed.extracted) : x.signer ∈ honest ∧ PreRelease.Emitted pc r (sweepTrace T) x :=
  PreRelease.no_premature_exposure (to_prerelease hpc hx hc) hm hs

end BtcPolicy.Recovery
