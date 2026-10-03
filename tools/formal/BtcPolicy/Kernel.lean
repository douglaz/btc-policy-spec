import BtcPolicy.Clocks
/-! The release and Carrier kernel (`ADR-0023` decision 10 item 4, amended by the second panel):
one honest node's Carriers and candidates, the events that move them, and the exposure history
outside the node. Theorems and exhibits share one `step`; the exhibits over `current` live in
`Exhibits.lean`.

**Scope.** Milestone 7 added the Armed overlay — `T` with `DUR-14`'s dynamics, `sweep_active`,
`selected_escapes` and `DUR-20`'s windows — and with them the Escape half of `DUR-29`'s
re-authorization: `releaseAuthorized` gates the fire pass, the package test and the send alike.
The Hot ledger is composed on top in `Ledger.lean` and the two-run relation over this step is
`Silence.lean`'s. `DEF-7`'s preflight marker and any multi-node world are still outside. The
Escape member of a pair is registered with no fire window (`SPN-37`); the holder decision installs
one (`DUR-20`).

**Boundary hypotheses, named and not proved here.** The sighash is `Sighash`, a function of the
transaction and the input index and of no request field (`CHN-11`; `CHN-24`'s expiry and
`policy_version` are outside it); milestone 5 supplies the BIP143 encoder as its instance.
Unforgeability of honest keys; the backend's truth (`WTC-2`); delivery, delay and `F39`'s
partition (receipts are events with no delivery model, so local safety is proved against any
schedule); lock discipline (the atomicity is modelled, the lock is not); the `≤ t − 1` compromise
bound (`adversaryExposes` is unconstrained, so the node-local theorems hold against any number of
compromised signers, and `DUR-8`'s federation consequence is a counting statement under
`compromised < t`, not a theorem here); clock sample provenance (`NCH-33`'s "sample taken before
authentication" is `Env.mono` of the `accept` step); and a wall clock already wrong at acceptance
(`SEC-45`), which `D` inherits. Receipts prove receipt, not freezing or signing (`DUR-5`):
`receipt` touches the holder set and nothing in the exposure. A relay's `sender_node_id` is the
transport's, which is a boundary hypothesis like unforgeability: `NCH-5` says "possession of the
channel key is proven per message by the envelope signature", and `sender_node_id` is a member of
the signed preimage (`NCH-11`), so the sender a `receipt` carries is the one the wire proved and
nothing below re-checks it. -/

namespace BtcPolicy.Kernel
open BtcPolicy.Clocks

/-! ## Environment inputs: read by a step, never written by one -/

/-- One transaction, abstractly: its id, the inputs it spends, and `POL-11`'s `hot_outflow` —
"the sum of every output's value EXCEPT outputs that derive from the vault descriptor and outputs
that derive from the escape descriptor". It hangs on the transaction because it is a function of
the outputs alone, so two commitments over one transaction (`CHN-24`) meter one amount, and
"refresh and escape sweeps have zero outflow by construction". Nothing here reads it: the Hot
ledger of `Ledger.lean` meters it (`POL-16`). -/
structure Tx where
  id : Nat
  inputs : List Nat
  outflow : Nat
  deriving DecidableEq, Repr

/-- What this node's backend shows. `mtp` is here and nowhere else. -/
structure ChainView where
  mtp : Mtp
  /-- Transactions resident in the mempool or confirmed: the settlement evidence `SPN-33` reads
  ("seen in the mempool or confirmed"). Eviction is this list shrinking, an environment change,
  not a node event. -/
  seen : List Tx
  deriving DecidableEq, Repr

/-- Every clock sample and the chain view a step may read. -/
structure Env where
  wall : Wall
  hw : HighWater
  mono : Mono
  chain : ChainView
  deriving DecidableEq, Repr

def Env.eff (e : Env) : Effective := Effective.ofWall e.wall e.hw

/-- The boundary assumption on sighash evidence: `CHN-11`'s "the BIP143 P2WSH sighash computed
with `SIGHASH_ALL` … with the input's `witness_utxo` value" is a function of the transaction and
the input alone, so two commitments over one transaction have one message per input. Here the
message IS the pair; nothing below inspects it. -/
abbrev Sighash := Nat × Nat
@[req "CHN-11"]
def sighash (tx : Tx) (i : Nat) : Sighash := (tx.id, i)

/-- One exposed authority, keyed `(sighash message, input, signer)` (`ADR-0023` decision 9),
with the class of the candidate it left under, for the invariant, and the commitment it was
released under — recorded so the WRONG key can be computed beside the right one in the exhibit,
never read by `exposedQuorum`. -/
structure Exp where
  msg : Sighash
  input : Nat
  signer : Nat
  hot : Bool
  cid : Nat
  deriving DecidableEq, Repr

/-! ## Node state -/

/-- `SPN-36`'s candidate, reduced to the flags the release gate reads. `id` is the commitment id:
`CHN-24` binds the expiry, so two ids can name one `tx`. -/
structure Cand where
  id : Nat
  tx : Tx
  hot : Bool
  /-- `SPN-37`: born `false`, "opened only by its own Carrier's holder decision". -/
  quorum : Bool
  /-- `DUR-11`'s freeze bit, meaningful on hot candidates. -/
  frozen : Bool
  /-- `SPN-33`'s terminal mark. -/
  terminal : Bool
  /-- The candidate itself was seen on the network (`SPN-39`: "settle it if the network already
  shows it"). -/
  settled : Bool
  broadcast : Bool
  /-- `SPN-36`'s `released`: this node's partial has been queued for transport. -/
  released : Bool
  /-- `CONTEXT.md`'s *Held partial* as a set of signers, which is `DUR-28`'s "`≥ t` distinct
  valid partials on every input" read as THIS node holds them. That entry owns what the set is
  and how it stands to exposed authority; here is the representation alone. This node's own
  signature is a member from registration. `SPN-36` says a candidate is "born fully signed and
  fully withheld". `SPN-32` says "The node MUST sign the spend, the Escape and every rung at
  ingress". So `born` seeds the set and no separate `ownSigned` bit is needed: `node.id` is what
  distinguishes self. A peer's joins it when the store accepts one (`NCH-24`, `NCH-25`).
  `heldQuorum` is what counts it, and it reads `.eraseDups.length`, which is total over any value
  rather than resting on a reachable-state invariant as `holderCount`'s `length` does. Of the key
  `NCH-25` gives the store — "at most one partial per `(rung, input, signer)`" — this kernel
  carries the signer alone: input 0 stands for every input, as `Effect.queuePartial` and
  `exposedQuorum` already declare, and one candidate is one rung. -/
  heldSigners : List Nat
  /-- Package assembled and mempool-tested, awaiting the send (`SPN-39`, `DUR-29`). -/
  packageOk : Bool
  /-- `SPN-37`: the Escape member "is registered with no fire window"; the arm commit installs
  one (`DUR-20`). -/
  fireAt : Option Wall
  /-- `DUR-20`'s window close, `T + combine_slack_secs`, on a selected Escape: the window is
  "not capped by its commitment's expiry", so when it is present it closes the window and
  `expiry` does not. -/
  windowClose : Option Wall
  expiry : Wall
  /-- Registration-owned `(spend, Escape)` ids: `SPN-32`'s "requested role (spend or Escape)"
  and `SPN-36`'s "its paired sibling's id" as one value. A candidate's own id identifies its role.
  Distinct ids make the ordered pair encode both role and sibling. Incoming metadata is ignored;
  `none` represents an unpaired candidate, including a hand-seeded claw-back boundary fixture. -/
  pair : Option (Nat × Nat) := none
  deriving DecidableEq, Repr

/-- `DUR-4`'s arm intent and `NCH-32`'s memo as one record. -/
structure Carrier where
  cid : Nat
  duress : Bool
  /-- `DUR-5`'s holder set less this node: "each distinct peer whose authenticated relay of the
  same Carrier this node receives", held by the `sender_node_id` the relay carried. This node is
  implicit and `holderCount` adds it, which is `ADR-0012`'s shape — a node "counts ITSELF … plus
  the distinct `sender_node_id`s that relay it back". `addSender` is the only writer besides the
  empty list `accept` starts it with, so it is a set of PEERS: no duplicate, and never this
  node's own id. A `Nat` here cannot express `DUR-6`'s "a sender already counted … MUST be an
  idempotent no-op", which is `F65`. -/
  relaySenders : List Nat
  E : Wall
  /-- `NCH-33`: fixed at acceptance; nothing below writes it. -/
  D : Mono
  /-- `DUR-13`: "the INGRESS-hold effective time at which the nonce was consumed, never the
  commit-hold time, so that slow or selective delivery cannot stretch the hostage window". -/
  firstSeen : Effective
  spend : Nat
  escape : Nat
  deriving DecidableEq, Repr

structure Node where
  id : Nat
  t : Nat
  /-- `DUR-10`'s `active`: "once set it is never cleared". -/
  armed : Bool
  /-- `DUR-9`: a panic while holding a critical lock. -/
  poisoned : Bool
  lockedDown : Bool
  carriers : List Carrier
  cands : List Cand
  /-- `DUR-10`'s overlay deadline `T`, written at every holder decision under both PINs
  (`DUR-13`) and shrunk on a hot acceptance while armed (`DUR-14`). Internal state: its value
  differs between the two runs of the SILENCE relation, and reaches no surface. -/
  T : Wall
  /-- `DUR-10`: "a single overlay flag that a duress Carrier sets for the whole node". -/
  sweepActive : Bool
  /-- `DUR-10`'s `selected_escapes`, "keyed by Escape commitment id" with the intent's duress
  bit: "the entry's duress bit becomes the OR of its old value and the new intent's". -/
  selected : List (Nat × Bool)
  /-- Sealed configuration (`MAN-2`): `duress_delay_secs`, `epsilon_secs`, `combine_slack_secs`. -/
  duressDelay : Secs
  epsilon : Secs
  combineSlack : Secs
  deriving DecidableEq, Repr

/-- The world: the honest node under study and the exposure history outside it. Compromised
signers are not nodes; `adversaryExposes` records their authority without delivery. -/
structure World where
  node : Node
  exposure : List Exp
  deriving DecidableEq, Repr

/-! ## Guard parameters (`ADR-0023` decision 6), one `current` -/

/-- `NCH-35`: "Raw wall time … MAY refuse the current attempt but MUST NOT retire, replace or
extend an active … Carrier while `mono_now < D`". `byWall` is `DEF-1`: intents pruned against
the raw wall clock. It confuses no clock type — it compares the signed expiry to a wall sample —
which is why it is a parameter beside the type error. -/
inductive Retire
  | byMono | byWall
  deriving DecidableEq, Repr

/-- `DUR-29`/`SPN-39`: re-authorize "under the store lock … immediately before the send".
`beforeAssembly` is the check placed before assembly instead of before the send, which leaves the
window `DUR-11` exists to close. -/
inductive Reauth
  | beforeSend | beforeAssembly
  deriving DecidableEq, Repr

/-- `DUR-9`: "a poisoned node MUST release nothing … asserted by a test that poisons the lock and
drives a fire pass, not left to the accident of lock order". `byLockOrder` is `DEF-4`'s accident
with the lock order refactored away. -/
inductive PoisonGate
  | asserted | byLockOrder
  deriving DecidableEq, Repr

/-- `SPN-33`: defeat is the terminal flag. `mempoolResidency` is `F57` row 8: defeat read off the
claw-back's residency, so an evicted claw-back un-defeats the spend. -/
inductive Defeat
  | terminalFlag | mempoolResidency
  deriving DecidableEq, Repr

/-- `DUR-20`: "every hot acceptance and every holder decision MUST visit every selected entry and
write its window … under BOTH PINs and whether or not `T` actually moved (`DUR-13`, `DUR-14`): an
actual shrink MUST NOT trigger a traversal a non-shrink does not". `onlyWhenMoved` is the
traversal made conditional on the shrink, which `DUR-14` performs only on an armed node — so it is
work a duress carrier's twin does not do (`F54`'s `DUR-20` row). It writes the same windows
whenever it runs, so what it changes is the visit trace and nothing else. -/
inductive Traversal
  | always | onlyWhenMoved
  deriving DecidableEq, Repr

/-- `DUR-14`'s dynamic `T`. `static` is the deadline as it stood before that clause, `DUR-13`'s
value alone: `ADR-0012`'s verification round of 2026-07-15 records "One true silence break →
FIXED: dynamic T", and `DUR-14` states what the break was — "without it a post-arm hot spend with
a nearer Hold expiry would settle visibly under the normal PIN and be frozen under duress,
leaking the armed state before `T`". -/
inductive Dynamics
  | dynamic | static
  deriving DecidableEq, Repr

/-- Registration before the 2026-10-03 repair rebirthed resident ids. -/
inductive Registration
  | preserve | rebirth
  deriving DecidableEq, Repr

structure Rules where
  retire : Retire
  reauth : Reauth
  poison : PoisonGate
  defeat : Defeat
  traversal : Traversal
  dynamics : Dynamics
  registration : Registration := .preserve
  deriving DecidableEq, Repr

def current : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic, registration := .preserve }

/-! ## Effects and events -/

inductive Effect
  /-- A partial queued for transport: `SPN-38`'s "The cursor records that a rung has been queued
  for transport, not that a peer received it" is where a partial is exposed. One input stands
  for every input. -/
  | queuePartial (msg : Sighash) (input : Nat) (hot : Bool) (cid : Nat)
  /-- Irrevocable submission of the finalized transaction. An implementation that unlocks
  between `DUR-29`'s recheck and the socket write refines this; one that rechecks before
  assembly does not. -/
  | broadcast (tx : Nat)
  deriving DecidableEq, Repr

inductive Event
  /-- Ingress accepted (`SPN-32`, `DUR-4`): the pair registered closed, the intent written with
  its duress bit, `D` computed from this step's samples. -/
  | accept (cid : Nat) (duress : Bool) (E : Wall) (spend escape : Cand)
  /-- A peer's authenticated relay of the Carrier (`NCH-29`, `DUR-5`, `DUR-6`), carrying the
  wire's `sender_node_id`. Reaching `t` runs the holder decision in this same step: there is no
  `arm` event, because `DUR-10` gives `active` "exactly one writer — the holder decision with
  `arm = true`". -/
  | receipt (cid : Nat) (sender : Nat)
  /-- The fire pass's release loop over every due candidate (`SPN-38`, `DUR-8`). -/
  | firePass
  /-- Assembly and the mempool-acceptance test returned for a candidate (`SPN-39`). -/
  | packageAccepted (cand : Nat)
  /-- The send, with `DUR-29`'s re-authorization under the store lock. -/
  | send (cand : Nat)
  /-- A settlement observed (`SPN-33`): the transaction named is in `env.chain.seen`. -/
  | settle (tx : Tx)
  /-- `SPN-41`'s expiry pruning. -/
  | prune
  /-- The store prune driver's Carrier retirement, `NCH-40` (3): "`mono_now ≥ D` … using
  HotClock time and never its caller's wall value". -/
  | tick
  /-- A panic under a critical lock (`STO-10`). -/
  | panic
  /-- A compromised signer's partial appears in the world. -/
  | adversaryExposes (msg : Sighash) (input : Nat) (signer : Nat) (cid : Nat)
  /-- Authenticated inbound partial, represented as an internal post-response transition.
  `receivePartial` names the validation boundary for its guarded store. The world records
  exposed authority even when that store drops the partial; this does not certify acceptance.
  `NCH-25`: "A duplicate is an idempotent `ACCEPTED` and never displaces the first."
  That channel answer is upstream: `Silence.respond` emits no additional response here. -/
  | receivePartial (msg : Sighash) (input : Nat) (signer : Nat) (cid : Nat)
  deriving DecidableEq, Repr

/-! ## The step -/

/-- `SPN-33`: "shares an input with it". -/
def conflicts (tx : Tx) (c : Cand) : Bool := c.tx.inputs.any (tx.inputs.contains ·)

/-- A conflicting transaction resident right now, the withdrawn reading `F57` row 8 records. -/
def residentConflict (env : Env) (c : Cand) : Bool :=
  env.chain.seen.any fun tx => tx.id != c.tx.id && conflicts tx c

/-- The closing conjunct of `SPN-38`'s "its fire window is open now": a selected Escape's window
close decides it when one is installed, because that window is "deliberately not capped by the
commitment expiry" (`SPN-37`), and the commitment's own expiry decides it otherwise (`SPN-41`:
"The last authorized second is `now == expiry`"). One home — `due` reads it and so does the
concealment horizon of `Silence.lean`. -/
@[req "SPN-38"]
def windowOpen (now : Effective) (c : Cand) : Bool :=
  match c.windowClose with
  | none => now.atOrBefore c.expiry
  | some wc => now.atOrBefore wc

/-- `SPN-38`: "A candidate is due iff it is not broadcast, is not terminal (`SPN-33`), is not a
frozen hot candidate (`DUR-11`), its slot is active — its quorum is reached … — and its fire
window is open now." -/
@[req "SPN-38"]
def due (r : Rules) (env : Env) (c : Cand) : Bool :=
  !c.broadcast && !c.settled &&
  (match r.defeat with | .terminalFlag => !c.terminal | .mempoolResidency => !residentConflict env c) &&
  !(c.hot && c.frozen) && c.quorum &&
  (match c.fireAt with | none => false | some f => env.eff.atOrAfter f) &&
  windowOpen env.eff c

/-- `DUR-10`: "Release of an entry requires BOTH `sweep_active` AND that entry's own duress bit:
`sweep_active` is a single overlay flag that a duress Carrier sets for the whole node, so it
alone cannot make a normal-PIN pair's Escape inert once some other Carrier has armed — the
per-entry bit is what does." A candidate that is not a selected Escape is gated by `due` alone. -/
@[req "DUR-10"]
def releaseAuthorized (n : Node) (c : Cand) : Bool :=
  match n.selected.find? (·.1 == c.id) with
  | none => true
  | some e => n.sweepActive && e.2

/-- `DUR-13`'s `earliest_hot`: "`min{ fire_at : candidate is hot, not broadcast, expiry ≥ now }`". -/
@[req "DUR-13"]
def earliestHotFire (env : Env) (n : Node) : Option Wall :=
  (n.cands.filterMap fun c =>
      if c.hot && !c.broadcast && env.eff.atOrBefore c.expiry then c.fireAt else none).foldl
    (fun acc w => some (match acc with | none => w | some a => Wall.earlier a w)) none

/-- The fold `earliestHotFire` runs, as its own function so the two lemmas below can be stated
about it: `DUR-13`'s `min` over the pending hot candidates' fire times. -/
def foldEarliest (l : List Wall) (acc : Option Wall) : Option Wall :=
  l.foldl (fun acc w => some (match acc with | none => w | some a => Wall.earlier a w)) acc

theorem foldEarliest_le_acc : ∀ (l : List Wall) (a : Wall),
    ∃ e, foldEarliest l (some a) = some e ∧ Wall.atOrBefore e a = true := by
  intro l
  induction l with
  | nil => intro a; exact ⟨a, rfl, Wall.atOrBefore_refl a⟩
  | cons w ws ih =>
    intro a
    obtain ⟨e, he, hle⟩ := ih (Wall.earlier a w)
    exact ⟨e, he, Wall.atOrBefore_trans hle (Wall.earlier_atOrBefore_left a w)⟩

/-- Every element of the fold bounds its result: the minimum is at or before each candidate's
fire time it ranged over. -/
@[req "DUR-13"]
theorem foldEarliest_le_mem : ∀ (l : List Wall) (acc : Option Wall) (x : Wall), x ∈ l →
    ∃ e, foldEarliest l acc = some e ∧ Wall.atOrBefore e x = true := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons w ws ih =>
    intro acc x hx
    have hstep : foldEarliest (w :: ws) acc =
        foldEarliest ws (some (match acc with | none => w | some a => Wall.earlier a w)) := rfl
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hstep]
      cases acc with
      | none =>
        obtain ⟨e, he, hle⟩ := foldEarliest_le_acc ws x
        exact ⟨e, he, hle⟩
      | some a =>
        obtain ⟨e, he, hle⟩ := foldEarliest_le_acc ws (Wall.earlier a x)
        exact ⟨e, he, Wall.atOrBefore_trans hle (Wall.earlier_atOrBefore_right a x)⟩
    · rw [hstep]; exact ih _ x hx

/-- `DUR-13`'s scan covers every hot, non-broadcast, unexpired candidate that carries a fire time:
for each of them the deadline's `earliest_hot` exists and is at or before that fire time. -/
@[req "DUR-13"]
theorem earliestHotFire_le (env : Env) (n : Node) (c : Cand) (hc : c ∈ n.cands)
    (hhot : c.hot = true) (hb : c.broadcast = false)
    (hexp : env.eff.atOrBefore c.expiry = true) (f : Wall) (hf : c.fireAt = some f) :
    ∃ e, earliestHotFire env n = some e ∧ Wall.atOrBefore e f = true := by
  have hmem : f ∈ n.cands.filterMap fun d =>
      if d.hot && !d.broadcast && env.eff.atOrBefore d.expiry then d.fireAt else none := by
    refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
    simp [hhot, hb, hexp, hf]
  exact foldEarliest_le_mem _ none f hmem

/-- `DUR-10`: "nothing is ever displaced", and "Entries are keyed by Escape commitment id alone;
when two Carriers name the same Escape, the entry's duress bit becomes the OR of its old value and
the new intent's". -/
@[req "DUR-10"]
def insertSelected (sel : List (Nat × Bool)) (id : Nat) (duress : Bool) : List (Nat × Bool) :=
  if sel.any (·.1 == id) then sel.map fun e => if e.1 == id then (e.1, e.2 || duress) else e
  else sel ++ [(id, duress)]

/-- `DUR-20`'s window write on one candidate: a selected Escape's window is `[T, T +
combine_slack_secs]` for the overlay's CURRENT `T`. -/
@[req "DUR-20"]
def withWindow (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) : Cand :=
  if sel.any (·.1 == c.id) then { c with fireAt := some T, windowClose := some (T.plus slack) }
  else c

/-- `DUR-20`: "every hot acceptance and every holder decision MUST visit every selected entry and
write its window … under BOTH PINs and whether or not `T` actually moved (`DUR-13`, `DUR-14`): an
actual shrink MUST NOT trigger a traversal a non-shrink does not". The traversal is over the whole
list, never over the entries whose window changed. -/
@[req "DUR-20"]
def writeWindows (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (cands : List Cand) : List Cand :=
  cands.map (withWindow sel T slack)

theorem withWindow_hot (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).hot = c.hot := by unfold withWindow; split <;> rfl

theorem withWindow_frozen (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).frozen = c.frozen := by unfold withWindow; split <;> rfl

theorem withWindow_id (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).id = c.id := by unfold withWindow; split <;> rfl

theorem withWindow_terminal (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).terminal = c.terminal := by unfold withWindow; split <;> rfl

theorem withWindow_released (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).released = c.released := by unfold withWindow; split <;> rfl

theorem withWindow_broadcast (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).broadcast = c.broadcast := by unfold withWindow; split <;> rfl

theorem withWindow_tx (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).tx = c.tx := by unfold withWindow; split <;> rfl

theorem withWindow_held (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (c : Cand) :
    (withWindow sel T slack c).heldSigners = c.heldSigners := by unfold withWindow; split <;> rfl

/-- `DUR-11`: "existing and future" — a hot candidate accepted on an armed node is born frozen.
`self` is this node's own id, the sole member of the held set at registration: `SPN-36`'s
candidate is "born fully signed and fully withheld" and `SPN-32` requires the signature "at
ingress", so possession begins with this node's own partial and never with none. -/
@[req "DUR-11"]
def born (self : Nat) (armed : Bool) (c : Cand) : Cand :=
  { c with quorum := false, frozen := armed && c.hot, terminal := false, settled := false,
           released := false, packageOk := false, broadcast := false, heldSigners := [self] }

/-- `DUR-13`'s deadline for this holder decision. Computed under both PINs: `DUR-5` makes the
overlay write pin-uniform, and only the bit inside it differs. -/
@[req "DUR-13"]
def newDeadline (env : Env) (n : Node) (k : Carrier) : Wall :=
  Wall.initialDeadline k.firstSeen n.duressDelay env.eff (earliestHotFire env n) n.epsilon

/-- `DUR-5`'s holder decision as one write: open the pair, freeze every hot candidate with the
intent's bit (`DUR-9`: "Opening the pair and setting the arm bit MUST be one atomic write"), set
`active`, retire the Carrier (`NCH-40` (2)). The scan is the same map under both PINs; a normal
commit ORs `false` into every freeze bit. -/
@[req "DUR-5"]
def holderDecision (env : Env) (n : Node) (k : Carrier) : Node :=
  { n with
    armed := n.armed || k.duress,
    sweepActive := n.sweepActive || k.duress,
    T := newDeadline env n k,
    selected := insertSelected n.selected k.escape k.duress,
    cands := n.cands.map fun c =>
      withWindow (insertSelected n.selected k.escape k.duress) (newDeadline env n k) n.combineSlack
        { c with quorum := c.quorum || (c.id == k.spend || c.id == k.escape),
                 frozen := c.frozen || (c.hot && k.duress) },
    carriers := n.carriers.filter (·.cid != k.cid) }

/-- `DUR-14`: "On every hot spend accepted while armed, `T ← max(min(T, its fire_at −
epsilon_secs), now)`." Only while armed, and only for a hot spend; the window traversal
`DUR-20` requires happens either way, so a shrink triggers no work a non-shrink does not. -/
@[req "DUR-14"]
def shrunkDeadline (r : Rules) (env : Env) (n : Node) (sp : Cand) : Wall :=
  if r.dynamics == .dynamic && n.armed && sp.hot then
    match sp.fireAt with
    | none => n.T
    | some f => Wall.shrinkDeadline n.T f n.epsilon env.eff
  else n.T

/-- `DUR-20`'s traversal condition on an acceptance: every hot acceptance visits every selected
entry, whether or not `T` moved. One home — `accept` branches on it and `Silence.work` reads it
for `DUR-1`'s "candidate visits" — so the withdrawn value is one flip and not two definitions. -/
@[req "DUR-20"]
def traverses (r : Rules) (env : Env) (n : Node) (sp : Cand) : Bool :=
  sp.hot && (r.traversal == .always || shrunkDeadline r env n sp != n.T)

/-- `SPN-32`: "a conflicting resident commitment is `PSBT_INCONSISTENT` / `candidate_identity`".
A pair is admitted when neither member is resident, or when both are resident as THIS pair: every
resident candidate under either id agrees with the request on `tx`, `hot` and `expiry` and was
registered under `(sp.id, es.id)`, which fixes its role and its sibling. -/
@[req "SPN-32"]
def pairAdmits (r : Rules) (n : Node) (sp es : Cand) : Bool :=
  let same (x c : Cand) :=
    c.tx == x.tx && c.hot == x.hot && c.expiry == x.expiry && c.pair == some (sp.id, es.id)
  r.registration == .rebirth || (sp.id != es.id &&
    (n.cands.any (·.id == sp.id) == n.cands.any (·.id == es.id)) &&
    !n.cands.any (fun c => (c.id == sp.id && !same sp c) || (c.id == es.id && !same es c)))

/-- `SPN-32`: "an already resident compatible pair is left exactly as is". Called after
`pairAdmits` succeeds; this helper neither decides refusal nor re-applies the schedule. -/
@[req "SPN-32"]
def register (r : Rules) (n : Node) (sp es : Cand) : List Cand :=
  if r.registration == .preserve && n.cands.any (·.id == sp.id) then n.cands
  else born n.id n.armed { sp with pair := some (sp.id, es.id) } ::
    born n.id n.armed { es with pair := some (sp.id, es.id) } :: n.cands

theorem mem_register {r : Rules} {n : Node} {sp es x : Cand} (h : x ∈ register r n sp es) :
    x ∈ born n.id n.armed { sp with pair := some (sp.id, es.id) } ::
      born n.id n.armed { es with pair := some (sp.id, es.id) } :: n.cands := by
  unfold register at h; split at h
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  · exact h

/-- Registration retains residents before schedule reapplication: `SPN-23` says an accepted
replay "re-applies its schedule and intent, and re-stages". The hot traversal and shrink still
run over the retained list. This kernel abstracts away staged refusals: refusal here is a no-op,
not a model of `SPN-5` row 29's staging (Staging: "yes").

`DUR-7`: a locked-down node refuses every request. `NCH-30`: one resident Carrier per nonce.
`DUR-11`: "existing and future" — a hot candidate accepted on an armed node is born frozen. -/
@[req "DUR-11"]
def accept (r : Rules) (env : Env) (n : Node) (cid : Nat) (duress : Bool) (E : Wall) (sp es : Cand) :
    Node :=
  if n.lockedDown || n.carriers.any (·.cid == cid) || !pairAdmits r n sp es then n
  else match Mono.deadline env.mono E env.eff with
    | none => n
    | some D =>
      { n with carriers := { cid := cid, duress := duress, relaySenders := [], E := E, D := D,
                             firstSeen := env.eff, spend := sp.id, escape := es.id } :: n.carriers,
               T := shrunkDeadline r env n sp,
               cands := if traverses r env n sp
                        then writeWindows n.selected (shrunkDeadline r env n sp) n.combineSlack
                               (register r n sp es)
                        else register r n sp es }

/-- `DUR-6`: "a sender already counted … MUST be an idempotent no-op". Admitting a relay is an
insertion into a set, so a repeat sender leaves the Carrier's field the very list it was, and
the no-op is the identity rather than a count that happens not to be read. `self` is this node's
own id, which is never inserted: `DUR-5` counts "each distinct peer", and this node is already a
holder "once it has staged the Carrier for propagation (`SPN-32`)", so `holderCount`'s `+ 1` is
the whole of its own membership and a relay carrying this node's id must add nothing. -/
@[req "DUR-6"]
def addSender (self : Nat) (senders : List Nat) (sender : Nat) : List Nat :=
  if sender == self || senders.contains sender then senders else senders ++ [sender]

/-- `NCH-25`: "The store holds at most one partial per `(rung, input, signer)`. A duplicate is an
idempotent `ACCEPTED` and never displaces the first." The insertion into `Cand.heldSigners`,
mirroring `addSender` and differing in exactly one way: there is no self-refusal, because this
node's own signer is a MEMBER of the held set from registration (`SPN-32`, `SPN-36`), where
`DUR-5`'s holder set counts "each distinct peer" and excludes it. -/
@[req "NCH-25"]
def addHeld (held : List Nat) (signer : Nat) : List Nat :=
  if held.contains signer then held else held ++ [signer]

/-- `NCH-25`'s "A duplicate is an idempotent `ACCEPTED` and never displaces the first", read
literally as `addSender_of_counted` reads `DUR-6`'s no-op: a signer already held leaves the set
the very list it was, so a second copy of one partial neither displaces the first nor moves any
count taken over it. -/
@[req "NCH-25"]
theorem addHeld_of_held (held : List Nat) (signer : Nat) (h : signer ∈ held) :
    addHeld held signer = held := by simp [addHeld, h]

/-- The guarded post-validation store, keyed by candidate id and recomputed sighash.

**Boundary hypothesis, not modelled:** `NCH-24` requires, in order, "check wallet equality,
signer equals sender, sighash type; then under the store lock: the candidate exists, else
`UNKNOWN_CANDIDATE`; it is not expired (`expiry < now`, except the delayed-slot exemption of
`SPN-41`), else evict it, refund its unexposed reservation, and answer `UNKNOWN_CANDIDATE`;
the rung is found by txid; the user-signature hash matches; the input and signer are in range;
the signature verifies against this node's own recomputed sighash for that rung and input and
the signer's descriptor key (`CHN-11`); then store it." Authentication alone is not storability:
a naked signer id is not evidence of a valid partial. The guarded insertion assumes those
upstream checks succeeded; this kernel models neither their validation nor their responses.
The delayed-slot exemption stays outside scope, as in `prune`. `Cand.heldSigners` owns the
one-rung, representative-input abstraction.

The map performs the candidate lookup by `cid`; a missing id, a mismatched message or an input
other than 0 leaves possession unchanged. `step` appends exposed authority independently, even on
these failures: a partial that arrived has left its signer whether or not this node stores it.

The guard reads the input because a partial on an unmodelled input is exposed authority but not
modelled possession. That is `Cand.heldSigners`' "input 0 stands for every input", which
`Effect.queuePartial` and `exposedQuorum` share, applied to the store, and `NCH-24`'s "the input and
signer are in range" at the only input this kernel models: the store admits exactly the row
`exposedQuorum` counts, and `released_held_exposed` rests on it. -/
@[req "NCH-24"]
def receivePartial (n : Node) (msg : Sighash) (input signer cid : Nat) : Node :=
  { n with cands := n.cands.map fun c =>
      if c.id == cid && input == 0 && msg == sighash c.tx 0 then
        { c with heldSigners := addHeld c.heldSigners signer } else c }

/-- `DUR-5`'s holder set, counted: "this node once it has staged the Carrier for propagation
(`SPN-32`), plus each distinct peer whose authenticated relay of the same Carrier this node
receives". This node is the `+ 1`; the list holds the peers, and `addSender` is what keeps it a
set of them. One home — `commits` reads it and so does `F65`'s exhibit
(`Exhibits.ReleaseKernel.duplicate_relay_is_one_holder`) — so the count the release gate waits
on has one definition. -/
@[req "DUR-5"]
def holderCount (senders : List Nat) : Nat := senders.length + 1

/-- `DUR-5`: "When the holder set reaches `t`, the node MUST run one pin-uniform holder decision
under a single store lock", on a Carrier `DUR-6` still admits a holder for. The set is read with
this relay already admitted, because the decision runs in the step that receives it. The
condition is named because `DEF-12`'s prohibition is about what keys on it: "every artifact
derived from a holder confirmation MUST key on pin-uniform state, never on the arm bit". One
home — `receipt` branches on it and `Silence.markerOf` reads it — so the marker cannot drift
from the decision. -/
@[req "DUR-5"]
def commits (env : Env) (n : Node) (cid : Nat) (sender : Nat) : Bool :=
  match n.carriers.find? (·.cid == cid) with
  | none => false
  | some k =>
    env.mono.before k.D && env.eff.before k.E &&
      n.t ≤ holderCount (addSender n.id k.relaySenders sender)

/-- `DUR-6`: "A receipt for an intent whose `deadline ≤ mono_now` MUST be ignored; one whose
`expiry ≤ now` MUST answer the fixed 30-second retry (`NCH-36`) and change nothing"; then
`DUR-5`: "When the holder set reaches `t`, the node MUST run one pin-uniform holder decision under
a single store lock". -/
@[req "DUR-6"]
def receipt (env : Env) (n : Node) (cid : Nat) (sender : Nat) : Node :=
  match n.carriers.find? (·.cid == cid) with
  | none => n
  | some k =>
    if !(env.mono.before k.D) || !(env.eff.before k.E) then n
    else
      let k' := { k with relaySenders := addSender n.id k.relaySenders sender }
      if commits env n cid sender then holderDecision env n k'
      else { n with carriers := n.carriers.map fun c => if c.cid == cid then k' else c }

/-- The release loop. `DUR-9`: "a poisoned node MUST release nothing, MUST force the Lockdown
latch through a path that takes no lock". -/
@[req "DUR-8"]
def firePass (r : Rules) (env : Env) (n : Node) : Node × List Effect :=
  if r.poison == .asserted && n.poisoned then ({ n with lockedDown := true }, [])
  else
    let rel := n.cands.filter fun c => due r env c && releaseAuthorized n c && !c.released
    ({ n with cands := n.cands.map fun c =>
        if due r env c && releaseAuthorized n c then { c with released := true } else c },
     rel.map fun c => Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id)

/-- `POL-18`'s "A partial that has left the node is finalizable authority in `t − 1` compromised
hands", counted: the distinct signers whose partial over this candidate's sighash has left its
node, read off the world's exposure. Input 0 stands for every input — the boundary assumption
made visible. This is availability in the world, never possession at this node, and the two are
not the same predicate: `heldQuorum` is what a node finalizes from.

No transition reads it: `packageAccepted` reads `heldQuorum`, and this predicate is exhibit-only
— `ADR-0023` decision 9's retained trap, which `Exhibits.ReleaseKernel.exposure_key_exhibit` is
stated over, with the exhibits that read it beside that one — and the conclusion of
`released_held_exposed`. A cleanup deleting it as unreferenced takes every one of them with
it. -/
@[req "POL-18"]
def exposedQuorum (w : World) (c : Cand) : Bool :=
  w.node.t ≤ ((w.exposure.filter fun (e : Exp) => e.msg == sighash c.tx 0 && e.input == 0).map
    Exp.signer).eraseDups.length

/-- `DUR-28`'s "`≥ t` distinct valid partials on every input", counted over the set the node
finalizes from: `Cand.heldSigners`, which owns what that set is and how it is counted. One
candidate is one rung, so "the highest rung at or below the latch" collapses here.

Quorum alone, which is why the name says quorum and not finalization: `DUR-28` also requires
that "The finalized transaction MUST pass `DUR-23` and `DUR-24` again at its exact vsize", and
that test is `packageAccepted` while `DUR-29`'s re-authorization is `send`'s own.
`packageAccepted` reads it, behind this node's own release;
`Exhibits.ReleaseKernel.receivePartial_admits_peer` and
`Exhibits.ReleaseKernel.exposure_without_receivePartial_is_not_held` read it too. -/
@[req "DUR-28"]
def heldQuorum (t : Nat) (c : Cand) : Bool :=
  t ≤ c.heldSigners.eraseDups.length

/-- `SPN-39`: "assemble the package (`WTC-24`); test it for mempool acceptance" — the candidate
must be due, authorized to release (`DUR-10`), released by this node, and carry a quorum. The
quorum conjunct is `heldQuorum`, the possession `DUR-28` counts, never the world's exposed
authority: a node cannot assemble from partials it was never delivered.
`released_held_exposed` is the bridge back — on every reachable world what this test admits
`exposedQuorum` admits too.

The `released` conjunct is a MODELLING ORDER, not a rule read off the set. `SPN-39` puts
finalization on the fire pass — "On every fire pass, for each due candidate, the node MUST …
finalize" — but `SPN-38` permits a pass that releases nothing: "If `affordable_rungs = 0`,
release nothing and advance no release bookkeeping on this pass." So `released` stands for "a
pass processed this candidate" only inside this kernel's no-quota abstraction, where `firePass`
releases every due candidate. The conjunct reads "this node released the rung being assembled":
`Cand` carries no ladder and the kernel finalizes at `sighash c.tx 0`, so `released` IS
`released_through` at rung 0, and the sentence becomes `released_through ≥ rung` when `DUR-28`'s
latch enters the kernel. The recorded upgrade path is a fire-pass assembly token carrying the
selected rung (`16-open-findings.md`, `F65`). It is not built here, because an `Option Rung`
field in a kernel with no rungs is a boolean in disguise.

`SPN-39` puts the re-check of "the slot, the freeze and the window under the store lock" after
this test and calls THAT "the linearization point between arming and sending"; reading the slot
here as well is modelling slack that refuses earlier, never later, and it grants no authority the
send may trust — `send` reads it again.

The ancestry rule the assembly reads, `WTC-24`'s validation and `WTC-25`'s replacement, is
`Package.validate`, stated over the `WTC-10` snapshot in `Package.lean`, and it is not a conjunct
here for the reason the ladder is not: this transition stands for the whole of `SPN-39`'s
"assemble the package (`WTC-24`); test it for mempool acceptance" as one step whose result is
`packageOk`, and the kernel's chain view is `{mtp, seen}` — no prevout set, no
confirmed-versus-resident distinction, no ancestor graph, none of the facts the rule reads.
`Package.validate`'s admitted verdict is what the assembly step reads before this flag is set. -/
@[req "SPN-39"]
def packageAccepted (r : Rules) (env : Env) (w : World) (cid : Nat) : Node :=
  { w.node with cands := w.node.cands.map fun c =>
      if c.id == cid && due r env c && releaseAuthorized w.node c && c.released &&
          heldQuorum w.node.t c then
        { c with packageOk := true } else c }

/-- `DUR-29`: "re-authorized under the store lock — this Escape still in `selected_escapes` with
`sweep_active` AND its own duress bit set, not frozen, window open — immediately before the
send". The Escape half of that conjunction is `releaseAuthorized` (`DUR-10`), which the send and
`SPN-39`'s package test read exactly as the fire pass does; under the withdrawn value the send
trusts the check `packageAccepted` ran. -/
@[req "DUR-29"]
def send (r : Rules) (env : Env) (n : Node) (cid : Nat) : Node × List Effect :=
  match n.cands.find? (·.id == cid) with
  | none => (n, [])
  | some c =>
    let go := c.packageOk && (r.reauth == .beforeAssembly || (due r env c && releaseAuthorized n c))
    ({ n with cands := n.cands.map fun d =>
        if d.id == cid then { d with packageOk := false, broadcast := d.broadcast || go } else d },
     if go then [Effect.broadcast c.tx.id] else [])

/-- `SPN-33`: "When any transaction settles — seen in the mempool or confirmed … the node MUST
remove from the pending log the settled id, its paired sibling, and every other resident hot
candidate that shares an input with it, and mark the input-conflicting candidates terminal". -/
@[req "SPN-33"]
def settle (env : Env) (n : Node) (tx : Tx) : Node :=
  if !(env.chain.seen.contains tx) then n
  else { n with cands := n.cands.map fun c =>
    if c.tx.id == tx.id then { c with settled := true }
    else if c.hot && conflicts tx c then { c with terminal := true } else c }

/-- `SPN-41`: "prune every candidate whose `expiry < now`". The Escape exemption is outside the
kernel's scope. A terminal candidate is pruned by its expiry like any other, never earlier. -/
@[req "SPN-41"]
def prune (env : Env) (n : Node) : Node :=
  { n with cands := n.cands.filter fun c => env.eff.atOrBefore c.expiry }

/-- `NCH-40` (3): retirement at `mono_now ≥ D`, from the HotClock. Under `byWall` the driver
reads the signed expiry against the wall sample — `DEF-1`'s "pruned intents against the RAW
wall clock" — and no clock type objects, because both sides are wall-domain values. -/
@[req "NCH-35"]
def tick (r : Rules) (env : Env) (n : Node) : Node :=
  { n with carriers := n.carriers.filter fun k =>
      match r.retire with
      | .byMono => env.mono.before k.D
      | .byWall => !(Wall.atOrBefore k.E env.wall) }

def step (r : Rules) (env : Env) (w : World) : Event → World × List Effect
  | .accept cid d E sp es => ({ w with node := accept r env w.node cid d E sp es }, [])
  | .receipt cid s => ({ w with node := receipt env w.node cid s }, [])
  | .firePass =>
    let (n, effs) := firePass r env w.node
    ({ node := n,
       exposure := w.exposure ++ effs.filterMap fun
         | .queuePartial m i h c => some { msg := m, input := i, signer := w.node.id, hot := h, cid := c }
         | .broadcast _ => none }, effs)
  | .packageAccepted c => ({ w with node := packageAccepted r env w c }, [])
  | .send c =>
    let (n, effs) := send r env w.node c
    ({ w with node := n }, effs)
  | .settle tx => ({ w with node := settle env w.node tx }, [])
  | .prune => ({ w with node := prune env w.node }, [])
  | .tick => ({ w with node := tick r env w.node }, [])
  | .panic => ({ w with node := { w.node with poisoned := true } }, [])
  | .adversaryExposes m i s c =>
    ({ w with exposure := w.exposure ++ [{ msg := m, input := i, signer := s, hot := true, cid := c }] }, [])
  | .receivePartial m i s c =>
    ({ node := receivePartial w.node m i s c,
       exposure := w.exposure ++ [{ msg := m, input := i, signer := s, hot := true, cid := c }] }, [])

def run (r : Rules) : World → List (Env × Event) → World × List Effect
  | w, [] => (w, [])
  | w, (env, e) :: rest =>
    let (w', effs) := step r env w e
    let (w'', effs') := run r w' rest
    (w'', effs ++ effs')

/-- Reachable from a world with nothing accepted yet and nothing armed. -/
inductive Reachable (r : Rules) : World → Prop
  | init (n : Node) (h : n.armed = false ∧ n.cands = [] ∧ n.carriers = []) :
      Reachable r { node := n, exposure := [] }
  | next {w : World} (env : Env) (e : Event) : Reachable r w → Reachable r (step r env w e).1

/-- `SPN-30`'s pending log is a projection of the registry: hot, unsettled, not terminal, not
broadcast, `expiry ≥ now` (`SPN-42`). `DEF-5` — a defeated candidate still in `/pending` — is
then the same defect as an unset terminal flag, not a second list to keep in step. -/
@[req "SPN-30"]
def pending (env : Env) (n : Node) : List Nat :=
  (n.cands.filter fun c => c.hot && !c.settled && !c.terminal && !c.broadcast &&
    env.eff.atOrBefore c.expiry).map (·.id)

/-! ## Invariant: an armed node has every hot candidate frozen (`DUR-11`), by induction -/

def Inv (w : World) : Prop := w.node.armed = true → ∀ c ∈ w.node.cands, c.hot = true → c.frozen = true

theorem inv_holderDecision (env : Env) (n : Node) (k : Carrier)
    (h : n.armed = true → ∀ c ∈ n.cands, c.hot = true → c.frozen = true) :
    (holderDecision env n k).armed = true →
      ∀ c ∈ (holderDecision env n k).cands, c.hot = true → c.frozen = true := by
  intro ha c hc hh
  simp only [holderDecision, List.mem_map] at hc ha
  obtain ⟨d, hd, rfl⟩ := hc
  rw [withWindow_hot] at hh
  rw [withWindow_frozen]
  simp only at hh ⊢
  cases hk : k.duress
  · simp [hk] at ha; have := h ha d hd hh; simp [this]
  · simp [hh]

theorem inv_writeWindows (sel : List (Nat × Bool)) (T : Wall) (slack : Secs) (cs : List Cand)
    (h : ∀ c ∈ cs, c.hot = true → c.frozen = true) :
    ∀ c ∈ writeWindows sel T slack cs, c.hot = true → c.frozen = true := by
  intro c hc hh
  simp only [writeWindows, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  rw [withWindow_hot] at hh
  rw [withWindow_frozen]
  exact h d hd hh

theorem inv_accept (r : Rules) (env : Env) (n : Node) (cid : Nat) (d : Bool) (E : Wall)
    (sp es : Cand) (h : n.armed = true → ∀ c ∈ n.cands, c.hot = true → c.frozen = true) :
    (accept r env n cid d E sp es).armed = true →
      ∀ c ∈ (accept r env n cid d E sp es).cands, c.hot = true → c.frozen = true := by
  unfold accept
  split
  · exact h
  · split
    · exact h
    · intro ha c hc hh
      simp only at ha
      have base : ∀ x ∈ register r n sp es,
          x.hot = true → x.frozen = true := by
        intro x hx hxh
        have hx := mem_register hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp only [born] at hxh ⊢; simp [ha, hxh]
        · simp only [born] at hxh ⊢; simp [ha, hxh]
        · exact h ha x hx hxh
      split at hc
      · exact inv_writeWindows _ _ _ _ base c hc hh
      · exact base c hc hh

theorem inv_map_frame (n : Node) (f : Cand → Cand)
    (hf : ∀ c, (f c).hot = c.hot ∧ (f c).frozen = c.frozen)
    (h : n.armed = true → ∀ c ∈ n.cands, c.hot = true → c.frozen = true) :
    n.armed = true → ∀ c ∈ n.cands.map f, c.hot = true → c.frozen = true := by
  intro ha c hc hh
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  rw [(hf d).2]; exact h ha d hd (by rw [← (hf d).1]; exact hh)

/-- `DUR-9`'s atomicity is a theorem, not a parameter: the invariant survives every step because
the holder decision is one write. Split it into open-then-freeze and this fails at the state in
between. -/
@[req "DUR-9"]
theorem inv_step (r : Rules) (env : Env) (w : World) (e : Event) (h : Inv w) :
    Inv (step r env w e).1 := by
  unfold Inv at *
  cases e with
  | accept cid d E sp es => exact inv_accept r env w.node cid d E sp es h
  | receipt cid s =>
    simp only [step, receipt]
    split
    · exact h
    · split
      · exact h
      · split
        · exact inv_holderDecision _ _ _ h
        · exact h
  | firePass =>
    simp only [step, firePass]
    split
    · exact h
    · exact inv_map_frame w.node _ (fun c => by split <;> simp) h
  | packageAccepted c =>
    simp only [step, packageAccepted]
    exact inv_map_frame w.node _ (fun c => by split <;> simp) h
  | send c =>
    simp only [step, send]
    split
    · exact h
    · exact inv_map_frame w.node _ (fun c => by split <;> simp) h
  | settle tx =>
    simp only [step, settle]
    split
    · exact h
    · exact inv_map_frame w.node _ (fun c => by split <;> (try split) <;> simp) h
  | prune =>
    simp only [step, prune]
    intro ha c hc hh
    exact h ha c (List.mem_filter.1 hc).1 hh
  | tick => exact h
  | panic => exact h
  | adversaryExposes m i s c => exact h
  | receivePartial m i s c =>
    simp only [step, receivePartial]
    exact inv_map_frame w.node _ (fun c => by split <;> simp) h

@[req "DUR-11"]
theorem inv_reachable (r : Rules) (w : World) (hr : Reachable r w) : Inv w := by
  induction hr with
  | init n h => intro ha; rw [h.1] at ha; cases ha
  | next env e _ ih => exact inv_step r env _ e ih

/-- `DUR-8`: "a hot partial is released only when the node is NOT armed". For every reachable
world, every rule value, every environment: a fire pass on an armed node queues no hot partial.
Over transitions, not history: an armed node still holds the authority it released before. -/
@[req "DUR-8"]
theorem no_hot_partial_while_armed (r : Rules) (env : Env) (w : World) (hr : Reachable r w)
    (ha : w.node.armed = true) :
    ∀ eff ∈ (step r env w .firePass).2, ∀ m i c, eff ≠ .queuePartial m i true c := by
  have inv := inv_reachable r w hr ha
  intro eff heff m i c heq
  subst heq
  simp only [step, firePass] at heff
  split at heff
  · simp at heff
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true] at heff
    obtain ⟨c, ⟨hc, hdue, _⟩, hq⟩ := heff
    simp only [Effect.queuePartial.injEq] at hq
    obtain ⟨_, _, hhot, _⟩ := hq
    have hfr := inv c hc hhot
    simp [due, hhot, hfr] at hdue

/-- `DUR-10`: `active` "once set it is never cleared". -/
@[req "DUR-10"]
theorem armed_sticky (r : Rules) (env : Env) (w : World) (e : Event) (ha : w.node.armed = true) :
    (step r env w e).1.node.armed = true := by
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept]
    split
    · exact ha
    · split
      · exact ha
      · exact ha
  | receipt cid s =>
    simp only [step, receipt]
    split
    · exact ha
    · split
      · exact ha
      · split
        · simp [holderDecision, ha]
        · exact ha
  | firePass =>
    simp only [step, firePass]
    split <;> exact ha
  | send c =>
    simp only [step, send]
    split <;> exact ha
  | settle tx =>
    simp only [step, settle]
    split <;> exact ha
  | packageAccepted c => exact ha
  | prune => exact ha
  | tick => exact ha
  | panic => exact ha
  | adversaryExposes m i s c => exact ha
  | receivePartial m i s c => exact ha

/-! ## Immutable `D` (`NCH-33`): nothing after acceptance writes it -/

/-- For every event and environment: a Carrier resident after the step either was resident before
with the same `D`, or the event is the acceptance that created it. Retirement removes; nothing
moves `D`. Per Carrier instance: a later, separately accepted nonce may carry its own `D`. -/
@[req "NCH-33"]
theorem D_immutable (r : Rules) (env : Env) (w : World) (e : Event) :
    ∀ k' ∈ (step r env w e).1.node.carriers,
      (∃ k ∈ w.node.carriers, k.cid = k'.cid ∧ k.D = k'.D) ∨
      ∃ cid d E sp es, e = .accept cid d E sp es ∧ k'.cid = cid := by
  intro k' hk
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept] at hk
    split at hk
    · exact .inl ⟨k', hk, rfl, rfl⟩
    · split at hk
      · exact .inl ⟨k', hk, rfl, rfl⟩
      · simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact .inr ⟨cid, d, E, sp, es, rfl, rfl⟩
        · exact .inl ⟨k', hk, rfl, rfl⟩
  | receipt cid s =>
    simp only [step, receipt] at hk
    split at hk
    · exact .inl ⟨k', hk, rfl, rfl⟩
    · rename_i k0 hf
      split at hk
      · exact .inl ⟨k', hk, rfl, rfl⟩
      · split at hk
        · simp only [holderDecision] at hk
          exact .inl ⟨k', (List.mem_filter.1 hk).1, rfl, rfl⟩
        · simp only [List.mem_map] at hk
          obtain ⟨k, hkm, hke⟩ := hk
          left
          split at hke
          · subst hke; exact ⟨k0, List.mem_of_find?_eq_some hf, rfl, rfl⟩
          · subst hke; exact ⟨k, hkm, rfl, rfl⟩
  | firePass =>
    simp only [step, firePass] at hk
    split at hk <;> exact .inl ⟨k', hk, rfl, rfl⟩
  | packageAccepted c => exact .inl ⟨k', hk, rfl, rfl⟩
  | send c =>
    simp only [step, send] at hk
    split at hk <;> exact .inl ⟨k', hk, rfl, rfl⟩
  | settle tx =>
    simp only [step, settle] at hk
    split at hk <;> exact .inl ⟨k', hk, rfl, rfl⟩
  | prune => exact .inl ⟨k', hk, rfl, rfl⟩
  | tick =>
    simp only [step, tick] at hk
    exact .inl ⟨k', (List.mem_filter.1 hk).1, rfl, rfl⟩
  | panic => exact .inl ⟨k', hk, rfl, rfl⟩
  | adversaryExposes m i s c => exact .inl ⟨k', hk, rfl, rfl⟩
  | receivePartial m i s c => exact .inl ⟨k', hk, rfl, rfl⟩

/-! ## Exposure only grows (`POL-18`) -/

/-- `POL-18`: "A partial that has left the node is finalizable authority in `t − 1` compromised
hands". No step removes an entry: settlement, pruning, poison, arming and retirement leave the
history as it was. Membership, not a container: a `List` read extensionally. -/
@[req "POL-18"]
theorem exposure_monotone (r : Rules) (env : Env) (w : World) (e : Event) :
    ∀ x ∈ w.exposure, x ∈ (step r env w e).1.exposure := by
  intro x hx
  cases e <;> simp [step] <;> first | exact hx | (split <;> simp [hx]) | skip
  all_goals (try simp_all)

/-! ## Terminal candidates (`SPN-33`): marked at settlement, sticky, never due -/

/-- Settlement of a transaction the chain view shows (`hs`) marks every resident hot candidate over
a different transaction that shares an input with it terminal, so the flag is never vacuous. A
candidate whose own transaction settled is marked settled instead. -/
@[req "SPN-33"]
theorem settle_marks_conflicts (env : Env) (n : Node) (tx : Tx) (hs : env.chain.seen.contains tx = true) :
    ∀ c ∈ n.cands, c.hot = true → c.tx.id ≠ tx.id → conflicts tx c = true →
      ∃ c' ∈ (settle env n tx).cands, c'.id = c.id ∧ c'.terminal = true := by
  intro c hc hh hid hcf
  have hne : (c.tx.id == tx.id) = false := by simpa using hid
  simp only [settle, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by simp [hne, hh, hcf], by simp [hne, hh, hcf]⟩

/-- For every environment, under the terminal flag: a terminal candidate is never due. -/
@[req "SPN-33"]
theorem terminal_never_due (r : Rules) (hr : r.defeat = .terminalFlag) (env : Env) (c : Cand)
    (h : c.terminal = true) : due r env c = false := by simp [due, hr, h]

/-- Registration's residency shape under the repaired rule. No common-expiry premise is needed:
unequal-expiry pruning may leave one member, and `pairAdmits` still refuses that request. -/
theorem pairAdmits_shape {r : Rules} (hr : r.registration = .preserve) {n : Node} {sp es : Cand}
    (ha : pairAdmits r n sp es = true) :
    sp.id ≠ es.id ∧ n.cands.any (·.id == sp.id) = n.cands.any (·.id == es.id) := by
  simp [pairAdmits, hr] at ha
  exact ⟨ha.1.1, ha.1.2⟩

/-- Registration never duplicates a resident id, including identical records. -/
@[req "SPN-32"]
theorem register_nodup {r : Rules} (hr : r.registration = .preserve) {n : Node} {sp es : Cand}
    (ha : pairAdmits r n sp es = true) (hn : (n.cands.map Cand.id).Nodup) :
    ((register r n sp es).map Cand.id).Nodup := by
  obtain ⟨hne, heq⟩ := pairAdmits_shape hr ha
  unfold register
  split
  · exact hn
  · rename_i hab
    have hs : n.cands.any (·.id == sp.id) = false := by simpa [hr] using hab
    have he : n.cands.any (·.id == es.id) = false := by rw [← heq]; exact hs
    have absent (i : Nat) (hi : n.cands.any (·.id == i) = false) : i ∉ n.cands.map Cand.id := by
      intro hm
      obtain ⟨c, hc, hid⟩ := List.mem_map.1 hm
      have ht : n.cands.any (·.id == i) = true := List.any_eq_true.2 ⟨c, hc, by simp [hid]⟩
      rw [hi] at ht
      cases ht
    simp only [List.map_cons, born, List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨hne, absent _ hs⟩, ⟨absent _ he, hn⟩⟩

/-- An id-preserving map preserves duplicate-free resident ids. -/
theorem ids_map (cs : List Cand) (f : Cand → Cand) (hf : ∀ c, (f c).id = c.id) :
    (cs.map f).map Cand.id = cs.map Cand.id := by simp [List.map_map, Function.comp_def, hf]

theorem ids_nodup_step {r : Rules} (hr : r.registration = .preserve)
    (env : Env) (w : World) (e : Event) (hn : (w.node.cands.map Cand.id).Nodup) :
    ((step r env w e).1.node.cands.map Cand.id).Nodup := by
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept]
    split
    · exact hn
    · rename_i hg
      have ha : pairAdmits r w.node sp es = true := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true'] at hg
        simpa using hg.2
      split
      · exact hn
      · have hb := register_nodup hr ha hn
        split
        · simpa only [writeWindows, ids_map _ _ (withWindow_id _ _ _)] using hb
        · exact hb
  | receipt cid s =>
    simp only [step, receipt]
    split
    · exact hn
    · split
      · exact hn
      · split
        · simp only [holderDecision]
          rw [ids_map _ _ (fun c => by rw [withWindow_id])]; exact hn
        · exact hn
  | firePass =>
    simp only [step, firePass]
    split
    · exact hn
    · rw [ids_map _ _ (fun c => by split <;> rfl)]; exact hn
  | packageAccepted c =>
    simp only [step, packageAccepted]
    rw [ids_map _ _ (fun c => by split <;> rfl)]; exact hn
  | send c =>
    simp only [step, send]
    split
    · exact hn
    · rw [ids_map _ _ (fun c => by split <;> rfl)]; exact hn
  | settle tx =>
    simp only [step, settle]
    split
    · exact hn
    · rw [ids_map _ _ (fun c => by split <;> (try split) <;> rfl)]; exact hn
  | prune =>
    exact List.Nodup.sublist (List.Sublist.map Cand.id (List.filter_sublist)) hn
  | tick => exact hn
  | panic => exact hn
  | adversaryExposes m i s c => exact hn
  | receivePartial m i s c =>
    simp only [step, receivePartial]
    rw [ids_map _ _ (fun c => by split <;> rfl)]; exact hn

/-- On every reachable world under the repaired registration rule, the LIST of resident ids is
free of duplicates. This is stronger than equality of records under equal ids. -/
@[req "SPN-32"]
theorem ids_nodup {r : Rules} (hr : r.registration = .preserve) {w : World} (hw : Reachable r w) :
    (w.node.cands.map Cand.id).Nodup := by
  induction hw with
  | init n h => simp [h.2.1]
  | next env e _ ih => exact ids_nodup_step hr env _ e ih

/-- Each registered record is retained verbatim or has an id absent before registration. -/
theorem register_origin {r : Rules} (hr : r.registration = .preserve) {n : Node} {sp es c : Cand}
    (ha : pairAdmits r n sp es = true) (hc : c ∈ register r n sp es) :
    c ∈ n.cands ∨ ∀ x ∈ n.cands, x.id ≠ c.id := by
  obtain ⟨_, heq⟩ := pairAdmits_shape hr ha
  unfold register at hc
  split at hc
  · exact .inl hc
  · rename_i hab
    have hs : n.cands.any (·.id == sp.id) = false := by simpa [hr] using hab
    have he : n.cands.any (·.id == es.id) = false := by rw [← heq]; exact hs
    have absent (i : Nat) (hi : n.cands.any (·.id == i) = false) : ∀ x ∈ n.cands, x.id ≠ i := by
      intro x hx hid
      have ht : n.cands.any (·.id == i) = true :=
        List.any_eq_true.2 ⟨x, hx, by simp [hid]⟩
      rw [hi] at ht
      cases ht
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inr (absent _ hs)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inr (absent _ he)
    · exact .inl hc

/-- A nonterminal candidate after a step has a nonterminal predecessor, or its id was absent
before the step. Acceptance must establish absence; resident ids have no birth exception. -/
@[req "SPN-33"]
theorem nonterminal_origin (r : Rules) (hr : r.registration = .preserve) (env : Env) (w : World) (e : Event) :
    ∀ c' ∈ (step r env w e).1.node.cands, c'.terminal = false →
      (∃ c ∈ w.node.cands, c.id = c'.id ∧ c.terminal = false) ∨
      (∀ c ∈ w.node.cands, c.id ≠ c'.id) := by
  intro c' hc ht
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept] at hc
    split at hc
    · exact .inl ⟨c', hc, rfl, ht⟩
    · rename_i hg
      have ha : pairAdmits r w.node sp es = true := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true'] at hg
        simpa using hg.2
      split at hc
      · exact .inl ⟨c', hc, rfl, ht⟩
      · have base : ∀ x ∈ register r w.node sp es, x.terminal = false →
            (∃ c ∈ w.node.cands, c.id = x.id ∧ c.terminal = false) ∨
            (∀ c ∈ w.node.cands, c.id ≠ x.id) := by
          intro x hx ht
          rcases register_origin hr ha hx with hx | hx
          · exact .inl ⟨x, hx, rfl, ht⟩
          · exact .inr hx
        split at hc
        · simp only [writeWindows, List.mem_map] at hc
          obtain ⟨x, hx, rfl⟩ := hc
          rw [withWindow_terminal] at ht
          simpa only [withWindow_id] using base x hx ht
        · exact base c' hc ht
  | receipt cid s =>
    simp only [step, receipt] at hc
    split at hc
    · exact .inl ⟨c', hc, rfl, ht⟩
    · split at hc
      · exact .inl ⟨c', hc, rfl, ht⟩
      · split at hc
        · simp only [holderDecision, List.mem_map] at hc
          obtain ⟨c, hcm, rfl⟩ := hc
          rw [withWindow_terminal] at ht
          refine .inl ⟨c, hcm, ?_, ht⟩
          rw [withWindow_id]
        · exact .inl ⟨c', hc, rfl, ht⟩
  | firePass =>
    simp only [step, firePass] at hc
    split at hc
    · exact .inl ⟨c', hc, rfl, ht⟩
    · simp only [List.mem_map] at hc
      obtain ⟨c, hcm, hce⟩ := hc
      left; refine ⟨c, hcm, ?_, ?_⟩ <;> (split at hce <;> subst hce <;> simp_all)
  | packageAccepted x =>
    simp only [step, packageAccepted, List.mem_map] at hc
    obtain ⟨c, hcm, hce⟩ := hc
    left; refine ⟨c, hcm, ?_, ?_⟩ <;> (split at hce <;> subst hce <;> simp_all)
  | send x =>
    simp only [step, send] at hc
    split at hc
    · exact .inl ⟨c', hc, rfl, ht⟩
    · simp only [List.mem_map] at hc
      obtain ⟨c, hcm, hce⟩ := hc
      left; refine ⟨c, hcm, ?_, ?_⟩ <;> (split at hce <;> subst hce <;> simp_all)
  | settle tx =>
    simp only [step, settle] at hc
    split at hc
    · exact .inl ⟨c', hc, rfl, ht⟩
    · simp only [List.mem_map] at hc
      obtain ⟨c, hcm, hce⟩ := hc
      left; refine ⟨c, hcm, ?_, ?_⟩ <;> (split at hce <;> (try split at hce) <;> subst hce <;> simp_all)
  | prune =>
    simp only [step, prune] at hc
    exact .inl ⟨c', (List.mem_filter.1 hc).1, rfl, ht⟩
  | tick => exact .inl ⟨c', hc, rfl, ht⟩
  | panic => exact .inl ⟨c', hc, rfl, ht⟩
  | adversaryExposes m i s c => exact .inl ⟨c', hc, rfl, ht⟩
  | receivePartial m i s cid =>
    simp only [step, receivePartial, List.mem_map] at hc
    obtain ⟨c, hcm, hce⟩ := hc
    left; refine ⟨c, hcm, ?_, ?_⟩ <;> (split at hce <;> subst hce <;> simp_all)

theorem eq_of_mem_ids_nodup {cs : List Cand} (hn : (cs.map Cand.id).Nodup)
    {a b : Cand} (ha : a ∈ cs) (hb : b ∈ cs) (he : a.id = b.id) : a = b := by
  induction cs with
  | nil => cases ha
  | cons c cs ih =>
    obtain ⟨hnc, hns⟩ := List.nodup_cons.1 hn
    rcases List.mem_cons.1 ha with hac | hat
    · subst a
      rcases List.mem_cons.1 hb with hbc | hbt
      · exact hbc.symm
      · exact False.elim (hnc (List.mem_map.2 ⟨b, hbt, he.symm⟩))
    · rcases List.mem_cons.1 hb with hbc | hbt
      · subst b
        exact False.elim (hnc (List.mem_map.2 ⟨a, hat, he⟩))
      · exact ih hns hat hbt

/-- On reachable worlds under repaired registration, an id terminal before ANY step cannot
name a nonterminal resident after it. Pruning may remove it; acceptance cannot rebirth it. -/
@[req "SPN-33"]
theorem terminal_sticky (r : Rules) (hr : r.registration = .preserve) (env : Env)
    (w : World) (hw : Reachable r w) (e : Event) (c : Cand)
    (hc : c ∈ w.node.cands) (ht : c.terminal = true) :
    ∀ c' ∈ (step r env w e).1.node.cands, c'.id = c.id → c'.terminal = true := by
  intro c' hc' hid
  cases hnt : c'.terminal with
  | true => rfl
  | false =>
    rcases nonterminal_origin r hr env w e c' hc' hnt with ⟨x, hx, hxi, hxt⟩ | hab
    · have hxc := eq_of_mem_ids_nodup (ids_nodup hr hw) hx hc (hxi.trans hid)
      subst x
      rw [ht] at hxt
      cases hxt
    · exact False.elim (hab c hc hid.symm)

/-! ## Poison (`DUR-9`): a state bit the fire pass reads -/

/-- For every rule value with the gate asserted, every environment and world: a poisoned node's
fire pass releases nothing and latches Lockdown. The transition exists and emits nothing, so
`DEF-4`'s accident — fail-closed by lock order alone — has a place to be wrong. -/
@[req "DUR-9"]
theorem poisoned_releases_nothing (r : Rules) (hr : r.poison = .asserted) (env : Env) (w : World)
    (hp : w.node.poisoned = true) :
    (step r env w .firePass).2 = [] ∧ (step r env w .firePass).1.node.lockedDown = true := by
  simp [step, firePass, hr, hp]

/-- `DUR-5`: "Receiving a peer's relay proves the peer received and processed the Carrier, not
that it froze or signed": a receipt adds nothing to the exposure. -/
@[req "DUR-5"]
theorem receipt_exposes_nothing (r : Rules) (env : Env) (w : World) (cid sender : Nat) :
    (step r env w (.receipt cid sender)).1.exposure = w.exposure := by
  simp [step]

/-! ## The holder set (`DUR-5`, `DUR-6`): a relay already counted moves nothing -/

/-- `DUR-6`: "a sender already counted … MUST be an idempotent no-op". Admission is a set
insertion, so the repeat leaves the Carrier's holder set the list it already was. A relay
carrying this node's own id is the same no-op, because `DUR-5` counts each distinct PEER and
this node is already the `+ 1`. -/
@[req "DUR-6"]
theorem addSender_of_counted (self : Nat) (senders : List Nat) (sender : Nat)
    (h : sender = self ∨ sender ∈ senders) : addSender self senders sender = senders := by
  rcases h with rfl | h
  · simp [addSender]
  · simp [addSender, h]

/-- And therefore nothing the release gate waits on moves: the commit test such a relay runs is
the one the Carrier's own holder set already answered. A count bumped per receipt answers a
larger one, which is `F65` — one peer relaying twice reaches `t` and opens `DUR-8`'s gate a
relay early. -/
@[req "DUR-6"]
theorem commits_of_counted_sender (env : Env) (n : Node) (cid sender : Nat) (k : Carrier)
    (hf : n.carriers.find? (·.cid == cid) = some k)
    (h : sender = n.id ∨ sender ∈ k.relaySenders) :
    commits env n cid sender =
      (env.mono.before k.D && env.eff.before k.E && n.t ≤ holderCount k.relaySenders) := by
  simp [commits, hf, addSender_of_counted _ _ _ h]

/-- The other half of `DUR-5`'s "each distinct peer": a relay from a peer this node has not
heard from adds exactly one holder. -/
@[req "DUR-5"]
theorem holderCount_addSender_of_new (self : Nat) (senders : List Nat) (sender : Nat)
    (hself : sender ≠ self) (h : sender ∉ senders) :
    holderCount (addSender self senders sender) = holderCount senders + 1 := by
  simp [holderCount, addSender, h, hself]

/-- `addSender` keeps the holder set a set. This is the step; `relaySenders_nodup` is the
statement about reachable worlds that makes `holderCount`'s `length` a count of distinct peers
rather than of relays. -/
@[req "DUR-5"]
theorem addSender_nodup (self : Nat) (senders : List Nat) (sender : Nat)
    (hn : senders.Nodup) : (addSender self senders sender).Nodup := by
  unfold addSender
  split
  · exact hn
  · rename_i hne
    have hns : sender ∉ senders := by
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq,
        not_or] at hne
      exact hne.2
    simp only [List.nodup_append]
    refine ⟨hn, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro heq
    exact hns (heq ▸ ha)

/-- For every event: a Carrier resident after the step carries a duplicate-free holder set if
every Carrier resident before it did. `accept` prepends one whose set is `[]`, `receipt` maps
`addSender` over the named one, the holder decision and the retirement driver only filter, and
no other event touches the list. -/
@[req "DUR-5"]
theorem relaySenders_nodup_step (r : Rules) (env : Env) (w : World) (e : Event)
    (h : ∀ k ∈ w.node.carriers, k.relaySenders.Nodup) :
    ∀ k ∈ (step r env w e).1.node.carriers, k.relaySenders.Nodup := by
  intro k' hk
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept] at hk
    split at hk
    · exact h k' hk
    · split at hk
      · exact h k' hk
      · simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp
        · exact h k' hk
  | receipt cid s =>
    simp only [step, receipt] at hk
    split at hk
    · exact h k' hk
    · rename_i k0 hf
      split at hk
      · exact h k' hk
      · split at hk
        · simp only [holderDecision] at hk
          exact h k' (List.mem_filter.1 hk).1
        · simp only [List.mem_map] at hk
          obtain ⟨k1, hkm, hke⟩ := hk
          split at hke
          · subst hke
            exact addSender_nodup _ _ _ (h k0 (List.mem_of_find?_eq_some hf))
          · subst hke; exact h k1 hkm
  | firePass =>
    simp only [step, firePass] at hk
    split at hk <;> exact h k' hk
  | packageAccepted c => exact h k' hk
  | send c =>
    simp only [step, send] at hk
    split at hk <;> exact h k' hk
  | settle tx =>
    simp only [step, settle] at hk
    split at hk <;> exact h k' hk
  | prune => exact h k' hk
  | tick =>
    simp only [step, tick] at hk
    exact h k' (List.mem_filter.1 hk).1
  | panic => exact h k' hk
  | adversaryExposes m i sg c => exact h k' hk
  | receivePartial m i sg c => exact h k' hk

/-- `DUR-5` counts "each distinct peer", and on every reachable world that is what
`holderCount` counts: the holder set of every resident Carrier is duplicate-free, so its
`length` is a number of peers and not a number of relays. Without this the repair of `F65`
would be `addSender` guarding one road into the field while `holderCount` trusted every
road. -/
@[req "DUR-5"]
theorem relaySenders_nodup (r : Rules) (w : World) (hr : Reachable r w) :
    ∀ k ∈ w.node.carriers, k.relaySenders.Nodup := by
  induction hr with
  | init n h => intro k hk; rw [h.2.2] at hk; cases hk
  | next env e _ ih => exact relaySenders_nodup_step r env _ e ih

/-! ## Possession is exposed authority on reachable worlds (`DUR-28`, `POL-18`) -/

/-- `Node.id` has no writer: every event leaves it as it was, so "this node" names one signer
over a whole run. -/
theorem step_id (r : Rules) (env : Env) (w : World) (e : Event) :
    (step r env w e).1.node.id = w.node.id := by
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept]
    split
    · rfl
    · split <;> rfl
  | receipt cid s =>
    simp only [step, receipt]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | firePass => simp only [step, firePass]; split <;> rfl
  | send c => simp only [step, send]; split <;> rfl
  | settle tx => simp only [step, settle]; split <;> rfl
  | packageAccepted c => rfl
  | prune => rfl
  | tick => rfl
  | panic => rfl
  | adversaryExposes m i s c => rfl
  | receivePartial m i s c => rfl

/-- One candidate's held set read against an exposure `xs`: every held signer has an input-0 row
on the candidate's sighash, except this node's own partial before it is released. -/
def HeldExposed (xs : List Exp) (self : Nat) (c : Cand) : Prop :=
  ∀ s ∈ c.heldSigners, (s ≠ self ∨ c.released = true) →
    ∃ e ∈ xs, e.msg = sighash c.tx 0 ∧ e.input = 0 ∧ e.signer = s

/-- It reads the transaction, the held set and `released` alone, and a longer exposure keeps it. -/
theorem HeldExposed.transfer {xs xs' : List Exp} {self : Nat} {c c' : Cand}
    (h : HeldExposed xs self c) (hx : ∀ x ∈ xs, x ∈ xs') (htx : c'.tx = c.tx)
    (hh : c'.heldSigners = c.heldSigners) (hr : c'.released = c.released) :
    HeldExposed xs' self c' := by
  intro s hs hor
  rw [hh] at hs
  rw [hr] at hor
  obtain ⟨e, he, hm, hi, hsg⟩ := h s hs hor
  exact ⟨e, hx e he, by rw [htx]; exact hm, hi, hsg⟩

/-- `born`'s sanitization: the held set is `[self]` and nothing is released, so there is nothing
to find in any exposure. -/
theorem heldExposed_born (xs : List Exp) (self : Nat) (armed : Bool) (c : Cand) :
    HeldExposed xs self (born self armed c) := by
  intro s hs hor
  simp only [born, List.mem_singleton] at hs hor
  subst hs
  simp at hor

theorem mem_addHeld {held : List Nat} {signer x : Nat} :
    x ∈ addHeld held signer ↔ x ∈ held ∨ x = signer := by
  unfold addHeld
  split
  · rename_i h
    simp only [List.contains_iff_mem] at h
    exact ⟨.inl, fun hx => hx.elim id fun hx => hx ▸ h⟩
  · simp

/-- For every event: every resident candidate keeps its held set exposed if every one did before.
`born` resets the set to `[self]` and clears `released`; `receivePartial` inserts a signer only
when the input is 0 and the message is `sighash c.tx 0`, and the same step appends exactly that
row; `firePass` sets `released` only on a candidate whose own row it appends in the same step, or
that was already released; every other event leaves the three fields alone, and the exposure only
grows (`exposure_monotone`). -/
theorem heldExposed_step (r : Rules) (env : Env) (w : World) (e : Event)
    (h : ∀ c ∈ w.node.cands, HeldExposed w.exposure w.node.id c) :
    ∀ c ∈ (step r env w e).1.node.cands,
      HeldExposed (step r env w e).1.exposure (step r env w e).1.node.id c := by
  rw [step_id]
  have old : ∀ c ∈ w.node.cands, HeldExposed (step r env w e).1.exposure w.node.id c :=
    fun c hc => (h c hc).transfer (exposure_monotone r env w e) rfl rfl rfl
  intro c' hc'
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept] at hc'
    split at hc'
    · exact old c' hc'
    · split at hc'
      · exact old c' hc'
      · have base : ∀ x ∈ register r w.node sp es, HeldExposed w.exposure w.node.id x := by
          intro x hx
          have hx := mem_register hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact heldExposed_born _ _ _ _
          · exact heldExposed_born _ _ _ _
          · exact h x hx
        split at hc'
        · simp only [writeWindows, List.mem_map] at hc'
          obtain ⟨x, hx, rfl⟩ := hc'
          exact (base x hx).transfer (fun _ hy => hy) (withWindow_tx _ _ _ _)
            (withWindow_held _ _ _ _) (withWindow_released _ _ _ _)
        · exact base c' hc'
  | receipt cid s =>
    simp only [step, receipt] at hc'
    split at hc'
    · exact old c' hc'
    · split at hc'
      · exact old c' hc'
      · split at hc'
        · simp only [holderDecision, List.mem_map] at hc'
          obtain ⟨x, hx, rfl⟩ := hc'
          exact (old x hx).transfer (fun _ hy => hy) (withWindow_tx _ _ _ _)
            (withWindow_held _ _ _ _) (withWindow_released _ _ _ _)
        · exact old c' hc'
  | firePass =>
    by_cases hp : (r.poison == .asserted && w.node.poisoned) = true
    · simp only [step, firePass, hp, if_true] at hc'
      exact old c' hc'
    · have hrow : ∀ c ∈ w.node.cands,
          (due r env c && releaseAuthorized w.node c && !c.released) = true →
          ∃ x ∈ (step r env w .firePass).1.exposure,
            x.msg = sighash c.tx 0 ∧ x.input = 0 ∧ x.signer = w.node.id := by
        intro c hc hsel
        refine ⟨{ msg := sighash c.tx 0, input := 0, signer := w.node.id, hot := c.hot,
                  cid := c.id }, ?_, rfl, rfl, rfl⟩
        simp only [step, firePass, hp, Bool.false_eq_true, if_false]
        exact List.mem_append_right _ (List.mem_filterMap.2
          ⟨_, List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hsel⟩, rfl⟩, rfl⟩)
      simp only [step, firePass, hp, Bool.false_eq_true, if_false, List.mem_map] at hc'
      obtain ⟨c, hc, rfl⟩ := hc'
      split
      · rename_i hd
        intro s hs hor
        by_cases hcr : c.released = true
        · exact old c hc s hs (.inr hcr)
        · by_cases hs' : s = w.node.id
          · subst hs'
            exact hrow c hc (by simp [hd, hcr])
          · exact old c hc s hs (.inl hs')
      · exact old c hc
  | packageAccepted x =>
    simp only [step, packageAccepted, List.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    split <;> exact old c hc
  | send x =>
    simp only [step, send] at hc'
    split at hc'
    · exact old c' hc'
    · simp only [List.mem_map] at hc'
      obtain ⟨c, hc, rfl⟩ := hc'
      split <;> exact old c hc
  | settle tx =>
    simp only [step, settle] at hc'
    split at hc'
    · exact old c' hc'
    · simp only [List.mem_map] at hc'
      obtain ⟨c, hc, rfl⟩ := hc'
      split
      · exact old c hc
      · split <;> exact old c hc
  | prune =>
    simp only [step, prune] at hc'
    exact old c' (List.mem_filter.1 hc').1
  | tick => exact old c' hc'
  | panic => exact old c' hc'
  | adversaryExposes m i s x => exact old c' hc'
  | receivePartial m i s x =>
    simp only [step, receivePartial, List.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    split
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      intro s' hs' hor
      rcases mem_addHeld.1 hs' with hs' | rfl
      · exact old c hc s' hs' hor
      · exact ⟨{ msg := m, input := i, signer := s', hot := true, cid := x }, by simp [step],
          hg.2, hg.1.2, rfl⟩
    · exact old c hc

/-- On every reachable world every resident candidate's held set is exposed, bar this node's own
unreleased partial. -/
theorem heldExposed_reachable (r : Rules) (w : World) (hr : Reachable r w) :
    ∀ c ∈ w.node.cands, HeldExposed w.exposure w.node.id c := by
  induction hr with
  | init n h => intro c hc; rw [h.2.1] at hc; cases hc
  | next env e _ ih => exact heldExposed_step r env _ e ih

/-- `eraseDups` leaves no duplicate. Core Lean states its membership and not this. -/
theorem nodup_eraseDups (l : List Nat) : l.eraseDups.Nodup := by
  suffices ∀ n (l : List Nat), l.length ≤ n → l.eraseDups.Nodup from this _ l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => exact List.nodup_nil
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => exact List.nodup_nil
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨?_, ih _ (Nat.le_trans (List.length_filter_le _ _) ?_)⟩
      · simp [List.mem_eraseDups, List.mem_filter]
      · simp only [List.length_cons] at hl; omega

/-- A duplicate-free list inside another is no longer than it. -/
theorem length_le_of_nodup_subset :
    ∀ {l m : List Nat}, l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, m, hn, hs => by
    obtain ⟨ha, hn⟩ := List.nodup_cons.1 hn
    have ham : a ∈ m := hs a (by simp)
    have hle := length_le_of_nodup_subset hn (m := m.erase a) fun x hx =>
      (List.mem_erase_of_ne fun hxa => ha (by rw [← hxa]; exact hx)).2 (hs x (List.mem_cons_of_mem a hx))
    rw [List.length_erase_of_mem ham] at hle
    have hpos := List.length_pos_of_mem ham
    simp only [List.length_cons]
    omega

/-- The bridge from node-local possession to world-level availability: on every reachable world,
a resident candidate this node has released and whose held set reaches `t` has `t` distinct
signers in the world's exposed authority. So `packageAccepted`'s switch from `exposedQuorum` to
`heldQuorum` narrows what a node may assemble and never widens it.

True only over `Reachable`, and false for a hand-built `World`, which can hold a signer with no
exposure row. What rules that out is `born`'s sanitization — `heldSigners := [self]`,
`released := false` — and `step`'s unconditional exposure append on every `receivePartial`, with
the store guard admitting only the input-0 partial on `sighash c.tx 0` that the append records
(`heldExposed_step`).

One-directional: exposed authority this node never received does not become possession, and
`Exhibits.ReleaseKernel.exposed_not_held_cannot_assemble` is that counterexample to the converse.
Without `released` it fails too — own withheld possession plus a received peer is held quorum with
nothing of this node's exposed (`Exhibits.ReleaseKernel.receivePartial_admits_peer`) — so the two
predicates remain incomparable in general.

Tagged `DUR-28` and not `POL-18` because the sentence it states is `DUR-28`'s: "The partials
counted are the finalizing node's *Held partial* set", which it cites as `SPN-36`'s "the partials
received per `(input, signer)`" — every one of them received, so every one exposed by its signer,
this node's own included once it is released. `POL-18`'s "A partial that has left the node is
finalizable authority" runs the other way, from exposure to finalizability, and this theorem does
not state it. -/
@[req "DUR-28"]
theorem released_held_exposed (r : Rules) (w : World) (hr : Reachable r w) (c : Cand)
    (hc : c ∈ w.node.cands) (hrel : c.released = true) (hq : heldQuorum w.node.t c = true) :
    exposedQuorum w c = true := by
  have hi := heldExposed_reachable r w hr c hc
  simp only [heldQuorum, decide_eq_true_eq] at hq
  simp only [exposedQuorum, decide_eq_true_eq]
  refine Nat.le_trans hq (length_le_of_nodup_subset (nodup_eraseDups _) fun s hs => ?_)
  rw [List.mem_eraseDups] at hs ⊢
  obtain ⟨e, he, hm, hi0, rfl⟩ := hi s hs (.inr hrel)
  exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [hm, hi0]⟩, rfl⟩

/-! ## The overlay (`DUR-10`, `DUR-13`, `DUR-14`, `DUR-20`) -/

/-- `DUR-10`: "`sweep_active` is a single overlay flag that a duress Carrier sets for the whole
node … it alone cannot make a normal-PIN pair's Escape inert". Once set it stays set. -/
@[req "DUR-10"]
theorem sweepActive_sticky (r : Rules) (env : Env) (w : World) (e : Event)
    (hs : w.node.sweepActive = true) : (step r env w e).1.node.sweepActive = true := by
  cases e with
  | accept cid d E sp es =>
    simp only [step, accept]
    split; · exact hs
    split; · exact hs
    exact hs
  | receipt cid s =>
    simp only [step, receipt]
    split; · exact hs
    split; · exact hs
    split
    · simp [holderDecision, hs]
    · exact hs
  | firePass => simp only [step, firePass]; split <;> exact hs
  | send c => simp only [step, send]; split <;> exact hs
  | settle tx => simp only [step, settle]; split <;> exact hs
  | packageAccepted c => exact hs
  | prune => exact hs
  | tick => exact hs
  | panic => exact hs
  | adversaryExposes m i s c => exact hs
  | receivePartial m i s c => exact hs

/-- `DUR-10`: "Release of an entry requires BOTH `sweep_active` AND that entry's own duress
bit". A normal-PIN entry — bit clear — is never released, whatever `sweep_active` is: `F54`'s
row, where one flag for the node made another Carrier's arming release it. -/
@[req "DUR-10"]
theorem normal_entry_never_released (n : Node) (c : Cand) (e : Nat × Bool)
    (hf : n.selected.find? (·.1 == c.id) = some e) (hb : e.2 = false) :
    releaseAuthorized n c = false := by simp [releaseAuthorized, hf, hb]

/-- And no selected entry is released before some Carrier arms the node. -/
@[req "DUR-10"]
theorem no_entry_released_before_arming (n : Node) (c : Cand) (e : Nat × Bool)
    (hf : n.selected.find? (·.1 == c.id) = some e) (hs : n.sweepActive = false) :
    releaseAuthorized n c = false := by simp [releaseAuthorized, hf, hs]

/-- `DUR-10`: "nothing is ever displaced". An id in the set stays in it. -/
@[req "DUR-10"]
theorem mem_insertSelected_of_mem (sel : List (Nat × Bool)) (id : Nat) (duress : Bool) (i : Nat)
    (h : ∃ e ∈ sel, e.1 = i) : ∃ e ∈ insertSelected sel id duress, e.1 = i := by
  obtain ⟨e, he, rfl⟩ := h
  unfold insertSelected
  split
  · exact ⟨if e.1 == id then (e.1, e.2 || duress) else e,
      List.mem_map_of_mem he, by split <;> rfl⟩
  · exact ⟨e, by simp [he], rfl⟩

/-- The set only grows, over every event. -/
@[req "DUR-10"]
theorem selected_grows (r : Rules) (env : Env) (w : World) (e : Event) (i : Nat)
    (h : ∃ x ∈ w.node.selected, x.1 = i) :
    ∃ x ∈ (step r env w e).1.node.selected, x.1 = i := by
  cases e with
  | receipt cid s =>
    simp only [step, receipt]
    split; · exact h
    split; · exact h
    split
    · simp only [holderDecision]
      exact mem_insertSelected_of_mem _ _ _ _ h
    · exact h
  | accept cid d E sp es =>
    simp only [step, accept]
    split; · exact h
    split; · exact h
    exact h
  | firePass => simp only [step, firePass]; split <;> exact h
  | send c => simp only [step, send]; split <;> exact h
  | settle tx => simp only [step, settle]; split <;> exact h
  | packageAccepted c => exact h
  | prune => exact h
  | tick => exact h
  | panic => exact h
  | adversaryExposes m i s c => exact h
  | receivePartial m i s c => exact h

/-- `DUR-20`: the holder decision "MUST visit every selected entry and write its window … under
BOTH PINs and whether or not `T` actually moved". Every selected candidate carries the new
window afterwards, so the traversal is over the whole set and not over the entries that
changed. -/
@[req "DUR-20"]
theorem holderDecision_writes_every_window (env : Env) (n : Node) (k : Carrier) (c : Cand)
    (hc : c ∈ (holderDecision env n k).cands)
    (hsel : (insertSelected n.selected k.escape k.duress).any (·.1 == c.id) = true) :
    c.fireAt = some (newDeadline env n k) ∧
      c.windowClose = some ((newDeadline env n k).plus n.combineSlack) := by
  simp only [holderDecision, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  rw [withWindow_id] at hsel
  simp [withWindow, hsel]

/-- `T` is written by the holder decision (`DUR-13`) and by a hot acceptance while armed
(`DUR-14`), and by nothing else: the analogue of `D_immutable` for the overlay's deadline, and
what the concealment horizon of milestone 7.4 rests on. -/
@[req "DUR-14"]
theorem T_written_only_by_arm_or_accept (r : Rules) (env : Env) (w : World) (e : Event)
    (h : (step r env w e).1.node.T ≠ w.node.T) :
    (∃ cid s, e = .receipt cid s) ∨ ∃ cid d E sp es, e = .accept cid d E sp es := by
  cases e with
  | receipt cid s => exact .inl ⟨cid, s, rfl⟩
  | accept cid d E sp es => exact .inr ⟨cid, d, E, sp, es, rfl⟩
  | firePass => exact absurd (by simp only [step, firePass]; split <;> rfl) h
  | send c => exact absurd (by simp only [step, send]; split <;> rfl) h
  | settle tx => exact absurd (by simp only [step, settle]; split <;> rfl) h
  | packageAccepted c => exact absurd rfl h
  | prune => exact absurd rfl h
  | tick => exact absurd rfl h
  | panic => exact absurd rfl h
  | adversaryExposes m i s c => exact absurd rfl h
  | receivePartial m i s c => exact absurd rfl h

/-- A trace whose samples never step backward. `SPN-13`'s effective time is not monotone on its
own, and `F60` is what a backward step costs before `T`; the lemmas of the ledger and of the
SILENCE relation that need a monotone clock carry this as a premise on the trace rather than as
a property of the clock types. -/
def MonotoneSamples : List (Env × Event) → Prop
  | [] => True
  | [_] => True
  | (a, _) :: (b, y) :: rest =>
      a.eff.notAfter b.eff = true ∧ a.mono.notAfter b.mono = true ∧
        MonotoneSamples ((b, y) :: rest)

theorem MonotoneSamples.tail {x : Env × Event} {rest : List (Env × Event)}
    (h : MonotoneSamples (x :: rest)) : MonotoneSamples rest := by
  cases rest with
  | nil => exact trivial
  | cons y ys => exact h.2.2

namespace RegistrationCases

def A : Node := { id := 0, t := 2, armed := false, poisoned := false, lockedDown := false,
                  carriers := [], cands := [], T := Wall.sample 0, sweepActive := false,
                  selected := [], duressDelay := 200, epsilon := 5, combineSlack := 40 }
def w0 : World := { node := A, exposure := [] }

/-- The hot spend and its Escape; a second pair under a duress Carrier; a claw-back over input 0.
Nothing in this section meters `outflow`; `POL-11` gives the two Escapes and the claw-back zero —
"refresh and escape sweeps have zero outflow by construction" — and the Hot ledger of
`Ledger.lean` is where a hot spend's outflow is read. -/
def tx1 : Tx := { id := 100, inputs := [0], outflow := 100 }
def txE : Tx := { id := 101, inputs := [0, 1], outflow := 0 }
def tx3 : Tx := { id := 102, inputs := [1], outflow := 100 }
def claw : Tx := { id := 500, inputs := [0], outflow := 0 }

/-- A candidate as it is handed to `.accept`, where `born` writes the flags and seeds
`heldSigners` with this node's own id. The held set is `[]` here for that reason, so an exhibit
that seeds a registry directly rather than through an acceptance — `twinNode`, `soloNode` — holds
a candidate with no possession, which `born` never produces. -/
def cand (id : Nat) (tx : Tx) (hot : Bool) (fireAt : Option Nat) (expiry : Nat) : Cand :=
  { id := id, tx := tx, hot := hot, quorum := false, frozen := false, terminal := false,
    settled := false, broadcast := false, released := false, packageOk := false,
    heldSigners := [], fireAt := fireAt.map Wall.sample, windowClose := none,
    expiry := Wall.sample expiry }

def c1 : Cand := cand 1 tx1 true (some 100) 200
def e1 : Cand := cand 2 txE false none 200
def c3 : Cand := cand 3 tx3 true (some 300) 400
def e3 : Cand := cand 4 txE false none 400
/-- A second SpendRequest over the SAME transaction `tx1` with a different expiry: a different
commitment (`CHN-24`), the same sighash per input (`CHN-11`). -/
def c1' : Cand := cand 5 tx1 true (some 150) 250
def e1' : Cand := cand 6 txE false none 250

/-- Raw wall and HotClock samples, no high-water advance, with a chain view. -/
def envAt (wall mono : Nat) (seen : List Tx := []) : Env :=
  { wall := Wall.sample wall, hw := HighWater.sample 0, mono := Mono.sample mono,
    chain := { mtp := Mtp.sample 0, seen := seen } }

def env0 : Env := envAt 50 5
def envFire : Env := envAt 120 60
def envClaw : Env := envAt 120 60 [claw]
def envLate : Env := envAt 201 140
/-- `DEF-1`'s excursion: the wall reads a million, the HotClock has moved ten seconds. -/
def envExcursion : Env := envAt 1000000 15
def envBack : Env := envAt 60 20

/-- Another pair with the same request expiry, so crossed-pair fixtures do not rely on
an expiry mismatch that an earlier wire check would refuse. -/
def c2 : Cand := cand 3 tx3 true (some 100) 200
def e2 : Cand := cand 4 { txE with id := 103 } false none 200

/-- Full historical rule record, independent of `current` mutations. -/
def withdrawn : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic, registration := .rebirth }

def replayFire : List (Env × Event) :=
  [(env0, .accept 10 false (Wall.sample 200) c1 e1), (envClaw, .settle claw),
   (envFire, .accept 11 false (Wall.sample 200) c1 e1), (envFire, .receipt 11 1),
   (envFire, .firePass)]

/-- A replay fixture with non-default lifecycle state, and no window change on acceptance. -/
def lifecycleTrace : List (Env × Event) :=
  [(env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1),
   (envFire, .receivePartial (sighash tx1 0) 0 1 1), (envFire, .firePass),
   (envClaw, .settle claw)]

def lifecycle (r : Rules) : World := (run r w0 lifecycleTrace).1

def freshChecks (r : Rules) : Bool :=
  let n := accept r env0 A 10 false (Wall.sample 200)
    { c1 with pair := some (99, 98) } { e1 with pair := some (99, 98) }
  n.cands.map Cand.id == [1, 2] && n.cands.map Cand.pair == [some (1, 2), some (1, 2)] &&
    n.carriers.map Carrier.cid == [10]

def replayChecks (r : Rules) : Bool :=
  let n := (lifecycle r).node
  n.cands.any (fun c => c.id == 1 && c.terminal && c.released && c.quorum &&
    c.heldSigners == [0, 1]) &&
  [false, true].all fun d =>
    let n' := accept r envFire n 11 d (Wall.sample 200) c1 e1
    n'.cands == n.cands && n'.carriers.map Carrier.cid == [11]

/-- All identity conflicts over two resident pairs, plus an unpaired boundary in either
position. A seeded unpaired candidate is not a model of claw-back ingress. -/
def refusalChecks (r : Rules) : Bool :=
  let n := accept r env0 (accept r env0 A 10 false (Wall.sample 200) c1 e1)
    20 false (Wall.sample 200) c2 e2
  let conflicts : List (Cand × Cand) :=
    [(c1, { e2 with id := 9 }), ({ c2 with id := 9 }, e1), (c1, e2), (e1, c1),
     ({ c1 with tx := tx3 }, e1), (c1, { e1 with tx := tx3 }),
     ({ c1 with hot := false }, e1), (c1, { e1 with hot := true }),
     ({ c1 with expiry := Wall.sample 201 }, e1), (c1, { e1 with expiry := Wall.sample 201 })]
  [false, true].all fun d =>
    (conflicts.all fun (sp, es) =>
      let n' := accept r env0 n 11 d (Wall.sample 200) sp es
      n' == n && (receipt env0 n' 11 1) == n) &&
    (accept r env0 A 11 d (Wall.sample 200) c1 c1 == A) &&
    ([c1, e1].all fun c =>
      let single := { A with cands := [c] }
      accept r env0 single 11 d (Wall.sample 200) c1 e1 == single) &&
    ([1, 2].all fun id =>
      let unpaired := { n with cands := n.cands.map fun c =>
        if c.id == id then { c with pair := none } else c }
      accept r env0 unpaired 11 d (Wall.sample 200) c1 e1 == unpaired) &&
    ([1, 2].all fun id =>
      let half := { n with cands := n.cands.filter (·.id == id) }
      accept r env0 half 11 d (Wall.sample 200) c1 e1 == half)

/-- Registration and schedule work are different writes. The armed fixture has stale selected
windows at 150; acceptance shrinks to 95 and traverses under either PIN, retaining lifecycle. -/
def scheduleBefore (r : Rules) : Node :=
  let n := (lifecycle r).node
  { n with
    armed := true, sweepActive := true, T := Wall.sample 150,
    cands := writeWindows n.selected (Wall.sample 150) n.combineSlack
      (n.cands.map fun c => { c with frozen := c.hot || c.frozen }) }

def lifecycleFields (c : Cand) :=
  (c.id, c.tx, c.hot, c.quorum, c.frozen, c.terminal, c.settled, c.broadcast,
   c.released, c.heldSigners, c.packageOk, c.expiry, c.pair)

def scheduleChecks (r : Rules) : Bool :=
  let n := scheduleBefore r
  [false, true].all fun d =>
    let n' := accept r env0 n 11 d (Wall.sample 200) c1 e1
    n'.T == Wall.sample 95 && n'.cands.map lifecycleFields == n.cands.map lifecycleFields &&
      n'.cands.any (fun c => c.id == 2 && c.fireAt == some (Wall.sample 95) &&
        c.windowClose == some (Wall.sample 135)) && n'.carriers.map Carrier.cid == [11]

end RegistrationCases

end BtcPolicy.Kernel
