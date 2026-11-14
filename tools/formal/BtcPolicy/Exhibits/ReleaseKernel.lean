import BtcPolicy.Evaluate
import BtcPolicy.Cursor
import BtcPolicy.Coverage
import BtcPolicy.Deadline
import BtcPolicy.Classification
import BtcPolicy.Membership
import BtcPolicy.RefreshAge
import BtcPolicy.Kernel
import BtcPolicy.Federation
import BtcPolicy.Ingress
import BtcPolicy.Lifetime
import BtcPolicy.Sweep
import BtcPolicy.Settlement
import BtcPolicy.Budget
import BtcPolicy.Ledger
import BtcPolicy.Silence
import BtcPolicy.FedSilence
import BtcPolicy.Admission
import BtcPolicy.Progress
import BtcPolicy.Delivery
import BtcPolicy.Chain
import BtcPolicy.Watchtower
import BtcPolicy.VaultUnspent
import BtcPolicy.Alerts
import BtcPolicy.Package
import BtcPolicy.Trace
import BtcPolicy.TxAccounting
import BtcPolicy.Feasibility
import BtcPolicy.Recovery
import BtcPolicy.EscapeCustody
import BtcPolicy.ClawbackIngress
import BtcPolicy.ClawHandler
import BtcPolicy.PreRelease
import BtcPolicy.Coinbase
import BtcPolicy.Ladder
import BtcPolicy.Assembly
import BtcPolicy.RungRelease
import BtcPolicy.LadderRelease
import BtcPolicy.RungIngress
import BtcPolicy.RungAssembly
import BtcPolicy.VariantReceipt
import BtcPolicy.ClassAssembly
import BtcPolicy.LadderShape
import BtcPolicy.AcceptedSet
import BtcPolicy.Lifecycle
import BtcPolicy.Retained
import BtcPolicy.ReceiptExpiry
import BtcPolicy.ReleaseQuota
import BtcPolicy.Possession
import BtcPolicy.ExpirySilence
import BtcPolicy.VariantSilence
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.ReleaseKernel
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## The release and Carrier kernel: `DEF-1`, `DEF-4`, `F57` row 8, `DUR-29`'s race, and
decision 9's exposure case, each over `current` and beside it the same trace under the
withdrawn value written out in full (so a flip of `current` reaches only the `current` twin). -/

abbrev A := Kernel.RegistrationCases.A
abbrev w0 := Kernel.RegistrationCases.w0
abbrev tx3 := Kernel.RegistrationCases.tx3
abbrev claw := Kernel.RegistrationCases.claw
abbrev c1 := Kernel.RegistrationCases.c1
abbrev e1 := Kernel.RegistrationCases.e1
abbrev c3 := Kernel.RegistrationCases.c3
abbrev e3 := Kernel.RegistrationCases.e3
abbrev c1' := Kernel.RegistrationCases.c1'
abbrev e1' := Kernel.RegistrationCases.e1'
abbrev env0 := Kernel.RegistrationCases.env0
abbrev envFire := Kernel.RegistrationCases.envFire
abbrev envClaw := Kernel.RegistrationCases.envClaw
abbrev envLate := Kernel.RegistrationCases.envLate
abbrev envExcursion := Kernel.RegistrationCases.envExcursion
abbrev envBack := Kernel.RegistrationCases.envBack

def withdrawnRetire : Rules :=
  { retire := .byWall, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }
def withdrawnReauth : Rules :=
  { retire := .byMono, reauth := .beforeAssembly, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }
def withdrawnPoison : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .byLockOrder, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }

def isBroadcast : Effect → Bool
  | .broadcast _ => true
  | _ => false

/-! ### `DEF-1`: the Carrier survives a forward wall excursion -/

/-- Accepted at wall 50 with `E = 200`, so `D = 155`; the prune driver runs at the excursion; a
receipt arrives once the wall is back. -/
def def1Trace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (envExcursion, .tick), (envBack, .receipt 10 1) ]

/-- As it stands, `NCH-40` (3) reads the HotClock: the intent is still there and the receipt
commits it. -/
@[req "NCH-35"]
theorem def1_refused_with_current :
    (run current w0 (def1Trace.take 2)).1.node.carriers.any (fun k => k.cid == 10 && k.D == Mono.sample 155) = true ∧
    (run current w0 def1Trace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = true := by
  decide

/-- Under the withdrawn value the excursion deletes the node's own intent, and the receipt
finds nothing: the node is left unarmed beside whoever holds the partial. -/
@[req "NCH-35"]
theorem def1_admitted_with_withdrawn :
    (run withdrawnRetire w0 (def1Trace.take 2)).1.node.carriers = [] ∧
    (run withdrawnRetire w0 def1Trace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false := by
  decide

/-! ### `F65`: one peer relaying twice is one holder

At a threshold `A3.t` two distinct relays are needed and the duplicate has somewhere to go
wrong; on `A` the first relay already reaches `t`. -/

/-- `A` with a higher threshold. A `Node` carries no `n`, so the shape here is `t` alone. -/
def A3 : Node := { A with t := 3 }
def w3 : World := { node := A3, exposure := [] }

def oneRelayTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1) ]
/-- Peer 1 relays the same Carrier twice. -/
def dupRelayTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 1)]
/-- Peers 1 and 2 relay it once each: the same two receipts, differing only in who sent the
second. -/
def twoRelaysTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 2)]
/-- A relay carrying this node's OWN id after peer 1's. `DUR-5` counts each distinct PEER and
`A3.id` is already the `+ 1`, so it must add nothing. -/
def selfRelayTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 0)]


def relaySendersOf (w : World) (cid : Nat) : List Nat :=
  ((w.node.carriers.find? (·.cid == cid)).map Carrier.relaySenders).getD []

/-- `DUR-5` counts "each distinct peer whose authenticated relay of the same Carrier this node
receives" and `DUR-6` says "a sender already counted … MUST be an idempotent no-op". Peer 1
relaying
twice is one holder by `holderCount`, so the pair's release gate stays shut — that second
conjunct is what goes red if the count comes back. Beside it the withdrawn count reaches `t` on
the same trace, which is `DUR-8`'s gate opened a relay early, under either PIN. Two distinct
peers do reach it, so what the holder set refuses is the duplicate and not the relay; a relay
carrying this node's own id is refused the same way (`self_relay_is_not_a_second_holder`). -/
@[req "DUR-6"]
theorem duplicate_relay_is_one_holder :
    holderCount (relaySendersOf (run current w3 dupRelayTrace).1 10) = 2 ∧
    (run current w3 dupRelayTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false ∧
    A3.t ≤ f65RelayCount dupRelayTrace ∧
    (run current w3 twoRelaysTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = true := by
  decide

/-- `DUR-5`'s "each distinct peer": a relay carrying this node's own `sender_node_id` is the
node it already counts, so it is the same no-op as a duplicate. Without the check `holderCount`
would count this node twice and reach `t` a relay early, exactly as the duplicate did. -/
@[req "DUR-5"]
theorem self_relay_is_not_a_second_holder :
    holderCount (relaySendersOf (run current w3 selfRelayTrace).1 10) = 2 ∧
    (run current w3 selfRelayTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false := by
  decide

/-- And the repeat is a no-op on the whole world, not only on the count: `DUR-6`'s "idempotent
no-op" read literally, at a state where the Carrier already holds that sender. -/
@[req "DUR-6"]
theorem duplicate_relay_changes_nothing :
    step current env0 (run current w3 oneRelayTrace).1 (.receipt 10 1)
      = ((run current w3 oneRelayTrace).1, []) := by
  decide

/-! ### Authenticated partial receipt: possession and exposed authority stay distinct -/

/-- Acceptance supplies this node's own withheld partial through `born`; the Carrier's holder
set is then complete. No partial has left this node yet. -/
def partialStart : World := (run current w0 oneRelayTrace).1

def partialOnce : World :=
  (step current env0 partialStart (.receivePartial (sighash tx1 0) 0 1 1)).1

def heldOf (w : World) (cid : Nat) : List Nat :=
  ((w.node.cands.find? (·.id == cid)).map Cand.heldSigners).getD []

/-- The accepted candidate holds self, then admits peer 1. The distinct held count rises and
reaches quorum, while self's withheld partial is still absent from exposed authority. -/
@[req "NCH-24"]
theorem receivePartial_admits_peer :
    heldOf partialStart 1 = [A.id] ∧
    heldOf partialOnce 1 = [A.id, 1] ∧
    (heldOf partialOnce 1).eraseDups.length = (heldOf partialStart 1).eraseDups.length + 1 ∧
    partialOnce.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = true ∧
    exposedQuorum partialOnce c1 = false ∧
    partialOnce.node.cands.any (·.released) = false ∧
    (step current env0 partialStart (.receivePartial (sighash tx1 0) 0 1 1)).2 = [] := by
  decide

/-- `NCH-25`: "A duplicate is an idempotent `ACCEPTED` and never displaces the first."
The exact held list stays put; the world legitimately appends another exposed-authority row. -/
@[req "NCH-25"]
theorem duplicate_partial_preserves_held :
    let again := (step current env0 partialOnce (.receivePartial (sighash tx1 0) 0 1 1)).1
    heldOf again 1 = heldOf partialOnce 1 ∧
    again.node.cands.map Cand.heldSigners = partialOnce.node.cands.map Cand.heldSigners ∧
    again.exposure = partialOnce.exposure ++
      [{ msg := sighash tx1 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- The honest node releases and another signer exposes, without delivering. The candidate
still holds only self, despite world-level quorum. -/
def partialExposedOnly : World :=
  (run current partialStart [(envFire, .firePass),
    (envFire, .adversaryExposes (sighash tx1 0) 0 1 1)]).1

@[req "POL-18"]
theorem exposure_without_receivePartial_is_not_held :
    exposedQuorum partialExposedOnly c1 = true ∧
    heldOf partialExposedOnly 1 = [A.id] ∧
    partialExposedOnly.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = false := by
  decide

/-- The candidate has been pruned. Arrival still records exposed authority, and creates no
candidate or possession. -/
@[req "NCH-24"]
theorem receivePartial_after_prune_still_exposes :
    let pruned := (step current envLate partialStart .prune).1
    let received := (step current envLate pruned (.receivePartial (sighash tx1 0) 0 1 1)).1
    pruned.node.cands = [] ∧ received.node = pruned.node ∧
    received.exposure = pruned.exposure ++
      [{ msg := sighash tx1 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- A resident id with the wrong sighash cannot gain possession, and cannot suppress the
independent exposed-authority append either. -/
@[req "NCH-24"]
theorem mismatched_receivePartial_still_exposes :
    let received := (step current env0 partialStart (.receivePartial (sighash tx3 0) 0 1 1)).1
    heldOf partialStart 1 = [A.id] ∧ received.node = partialStart.node ∧
    received.exposure = partialStart.exposure ++
      [{ msg := sighash tx3 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- The package test reads possession. This node has released and the world holds `t` exposed
signers on `tx1`, but the peer's partial was exposed and never delivered, so `packageAccepted`
leaves the package unassembled: exposed authority this node never received is not something it
can finalize from. -/
@[req "SPN-39"]
theorem exposed_not_held_cannot_assemble :
    let assembled := (step current envFire partialExposedOnly (.packageAccepted 1)).1
    exposedQuorum partialExposedOnly c1 = true ∧
    partialExposedOnly.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-- The same release with the peer's partial delivered: the store holds it, and the package can
be assembled (`received_can_assemble`). -/
def partialReceived : World :=
  (run current partialStart [(envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 1 1)]).1

/-- And a node that received can assemble: released, `t` held, and the package test passes. -/
@[req "SPN-39"]
theorem received_can_assemble :
    let assembled := (step current envFire partialReceived (.packageAccepted 1)).1
    heldOf partialReceived 1 = [A.id, 1] ∧
    partialReceived.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = true := by
  decide

/-- A partial on input 7 — an input this kernel does not model — is exposed authority and not
possession: the step appends its row, the store keeps the held set `[A.id]`, and after this node
releases the package test still refuses. The trap that goes red if the store guard stops reading
the input: without it the held set reaches `t` on a row `exposedQuorum` never counts, and
`Kernel.released_held_exposed` is false. -/
@[req "NCH-24"]
theorem input7_receipt_is_exposed_not_held :
    let received := (step current env0 partialStart (.receivePartial (sighash tx1 0) 7 1 1)).1
    let assembled := (run current received [(envFire, .firePass),
      (envFire, .packageAccepted 1)]).1
    received.exposure = partialStart.exposure ++
      [{ msg := sighash tx1 0, input := 7, signer := 1, hot := true, cid := 1 }] ∧
    heldOf received 1 = [A.id] ∧
    received.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = false ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-- The `released` conjunct is live: the peer's partial is held and the candidate is due, but
this node has run no fire pass, so it has released nothing and assembles nothing. -/
@[req "SPN-39"]
theorem held_without_release_cannot_assemble :
    let assembled := (step current envFire partialOnce (.packageAccepted 1)).1
    partialOnce.node.cands.any
      (fun c => c.id == 1 && due current envFire partialOnce.node c && heldQuorum A.t c && !c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-! ### `DUR-29`'s race under both values, over one `step` -/

/-- `SPN-39`: "the linearization point between arming and sending". The current rule
discharges the general theorem's re-authorization premise, independently of any chosen trace. -/
@[req "SPN-39"]
theorem no_hot_broadcast_while_armed_with_current (env : Env) (w : World)
    (hw : Reachable current w) (ha : w.node.armed = true) (cid : Nat) :
    ∀ eff ∈ (step current env w (.send cid)).2,
      ∃ c ∈ w.node.cands, c.id = cid ∧ c.hot = false ∧ eff = .broadcast c.tx.id :=
  no_hot_broadcast_while_armed current rfl env w hw ha cid

/-- Acceptance, the duress holder decision, release, peer possession and package acceptance
of the selected Escape, through the existing kernel transitions. -/
def armedEscapePrefix : List (Env × Event) :=
  [(env0, .accept 10 true (Wall.sample 200) c1 e1), (env0, .receipt 10 1),
   (envFire, .firePass), (envFire, .receivePartial (sighash txE 0) 0 1 2),
   (envFire, .packageAccepted 2)]

/-- The armed-send premises are inhabited and permit a non-hot broadcast. -/
@[req "DUR-11"]
theorem armed_escape_can_broadcast :
    let w := (run current w0 armedEscapePrefix).1
    Reachable current w ∧ w.node.armed = true ∧
      (step current envFire w (.send 2)).2 = [.broadcast txE.id] := by
  refine ⟨(ProvenanceCases.execution_run current armedEscapePrefix
    (.init A (by decide))).reachable, ?_, ?_⟩ <;> decide

/-- The arm — the second Carrier's holder decision — injected after package acceptance and before
the send: `DUR-11`'s "refused at the broadcast authorization even after mempool acceptance
passed". -/
def raceTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .receipt 10 1),                                 -- holder decision: pair opened
    (envFire, .firePass),                                  -- A's partial queued: exposed
    (envFire, .receivePartial (sighash tx1 0) 0 2 1),      -- peer 2's partial delivered, held
    (envFire, .packageAccepted 1),                         -- assembled and mempool-tested
    (envFire, .accept 20 true (Wall.sample 300) c3 e3),
    (envFire, .receipt 20 1),                              -- ARM: every hot candidate frozen
    (envFire, .send 1) ]

/-- As it stands: nothing is broadcast, and the node is armed. -/
@[req "DUR-29"]
theorem race_refused_with_current :
    ((run current w0 raceTrace).2.filter isBroadcast) = [] ∧
    (run current w0 raceTrace).1.node.armed = true := by decide

/-- Under the withdrawn value — the check before assembly instead of before the send — the same
trace broadcasts the coerced spend. -/
@[req "DUR-29"]
theorem race_admitted_with_withdrawn :
    (run withdrawnReauth w0 raceTrace).2.filter isBroadcast = [.broadcast 100] := by decide

/-- The partial itself left at the fire pass: exposure is at "queued for transport", not at the
send, so the refused broadcast revokes nothing. -/
@[req "POL-18"]
theorem race_partial_already_exposed :
    (run current w0 raceTrace).1.exposure.any (fun e => e.signer == 0 && e.msg == sighash tx1 0) = true := by
  decide

/-! ### Decision 9: exposure at world level -/

/-- Two SpendRequests over one transaction with different expiries. `c1`'s partial is released,
`c1` is pruned at its expiry, `c1'` over the same `tx1` is accepted; one compromised signer adds
its partial. -/
def twoRequestsTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .receipt 10 1),
    (envFire, .firePass),                                   -- A releases under commitment 1
    (envLate, .prune),                                      -- c1 expired: gone from the registry
    (envLate, .accept 30 false (Wall.sample 250) c1' e1'),  -- commitment 5, same tx1
    (envLate, .adversaryExposes (sighash tx1 0) 0 2 5) ]

def wTwo : World := (run current w0 twoRequestsTrace).1

/-- The count a commitment-keyed history would give `c1'`. -/
def finalizableByCommitment (w : World) (c : Cand) : Bool :=
  w.node.t ≤ ((w.exposure.filter fun (e : Exp) => e.cid == c.id && e.input == 0).map
    Exp.signer).eraseDups.length

/-- The count a node-local history pruned with the candidate would give: this node's own
RELEASED partials, read from resident candidates only. Decision 9's retained WRONG model, and
named for what it reads rather than for finalizability — `Cand.heldSigners` is the real
node-local possession, and release is not possession. -/
def releasedResidentQuorum (w : World) (c : Cand) : Bool :=
  let own := if w.node.cands.any (fun d => d.id == c.id && d.released) then 1 else 0
  let others := ((w.exposure.filter fun (e : Exp) => e.msg == sighash c.tx 0 && e.signer != w.node.id).map
    Exp.signer).eraseDups.length
  w.node.t ≤ own + others

/-- `c1` is gone, `c1'` was never released by this node, and yet the world holds `t` partials on
`c1'`'s sighash: `c1'` is finalizable. The two wrong models each report it safe. -/
@[req "POL-18"]
theorem exposure_key_exhibit :
    wTwo.node.cands.any (fun c => c.id == 1) = false ∧
    wTwo.node.cands.any (fun c => c.id == 5 && c.released) = false ∧
    exposedQuorum wTwo c1' = true ∧
    finalizableByCommitment wTwo c1' = false ∧
    releasedResidentQuorum wTwo c1' = false := by decide

/-- The safety statement the wrong models would let one prove — "if this node released nothing
resident over the transaction, the transaction is not finalizable" — is false at world level. -/
@[req "POL-18"]
theorem no_resident_release_does_not_mean_safe :
    ¬ (∀ w : World, ∀ c : Cand,
        (∀ d ∈ w.node.cands, d.tx = c.tx → d.released = false) → exposedQuorum w c = false) := by
  intro h
  have := h wTwo c1' (by decide)
  simp [exposure_key_exhibit.2.2.1] at this

/-! ### `DEF-4`: poison the lock, drive a fire pass -/

def poisonTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1), (envFire, .panic), (envFire, .firePass) ]

@[req "DUR-9"]
theorem def4_refused_with_current :
    (run current w0 poisonTrace).2 = [] ∧ (run current w0 poisonTrace).1.node.lockedDown = true := by decide

/-- With the gate resting on lock order alone, the same pass releases the partial. -/
@[req "DUR-9"]
theorem def4_admitted_with_withdrawn :
    (run withdrawnPoison w0 poisonTrace).2 = [.queuePartial (sighash tx1 0) 0 true 1] := by decide

/-! ### `F57` row 8: a defeated hot spend at its fire time after the claw-back is evicted -/

/-- The claw-back is seen at wall 120, past `c1`'s fire time of 100; then it is evicted (the chain
view no longer shows it) and a fire pass runs. -/
def f57Trace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1),
    (envClaw, .settle claw), (envFire, .firePass) ]

/-- As it stands: the defeated spend is resident, terminal, and releases nothing. -/
@[req "SPN-33"]
theorem f57row8_refused_with_current :
    (run current w0 f57Trace).2 = [] ∧
    (run current w0 f57Trace).1.node.cands.any (fun c => c.id == 1 && c.terminal) = true := by decide

/-- Under the withdrawn reading the evicted claw-back un-defeats it and the spend fires. -/
@[req "SPN-33"]
theorem f57row8_admitted_with_withdrawn :
    (run withdrawnDefeat w0 f57Trace).2 = [.queuePartial (sighash tx1 0) 0 true 1] := by decide

/-- `DEF-5` on the same trace: the claw-back's settlement clears the defeated spend from the
pending log, which `/pending` reads, and the candidate stays resident; `SPN-33` says
"removal from the pending log is not removal from the registry". -/
@[req "SPN-30"]
theorem def5_defeated_off_pending :
    pending current envFire (run current w0 f57Trace).1.node = [] ∧
    (run current w0 f57Trace).1.node.cands.any (fun c => c.id == 1) = true := by decide

/-! ### A normal release completes -/

def normalTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1), (envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 1 1), (envFire, .packageAccepted 1),
    (envFire, .send 1) ]

@[req "SPN-39"]
theorem normal_release_completes :
    (run current w0 normalTrace).2 = [.queuePartial (sighash tx1 0) 0 true 1, .broadcast 100] ∧
    (run current w0 normalTrace).1.node.cands.any (fun c => c.id == 1 && c.broadcast) = true := by
  decide

/-! ### Bounded enumeration, from the package-accepted state

An exhibit over a stated bound, with no completeness claim: 2-of-3, one hot pair and one duress
pair accepted, the hot partial released, the peer's partial received and the package accepted
(`wReady`), every word of up to three events over the ten-event alphabet, one environment (the
claw-back visible) per step. From acceptance the race is six events away and a three-deep
enumeration is a silent success under the flip; from `wReady` it is two.

It is not evidence for `packageAccepted`'s quorum conjunct. `safeStep` checks nothing possession
can affect — no hot `queuePartial` and no `broadcast` on an armed node, every hot candidate of an
armed node frozen — so it proves the same with the package test reading possession or exposure.
The exhibits of the receipt section are the evidence for that conjunct. -/

def wReady : World :=
  (run current w0 [(env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .accept 20 true (Wall.sample 300) c3 e3), (env0, .receipt 10 1), (envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 2 1), (envFire, .packageAccepted 1)]).1

def alphabet : List Event :=
  [ .receipt 10 1, .receipt 20 1, .firePass, .packageAccepted 1, .send 1, .settle claw, .prune,
    .tick, .panic, .receivePartial (sighash tx1 0) 0 2 1 ]

def traces : Nat → List (List Event)
  | 0 => [[]]
  | k + 1 => (traces k).flatMap fun t => alphabet.map fun e => t ++ [e]

/-- What every step must satisfy: on an armed node no hot partial is queued and nothing is
broadcast (`DUR-8`, `DUR-11`), and afterwards every hot candidate of an armed node is frozen. -/
def safeStep (r : Rules) (env : Env) (w : World) (e : Event) : Bool :=
  let (w', effs) := step r env w e
  (!w.node.armed || effs.all fun eff => match eff with
    | .queuePartial _ _ hot _ => !hot
    | .broadcast _ => false) &&
  (!w'.node.armed || w'.node.cands.all fun c => !c.hot || c.frozen)

def safeRun (r : Rules) (w : World) : List Event → Bool
  | [] => true
  | e :: es => safeStep r envClaw w e && safeRun r (step r envClaw w e).1 es

theorem traces_count : (traces 3).length = 1000 := by decide +kernel

set_option maxRecDepth 100000 in
@[req "DUR-8"]
theorem bounded_from_ready : (traces 3).all (safeRun current wReady) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The enumeration is not vacuous: under the withdrawn value it finds the race, the shortest
offending word is `[receipt 20 1, send 1]` — arm, then send — and no one-event word offends. -/
@[req "DUR-29"]
theorem bounded_from_ready_withdrawn_finds_race :
    (traces 3).all (safeRun withdrawnReauth wReady) = false ∧
    safeRun withdrawnReauth wReady [.receipt 20 1, .send 1] = false ∧
    (traces 1).all (safeRun withdrawnReauth wReady) = true := by decide +kernel

end BtcPolicy.Exhibits.ReleaseKernel

namespace BtcPolicy.Exhibits.HotLedger
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt)

/-! ## The Hot ledger: `ADR-0014`'s trace made reachable, and `DEF-5`'s settlement refund

`ADR-0014`'s configuration, read from `Budget.params` rather than restated: 2-of-3 with no
compromised node, `hot_window_secs = max_commitment_age_secs = 120`, `hold_secs = 20`,
`combine_slack_secs = 100`. The cap is `V`, so one maximal spend fills a window.

`Budget.lean` holds the same timeline as data — "the timeline as data … not a lifecycle exhibit
showing each row reachable" — and names what it does not carry. The run below carries four of
those five: `DUR-8` withholding the first release until the holder decision, that decision
admitted at 100, the release of the first charge at the second acceptance's own admission check at
121 (`POL-19`), and the completion at 141 as a fresh exposure. The fifth — that pruning has not
collected the first candidate — is vacuous here, because the run prunes nothing. -/




def clawBack : Tx := { id := 206, inputs := [0], outflow := 0 }


/-- The instant the claw-back reaches the mempool, which is the instant it settles, and the
instant `DEF-5`'s second spend arrives. -/
def clawSeen : Nat := 40

def s3 : Cand := cand 7 hot3 true (some (fireOf clawSeen)) (expiryOf clawSeen)
def e3 : Cand := cand 8 esc3 false none (expiryOf clawSeen)

def withClaw (n : Nat) : Env := envAt n n (if clawSeen ≤ n then [clawBack] else [])

/-- The run, with each effect stamped with the instant that emitted it. `Wall` has no accessor —
the clock types are opaque outside `Clocks.lean` — and a completion TIME is what `ADR-0014`
counts, so the instant is carried beside the event and the environment is built from it. Wall and
HotClock read the same number here: one node, no excursion, `NCH-41`'s lag not exercised. -/
def timedRun (mk : Nat → Env) (g : Guards) :
    List (Nat × Event) → Sys → Sys × List (Nat × Effect)
  | [], sys => (sys, [])
  | (n, e) :: rest, sys =>
    let stepped := sysStep g cfg Kernel.current (mk n) sys e
    let ran := timedRun mk g rest stepped.1
    (ran.1, (stepped.2.map fun eff => (n, eff)) ++ ran.2)


/-- Stamping the effects changes no state: the run is `Ledger.sysRun`'s. -/
theorem timedRun_is_sysRun (mk : Nat → Env) (g : Guards) :
    ∀ (tr : List (Nat × Event)) (sys : Sys),
      (timedRun mk g tr sys).1 = (sysRun g cfg Kernel.current sys (steps mk tr)).1 := by
  intro tr
  induction tr with
  | nil => intro sys; rfl
  | cons x rest ih =>
    intro sys
    obtain ⟨n, e⟩ := x
    exact ih _

/-- The outflow a broadcast carried, read from the transactions themselves. -/
def amountOf (txid : Nat) : Nat :=
  ([hot1, esc1, hot2, esc2, hot3, esc3, clawBack].find? (·.id == txid)).elim 0 (·.outflow)

/-- The completions of a run: the instant of every `Effect.broadcast` and the outflow it carried.
`SPN-38`'s queued partial is an exposure, not a completion. -/
def completions (mk : Nat → Env) (g : Guards) (tr : List (Nat × Event)) : List (Nat × Nat) :=
  (timedRun mk g tr sys0).2.filterMap fun x =>
    match x.2 with
    | .broadcast txid => some (x.1, amountOf txid)
    | .queuePartial _ _ _ _ => none

def completedInWindow (start window : Nat) (cs : List (Nat × Nat)) : Nat :=
  ((cs.filter fun c => start ≤ c.1 && c.1 < start + window).map (·.2)).sum

/-! ### `ADR-0014`'s delayed-holder trace -/


/-- Both spends are admitted and both complete, at the instants `Budget.timeline` records. The
fire pass at the Hold releases nothing and exposes nothing: `DUR-8` withholds the release until
the holder decision, which is what puts the first completion at 100 rather than at 20. -/
@[req "POL-20"]
theorem adr0014_completions :
    (timedRun plain current (adr0014.take 2) sys0).1.world.exposure = [] ∧
    completions plain current adr0014 =
      [(Budget.timeline.firstComplete, V), (Budget.timeline.secondComplete, V)] := by decide

/-- The refutation, existential over that reachable trace: SOME window of length
`hot_window_secs` completes more than `(n / t) × cap`, cleared of its division.
`Budget.exceeds_withdrawn_bound` computes the coefficient; what is new here is that the trace is
run rather than tabulated. -/
@[req "POL-20"]
theorem adr0014_refutes_completion_bound :
    ∃ start, Budget.params.n * V <
      Budget.params.t * completedInWindow start Budget.params.window
        (completions plain current adr0014) :=
  ⟨Budget.intervalStart, by decide⟩

/-- And it hits exactly `2V`, which is `t × cap` at `t = 2`. So the trace refutes the `n / t`
reading and NOT `cap ≤ tolerable per-window loss ÷ t`, which `POL-20` withdraws for its own
reason: "No replacement rolling completion-loss formula is specified." -/
@[req "POL-20"]
theorem adr0014_hits_exactly_t_cap :
    completedInWindow Budget.intervalStart Budget.params.window
        (completions plain current adr0014) = Budget.statedTotalV * V ∧
      Budget.statedTotalV * V = Budget.params.t * V := by decide

/-- The admission bound stands on the same run, which is `POL-20`'s point — "an acceptance-time
admission bound, not a rolling completion-loss bound". Both spends were registered, so both passed
`POL-16` at their own acceptance, and the ledger is under the cap at the end by the invariant
rather than by inspection. -/
@[req "POL-16"]
theorem adr0014_admission_holds :
    (timedRun plain current adr0014 sys0).1.world.node.cands.any (·.id == 1) = true ∧
    (timedRun plain current adr0014 sys0).1.world.node.cands.any (·.id == 5) = true ∧
    liveSum (timedRun plain current adr0014 sys0).1.led ≤ cfg.cap := by
  refine ⟨by decide, by decide, ?_⟩
  rw [timedRun_is_sysRun]
  exact liveSum_le_cap current cfg Kernel.current _ sys0 (by decide)

/-! ### `DEF-5`: the settlement that refunded the reservation -/


/-- The claw-back is seen in the mempool and `SPN-33` marks the first spend terminal; its partial
is already out. A second hot spend of the whole cap arrives inside the same window. -/
def def5 : List (Nat × Event) :=
  [ (0, .accept 10 false (Wall.sample (expiryOf 0)) s1 e1),
    (30, .receipt 10 1),
    (30, .firePass),
    (30, .adversaryExposes (sighash hot1 0) 0 2 1),
    (clawSeen, .settle clawBack),
    (clawSeen, .accept 30 false (Wall.sample (expiryOf clawSeen)) s3 e3) ]

/-- As the rule stands: the mempool settlement refunds nothing, the charge is still the first
spend's, and the second spend is refused before signing — nothing of it is registered. The first
spend's authority is out and finalizable all the while, which is why the charge must stay. -/
@[req "SPN-33"]
theorem def5_refused_with_current :
    (timedRun withClaw current def5 sys0).1.led.map (·.cid) = [1] ∧
    (timedRun withClaw current def5 sys0).1.world.node.cands.any (·.id == 7) = false ∧
    exposedQuorum (timedRun withClaw current def5 sys0).1.world s1 = true := by decide

/-- Under the withdrawn value the settlement refunds the reservation of every candidate it
touched — here through the terminal mark `SPN-33` sets on the input-conflicting spend. The first
charge is gone, its exposed authority is not, and the same second spend is now admitted: a second
maximal hot spend accepted inside the window in which the first's partial is out and finalizable,
against a cap of one, with the ledger showing a single charge. `POL-20`'s counting theorem cannot
see this — the refunded reservation leaves its own cohort — which is why the defect is an exhibit
and not a theorem. -/
@[req "SPN-33"]
theorem def5_admitted_with_withdrawn :
    (timedRun withClaw withdrawnSettlement def5 sys0).1.led.map (·.cid) = [7] ∧
    (timedRun withClaw withdrawnSettlement def5 sys0).1.world.node.cands.any (·.id == 7) = true ∧
    exposedQuorum (timedRun withClaw withdrawnSettlement def5 sys0).1.world s1 = true := by decide

/-! ### `F63`: two commitments over one transaction, and the end of both their charges

The history `F63` records, run over the landed ledger's own transitions. The finding owns the
argument; nothing is re-argued here. -/



/-- The node at the moment the first twin's partial is out and the second's is not. -/
def twinNode : Node := { A with cands := [{ s1 with released := true }, s1Twin] }
/-- The same moment with one commitment only. -/
def soloNode : Node := { A with cands := [{ s1 with released := true }] }

/-- Both charges, `hot_outflow` each, EACH reserved at its own acceptance (`POL-18`: "at
acceptance"), which is what puts the twin's row inside a trailing window the first's has left. -/
def twinLed : Ledger :=
  [row 1 V Budget.timeline.firstAccept (expiryOf Budget.timeline.firstAccept),
   row 9 V twinAccept (expiryOf twinAccept)]
/-- The same history with a single commitment. -/
def soloLed : Ledger :=
  [row 1 V Budget.timeline.firstAccept (expiryOf Budget.timeline.firstAccept)]

/-- The sample at which the first charge is dead on both of `POL-19`'s disjuncts, which
`Budget.reservation_boundary` owns. -/
def deadAt : Env := envOf Budget.timeline.secondAccept Budget.timeline.secondAccept
/-- The prune pass, one sample past the twin's signed expiry and no further: its HotClock is
still inside the twin's trailing window, so no release at that sample could take it. -/
def pruneAt : Env := envOf (expiryOf twinAccept + 1) Budget.timeline.secondAccept

/-- The node that prune pass leaves: both twins are past their signed expiries and neither belongs to
an exempt Escape's pair, so `SPN-41`'s pruning collects both. -/
def prunedNode : Node := prune pruneAt twinNode

/-- Two commitments over one transaction are metered twice — `2V` against a cap of `V` — and the
two charges then leave by different doors. `markExposed` sets the released twin's bit; at
`deadAt`, a hot admission's check, both of `POL-19`'s disjuncts are dead for that row and it is
released, while the twin survives on its own later reservation; at `pruneAt` a release STILL could
not take the twin, and it is the prune pass that collects it, its wall sample past the twin's
expiry, which refunds it (`POL-18`: "a reservation is refundable exactly when it is unexposed, its
signed expiry has strictly passed on the wall sample `POL-19`'s expiry disjunct reads, and its
candidate is no longer resident"). The fifth conjunct is what makes the prune pass load-bearing rather
than decorative: a release at the prune pass's own sample leaves the charge standing. The sixth and
seventh are the collection: against the node before the prune pass, where the twin is resident, nothing
is refunded; the prune pass leaves no candidate; against the node it leaves, the twin's charge is
refunded.

The single-commitment history reaches the same empty ledger without the prune pass at all, which is
`F63`'s point that the refund reaches no state the release would not have reached alone. -/
@[req "POL-18"]
theorem f63_twins_end_charging_nothing :
    liveSum (markExposed twinNode twinLed) = 2 * V ∧
    (markExposed twinNode twinLed).map (·.exposed) = [true, false] ∧
    liveSum (ageOut deadAt cfg.window (markExposed twinNode twinLed)) = V ∧
    (ageOut deadAt cfg.window (markExposed twinNode twinLed)).map (·.cid) = [9] ∧
    liveSum (ageOut pruneAt cfg.window
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = V ∧
    liveSum (refundAtPrune Ledger.current.refund pruneAt twinNode
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = V ∧
    prunedNode.cands = [] ∧
    liveSum (refundAtPrune Ledger.current.refund pruneAt prunedNode
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = 0 ∧
    liveSum (ageOut deadAt cfg.window (markExposed soloNode soloLed)) = 0 := by
  decide

/-- The exposure the emptied ledger no longer prices: 2-of-3 with two distinct signers on the
transaction's input 0. `POL-20` states the residual — "Already exposed signatures also remain
valid after their reservations age out" — and `exposedQuorum` keys on `(sighash, input, signer)`,
so it does not read a commitment id and no charge was ever what held this. -/
def twinExposure : World :=
  { node := A,
    exposure := [{ msg := sighash hot1 0, input := 0, signer := 0, cid := 1, hot := true },
                 { msg := sighash hot1 0, input := 0, signer := 1, cid := 1, hot := true }] }

@[req "POL-20"]
theorem f63_exposure_outlives_the_charges : exposedQuorum twinExposure s1 = true := by decide

/-! ### `F62`: the release is one way, at an accepted hot admission, and the refund waits for
collection

The traces below run over `s1`, a spend of the whole cap accepted at wall and HotClock 0, with
`fire_at` 20 and its signed expiry at 120, opened by its holder decision. In each, a sample past both of
`POL-19`'s disjuncts for its charge is followed by a backward wall step to 50 while the HotClock
keeps moving, so `POL-19`'s wall disjunct holds the charge again. Wall and HotClock are sampled
apart, so these runs are `Ledger.sysRun`'s own. Each says which way it is closed: the second spend
of the whole cap is refused, or no candidate releases a partial while its commitment has no row. -/

/-- The release at every composed step, the requirement as it stood before 2026-10-09. An explicit
record, so a flip of `current` cannot reach it. -/
def withdrawnRelease : Guards :=
  { settlement := .retainOnMempool, release := .everyStep, refund := .onCollection }
/-- The refund at the prune pass after expiry whether or not the candidate is resident, the requirement
as it stood before 2026-10-09. -/
def withdrawnRefund : Guards :=
  { settlement := .retainOnMempool, release := .acceptedAdmission, refund := .atExpiry }

def runAt (g : Guards) (tr : List (Env × Event)) : Sys × List Effect :=
  sysRun g cfg Kernel.current sys0 tr






/-- Closed as the release point stands, by the refusal: the tick releases nothing, the second
spend's check finds `s1`'s charge live again on the wall, and the spend is refused before signing;
`s1`'s release that follows is charged. -/
@[req "POL-19"]
theorem uncharged_fire_closed_with_current :
    (runAt Ledger.current unchargedFire).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current unchargedFire).1.world.node.cands.any (·.id == 5) = false ∧
    (runAt Ledger.current unchargedFire).2 = [s1Partial] := by decide

/-- Red under the release at every step: the tick released the charge, the second spend of the
whole cap is admitted against the emptied ledger, and `s1` releases its partial with no row. -/
@[req "POL-19"]
theorem uncharged_fire_with_withdrawn :
    (runAt withdrawnRelease unchargedFire).1.led.map (·.cid) = [5] ∧
    (runAt withdrawnRelease unchargedFire).1.world.node.cands.any (·.id == 5) = true ∧
    (runAt withdrawnRelease unchargedFire).2 = [s1Partial] := by decide

/-- A request on `s1`'s retired nonce: its check passes the budget once `s1`'s charge is released,
and the kernel refuses it (`NCH-40`'s tombstone). -/
def replayed : Cand := cand 7 hot3 true (some 141) 241
def replayedEsc : Cand := cand 8 esc3 false none 241

/-- **The refused admission**: that request at wall and HotClock 121, then the step back. -/
def refusedAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, .accept 10 false (Wall.sample 241) replayed replayedEsc)] ++ afterBack

/-- A hot spend over the whole cap: its check releases `s1`'s charge, and the budget still refuses
it (`POL-16`). -/
def overCap : Cand := cand 7 { id := 207, inputs := [6], outflow := V + 1 } true (some 141) 241
def overCapEsc : Cand := cand 8 { id := 208, inputs := [6, 7], outflow := 0 } false none 241

/-- **The budget-refused admission**: that request at wall and HotClock 121, then the step back. -/
def budgetRefusedAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, .accept 30 false (Wall.sample 241) overCap overCapEsc)] ++ afterBack

/-- Closed as the release point stands, by the refusal, whichever refuses: the kernel's tombstone
or the budget. The refused request persists nothing (`SPN-14`: "A refused request MUST mutate
nothing"), so the second spend is refused as in the uncharged-fire trace. -/
@[req "POL-19"]
theorem refused_admission_closed_with_current :
    (runAt Ledger.current refusedAdmission).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current refusedAdmission).1.world.node.cands.any (fun c => c.id == 5 || c.id == 7)
      = false ∧
    (runAt Ledger.current refusedAdmission).2 = [s1Partial] ∧
    (runAt Ledger.current budgetRefusedAdmission).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current budgetRefusedAdmission).1.world.node.cands.any
      (fun c => c.id == 5 || c.id == 7) = false ∧
    (runAt Ledger.current budgetRefusedAdmission).2 = [s1Partial] := by decide

/-- **The refund exemption**: `s1`'s holder decision lands late, at 110, and installs its Escape's
window `[110, 210]` past `s1`'s expiry under the normal PIN (`DUR-20`); the prune pass at wall and
HotClock 121 finds `s1` expired and keeps it as the exempt Escape's pair (`SPN-41`); then the step
back. -/
def refundExemption : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 false (Wall.sample (expiryOf 0)) s1 e1),
    (envAt 110 110, .receipt 10 1),
    (envAt 121 121, .prune) ] ++ afterBack

/-- Closed as the refund point stands, by the refusal: the prune pass kept the pair, so it refunded
nothing, and the spend is not refunded while it is resident (`POL-18`: "never while the candidate
is resident"). -/
@[req "POL-18"]
theorem refund_exemption_closed_with_current :
    (runAt Ledger.current (refundExemption.take 3)).1.world.node.cands.map (·.id) = [1, 2] ∧
    (runAt Ledger.current refundExemption).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current refundExemption).1.world.node.cands.any (·.id == 5) = false ∧
    (runAt Ledger.current refundExemption).2 = [s1Partial] := by decide

/-- Red under the refund at expiry: the prune pass refunded the resident spend's charge, the second
spend of the whole cap is admitted, and `s1` releases its partial with no row. -/
@[req "POL-18"]
theorem refund_exemption_with_withdrawn :
    (runAt withdrawnRefund refundExemption).1.led.map (·.cid) = [5] ∧
    (runAt withdrawnRefund refundExemption).1.world.node.cands.any (·.id == 5) = true ∧
    (runAt withdrawnRefund refundExemption).2 = [s1Partial] := by decide

/-- A second spend of the whole cap accepted at wall and HotClock 121, where its check releases
`s1`'s charge. -/
def next : Cand := cand 5 hot2 true (some 141) 241
def nextEsc : Cand := cand 6 esc2 false none 241
def releaseStep : Event := .accept 20 false (Wall.sample 241) next nextEsc

def openedSys : Sys := (runAt Ledger.current opened).1
/-- The state the release leaves. -/
def released : Sys := (sysStep Ledger.current cfg Kernel.current (envAt 121 121) openedSys releaseStep).1

/-- **The release at an accepted admission**, then the step back and a fire pass. -/
def releasedAtAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, releaseStep), (envAt 50 122, .firePass)]

/-- Closed as the release point stands, with no candidate releasing uncharged: the acceptance that
released `s1`'s charge advanced the time ratchet to 121, `s1` is still resident, and after the step
back its window's close, 120, is below the ratchet, so the fire pass releases nothing. -/
@[req "POL-19"]
theorem release_at_admission_shuts_window :
    (runAt Ledger.current releasedAtAdmission).1.led.map (·.cid) = [5] ∧
    (runAt Ledger.current releasedAtAdmission).1.world.node.cands.any (·.id == 1) = true ∧
    (runAt Ledger.current releasedAtAdmission).2 = [] := by decide

/-- And at every sample from then on, for `s1` as it is resident in the state the release leaves
and through any later trace: the acceptance left the ratchet at 121, past `s1`'s expiry, no later
step lowers it (`Ledger.sysRun_ratchet_never_lowered`), and a hot window read at the ratchet is
closed (`Kernel.never_due_below_ratchet`). `Ledger.released_never_due` is the same argument over
every release. The proof takes the close's value and no other guard's. -/
@[req "POL-19"]
theorem release_at_admission_never_due (tr : List (Env × Event)) (env' : Env) (c : Cand)
    (hc : c ∈ released.world.node.cands) (hid : c.id = 1) :
    due Kernel.current env' (sysRun Ledger.current cfg Kernel.current released tr).1.world.node c
      = false := by
  have hshape : ∀ x ∈ released.world.node.cands, x.id = 1 →
      x.hot = true ∧ x.windowClose = none ∧ x.expiry = Wall.sample 120 := by decide
  obtain ⟨hhot, hwc, hexp⟩ := hshape c hc hid
  have hpast : released.world.node.ratchet.atOrBefore (Wall.sample 120) = false := by decide
  have hbelow := Effective.not_atOrBefore_weaken hpast
    (sysRun_ratchet_never_lowered Ledger.current cfg Kernel.current tr released)
  refine never_due_below_ratchet rfl hhot ?_ env'
  simp [windowOpen, hwc, hexp, hbelow]

/-! ### `POL-20`: one node's count at the end of its composed run -/

/-- The composed per-node count with the ledger guards as they stand; all run premises remain. -/
@[req "POL-20"]
theorem countsAt_of_sysRun_with_current (cfg : Config) (r : Rules) (sys : Sys)
    (pre : List (Env × Event)) (last : Env × Event)
    (hm : MonotoneHotClock (pre ++ [last]))
    (a b : List (Env × Event)) (envR : Env) (cid : Nat) (d : Bool) (E : Wall) (sp es : Cand)
    (hsplit : pre ++ [last] = a ++ (envR, .accept cid d E sp es) :: b)
    (ha : admitted (sysRun Ledger.current cfg r sys a).1.world
      (sysStep Ledger.current cfg r envR (sysRun Ledger.current cfg r sys a).1 (.accept cid d E sp es)).1.world
      (.accept cid d E sp es) = true)
    (hfresh : holds (checked Ledger.current.release envR cfg.window (sysRun Ledger.current cfg r sys a).1.led
      (.accept cid d E sp es)) sp.id = false)
    (hwin : Mono.withinWindow envR.mono last.1.mono cfg.window = true)
    (hprune : pruneKeeps Ledger.current cfg r sp.id envR.mono sys (pre ++ [last]) = true) :
    countsAt cfg.window sp.id
      { led := (sysRun Ledger.current cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true := by
  exact countsAt_of_sysRun Ledger.current rfl rfl cfg r sys pre last hm a b envR cid d E sp es
    hsplit ha hfresh hwin hprune

/-- Two hot spends fit together under this cap. -/
def cohortCfg : Config := { cfg with cap := 2 * V }
def cohortNext : Cand := cand 5 hot2 true (some 30) 130
def cohortNextEsc : Cand := cand 6 esc2 false none 130

def cohortPre : List (Env × Event) :=
  [(envAt 0 0, .accept 10 false (Wall.sample 120) s1 e1)]
def cohortLast : Env × Event :=
  (envAt 10 10, .accept 20 false (Wall.sample 130) cohortNext cohortNextEsc)

/-- The first reservation is still counted after a later accepted hot admission's release check.
Both reservation samples lie inside the final sample's trailing interval. -/
@[req "POL-20"]
theorem composed_reservation_counted_with_current :
    countsAt cohortCfg.window s1.id
      { led := (sysRun Ledger.current cohortCfg Kernel.current sys0 (cohortPre ++ [cohortLast])).1.led,
        now := cohortLast.1.mono } = true ∧
    holds (sysRun Ledger.current cohortCfg Kernel.current sys0 (cohortPre ++ [cohortLast])).1.led
      cohortNext.id = true := by
  decide

/-! ### `POL-20`: a counted row keeps its own reservation time

`composed_reservation_counted_with_current` checks 10 seconds after the first reservation, with
nothing in between. The run below adds a peer's relay that runs the holder decision, a fire pass
that exposes the row, a replay of the same pair under a fresh Carrier, and a wall excursion past
the row's signed expiry and back, with a prune pass at its peak that collects the pair while the
row stays. Its last check runs at exactly the reservation time plus the
window, with the wall past that expiry: only the monotonic disjunct, at its inclusive boundary,
keeps the row (`POL-19`: "a reservation is released when both disjuncts are false"). -/

/-- The first hot spend, fire time 30 and signed expiry 130, and its Escape, accepted at wall and
HotClock 10. -/
def keptSp : Cand := cand 1 hot1 true (some 30) 130
def keptEsc : Cand := cand 2 esc1 false none 130
def keptEnvR : Env := envAt 10 10
def keptAccept : Event := .accept 10 false (Wall.sample 130) keptSp keptEsc

/-- The relay that runs the holder decision at 20, the fire pass at 30, the same pair replayed
under Carrier 20 at 40, the prune pass that collects the pair at wall 500 and HotClock 60, and the
wall back at 50 with HotClock 70. -/
def keptMid : List (Env × Event) :=
  [ (envAt 20 20, .receipt 10 1),
    (envAt 30 30, .firePass),
    (envAt 40 40, .accept 20 false (Wall.sample 150) keptSp keptEsc),
    (envAt 500 60, .prune),
    (envAt 50 70, .tick) ]
def keptPre : List (Env × Event) := (keptEnvR, keptAccept) :: keptMid

/-- The second spend accepted at wall 131 and HotClock 130 = 10 + 120. -/
def keptLast : Env × Event := (envAt 131 130, .accept 30 false (Wall.sample 241) next nextEsc)
def keptRun : Sys :=
  (sysRun Ledger.current cohortCfg Kernel.current sys0 (keptPre ++ [keptLast])).1

/-- At the last check the first row has its commitment, its original reservation time, its signed
expiry and its exposure bit set, and it is counted (`POL-18`: "a retry keeps the original
reservation time"; `SPN-33`: "the ledger retains its original reservation time, expiry and
exposure state independently of candidate residency"). -/
@[req "POL-20"]
theorem composed_row_time_kept_with_current :
    keptRun.led.map (fun r => (r.cid, r.reservedAt, r.expiry, r.exposed)) =
      [(1, Mono.sample 10, Wall.sample 130, true), (5, Mono.sample 130, Wall.sample 241, false)] ∧
    countsAt cohortCfg.window keptSp.id { led := keptRun.led, now := keptLast.1.mono } = true := by
  decide

/-- `countsAt_of_sysRun_with_current` applies to this run: its premises hold across the exposure, the
replay, the prune pass and the wall excursion. -/
@[req "POL-20"]
theorem composed_row_counted_by_theorem_with_current :
    countsAt cohortCfg.window keptSp.id { led := keptRun.led, now := keptLast.1.mono } = true :=
  countsAt_of_sysRun_with_current cohortCfg Kernel.current sys0 keptPre keptLast
    (by simp only [keptPre, keptMid, keptLast, List.cons_append, List.nil_append,
      MonotoneHotClock]; decide)
    [] (keptMid ++ [keptLast]) keptEnvR 10 false (Wall.sample 130) keptSp keptEsc rfl
    (by decide) (by decide) (by decide) (by decide)

/-! ### `POL-21`: a frozen candidate's refund, at the prune pass that collects it

Through the composed step, not a ledger function called on a node pruned by hand. -/

/-- `s1` accepted at 0 under duress, so its holder decision at 10 arms the node and freezes it
(`DUR-11`); then the prune pass at wall and HotClock 121, past `s1`'s signed expiry of 120 and
its Escape's window. -/
def frozenPrune : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 true (Wall.sample (expiryOf 0)) s1 e1),
    (envAt 10 10, .receipt 10 1),
    (envAt 121 121, .prune) ]

/-- `POL-21`: "the frozen candidate's reservation is refunded at `SPN-41`'s prune pass that
collects it". The freeze leaves the charge standing; the prune pass at 121 collects `s1` and its Escape, and the
same composed step refunds the charge. A refund that waited for a later prune pass would leave it. -/
@[req "POL-21"]
theorem frozen_charge_refunded_at_collecting_prune :
    (runAt Ledger.current (frozenPrune.take 2)).1.world.node.cands.any
      (fun c => c.id == 1 && c.frozen) = true ∧
    (runAt Ledger.current (frozenPrune.take 2)).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current frozenPrune).1.world.node.cands = [] ∧
    (runAt Ledger.current frozenPrune).1.led = [] := by decide

end BtcPolicy.Exhibits.HotLedger
