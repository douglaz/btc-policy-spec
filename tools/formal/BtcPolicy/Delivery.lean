import BtcPolicy.Req
/-! The Operator's delivery knowledge and the output its watch polls. The reducer's contract
is `OPR-49`, quoted below; once an attempt might have delivered bytes, a later error cannot
restore certainty of non-delivery.

`OPR-49`: "The state starts “definitely not sent”, advances to “possibly delivered, exact bytes” on
EVERY attempt that is not `NotSent` — BEFORE the status line or body is decoded — and never moves
backward." `OPR-51` reads the state the loop ends in: "If EVERY endpoint was `NotSent`, the program
does not watch", and that is "the only outcome that authorizes reissuing a signed request
(`DEF-8`)".

Two guard parameters in one `current` record: where `NotSent` is reachable (`DEF-8`) and how the
watched output is chosen (`F56`). The theorems here hold under every value; `Exhibits.lean` holds
the ones over `current`, so a flip goes red there and nowhere else. Beside each parameter is its
trace under the withdrawn value.

**Not modelled.** `OPR-50`'s byte bounds and framing, which reach this module only as members of
the failure class; the watch loop's cadence, its final poll at the deadline and its latched report
failure; `OPR-51`'s warning text; and the poll verdict — the target is modelled, not the match.
Whether a response's bytes were decoded is not an input: the state advances "BEFORE the status line
or body is decoded". -/

namespace BtcPolicy.Delivery

/-! ## One attempt, and what the Operator knows after it -/

/-- A failure after connect returned. `OPR-49`: "once connect returns, every timeout, partial
write, read or framing failure is possible delivery"; `OPR-50`: "crossing the cap is a typed
ambiguous failure". -/
inductive Failure
  | timeout | partialWrite | read | framing | capCrossed
  deriving DecidableEq, Repr

/-- One endpoint's attempt. `notSent` is the one pre-connect outcome — `OPR-49`: "`NotSent` is
reachable ONLY when connect fails before any request byte could be written", and `OPR-48`: "An
endpoint reached at or after the aggregate is pre-connect `NotSent` and opens no socket". Every
other constructor is an attempt whose connect returned. -/
inductive Outcome
  | notSent
  /-- A `200` `accepted`, with the `commitment_id` the peer returned. -/
  | accepted (commitmentId : Nat)
  | nonceReplayed
  /-- `400`. -/
  | badRequest
  /-- `413`. -/
  | tooLarge
  /-- Any other status line. -/
  | otherStatus (code : Nat)
  | failed (f : Failure)
  deriving DecidableEq, Repr

/-- `OPR-49`'s two states, in its words: "definitely not sent" and "possibly delivered, exact
bytes". -/
inductive Knowledge
  | definitelyNotSent | possiblyDelivered
  deriving DecidableEq, Repr

/-! ## Guard parameters (`ADR-0023` decision 6), one `current` -/

/-- Where `NotSent` is reachable. `DEF-8`'s prohibition: "a `NotSent` outcome reachable only
before connect". `preConnectOnly` is that; `failureReadAsNotSent` reads a failure after connect — a
timeout, a partial write, a read or framing failure — as not sent, which leaves the knowledge where
it was. A status is a post-write fact under either value: `DEF-8` says "any post-write status,
`400` and `413` included, is possible delivery". -/
inductive NotSentReach
  | preConnectOnly | failureReadAsNotSent
  deriving DecidableEq, Repr

/-- How the watched output is chosen. `byKind` is `OPR-51`'s table as it stands; `outputOne` is the
withdrawn output-1 watch (`F56`). `OPR-51` now chooses "output 0 of the transaction for
`clawback` and for `refresh`, neither of which has an output 1". -/
inductive WatchChoice
  | byKind | outputOne
  deriving DecidableEq, Repr

structure Rules where
  notSent : NotSentReach
  watch : WatchChoice
  deriving DecidableEq, Repr

/-- `OPR-49` and `OPR-51` as they stand. -/
@[req "OPR-49"]
def current : Rules := { notSent := .preConnectOnly, watch := .byKind }

/-! ## The reducer, the stop rule and the run (`OPR-49`) -/

/-- The outcomes that leave the knowledge where it was: `NotSent`, and under the withdrawn value of
`DEF-8`'s parameter a failure after connect. -/
@[req "OPR-49"]
def readAsNotSent (r : Rules) : Outcome → Bool
  | .notSent => true
  | .failed _ =>
    match r.notSent with
    | .preConnectOnly => false
    | .failureReadAsNotSent => true
  | _ => false

/-- `OPR-49`: the state advances "on EVERY attempt that is not `NotSent`" and "never moves
backward". -/
@[req "OPR-49"]
def advance (r : Rules) (k : Knowledge) (o : Outcome) : Knowledge :=
  if readAsNotSent r o then k else .possiblyDelivered

/-- Whether an attempt stops the loop, read from the knowledge ENTERING it. `OPR-49`:
"`NONCE_REPLAYED` stops the loop only when the state immediately before that attempt was already
possibly-delivered, so a preceding `400` counts; on a first attempt a replay is someone else's and
the loop continues. The loop otherwise stops only on a `200` `accepted` whose `commitment_id`
equals the locally computed expected id". `API-16` says it from the coordinator's side: "stop on
an `accepted` whose `commitment_id` equals its own precomputed id or on a `NONCE_REPLAYED` that
follows a possible earlier delivery". -/
@[req "OPR-49"]
def stops (entering : Knowledge) (expected : Nat) : Outcome → Bool
  | .accepted cid => cid == expected
  | .nonceReplayed => entering == .possiblyDelivered
  | _ => false

/-- What a run of the loop leaves: the knowledge, and whether an `accepted` with the expected id
stopped it. -/
structure Result where
  knowledge : Knowledge
  accepted : Bool
  deriving DecidableEq, Repr

/-- The loop over the outcomes in `OPR-48`'s "manifest node and endpoint order", from a given
knowledge: each attempt advances it, and the first the stop rule stops returns — the endpoints
after it are never attempted. -/
@[req "OPR-49"]
def runFrom (r : Rules) (expected : Nat) (k : Knowledge) : List Outcome → Result
  | [] => ⟨k, false⟩
  | o :: os =>
    if stops k expected o then ⟨advance r k o, o == .accepted expected⟩
    else runFrom r expected (advance r k o) os

/-- The loop as the program runs it: "The state starts "definitely not sent"". -/
@[req "OPR-49"]
def run (r : Rules) (expected : Nat) (os : List Outcome) : Result :=
  runFrom r expected .definitelyNotSent os

/-- `OPR-51`: the program does not watch "If EVERY endpoint was `NotSent`", which is "the only
outcome that authorizes reissuing a signed request (`DEF-8`)". Read off the knowledge the run ends
in. -/
@[req "OPR-51"]
def reissue (res : Result) : Bool := res.knowledge == .definitelyNotSent

/-! ## The watch target (`OPR-51`) -/

/-- The three commands that relay a signed request and watch it. -/
inductive Kind
  | spend | clawback | refresh
  deriving DecidableEq, Repr

/-- The index of the output the watch polls. `OPR-51`: "output 1 of the primary — its vault change
— for `spend`, and output 0 of the transaction for `clawback` and for `refresh`, neither of which
has an output 1 (`OPR-68`, `OPR-65`)". Under the withdrawn value it is output 1 whatever the
kind. -/
@[req "OPR-51"]
def watchTarget (r : Rules) (k : Kind) : Nat :=
  match r.watch, k with
  | .byKind, .spend => 1
  | .byKind, .clawback => 0
  | .byKind, .refresh => 0
  | .outputOne, _ => 1

/-- The watched output exists among the composed transaction's outputs, given as their values in
output order. `OPR-51`'s success is "a non-null result matching both that output's composed value
and script", so an index past the last output has no composed value to match and no poll can
succeed. -/
@[req "OPR-51"]
def targetExists (r : Rules) (k : Kind) (outputs : List Nat) : Bool :=
  decide (watchTarget r k < outputs.length)

/-! ## Under every value of every parameter -/

/-- "never moves backward": from "possibly delivered, exact bytes" no outcome returns to "definitely
not sent", whatever the rules. -/
@[req "OPR-49"]
theorem advance_never_backward (r : Rules) (o : Outcome) :
    advance r .possiblyDelivered o = .possiblyDelivered := by
  unfold advance; split <;> rfl

/-- `NotSent` leaves the knowledge where it was, whatever the rules. -/
@[req "OPR-49"]
theorem notSent_leaves (r : Rules) (k : Knowledge) : advance r k .notSent = k := rfl

/-- The reducer's whole contract: it ends possibly-delivered iff it started there or the outcome is
not read as not sent. `Exhibits.lean` reads it at `current`. -/
@[req "OPR-49"]
theorem advance_possibly_iff (r : Rules) (k : Knowledge) (o : Outcome) :
    advance r k o = .possiblyDelivered ↔
      k = .possiblyDelivered ∨ readAsNotSent r o = false := by
  unfold advance
  cases h : readAsNotSent r o <;> cases k <;> simp

/-- A run entered possibly-delivered ends there: the attempt that stops it advances like any other,
and no later one moves the state backward. -/
@[req "OPR-49"]
theorem runFrom_possibly (r : Rules) (e : Nat) (os : List Outcome) :
    (runFrom r e .possiblyDelivered os).knowledge = .possiblyDelivered := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [runFrom, advance_never_backward]
    split
    · rfl
    · exact ih

/-- An outcome read as not sent never stops the loop: only an `accepted` and a replay do. -/
@[req "OPR-49"]
theorem readAsNotSent_continues (r : Rules) (k : Knowledge) (e : Nat) (o : Outcome)
    (h : readAsNotSent r o = true) : stops k e o = false := by
  cases o <;> simp_all [readAsNotSent, stops]

/-- `OPR-49`'s stop rule, case by case, under every rules value. A replay on a first attempt
continues: "on a first attempt a replay is someone else's and the loop continues". A replay after
a `400` stops: "so a preceding `400` counts". `400` and `413` "both advance it and both CONTINUE to
the next endpoint". A mismatched `accepted` "is not acceptance — it keeps that attempt's possible
delivery and continues". A matching one stops. -/
@[req "OPR-49"]
theorem stop_cases (r : Rules) (e : Nat) (k : Knowledge) :
    stops .definitelyNotSent e .nonceReplayed = false ∧
    stops (advance r k .badRequest) e .nonceReplayed = true ∧
    (stops k e .badRequest = false ∧ advance r k .badRequest = .possiblyDelivered) ∧
    (stops k e .tooLarge = false ∧ advance r k .tooLarge = .possiblyDelivered) ∧
    (∀ cid, cid ≠ e →
      stops k e (.accepted cid) = false ∧ advance r k (.accepted cid) = .possiblyDelivered) ∧
    stops k e (.accepted e) = true := by
  refine ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun cid h => ⟨?_, rfl⟩, ?_⟩ <;> simp [stops, *]

/-- The same cases as runs, under every rules value, where reading the knowledge ENTERING an
attempt is visible: a replay first continues, though that attempt advanced the knowledge, and the
matching `accepted` after it stops; after a `400` the replay stops the loop and the matching
`accepted` behind it is never attempted; a mismatched `accepted` continues. -/
@[req "OPR-49"]
theorem stop_runs (r : Rules) (e : Nat) :
    run r e [.nonceReplayed, .accepted e] = ⟨.possiblyDelivered, true⟩ ∧
    run r e [.badRequest, .nonceReplayed, .accepted e] = ⟨.possiblyDelivered, false⟩ ∧
    run r e [.accepted (e + 1), .tooLarge] = ⟨.possiblyDelivered, false⟩ := by
  simp [run, runFrom, stops, advance, readAsNotSent]

/-- Reissue, under every rules value, every expected id and every list of outcomes: authorized iff
every outcome is read as not sent. By induction on the list; `Exhibits.lean` reads it at
`current`, where only `NotSent` is. -/
@[req "OPR-51"]
theorem reissue_iff (r : Rules) (e : Nat) (os : List Outcome) :
    reissue (run r e os) = true ↔ ∀ o ∈ os, readAsNotSent r o = true := by
  unfold run reissue
  induction os with
  | nil => simp [runFrom]
  | cons o os ih =>
    by_cases h : readAsNotSent r o = true
    · simp only [runFrom, readAsNotSent_continues r _ e o h, advance, h]
      simp [ih, h]
    · have ha : advance r .definitelyNotSent o = .possiblyDelivered := by simp [advance, h]
      simp only [runFrom, ha]
      split <;> simp [runFrom_possibly, h]

/-! ## `DEF-8`'s twin under the withdrawn value

Three endpoints, each failing after connect. `Exhibits.lean` holds the trace under `current`. -/

/-- The id the program computes locally; no attempt below returns it. -/
@[req "OPR-49"]
def expectedId : Nat := 7

/-- A timeout, a partial write, a read failure. -/
@[req "OPR-49"]
def def8Failures : List Outcome := [.failed .timeout, .failed .partialWrite, .failed .read]

/-- `DEF-8`'s second shape: the same three endpoints where the second returns `400`. -/
@[req "OPR-49"]
def def8Status : List Outcome := [.failed .timeout, .badRequest, .failed .read]

/-- `DEF-8`'s parameter withdrawn and the other as it stands, written out in full so a flip of
`current` reaches only the `current` twin. -/
@[req "OPR-49"]
def withdrawnNotSent : Rules := { notSent := .failureReadAsNotSent, watch := .byKind }

/-- Under the withdrawn value the three failures leave the run "definitely not sent" and reissue is
authorized: a signed request reissued while its bytes may already be in a node's ingress. -/
@[req "OPR-51"]
theorem def8_admitted_with_withdrawn :
    run withdrawnNotSent expectedId def8Failures = ⟨.definitelyNotSent, false⟩ ∧
    reissue (run withdrawnNotSent expectedId def8Failures) = true := by
  decide

/-- The `400` shape is refused under the withdrawn value too: a status is a post-write fact under
either reading, so the twin's contrast is the failure class alone. -/
@[req "OPR-51"]
theorem def8_status_refused_with_withdrawn :
    run withdrawnNotSent expectedId def8Status = ⟨.possiblyDelivered, false⟩ ∧
    reissue (run withdrawnNotSent expectedId def8Status) = false := by
  decide

/-! ## `F56`'s twin under the withdrawn value

Each transaction's outputs as their values in satoshis, in output order. `Exhibits.lean` holds the
trace under `current`. -/

/-- A `spend`'s primary: output 0 pays the destination and output 1 is "its vault change". -/
@[req "OPR-51"]
def spendOutputs : List Nat := [40000, 59000]

/-- `OPR-68`'s claw-back "pays exactly one output to the escape descriptor … carries no vault
change". -/
@[req "OPR-51"]
def clawbackOutputs : List Nat := [98000]

/-- `OPR-65`'s refresh: "one one-input, one-output transaction per coin". -/
@[req "OPR-51"]
def refreshOutputs : List Nat := [99000]

/-- `F56`'s parameter withdrawn and the other as it stands, written out in full so a flip of
`current` reaches only the `current` twin. -/
@[req "OPR-51"]
def withdrawnWatch : Rules := { notSent := .preConnectOnly, watch := .outputOne }

/-- Under the withdrawn value the watch polls output 1 for every kind: the `spend` has one, and
neither the claw-back nor the refresh does, so the watch of `OPR-51` cannot succeed on any poll of
either. -/
@[req "OPR-51"]
theorem f56_target_missing_with_withdrawn :
    targetExists withdrawnWatch .clawback clawbackOutputs = false ∧
    targetExists withdrawnWatch .refresh refreshOutputs = false ∧
    targetExists withdrawnWatch .spend spendOutputs = true := by
  decide

end BtcPolicy.Delivery
