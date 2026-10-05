import BtcPolicy.Watchtower
import BtcPolicy.Encode
/-! Watchtower recognition and the alert queue. The
watchtower is a duty of every node and not a deployment (`ADR-0001`, "Vault nodes are the
watchtower"). The cursor, the scan proof and the pass this module extends are `Watchtower.lean`'s,
whose `pass` is called and never restated; the chain vocabulary is `Chain.lean`'s; a witness
element and a script are `Encode.lean`'s `Bytes`, the shape `Witness.lean` builds a stack from.
`Scan.spends` stays the opaque spend ids a scan finds: what recognition needs about a spend
comes from a model parameter keyed by that id, as `VaultUnspent.Ledger` keys outputs by height
and hash.

`WTC-17`: "Every node MUST scan its own chain every 10 seconds, first pass immediate, for every
spend of the vault's script, and classify each spend with this precedence: a witness whose
branch selector is the empty push (`CHN-9`) is a `RECOVERY_PATH_SPEND`, even if the txid is in
the authorized set; otherwise a txid NOT in the node's vault-authorized set is an
`UNRECOGNIZED_SPEND`; otherwise no alert". The cadence is timing and is not modelled: machine
timing is not claimed by the formal layer (`Silence.lean`).

`WTC-22`: "Alert delivery is coordinator-pull (`ADR-0002`); nodes never push. The operator
program's consumption of the queue is `OPR-60`. Watchtower duty continues during Lockdown."
Coordinator-pull and `OPR-60`'s consumer are docstring clauses here; the Lockdown clause is
`duty_ignores_lockdown`.

One guard parameter (`ADR-0023` decision 6), recognition: `validated` is `WTC-18` as it stands,
`coSigned` and `evaluated` are the two readings `WTC-18`'s own sentences refute. The theorems
here hold under every value or under every value but the one that refutes them; `Exhibits.lean`
holds every theorem over `current`, so a flip goes red there and nowhere else. Beside the
parameter sit the federation's two twins, stated under the refuted readings `.coSigned` and
`.evaluated` in full.

**Silence.** The queue adds no observable divergence between the two PINs before the horizon,
and `Silence.lean`'s module docstring states the same argument. The queue is a function of two
inputs only: the chain scan, an environment input equal in both runs, and the authorized set,
which under `current` is `SPN-33`'s accepted txids. Under `Silence.Coupled` the accepted
candidates' transactions are equal (`Silence.pubCand_tx` keeps a candidate's `tx` through the
projection the coupling equates) and a refusal is the same refusal in both runs (`Silence.Obs`'s
`resp`, equal at every step by `Silence.silence` under that theorem's own hypotheses), so the
accepted sets are equal, the snapshots
`snapshot` takes are equal, and the queues `duty` leaves are equal. Not claimed: anything at or
past the horizon, a compromised node or failure of `SEC-10`'s "release-history premise", and
`NCH-16`'s freshness diagnostic, which is not a watchtower alert and is not an event of this
queue. The premise is "no node has run a compromised release while the current PINs were in
use" (`SEC-10`); queue equality under honest transitions does not establish that premise or
cover PIN history a compromised release left on the coordinator.

**Not modelled.** `SPN-33`'s writer, the acceptance that adds to the set, which is the kernel's:
the record is a model parameter. `API-17`'s read of the queue and `API-18`'s cursor rule; the
`txid:vout` and lowercase-hex renderings; `NCH-16`'s in-place update; `STO-9`'s thread ownership
beyond the citation; `DUR-22`'s use of the set at fire time; and the "loud message". -/

namespace BtcPolicy.Alerts
open BtcPolicy.Chain
open BtcPolicy.Encode (Bytes)
open BtcPolicy.Watchtower (Cursor CursorShape TipTest Scan Outcome candidate result proven
  belowNewest tipChanged pass)

/-! ## The spend as the scan sees it (`WTC-17`, `WTC-19`, `CHN-9`) -/

/-- A spend of the vault's script as the scan sees it: its txid, the vault outpoint it spends as
the pair `(txid, vout)`, the script it spends, and its witness as the ordered stack of elements.
`WTC-20` says the wire carries "`outpoint` as `txid:vout`, and `script` as lowercase hex"; the
renderings are the wire's, and the pair is the faithful shape because the outpoint is half of
the queue's dedup key, which an opaque id would not distinguish from the txid's part. -/
structure Spend where
  txid : Nat
  outpoint : Nat × Nat
  script : Bytes
  witness : List Bytes
  deriving DecidableEq, Repr

/-- The branch selector, read off the witness. `CHN-9`: "The selector is the second-to-last
element: a single `0x01` byte for the Normal (`OP_IF`) branch, an **empty** push for the
Recovery (`OP_ELSE`) branch". None when the stack has fewer than two elements. -/
@[req "CHN-9"]
def selector : List Bytes → Option Bytes
  | [] => none
  | [_] => none
  | [sel, _] => some sel
  | _ :: b :: c :: rest => selector (b :: c :: rest)

/-- The selector of any stack with at least two elements is its second-to-last, whatever lies
before it. -/
@[req "CHN-9"]
theorem selector_snoc (l : List Bytes) (sel last : Bytes) :
    selector (l ++ [sel, last]) = some sel := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons x xs =>
      simp only [List.cons_append] at ih ⊢
      cases hx : xs ++ [sel, last] with
      | nil => simp at hx
      | cons c rest' => rw [hx] at ih; rw [selector]; exact ih

/-- Recovery-branch identification, from the witness alone: the branch is Recovery iff the
selector is the empty push. The predicate takes no script, which is how the rule is stated.
`WTC-19`: "Recovery-branch identification MUST read the witness, not the script: both branches
share one scriptPubKey. A witness with fewer than two elements reads as non-recovery, which is
the safe default because it still alerts as unrecognised when unauthorized." -/
@[req "WTC-19"]
def isRecovery (w : List Bytes) : Bool := decide (selector w = some [])

/-- `WTC-19`: "A witness with fewer than two elements reads as non-recovery", universal over the
witness. -/
@[req "WTC-19"]
theorem short_witness_non_recovery (w : List Bytes) (h : w.length < 2) : isRecovery w = false := by
  match w with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- The branch is a function of the witness alone: two spends with one witness have one branch,
whatever their scripts. `WTC-19`: "MUST read the witness, not the script". -/
@[req "WTC-19"]
theorem branch_reads_witness_only (s s' : Spend) (h : s.witness = s'.witness) :
    isRecovery s.witness = isRecovery s'.witness := by
  rw [h]

/-! ## Recognition: the guard parameter (`WTC-18`, `ADR-0001` revised by `ADR-0012`) -/

/-- What makes a spend recognised: the guard parameter (`ADR-0023` decision 6). -/
inductive Recognition
  /-- `WTC-18` as it stands. `WTC-18`: "Recognition is by **validation and acceptance**, never
  by co-signing and never by evaluation". -/
  | validated
  /-- Recognition by the co-signed set, the reading `ADR-0012` revised: `ADR-0001` alerted on
  "any vault UTXO spend it never co-signed". `WTC-18`: "Only `t` of `n` nodes sign a legitimate
  spend, so “I did not sign it” false-alarms on `n − t` honest nodes". -/
  | coSigned
  /-- Recognition by evaluation, the accepted and the refused together, the reading `ADR-0012`
  refused in passing as "saw and policy-checked". `WTC-18`: "a spend a node REFUSED was
  evaluated, so “I evaluated it” would let an attacker fanning a theft to honest nodes suppress
  its own alert". -/
  | evaluated
  deriving DecidableEq, Repr

/-- `WTC-18` as it stands. `WTC-18`: "Recognition is by **validation and acceptance**, never by
co-signing and never by evaluation". `ADR-0001` read recognition off the co-signed set, and
`ADR-0012` revised that reading to validation: "Recognition is by VALIDATION, not by signing". -/
@[req "WTC-18"]
def current : Recognition := .validated

/-- What a node did with the requests it saw: the txids it accepted, those among them whose
partial went into the signing quorum, and those it refused. A model parameter: `SPN-33`'s
writer, the acceptance that adds to the set, is the kernel's and is not modelled here. `SPN-33`:
"On acceptance the node MUST add the spend's, the Escape's and every rung's txid to its
**vault-authorized set**, which the watchtower recognises (`WTC-18`) and which qualifies
unconfirmed parents at fire time (`DUR-22`)." -/
structure Record where
  accepted : List Nat
  coSigned : List Nat
  refused : List Nat
  deriving DecidableEq, Repr

/-- A record is well-formed when every co-signed txid is an accepted one — a node signs only what
it accepted — and no txid is both accepted and refused. -/
@[req "WTC-18"]
def Record.wf (r : Record) : Prop :=
  (∀ t ∈ r.coSigned, t ∈ r.accepted) ∧ ∀ t ∈ r.refused, t ∉ r.accepted

/-- The authorized set under a guard value, taken as a value: the snapshot `WTC-21` names, "The
watchtower MUST snapshot the authorized set and release its lock BEFORE the slow chain read".
Under `validated` it is `SPN-33`'s set, the accepted txids. `WTC-18`: "The authorized set is the
txids of every spend, Escape, rung, refresh and claw-back this node accepted (`SPN-33`)". Under
`coSigned` it is the co-signed txids; under `evaluated` the accepted and the refused together. -/
@[req "WTC-18"]
def snapshot : Recognition → Record → List Nat
  | .validated, r => r.accepted
  | .coSigned, r => r.coSigned
  | .evaluated, r => r.accepted ++ r.refused

/-- Recognised: the txid is in the authorized set under the guard value. -/
@[req "WTC-18"]
def recognised (g : Recognition) (r : Record) (txid : Nat) : Bool :=
  decide (txid ∈ snapshot g r)

/-- Under every value but `.coSigned`, over every record and txid: a txid the record accepted is
recognised — the accepted set is the snapshot under `.validated` and is in it under
`.evaluated`. -/
@[req "WTC-18"]
theorem accepted_recognised (g : Recognition) (hg : g ≠ .coSigned) (r : Record) (txid : Nat)
    (h : txid ∈ r.accepted) : recognised g r txid = true := by
  cases g with
  | validated => simp [recognised, snapshot, h]
  | coSigned => exact absurd rfl hg
  | evaluated => simp [recognised, snapshot, h]

/-- Under every value but `.evaluated`, over every well-formed record and txid: a txid the record
refused is not recognised — a refused txid is not accepted, and a co-signed one is. `WTC-18`:
"a spend a node REFUSED was evaluated" — and evaluation is not acceptance. -/
@[req "WTC-18"]
theorem refused_not_recognised (g : Recognition) (hg : g ≠ .evaluated) (r : Record) (txid : Nat)
    (hw : r.wf) (h : txid ∈ r.refused) : recognised g r txid = false := by
  cases g with
  | validated => simp [recognised, snapshot, hw.2 txid h]
  | coSigned =>
    simp only [recognised, snapshot, decide_eq_false_iff_not]
    exact fun hc => hw.2 txid h (hw.1 txid hc)
  | evaluated => exact absurd rfl hg

/-! ## Classification (`WTC-17`) -/

/-- `WTC-17`'s three outcomes. -/
inductive Verdict
  | recoveryPathSpend | unrecognizedSpend | recognised
  deriving DecidableEq, Repr

/-- The verdict on one spend against one snapshot, total. `WTC-17`: "classify each spend with
this precedence: a witness whose branch selector is the empty push (`CHN-9`) is a
`RECOVERY_PATH_SPEND`, even if the txid is in the authorized set; otherwise a txid NOT in the
node's vault-authorized set is an `UNRECOGNIZED_SPEND`; otherwise no alert". -/
@[req "WTC-17"]
def classify (snap : List Nat) (s : Spend) : Verdict :=
  if isRecovery s.witness then .recoveryPathSpend
  else if s.txid ∈ snap then .recognised
  else .unrecognizedSpend

/-- The precedence is total, over every snapshot and spend: Recovery iff the witness reads
Recovery. -/
@[req "WTC-17"]
theorem classify_recovery_iff (snap : List Nat) (s : Spend) :
    classify snap s = .recoveryPathSpend ↔ isRecovery s.witness = true := by
  by_cases hr : isRecovery s.witness = true
  · simp [classify, hr]
  · have hr' : isRecovery s.witness = false := by simpa using hr
    by_cases hm : s.txid ∈ snap <;> simp [classify, hr', hm]

/-- Unrecognized iff the witness does not read Recovery and the txid is not in the snapshot. -/
@[req "WTC-17"]
theorem classify_unrecognized_iff (snap : List Nat) (s : Spend) :
    classify snap s = .unrecognizedSpend ↔ isRecovery s.witness = false ∧ s.txid ∉ snap := by
  by_cases hr : isRecovery s.witness = true
  · simp [classify, hr]
  · have hr' : isRecovery s.witness = false := by simpa using hr
    by_cases hm : s.txid ∈ snap <;> simp [classify, hr', hm]

/-- No alert iff the witness does not read Recovery and the txid is in the snapshot. -/
@[req "WTC-17"]
theorem classify_recognised_iff (snap : List Nat) (s : Spend) :
    classify snap s = .recognised ↔ isRecovery s.witness = false ∧ s.txid ∈ snap := by
  by_cases hr : isRecovery s.witness = true
  · simp [classify, hr]
  · have hr' : isRecovery s.witness = false := by simpa using hr
    by_cases hm : s.txid ∈ snap <;> simp [classify, hr', hm]

/-- `WTC-17`: "The recovery exit is never swallowed, because stolen recovery keys are otherwise
silent and that detection is the watchtower's most important job" — a Recovery-branch spend's
verdict is Recovery for every snapshot, its txid in the set or not. -/
@[req "WTC-17"]
theorem recovery_never_swallowed (snap : List Nat) (s : Spend) (h : isRecovery s.witness = true) :
    classify snap s = .recoveryPathSpend := by
  simp [classify, h]

/-- The alert's kind: the two verdicts that alert. -/
inductive Kind
  | recoveryPathSpend | unrecognizedSpend
  deriving DecidableEq, Repr

/-- `WTC-20`: "An alert carries `kind`, `spend_txid`, `outpoint` as `txid:vout`, and `script` as
lowercase hex." The two renderings are the wire's and are not modelled. -/
structure Alert where
  kind : Kind
  spendTxid : Nat
  outpoint : Nat × Nat
  script : Bytes
  deriving DecidableEq, Repr

/-- The alert a verdict raises; none for no alert. -/
@[req "WTC-17"]
def alertOf (snap : List Nat) (s : Spend) : Option Alert :=
  match classify snap s with
  | .recoveryPathSpend => some ⟨.recoveryPathSpend, s.txid, s.outpoint, s.script⟩
  | .unrecognizedSpend => some ⟨.unrecognizedSpend, s.txid, s.outpoint, s.script⟩
  | .recognised => none

/-- The alerts a list of spend ids raises against a snapshot, in scan order, read through the
spend-record parameter. -/
@[req "WTC-17"]
def alertsOf (snap : List Nat) (spendOf : Nat → Spend) (ids : List Nat) : List Alert :=
  ids.filterMap fun i => alertOf snap (spendOf i)

/-! ## The federation's verdicts (`WTC-18`) -/

/-- The nodes among a list of records whose verdict on a spend is the given one. -/
@[req "WTC-18"]
def countVerdict (v : Verdict) (g : Recognition) (records : List Record) (s : Spend) : Nat :=
  (records.filter fun r => classify (snapshot g r) s == v).length

/-- The nodes among a list of records whose verdict on a spend is an alert. -/
@[req "WTC-18"]
def alerting (g : Recognition) (records : List Record) (s : Spend) : Nat :=
  (records.filter fun r => classify (snapshot g r) s != .recognised).length

/-- Under every value but `.coSigned`, over every list of records and every Normal-branch spend:
a spend every record accepted alerts on none. `WTC-18`: "A legitimate spend is accepted by all
`n` and alerts nowhere". -/
@[req "WTC-18"]
theorem accepted_everywhere_silent (g : Recognition) (hg : g ≠ .coSigned) (records : List Record)
    (s : Spend) (hr : isRecovery s.witness = false) (h : ∀ r ∈ records, s.txid ∈ r.accepted) :
    alerting g records s = 0 := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    have hc : classify (snapshot g r) s = .recognised :=
      (classify_recognised_iff _ _).2
        ⟨hr, of_decide_eq_true (accepted_recognised g hg r s.txid (h r (by simp)))⟩
    simp only [alerting] at ih ⊢
    rw [List.filter_cons_of_neg (by simp [hc])]
    exact ih fun x hx => h x (by simp [hx])

/-- Under every value but `.evaluated`, over every list of well-formed records and every spend:
a spend every record refused alerts on all. `WTC-18`: "a theft the honest nodes refuse is in
nobody's set and alerts everywhere". -/
@[req "WTC-18"]
theorem refused_everywhere_alerts (g : Recognition) (hg : g ≠ .evaluated) (records : List Record)
    (s : Spend) (h : ∀ r ∈ records, r.wf ∧ s.txid ∈ r.refused) :
    alerting g records s = records.length := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    have hn : s.txid ∉ snapshot g r :=
      of_decide_eq_false (refused_not_recognised g hg r s.txid (h r (by simp)).1 (h r (by simp)).2)
    have hc : classify (snapshot g r) s ≠ .recognised :=
      fun e => hn ((classify_recognised_iff _ _).1 e).2
    simp only [alerting] at ih ⊢
    rw [List.filter_cons_of_pos (by simp [hc]), List.length_cons, List.length_cons]
    rw [ih fun x hx => h x (by simp [hx])]

/-! ## The alert queue (`WTC-20`) -/

/-- `WTC-20`: "capped at 1 024 events with the oldest evicted first". -/
@[req "WTC-20"] def capacity : Nat := 1024

/-- A retained event: a watchtower alert with its sequence number. Watchtower alerts and nothing
else. `WTC-20`: "Freshness diagnostics are keyed per peer and coalesced by `NCH-16`" — a
different event with in-place update semantics, out of scope here. -/
structure Event where
  seq : Nat
  alert : Alert
  deriving DecidableEq, Repr

/-- The alert queue: the retained events, oldest first, each with its number, and the next
number to assign. `WTC-20`: "The **alert queue** is RAM-only, capped at 1 024 events with the
oldest evicted first, sequence-numbered from 1, and served by `API-17`." The dedup key is read
off the retained events and no separate key set is kept, so an evicted entry releases its key by
construction. `API-17`'s read and `API-18`'s cursor are not modelled: the next number is kept in
the state so that read is derivable, and nothing is claimed about it. -/
structure Queue where
  events : List Event
  next : Nat
  deriving DecidableEq, Repr

/-- The empty queue: nothing retained, the next number 1. `WTC-20`: "sequence-numbered from 1". -/
@[req "WTC-20"]
def Queue.empty : Queue := { events := [], next := 1 }

/-- The dedup key. `WTC-20`: "Watchtower alerts are deduplicated on `spend_txid:outpoint`". -/
@[req "WTC-20"]
def Alert.key (a : Alert) : Nat × (Nat × Nat) := (a.spendTxid, a.outpoint)

/-- Whether some retained event carries the key. -/
@[req "WTC-20"]
def Queue.retains (q : Queue) (k : Nat × (Nat × Nat)) : Bool :=
  q.events.any fun e => decide (e.alert.key = k)

/-- Enqueue. `WTC-20`: "a re-scan of a retained spend never re-enqueues, and an evicted entry's
key is released so a later scan may re-alert it". A key already retained enqueues nothing and
consumes no number; otherwise the event takes the next number, the number advances, and if the
length now exceeds `capacity` the oldest is dropped. -/
@[req "WTC-20"]
def enqueue (q : Queue) (a : Alert) : Queue :=
  if q.retains a.key then q
  else
    let evs := q.events ++ [⟨q.next, a⟩]
    { events := if capacity < evs.length then evs.tail else evs, next := q.next + 1 }

/-- Alerts enqueued in order. -/
@[req "WTC-20"]
def enqueueAll (q : Queue) (alerts : List Alert) : Queue := alerts.foldl enqueue q

/-- Strictly ascending sequence numbers. -/
@[req "WTC-20"]
def ascending : List Event → Bool
  | a :: b :: rest => a.seq < b.seq && ascending (b :: rest)
  | _ => true

/-- The invariant: at most `capacity` events, their numbers strictly ascending, every one below
the next to assign. -/
@[req "WTC-20"]
def Queue.wf (q : Queue) : Prop :=
  q.events.length ≤ capacity ∧ ascending q.events = true ∧ ∀ e ∈ q.events, e.seq < q.next

/-- The empty queue satisfies it, with the next number 1. -/
@[req "WTC-20"]
theorem empty_wf : Queue.empty.wf ∧ Queue.empty.next = 1 :=
  ⟨⟨by decide, rfl, by intro e h; cases h⟩, rfl⟩

/-- An ascending list's tail is ascending. -/
@[req "WTC-20"]
theorem ascending_tail (l : List Event) (h : ascending l = true) : ascending l.tail = true := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp only [ascending, Bool.and_eq_true] at h; exact h.2

/-- Appending a number above every retained one keeps the list ascending. -/
@[req "WTC-20"]
theorem ascending_snoc (l : List Event) (e : Event) (hl : ascending l = true)
    (hb : ∀ x ∈ l, x.seq < e.seq) : ascending (l ++ [e]) = true := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => simp [ascending, hb a (by simp)]
    | cons b rest' =>
      simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.cons_append, ascending, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, ih hl.2 fun x hx => hb x (by simp [hx])⟩

/-- Enqueue preserves the invariant, over every queue and alert: the length never exceeds
`capacity`, and the numbers stay strictly ascending and below the next. -/
@[req "WTC-20"]
theorem enqueue_wf (q : Queue) (a : Alert) (h : q.wf) : (enqueue q a).wf := by
  obtain ⟨hlen, hasc, hlt⟩ := h
  by_cases hr : q.retains a.key = true
  · simp only [enqueue, hr, ↓reduceIte]; exact ⟨hlen, hasc, hlt⟩
  · have hr' : q.retains a.key = false := by simpa using hr
    have hmem : ∀ e ∈ q.events ++ [⟨q.next, a⟩], e.seq < q.next + 1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact Nat.lt_succ_of_lt (hlt e he)
      · simp at he; subst he; exact Nat.lt_succ_self _
    have hasc' : ascending (q.events ++ [⟨q.next, a⟩]) = true := ascending_snoc _ _ hasc hlt
    simp only [enqueue, hr', Bool.false_eq_true, ↓reduceIte, Queue.wf]
    refine ⟨?_, ?_, ?_⟩
    · split
      · simp only [List.length_tail, List.length_append, List.length_singleton]; omega
      · rename_i hc; simp only [List.length_append, List.length_singleton] at hc ⊢; omega
    · split
      · exact ascending_tail _ hasc'
      · exact hasc'
    · intro e he
      split at he
      · exact hmem e (List.mem_of_mem_tail he)
      · exact hmem e he

/-- Enqueueing any list keeps the invariant, over every well-formed queue: `WTC-20`'s cap, and
numbers strictly ascending and below the next. From `Queue.empty` the next number is 1
(`empty_wf`): "sequence-numbered from 1". -/
@[req "WTC-20"]
theorem enqueueAll_wf (q : Queue) (alerts : List Alert) (h : q.wf) : (enqueueAll q alerts).wf := by
  induction alerts generalizing q with
  | nil => exact h
  | cons a rest ih => exact ih _ (enqueue_wf q a h)

/-- `WTC-20`: "a re-scan of a retained spend never re-enqueues" — a key already retained enqueues
nothing, over every queue and alert. -/
@[req "WTC-20"]
theorem enqueue_retained (q : Queue) (a : Alert) (h : q.retains a.key = true) :
    enqueue q a = q := by
  simp [enqueue, h]

/-- Retained means some retained event carries the key. -/
@[req "WTC-20"]
theorem retains_iff (q : Queue) (k : Nat × (Nat × Nat)) :
    q.retains k = true ↔ ∃ e ∈ q.events, e.alert.key = k := by
  simp [Queue.retains]

/-- Enqueue with a fresh key appends: the new event is last, numbered `q.next`. -/
@[req "WTC-20"]
theorem enqueue_fresh_last (q : Queue) (a : Alert) (h : q.retains a.key = false) :
    ∃ front, (enqueue q a).events = front ++ [⟨q.next, a⟩] := by
  obtain ⟨events, next⟩ := q
  simp only [enqueue, h, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hc
    cases events with
    | nil => simp [capacity] at hc
    | cons c cs => exact ⟨cs, by simp⟩
  · exact ⟨events, rfl⟩

/-- An alert once enqueued is retained, over every queue: the new event is last and eviction
drops the oldest. -/
@[req "WTC-20"]
theorem enqueue_retains_self (q : Queue) (a : Alert) : (enqueue q a).retains a.key = true := by
  by_cases hr : q.retains a.key = true
  · simp only [enqueue, hr, ↓reduceIte]
  · have hr' : q.retains a.key = false := by simpa using hr
    obtain ⟨front, hf⟩ := enqueue_fresh_last q a hr'
    rw [retains_iff, hf]
    exact ⟨⟨q.next, a⟩, by simp, rfl⟩

/-- Enqueue at capacity with a fresh key: the oldest event is dropped and the new one is last. -/
@[req "WTC-20"]
theorem enqueue_full (q : Queue) (a : Alert) (e : Event) (rest : List Event)
    (hq : q.events = e :: rest) (hcap : q.events.length = capacity) (ha : q.retains a.key = false) :
    (enqueue q a).events = rest ++ [⟨q.next, a⟩] := by
  obtain ⟨events, next⟩ := q
  simp only at hq hcap
  subst hq
  simp only [enqueue, ha, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · rename_i hc
    exfalso
    simp only [List.length_append, List.length_cons] at hc hcap
    omega

/-- Eviction releases the key. `WTC-20`: "an evicted entry's key is released so a later scan may
re-alert it" — a queue at capacity whose oldest event alone carries `k`, enqueued with a fresh
key, does not retain `k`, and a later alert with key `k` is then appended, last and numbered
next. Universal over the queue and both alerts. -/
@[req "WTC-20"]
theorem evicted_key_released (q : Queue) (e : Event) (rest : List Event) (a b : Alert)
    (hq : q.events = e :: rest) (hcap : q.events.length = capacity)
    (hk : ∀ x ∈ rest, x.alert.key ≠ e.alert.key) (ha : q.retains a.key = false)
    (hb : b.key = e.alert.key) :
    (enqueue q a).retains e.alert.key = false ∧
      ∃ front, (enqueue (enqueue q a) b).events = front ++ [⟨(enqueue q a).next, b⟩] := by
  have hne : a.key ≠ e.alert.key := by
    intro heq
    have hmem : e ∈ q.events := by rw [hq]; simp
    have : q.retains a.key = true := (retains_iff q a.key).mpr ⟨e, hmem, heq.symm⟩
    rw [ha] at this; cases this
  have hev : (enqueue q a).events = rest ++ [⟨q.next, a⟩] := enqueue_full q a e rest hq hcap ha
  have hrel : (enqueue q a).retains e.alert.key = false := by
    rw [Bool.eq_false_iff]
    intro h'
    rw [retains_iff, hev] at h'
    obtain ⟨x, hx, hxk⟩ := h'
    rcases List.mem_append.mp hx with hx | hx
    · exact hk x hx hxk
    · simp at hx; subst hx; exact hne hxk
  exact ⟨hrel, enqueue_fresh_last (enqueue q a) b (by rw [hb]; exact hrel)⟩

/-- `WTC-14`: "The alert queue's dedup makes every redundant re-scan harmless." One alert enqueued
twice is enqueued once, over every queue. -/
@[req "WTC-14"]
theorem enqueue_twice (q : Queue) (a : Alert) : enqueue (enqueue q a) a = enqueue q a :=
  enqueue_retained _ _ (enqueue_retains_self q a)

/-- A re-scan of retained spends changes nothing: alerts whose keys the queue retains enqueue
nothing, however many, over every queue and list. -/
@[req "WTC-14"]
theorem enqueueAll_retained (q : Queue) (alerts : List Alert)
    (h : ∀ a ∈ alerts, q.retains a.key = true) : enqueueAll q alerts = q := by
  induction alerts with
  | nil => rfl
  | cons a rest ih =>
    simp only [enqueueAll, List.foldl_cons, enqueue_retained q a (h a (by simp))]
    exact ih fun x hx => h x (by simp [hx])

/-- Enqueueing a list of alerts twice is enqueueing it once, whenever the first pass leaves every
one of them retained. The hypothesis is the word "retained": a pass of more than `capacity`
alerts evicts its own oldest, and a queue whose oldest event already carries one of the pass's
keys may evict it during the pass; in both an evicted key is released by `WTC-20`'s own rule, and
a re-scan re-alerts it by that rule. -/
@[req "WTC-14"]
theorem enqueueAll_twice (q : Queue) (alerts : List Alert)
    (h : ∀ a ∈ alerts, (enqueueAll q alerts).retains a.key = true) :
    enqueueAll (enqueueAll q alerts) alerts = enqueueAll q alerts :=
  enqueueAll_retained _ _ h

/-! ## The duty: one watchtower pass with recognition (`WTC-21`, `WTC-22`, `WTC-14`) -/

/-- The spends a pass bound: `Watchtower.result`'s spends when `pass` takes the candidate — a
scan, proven and the cursor's range, on a pass whose tip is not below the newest anchor and whose
tip test found no change — and none otherwise. The conditions are `pass`'s own, read from its
definition, so that a scan `pass` discards is one that binds nothing here; the tip test is
`Watchtower.lean`'s guard parameter, taken as an argument here as the cursor's shape is. -/
@[req "WTC-21"]
def bound (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) : Outcome → List Nat
  | .scanned s =>
    if belowNewest c tip || tipChanged tt tip s.after then []
    else ((result sh c s).map (·.2)).getD []
  | _ => []

/-- The lock touches of one pass, in the order `WTC-21` fixes. `STO-9` owns the general
lock-order rule and the rule that the `/events` read runs its lock touches in a dedicated
blocking section; neither is restated here. -/
inductive Step
  | snapshotAuthorized | releaseAuthorizedLock | chainRead | scanProof | alertLock
  deriving DecidableEq, Repr

/-- The duty: one watchtower pass with recognition, yielding the cursor after, the queue after
and the lock touches it made. The cursor after is `Watchtower.pass`, called and not restated.
The spends are consumed only when the pass bound them (`bound`), each classified against the
snapshot and its alert, if any, enqueued in scan order.

The signature is the statement of `WTC-21`: "The watchtower MUST snapshot the authorized set and
release its lock BEFORE the slow chain read, so a concurrent ingress is never blocked on chain
I/O, and MUST take the alert lock only after the scan has been proven (`WTC-12`)". The snapshot
is an argument taken before the scan, and the live set is not an argument at all; the alert lock
is emitted last and only when a proven scan bound an alert (`alert_lock_only_after_proof`).

The Lockdown latch is an argument the duty provably ignores (`duty_ignores_lockdown`). It is an
argument at all because `WTC-22` forbids a gate on it, and a function that takes the latch and
demonstrably does not read it is the model of no gate; `DUR-7`'s "Lockdown blocks NEW signing"
gates signing, which is not this duty. -/
@[req "WTC-21"]
def duty (sh : CursorShape) (tt : TipTest) (snap : List Nat) (_lockedDown : Bool) (c : Cursor)
    (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue) : Cursor × Queue × List Step :=
  let alerts := alertsOf snap spendOf (bound sh tt c tip o)
  (pass sh tt c tip o, enqueueAll q alerts,
    [.snapshotAuthorized, .releaseAuthorizedLock, .chainRead, .scanProof] ++
      if alerts.isEmpty then [] else [.alertLock])

/-- The cursor after is the pass's, over every input. -/
@[req "WTC-14"]
theorem duty_cursor (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool) (c : Cursor)
    (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue) :
    (duty sh tt snap l c tip o spendOf q).1 = pass sh tt c tip o := rfl

/-- `WTC-22`: "Watchtower duty continues during Lockdown" — the duty's result is the same with the
latch set and clear, over every other argument. `DUR-7`: "Lockdown is a latch that survives for
the process lifetime with no reset"; the kernel's latch is `BtcPolicy.Kernel.Node.lockedDown`,
and a `Bool` carries what the duty is required not to read. -/
@[req "WTC-22"]
theorem duty_ignores_lockdown (sh : CursorShape) (tt : TipTest) (snap : List Nat) (c : Cursor)
    (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue) :
    duty sh tt snap true c tip o spendOf q = duty sh tt snap false c tip o spendOf q := rfl

/-- When the pass takes the candidate — tip not below the newest anchor, the tip test finding no
change, a proven scan of the cursor's range — the bound spends are the scan's and the cursor after
is the candidate. -/
@[req "WTC-21"]
theorem bound_when_taken (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (s : Scan)
    (c' : Cursor) (hb : belowNewest c tip = false) (ht : tipChanged tt tip s.after = false)
    (hc : candidate sh c s = some c') :
    bound sh tt c tip (.scanned s) = s.spends ∧ pass sh tt c tip (.scanned s) = c' := by
  simp [bound, pass, hb, ht, result, hc]

/-- Anything bound came from a scan the pass took: the outcome was a scan, the tip was not below
the newest anchor, the tip test found no change, and the candidate exists. -/
@[req "WTC-21"]
theorem bound_nonempty (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (o : Outcome)
    (h : bound sh tt c tip o ≠ []) :
    ∃ s c', o = .scanned s ∧ belowNewest c tip = false ∧ tipChanged tt tip s.after = false ∧
      candidate sh c s = some c' ∧ bound sh tt c tip o = s.spends := by
  cases o with
  | errored => exact absurd rfl h
  | panicked => exact absurd rfl h
  | scanned s =>
    simp only [bound] at h ⊢
    by_cases hc : (belowNewest c tip || tipChanged tt tip s.after) = true
    · simp [hc] at h
    · have hc' : (belowNewest c tip || tipChanged tt tip s.after) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [Bool.or_eq_false_iff] at hc'
      cases hcand : candidate sh c s with
      | none => simp [result, hcand] at h
      | some c' => exact ⟨s, c', rfl, hc'.1, hc'.2, hcand, by simp [result, hcand]⟩

/-- A candidate exists only for a proven scan. -/
@[req "WTC-12"]
theorem candidate_proven (sh : CursorShape) (c : Cursor) (s : Scan) (c' : Cursor)
    (h : candidate sh c s = some c') : proven c s = true := by
  unfold candidate at h
  split at h
  · rename_i hp; simp only [Bool.and_eq_true] at hp; exact hp.1
  · cases h

/-- `WTC-21`'s order, with alerts: the steps the duty emits are the snapshot, its release, the
chain read, the `WTC-12` proof, then the alert lock, exactly, whenever the pass bound an alert. -/
@[req "WTC-21"]
theorem steps_with_alerts (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool)
    (c : Cursor) (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue)
    (h : alertsOf snap spendOf (bound sh tt c tip o) ≠ []) :
    (duty sh tt snap l c tip o spendOf q).2.2 =
      [.snapshotAuthorized, .releaseAuthorizedLock, .chainRead, .scanProof, .alertLock] := by
  cases hl : alertsOf snap spendOf (bound sh tt c tip o) with
  | nil => exact absurd hl h
  | cons a rest => simp [duty, hl]

/-- `WTC-21`'s order, without alerts: the same prefix and no alert lock, and the queue unchanged,
whenever the pass bound no alert — the scan discarded, or every bound spend recognised. -/
@[req "WTC-21"]
theorem steps_without_alerts (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool)
    (c : Cursor) (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue)
    (h : alertsOf snap spendOf (bound sh tt c tip o) = []) :
    (duty sh tt snap l c tip o spendOf q).2.2 =
        [.snapshotAuthorized, .releaseAuthorizedLock, .chainRead, .scanProof] ∧
      (duty sh tt snap l c tip o spendOf q).2.1 = q := by
  simp [duty, h, enqueueAll]

/-- `WTC-21`: "MUST take the alert lock only after the scan has been proven (`WTC-12`)" — the
alert lock is in the emitted steps only when the outcome was a proven scan the pass took, and
it bound an alert. -/
@[req "WTC-21"]
theorem alert_lock_only_after_proof (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool)
    (c : Cursor) (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue)
    (h : Step.alertLock ∈ (duty sh tt snap l c tip o spendOf q).2.2) :
    ∃ s, o = .scanned s ∧ proven c s = true ∧ belowNewest c tip = false ∧
      tipChanged tt tip s.after = false ∧ alertsOf snap spendOf s.spends ≠ [] := by
  have hne : alertsOf snap spendOf (bound sh tt c tip o) ≠ [] := by
    intro hnil
    simp [duty, hnil] at h
  have hb : bound sh tt c tip o ≠ [] := by
    intro hnil; apply hne; simp [alertsOf, hnil]
  obtain ⟨s, c', ho, h1, h2, h3, hbs⟩ := bound_nonempty sh tt c tip o hb
  exact ⟨s, ho, candidate_proven sh c s c' h3, h1, h2, by rw [← hbs]; exact hne⟩

/-- A scan `Watchtower.result` yields `none` for leaves the queue unchanged. -/
@[req "WTC-21"]
theorem duty_unproven (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool) (c : Cursor)
    (tip : Anchor) (s : Scan) (spendOf : Nat → Spend) (q : Queue) (h : result sh c s = none) :
    (duty sh tt snap l c tip (.scanned s) spendOf q).2.1 = q := by
  simp [duty, bound, alertsOf, enqueueAll, h]

/-- Composed with `Watchtower.unproven_binds_nothing`: a scan with any `WTC-12` check false
enqueues nothing. -/
@[req "WTC-12"]
theorem duty_unproven_check (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool)
    (c : Cursor) (tip : Anchor) (s : Scan) (spendOf : Nat → Spend) (q : Queue)
    (h : Watchtower.firstLinks c s = false ∨ Watchtower.laterLinks s.blocks = false ∨
      Watchtower.lastActive s = false) :
    (duty sh tt snap l c tip (.scanned s) spendOf q).2.1 = q :=
  duty_unproven sh tt snap l c tip s spendOf q (Watchtower.unproven_binds_nothing sh c s h)

/-- A scan `pass` discards for tip reasons — `WTC-14`'s tip below the newest anchor, or the tip
test finding a change — leaves the queue unchanged too. -/
@[req "WTC-14"]
theorem duty_discarded (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool) (c : Cursor)
    (tip : Anchor) (s : Scan) (spendOf : Nat → Spend) (q : Queue)
    (h : belowNewest c tip = true ∨ tipChanged tt tip s.after = true) :
    (duty sh tt snap l c tip (.scanned s) spendOf q).2.1 = q := by
  rcases h with h | h <;> simp [duty, bound, alertsOf, enqueueAll, h]

/-- An errored or panicked pass enqueues nothing: it bound nothing. -/
@[req "WTC-14"]
theorem duty_not_scanned (sh : CursorShape) (tt : TipTest) (snap : List Nat) (l : Bool)
    (c : Cursor) (tip : Anchor) (o : Outcome) (spendOf : Nat → Spend) (q : Queue)
    (h : o = .errored ∨ o = .panicked) : (duty sh tt snap l c tip o spendOf q).2.1 = q := by
  rcases h with rfl | rfl <;> rfl

/-! ## The federation, and `WTC-18`'s two refutations under the refuted readings

`n = 5`, `t = 3` (`OPS-5` speaks of "3-of-5"), one record per honest node. Every node accepted
the legitimate spend, txid 10, and nodes 1 to 3 co-signed it; every node refused the theft, txid
20, which was fanned to all five and is in nobody's accepted set; every node accepted the
Recovery-branch spend's txid, 30. Both twins carry a Normal-branch witness, so neither is
Recovery and the verdict turns on recognition alone. The halves under `current` are in
`Exhibits.lean`. -/

/-- A Normal-branch witness for `t = 3`: the dummy, three federation signatures, the user
signature, the selector `[0x01]` and the witness script, in `CHN-9`'s order; signatures and the
script are opaque bytes here. -/
@[req "CHN-9"]
def normalWitness : List Bytes := [[], [0x30], [0x30], [0x30], [0x30], [0x01], [0x63]]

/-- A Recovery-branch witness: signatures, the empty selector, the witness script. -/
@[req "CHN-9"]
def recoveryWitness : List Bytes := [[0x30], [0x30], [], [0x63]]

/-- `WTC-19`'s short witness: one element. -/
@[req "WTC-19"]
def shortWitness : List Bytes := [[0x30]]

/-- One vault outpoint and one script for every exhibit spend. -/
@[req "WTC-17"] def vaultOutpoint : Nat × Nat := (7, 0)
@[req "WTC-17"] def vaultScript : Bytes := [0x00, 0x20]

/-- The legitimate spend. -/
@[req "WTC-18"]
def legitSpend : Spend :=
  { txid := 10, outpoint := vaultOutpoint, script := vaultScript, witness := normalWitness }

/-- The theft fanned to every honest node. -/
@[req "WTC-18"]
def theftSpend : Spend :=
  { txid := 20, outpoint := vaultOutpoint, script := vaultScript, witness := normalWitness }

/-- The Recovery-branch spend whose txid is in every accepted set. -/
@[req "WTC-17"]
def recoverySpend : Spend :=
  { txid := 30, outpoint := vaultOutpoint, script := vaultScript, witness := recoveryWitness }

/-- `WTC-19`'s short-witness variant, authorized: txid 30. -/
@[req "WTC-19"]
def shortAuthorized : Spend :=
  { txid := 30, outpoint := vaultOutpoint, script := vaultScript, witness := shortWitness }

/-- `WTC-19`'s short-witness variant, unauthorized: txid 31, in no set. -/
@[req "WTC-19"]
def shortUnauthorized : Spend :=
  { txid := 31, outpoint := vaultOutpoint, script := vaultScript, witness := shortWitness }

/-- The five honest nodes' records. -/
@[req "WTC-18"]
def federation : List Record :=
  [ { accepted := [10, 30], coSigned := [10], refused := [20] },
    { accepted := [10, 30], coSigned := [10], refused := [20] },
    { accepted := [10, 30], coSigned := [10], refused := [20] },
    { accepted := [10, 30], coSigned := [], refused := [20] },
    { accepted := [10, 30], coSigned := [], refused := [20] } ]

/-- Under `.coSigned` the legitimate spend alerts `UNRECOGNIZED_SPEND` on exactly `n − t = 2`
nodes, the two honest nodes that did not sign it. `WTC-18`: "Only `t` of `n` nodes sign a
legitimate spend, so “I did not sign it” false-alarms on `n − t` honest nodes". The premises
are conjuncts: every one of the `n = 5` records accepted the spend, and the records that
co-signed it number exactly `t = 3`. Under `current` it alerts nowhere
(`legit_silent_with_current`). -/
@[req "WTC-18"]
theorem legit_false_alarms_with_coSigned :
    federation.length = 5 ∧ isRecovery legitSpend.witness = false ∧
      (∀ r ∈ federation, legitSpend.txid ∈ r.accepted) ∧
      (federation.filter fun r => legitSpend.txid ∈ r.coSigned).length = 3 ∧
      countVerdict .unrecognizedSpend .coSigned federation legitSpend = 2 := by
  decide

/-- Under `.evaluated` the theft every node refused alerts nowhere: each node evaluated it, so
each recognises it. `WTC-18`: "a spend a node REFUSED was evaluated, so “I evaluated it” would
let an attacker fanning a theft to honest nodes suppress its own alert". Under `current` it
alerts everywhere (`theft_alerts_everywhere_with_current`). -/
@[req "WTC-18"]
theorem theft_suppressed_with_evaluated :
    isRecovery theftSpend.witness = false ∧
      (∀ r ∈ federation, theftSpend.txid ∈ r.refused ∧ theftSpend.txid ∉ r.accepted) ∧
      alerting .evaluated federation theftSpend = 0 := by
  decide

end BtcPolicy.Alerts
