import BtcPolicy.Chain
/-! The watchtower cursor, its reconciliation, the scan proof and the pass
(`DEF-6`). The vocabulary — heights, hashes, anchors, the chain view and
`previousblockhash` linkage — is `Chain.lean`'s. This is not the release cursor (`Cursor.lean`,
`SPN-38`).

`WTC-13`: "The watchtower **cursor** MUST hold the `(height, hash)` anchors of the top of its
scanned range — at most 101, contiguous — and its next height, in RAM only; a process restart
scans from genesis." And: "Before each pass the cursor MUST be reconciled: one hash read at the
newest anchor detects any in-window reorg; on mismatch the cursor walks newest to oldest for the
highest still-active anchor, drops everything above it, and re-scans from there with a loud
message" and "if no anchor matches — a reorg deeper than 100 blocks — it clears and re-scans from
genesis rather than wedging or silently advancing".

`WTC-12`: "A scan of a height range MUST prove the chain it scanned with three checks, any
failure discarding the whole result: the first block's `previousblockhash` equals the cursor's
expected parent (closing a fork below the range that rebuilt taller); each later block's
`previousblockhash` equals the previous scanned hash (breaking a mixed-fork straddle)" and "after
the loop the hash at the last height still equals the last scanned hash (closing a scan that ran
entirely on an abandoned fork, including one that returned to the captured tip)".

`WTC-14`: "A pass whose tip is below the newest anchor MUST return without advancing; a pass
whose captured tip's hash is no longer the active hash at that height when the scan ends MUST
discard its candidate cursor — a block arriving on top during the scan is not such a change, and
is the next pass's range; a pass that errors keeps the unadvanced cursor so the same range is
retried and no block is skipped; a pass that panics, anywhere in it and the tip comparison
included, resets the cursor to genesis."

Two guard parameters (`ADR-0023` decision 6). The cursor's shape: `anchored` is `WTC-13` as it
stands and `bareHeight` is the defect `DEF-6` records. The tip test: `capturedHeight` is `WTC-14`
as amended on 2026-09-27..29 (`ADR-0024`) and `chainTip` is the reading it withdraws, under which
a block arriving on top during the scan discards the pass. The theorems here hold under either
value or are stated under the value as it stands; `Exhibits.lean` holds every theorem over
`current`, so a flip goes red there and nowhere else. Beside each parameter sits its trace under
each value: `DEF-6`'s under the withdrawn shape, and the block that arrives on top under both
tip tests.

**Not modelled.** `WTC-13`'s "loud message" on a rewind; `WTC-14`'s alert-queue dedup and the
recognition of the spends a scan finds (`WTC-17`–`WTC-22`), both `Alerts.lean`'s, which reach
this module only as the opaque result a discarded scan yields none of; the backend calls that
produce a scan; and `DEF-6`'s other two halves, `DUR-31`'s re-broadcast and `SPN-25`'s prevout
verification, which nothing here closes. -/

namespace BtcPolicy.Watchtower
open BtcPolicy.Chain

/-! ## The cursor and its shape -/

/-- The watchtower cursor: the anchors of the top of the scanned range, newest first, and the
next height to scan. -/
structure Cursor where
  anchors : List Anchor
  next : Height
  deriving DecidableEq, Repr

/-- The empty cursor. `WTC-13`: "a process restart scans from genesis"; `WTC-14`: "a pass that
panics, anywhere in it and the tip comparison included, resets the cursor to genesis". -/
@[req "WTC-13"]
def genesis : Cursor := { anchors := [], next := 0 }

/-- The cursor's shape. `anchored` is `WTC-13` as it stands. `bareHeight` is `DEF-6`'s twin, the
shape it records — `DEF-6`: "The watchtower cursor was a bare monotonic height that never rewound,
so a recovery-path or unrecognised spend re-landing below it after a reorg was silently missed" —
a next height that carries no anchors, is never reconciled and never rewinds. -/
inductive CursorShape
  | anchored | bareHeight
  deriving DecidableEq, Repr

/-- `WTC-13` as it stands. -/
@[req "WTC-13"]
def current : CursorShape := .anchored

/-- `WTC-13`: "at most 101, contiguous". -/
@[req "WTC-13"] def window : Nat := 101

/-- `WTC-14`'s tip test. `capturedHeight` reads the amended sentence: the captured tip's hash
against the active hash **at that height** when the scan ends. `chainTip` is the reading it
withdraws (`ADR-0024`), the chain tip read after the loop against the captured tip's hash, under
which a block arriving on top during the scan discards the pass — which can never finish a
`WTC-13` genesis re-scan on a chain that keeps growing. -/
inductive TipTest
  | capturedHeight | chainTip
  deriving DecidableEq, Repr

/-- `WTC-14` as amended. `WTC-14`: "a pass whose captured tip's hash is no longer the active hash
at that height when the scan ends MUST discard its candidate cursor — a block arriving on top
during the scan is not such a change, and is the next pass's range". -/
@[req "WTC-14"]
def currentTipTest : TipTest := .capturedHeight

/-- The test itself, on the view the scan read after the loop. Under `capturedHeight` it is
`Chain.Anchor.active` on the captured tip — `WTC-11`'s first site, "a block hash at a height that
no longer matches" — negated; under `chainTip` it is the withdrawn comparison of that view's own
tip hash. -/
@[req "WTC-14"]
def tipChanged (tt : TipTest) (tip : Anchor) (after : View) : Bool :=
  match tt with
  | .capturedHeight => !tip.active after
  | .chainTip => after.tip.hash != tip.hash

/-- Newest first, each anchor one height above the next. -/
@[req "WTC-13"]
def contiguous : List Anchor → Bool
  | a :: b :: rest => a.height == b.height + 1 && contiguous (b :: rest)
  | _ => true

/-- The invariant every reachable cursor satisfies: at most `window` anchors, contiguous, and the
next height one above the newest anchor when there is one. -/
@[req "WTC-13"]
def wellFormed (c : Cursor) : Bool :=
  c.anchors.length ≤ window && contiguous c.anchors &&
    c.anchors.head?.all fun a => c.next == a.height + 1

/-! ## Reconciliation (`WTC-13`) -/

/-- The walk "newest to oldest for the highest still-active anchor": the anchors from the first
active one down, everything above it dropped; `[]` when none is active. -/
@[req "WTC-13"]
def rewind (v : View) : List Anchor → List Anchor
  | [] => []
  | a :: older => if a.active v then a :: older else rewind v older

/-- Before each pass. Under `anchored`, `WTC-13`: "one hash read at the newest anchor detects any
in-window reorg; on mismatch the cursor walks newest to oldest for the highest still-active
anchor, drops everything above it", and the next height is set just above it; "if no anchor
matches … it clears and re-scans from genesis". A cursor with no anchor to read is genesis. Under
`bareHeight` the cursor is never reconciled: the identity. The loud message is not modelled. -/
@[req "WTC-13"]
def reconcile (sh : CursorShape) (v : View) (c : Cursor) : Cursor :=
  match sh, c.anchors with
  | .bareHeight, _ => c
  | .anchored, [] => genesis
  | .anchored, a :: older =>
    if a.active v then c
    else
      match rewind v older with
      | [] => genesis
      | b :: rest => { anchors := b :: rest, next := b.height + 1 }

/-! ## The scan proof (`WTC-12`) -/

/-- A scan of a height range: the blocks read, in height order, the spends found among them
(opaque here), and the chain view read after the loop, its tip included. -/
structure Scan where
  blocks : List Block
  spends : List Nat
  after : View

/-- "the cursor's expected parent": the newest anchor's hash. At genesis there is none. -/
@[req "WTC-12"]
def expectedParent (c : Cursor) : Option Hash := c.anchors.head?.map (·.hash)

/-- Check (a) against a parent hash, `WTC-11`'s third site: the first block read links to it;
vacuous when nothing was read. -/
@[req "WTC-12"]
def firstLinksTo (parent : Hash) : List Block → Bool
  | b :: _ => b.linksTo parent
  | [] => true

/-- Check (a), `WTC-12`: "the first block's `previousblockhash` equals the cursor's expected
parent". At genesis there is no parent, so the check is vacuous: the range starts at height 0 and
the first block has nothing to link to. -/
@[req "WTC-12"]
def firstLinks (c : Cursor) (s : Scan) : Bool :=
  (expectedParent c).all (firstLinksTo · s.blocks)

/-- Check (b), `WTC-12`: "each later block's `previousblockhash` equals the previous scanned
hash". -/
@[req "WTC-12"]
def laterLinks : List Block → Bool
  | b :: c :: rest => c.linksTo b.hash && laterLinks (c :: rest)
  | _ => true

/-- Check (c), `WTC-12`: "after the loop the hash at the last height still equals the last
scanned hash". -/
@[req "WTC-12"]
def lastActive (s : Scan) : Bool :=
  match s.blocks.getLast? with
  | some b => s.after.activeAt b.height == some b.hash
  | none => true

/-- `WTC-12`'s three checks against an expected parent, `none` where there is none to link to:
the one statement of the walk check, which the cursor's scan (`proven`), `WTC-6`'s delta walk
(`VaultUnspent.deltaWalk`) and `WTC-7`'s walk above the settled block
(`VaultUnspent.settledWalkProven`) all take. -/
@[req "WTC-12"]
def linked (parent : Option Hash) (s : Scan) : Bool :=
  parent.all (firstLinksTo · s.blocks) && laterLinks s.blocks && lastActive s

/-- The scan is proven iff all three checks hold. -/
@[req "WTC-12"]
def proven (c : Cursor) (s : Scan) : Bool := linked (expectedParent c) s

/-- The blocks are the range the cursor asked for: consecutive heights from `start`. -/
@[req "WTC-13"]
def rangeFrom (start : Height) : List Block → Bool
  | [] => true
  | b :: rest => b.height == start && rangeFrom (start + 1) rest

/-- The scanned blocks pushed onto the anchors, oldest first, so the last scanned ends newest. -/
@[req "WTC-13"]
def pushAll : List Block → List Anchor → List Anchor
  | [], acc => acc
  | b :: rest, acc => pushAll rest (b.anchor :: acc)

/-- The candidate cursor a scan yields, or `none` when the scan is not proven or is not the
cursor's range. Under `anchored` the anchors are the scanned range appended to the old, trimmed
to the newest `window`, and the next height is one above the last scanned block; under
`bareHeight` the next height alone moves. An empty range leaves the cursor as it is. -/
@[req "WTC-12"]
def candidate (sh : CursorShape) (c : Cursor) (s : Scan) : Option Cursor :=
  if proven c s && rangeFrom c.next s.blocks then
    some <|
      match s.blocks.getLast? with
      | none => c
      | some last =>
        match sh with
        | .anchored =>
          { anchors := (pushAll s.blocks c.anchors).take window, next := last.height + 1 }
        | .bareHeight => { c with next := last.height + 1 }
  else none

/-- What a scan binds: its candidate cursor and its spends, or nothing. -/
@[req "WTC-12"]
def result (sh : CursorShape) (c : Cursor) (s : Scan) : Option (Cursor × List Nat) :=
  (candidate sh c s).map fun c' => (c', s.spends)

/-- `WTC-12`: "any failure discarding the whole result" — a scan with any check false binds
nothing, no candidate cursor and no spends, under either shape, for every cursor and every
scan. -/
@[req "WTC-12"]
theorem unproven_binds_nothing (sh : CursorShape) (c : Cursor) (s : Scan)
    (h : firstLinks c s = false ∨ laterLinks s.blocks = false ∨ lastActive s = false) :
    result sh c s = none := by
  have hp : proven c s = false := by
    unfold proven linked
    rcases h with h | h | h <;> simp [firstLinks] at h ⊢ <;> simp [h]
  simp [result, candidate, hp]

/-- What accepting an unproven scan would do: bind a result to a chain the node is not on. The
parent the cursor expects, or some scanned block, is not active at its height on the view read
after the loop. -/
@[req "WTC-12"]
def bindsAbandoned (c : Cursor) (s : Scan) : Bool :=
  (match c.anchors with
    | a :: _ => !a.active s.after
    | [] => false) ||
  s.blocks.any fun b => !(s.after.activeAt b.height == some b.hash)

/-- A proven scan is one on which all three checks hold, and nothing less. -/
@[req "WTC-12"]
theorem proven_iff (c : Cursor) (s : Scan) :
    proven c s = true ↔
      firstLinks c s = true ∧ laterLinks s.blocks = true ∧ lastActive s = true := by
  simp [proven, linked, firstLinks, and_assoc]

/-! ### Coinbase inputs and prevouts

`WTC-12`: "Coinbase inputs are skipped; every other input MUST carry a prevout, and a missing one
is an error, never a silent negative." -/

/-- An input as the scan reads it: the coinbase, an input carrying its prevout, or one missing
it. -/
inductive Input
  | coinbase
  | prevout (p : Nat)
  | missingPrevout
  deriving DecidableEq, Repr

/-- The prevouts of an input list, coinbase inputs skipped; `none` is the error a missing prevout
raises. -/
@[req "WTC-12"]
def prevouts : List Input → Option (List Nat)
  | [] => some []
  | .coinbase :: rest => prevouts rest
  | .prevout p :: rest => (prevouts rest).map (p :: ·)
  | .missingPrevout :: _ => none

/-- `WTC-12`: "a missing one is an error, never a silent negative" — an input list with a missing
prevout anywhere is the error, never an empty or a shorter result. -/
@[req "WTC-12"]
theorem missing_prevout_is_error (ins : List Input) (h : .missingPrevout ∈ ins) :
    prevouts ins = none := by
  induction ins with
  | nil => simp at h
  | cons i rest ih =>
    cases i with
    | coinbase => exact ih (by simpa using h)
    | prevout p => rw [prevouts, ih (by simpa using h)]; rfl
    | missingPrevout => rfl

/-- `WTC-12`: "Coinbase inputs are skipped" — a coinbase contributes nothing and raises
nothing. -/
@[req "WTC-12"]
theorem coinbase_skipped (ins : List Input) : prevouts (.coinbase :: ins) = prevouts ins := rfl

/-- Every other input's prevout is carried, in order, when none is missing. -/
@[req "WTC-12"]
theorem prevout_carried (p : Nat) (ins : List Input) (ps : List Nat) (h : prevouts ins = some ps) :
    prevouts (.prevout p :: ins) = some (p :: ps) := by
  simp [prevouts, h]

/-! ## The pass (`WTC-14`) -/

/-- What a pass came to: a scan that ran to the end of the loop, an error, or a panic. Whether
the tip was below the newest anchor, and whether the tip test (`tipChanged`) finds a change, the
pass reads for itself from the tip it captured and the view the scan read after the loop. -/
inductive Outcome
  | scanned (s : Scan)
  | errored
  | panicked

/-- `WTC-14`: "A pass whose tip is below the newest anchor". -/
@[req "WTC-14"]
def belowNewest (c : Cursor) (tip : Anchor) : Bool :=
  match c.anchors with
  | a :: _ => tip.height < a.height
  | [] => false

/-- The cursor a pass leaves. `WTC-14`: "A pass whose tip is below the newest anchor MUST return
without advancing; a pass whose captured tip's hash is no longer the active hash at that height
when the scan ends MUST discard its candidate cursor — a block arriving on top during the scan is
not such a change, and is the next pass's range; a pass that errors keeps the unadvanced cursor so
the same range is retried and no block is skipped; a pass that panics, anywhere in it and the tip
comparison included, resets the cursor to genesis". A proven scan of the cursor's range yields its
candidate.

The outcome is read first, the tip comparison after: `WTC-14`'s panic clause is "a pass that
panics, anywhere in it and the tip comparison included, resets the cursor to genesis", so it is
unconditional and the below-tip clause applies to the passes that returned — a pass that returned
below the newest anchor is one that did not panic. -/
@[req "WTC-14"]
def pass (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (o : Outcome) : Cursor :=
  match o with
  | .panicked => genesis
  | .errored => c
  | .scanned s =>
    if belowNewest c tip || tipChanged tt tip s.after then c else (candidate sh c s).getD c

/-- One pass as the driver sequences it: reconcile against the view captured before the pass,
then pass with that view's tip. -/
@[req "WTC-14"]
def step (sh : CursorShape) (tt : TipTest) (v : View) (o : Outcome) (c : Cursor) : Cursor :=
  pass sh tt (reconcile sh v c) v.tip o

/-- Reachable from genesis through `step`. -/
inductive Reachable (sh : CursorShape) (tt : TipTest) : Cursor → Prop
  | init : Reachable sh tt genesis
  | next {c : Cursor} (v : View) (o : Outcome) :
      Reachable sh tt c → Reachable sh tt (step sh tt v o c)

/-! ## `WTC-14`'s outcomes, over every shape, cursor and tip -/

/-- Below the newest anchor, whatever else the pass that returned came to. `WTC-14`: "MUST
return without advancing". The hypothesis is that the pass returned: one that returned below the
newest anchor did not panic, and one that panicked reset (`pass_panicked`). -/
@[req "WTC-14"]
theorem pass_below_tip (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (o : Outcome)
    (ho : o ≠ .panicked) (hb : belowNewest c tip = true) : pass sh tt c tip o = c := by
  cases o with
  | panicked => exact absurd rfl ho
  | errored => rfl
  | scanned s => simp [pass, hb]

/-- Below the newest anchor, for every outcome, panic included, the pass never advances: the
`WTC-14` reading of "MUST return without advancing" that a reset to genesis also satisfies. -/
@[req "WTC-14"]
theorem pass_below_tip_never_advances (sh : CursorShape) (tt : TipTest) (c : Cursor)
    (tip : Anchor) (o : Outcome) (hb : belowNewest c tip = true) :
    (pass sh tt c tip o).next ≤ c.next := by
  cases o with
  | panicked => exact Nat.zero_le _
  | errored => exact Nat.le_refl _
  | scanned s => simp [pass, hb]

/-- A scan on which the selected tip test returns true (`hc`), whichever test it is: under
`capturedHeight` the captured tip's hash is no longer the active hash at that height, and under
`chainTip` the tip hash of the view read after the loop is not the captured one, which a block
arriving on top is enough for (`def14_discarded_with_chainTip`). The pass keeps the cursor it
started from. `WTC-14`: "MUST discard its candidate cursor". -/
@[req "WTC-14"]
theorem pass_tip_changed (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (s : Scan)
    (hc : tipChanged tt tip s.after = true) : pass sh tt c tip (.scanned s) = c := by
  simp [pass, hc]

/-- Under `capturedHeight` the test is exactly `WTC-11`'s first site on the captured tip: the test
returns true iff the hash the chain now has at the captured height is not the captured one. The iff
is the tip test's and not the pass's, which also keeps its cursor when the tip is below the newest
anchor or the scan yields no candidate (`pass`). `WTC-14`: "a pass whose captured tip's hash is no
longer the active hash at that height when the scan ends MUST discard its candidate cursor". -/
@[req "WTC-14"]
theorem tipChanged_capturedHeight_iff (tip : Anchor) (after : View) :
    tipChanged .capturedHeight tip after = true ↔ after.activeAt tip.height ≠ some tip.hash := by
  simp [tipChanged, Anchor.active]

/-- A block arriving on top is not a change under `capturedHeight`: whatever the view's own tip
became, a captured tip still active at its height passes the test. `WTC-14`: "a block arriving on
top during the scan is not such a change, and is the next pass's range". -/
@[req "WTC-14"]
theorem tipChanged_capturedHeight_false (tip : Anchor) (after : View)
    (ha : after.activeAt tip.height = some tip.hash) :
    tipChanged .capturedHeight tip after = false := by
  simp [tipChanged, Anchor.active, ha]

/-- A pass that errors. `WTC-14`: "keeps the unadvanced cursor so the same range is retried and no
block is skipped". -/
@[req "WTC-14"]
theorem pass_errored (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) :
    pass sh tt c tip .errored = c := rfl

/-- A pass that panics, over every shape, cursor and tip. `WTC-14`: "resets the cursor to
genesis". -/
@[req "WTC-14"]
theorem pass_panicked (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) :
    pass sh tt c tip .panicked = genesis := rfl

/-- The head of the pushed anchors is the last scanned block. -/
@[req "WTC-13"]
theorem pushAll_head (bs : List Block) (acc : List Anchor) (last : Block)
    (h : bs.getLast? = some last) : (pushAll bs acc).head? = some last.anchor := by
  induction bs generalizing acc with
  | nil => simp at h
  | cons b rest ih =>
    cases rest with
    | nil => simp at h; subst h; rfl
    | cons b' rest' =>
      simp only [pushAll]
      exact ih _ (by simpa [List.getLast?_cons_cons] using h)

/-- Trimming to a positive count keeps the head. -/
@[req "WTC-13"]
theorem take_head (l : List Anchor) (n : Nat) (hn : 0 < n) : (l.take n).head? = l.head? := by
  cases l <;> cases n <;> simp_all

/-- The positive outcome: a proven scan (`hp`) of the cursor's range (`hr`) with a last scanned
block (`hl`), on a pass whose tip is not below the newest anchor (`hb : belowNewest c tip = false`)
and whose tip test found no change (`ht`), advances the next height to one above the last scanned
block, and under `anchored` its newest anchor is that block. `hb` decides it: below the newest
anchor the pass returns the cursor it started from (`pass_below_tip`). Under either test — so under
`capturedHeight` a pass a block arrived on top of completes (`tipChanged_capturedHeight_false`). -/
@[req "WTC-14"]
theorem pass_completed (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor) (s : Scan)
    (last : Block) (hb : belowNewest c tip = false) (ht : tipChanged tt tip s.after = false)
    (hp : proven c s = true) (hr : rangeFrom c.next s.blocks = true)
    (hl : s.blocks.getLast? = some last) :
    (pass sh tt c tip (.scanned s)).next = last.height + 1 ∧
      (sh = .anchored → (pass sh tt c tip (.scanned s)).anchors.head? = some last.anchor) := by
  cases sh with
  | anchored =>
    simp [pass, hb, candidate, hp, hr, hl, ht, take_head _ _ (show 0 < window by decide),
      pushAll_head _ _ _ hl]
  | bareHeight => simp [pass, hb, candidate, hp, hr, hl, ht]

/-! ## Reconciliation's theorems (`WTC-13`), under `anchored` -/

/-- The walk: the anchors above the result are all inactive, and the result's head is active. -/
@[req "WTC-13"]
theorem rewind_spec (v : View) (l : List Anchor) :
    ∃ dropped, l = dropped ++ rewind v l ∧ (∀ x ∈ dropped, x.active v = false) ∧
      ∀ b rest, rewind v l = b :: rest → b.active v = true := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, by simp [rewind]⟩
  | cons a older ih =>
    by_cases ha : a.active v = true
    · refine ⟨[], by simp [rewind, ha], by simp, ?_⟩
      intro b rest h
      simp [rewind, ha] at h
      rw [← h.1]; exact ha
    · obtain ⟨d, hd, hdrop, hhead⟩ := ih
      have ha' : a.active v = false := by simpa using ha
      refine ⟨a :: d, ?_, ?_, ?_⟩
      · simp only [rewind, ha', Bool.false_eq_true, ↓reduceIte, List.cons_append]
        exact congrArg _ hd
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact ha'
        · exact hdrop x hx
      · intro b rest h
        simp only [rewind, ha', Bool.false_eq_true, ↓reduceIte] at h
        exact hhead b rest h

/-- No anchor active, nothing kept. -/
@[req "WTC-13"]
theorem rewind_nil (v : View) (l : List Anchor) (h : ∀ x ∈ l, x.active v = false) :
    rewind v l = [] := by
  induction l with
  | nil => rfl
  | cons a older ih =>
    have ha := h a (by simp)
    simp only [rewind, ha, Bool.false_eq_true, ↓reduceIte]
    exact ih fun x hx => h x (by simp [hx])

/-- Some anchor active, something kept. -/
@[req "WTC-13"]
theorem rewind_ne_nil (v : View) (l : List Anchor) (h : ∃ x ∈ l, x.active v = true) :
    rewind v l ≠ [] := by
  induction l with
  | nil => simp at h
  | cons a older ih =>
    by_cases ha : a.active v = true
    · simp [rewind, ha]
    · have ha' : a.active v = false := by simpa using ha
      simp only [rewind, ha', Bool.false_eq_true, ↓reduceIte]
      apply ih
      obtain ⟨x, hx, hxa⟩ := h
      simp at hx
      rcases hx with rfl | hx
      · rw [ha'] at hxa; cases hxa
      · exact ⟨x, hx, hxa⟩

/-- In-window detection, by one read: reconciliation is the identity iff the newest anchor is
active. -/
@[req "WTC-13"]
theorem reconcile_identity_iff (v : View) (c : Cursor) (a : Anchor) (older : List Anchor)
    (h : c.anchors = a :: older) : reconcile .anchored v c = c ↔ a.active v = true := by
  obtain ⟨anchors, next⟩ := c
  simp only at h
  subst h
  simp only [reconcile]
  by_cases ha : a.active v = true
  · simp [ha]
  · have ha' : a.active v = false := by simpa using ha
    simp only [ha', Bool.false_eq_true, ↓reduceIte, iff_false]
    obtain ⟨d, hd, -, -⟩ := rewind_spec v older
    split
    · simp [genesis]
    · rename_i b rest hr
      intro heq
      have hanc := congrArg Cursor.anchors heq
      simp only [List.cons.injEq] at hanc
      obtain ⟨-, hrest⟩ := hanc
      subst hrest
      rw [hr] at hd
      have := congrArg List.length hd
      simp only [List.length_append, List.length_cons] at this
      omega

/-- The rewind: when the newest anchor is not active and some anchor is, the reconciled anchors
are the old ones from the highest still-active one down — everything above it, all inactive, is
dropped — and the next height is one above it. -/
@[req "WTC-13"]
theorem reconcile_rewinds (v : View) (c : Cursor) (a : Anchor) (older : List Anchor)
    (h : c.anchors = a :: older) (ha : a.active v = false)
    (hsome : ∃ x ∈ older, x.active v = true) :
    ∃ dropped b rest, c.anchors = dropped ++ b :: rest ∧ (∀ x ∈ dropped, x.active v = false) ∧
      b.active v = true ∧
      reconcile .anchored v c = { anchors := b :: rest, next := b.height + 1 } := by
  obtain ⟨anchors, next⟩ := c
  simp only at h
  subst h
  obtain ⟨d, hd, hdrop, hhead⟩ := rewind_spec v older
  match hr : rewind v older with
  | [] => exact absurd hr (rewind_ne_nil v older hsome)
  | b :: rest =>
    refine ⟨a :: d, b, rest, ?_, ?_, hhead b rest hr, ?_⟩
    · rw [hr] at hd; simp [hd]
    · intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact ha
      · exact hdrop x hx
    · simp [reconcile, ha, hr]

/-- Deeper than the window: if no anchor is active, reconciliation is genesis. `WTC-13`: "it
clears and re-scans from genesis rather than wedging or silently advancing". -/
@[req "WTC-13"]
theorem reconcile_none_active (v : View) (c : Cursor) (h : ∀ x ∈ c.anchors, x.active v = false) :
    reconcile .anchored v c = genesis := by
  obtain ⟨anchors, next⟩ := c
  simp only at h
  cases anchors with
  | nil => rfl
  | cons a older =>
    have ha := h a (by simp)
    have hr := rewind_nil v older fun x hx => h x (by simp [hx])
    simp [reconcile, ha, hr]

/-- The anchors below a contiguous list's head are all lower than it. -/
@[req "WTC-13"]
theorem contiguous_below (a : Anchor) (older : List Anchor) (h : contiguous (a :: older) = true) :
    ∀ b ∈ older, b.height < a.height := by
  induction older generalizing a with
  | nil => simp
  | cons b rest ih =>
    simp only [contiguous, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    intro x hx
    simp at hx
    simp only [Height] at *
    rcases hx with rfl | hx
    · omega
    · have := ih b h2 x hx
      omega

/-- Reconciliation never advances: under either shape, over every well-formed cursor and every
view, the reconciled next height is at most the old one. Together with the two theorems above,
no branch of reconciliation "silently advancing". -/
@[req "WTC-13"]
theorem reconcile_never_advances (sh : CursorShape) (v : View) (c : Cursor)
    (hw : wellFormed c = true) : (reconcile sh v c).next ≤ c.next := by
  obtain ⟨anchors, next⟩ := c
  cases sh with
  | bareHeight => simp [reconcile]
  | anchored =>
    cases anchors with
    | nil => simp [reconcile, genesis]
    | cons a older =>
      simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.head?_cons,
        Option.all_some] at hw
      obtain ⟨⟨-, hc⟩, hn⟩ := hw
      by_cases ha : a.active v = true
      · simp [reconcile, ha]
      · have ha' : a.active v = false := by simpa using ha
        obtain ⟨d, hd, -, -⟩ := rewind_spec v older
        simp only [reconcile, ha', Bool.false_eq_true, ↓reduceIte]
        split
        · simp [genesis]
        · rename_i b rest hr
          have hb : b ∈ older := by rw [hd, hr]; simp
          have := contiguous_below a older hc b hb
          simp only [Height] at *
          omega

/-! ## Bounded and contiguous (`WTC-13`), by induction on reachability -/

/-- A contiguous list's tail is contiguous. -/
@[req "WTC-13"]
theorem contiguous_tail (a : Anchor) (l : List Anchor) (h : contiguous (a :: l) = true) :
    contiguous l = true := by
  cases l with
  | nil => rfl
  | cons b rest =>
    simp only [contiguous, Bool.and_eq_true] at h
    exact h.2

/-- The walk keeps a suffix, so contiguity survives it. -/
@[req "WTC-13"]
theorem rewind_contiguous (v : View) (l : List Anchor) (h : contiguous l = true) :
    contiguous (rewind v l) = true := by
  induction l with
  | nil => rfl
  | cons a older ih =>
    by_cases ha : a.active v = true
    · simpa [rewind, ha] using h
    · have ha' : a.active v = false := by simpa using ha
      simp only [rewind, ha', Bool.false_eq_true, ↓reduceIte]
      exact ih (contiguous_tail a older h)

/-- The walk never lengthens the list. -/
@[req "WTC-13"]
theorem rewind_length (v : View) (l : List Anchor) : (rewind v l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a older ih =>
    by_cases ha : a.active v = true
    · simp [rewind, ha]
    · have ha' : a.active v = false := by simpa using ha
      simp only [rewind, ha', Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.le_succ_of_le ih

/-- Reconciliation preserves the invariant, under either shape. -/
@[req "WTC-13"]
theorem reconcile_wellFormed (sh : CursorShape) (v : View) (c : Cursor)
    (hw : wellFormed c = true) : wellFormed (reconcile sh v c) = true := by
  obtain ⟨anchors, next⟩ := c
  cases sh with
  | bareHeight => simpa [reconcile] using hw
  | anchored =>
    cases anchors with
    | nil => rfl
    | cons a older =>
      simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.head?_cons,
        Option.all_some] at hw
      obtain ⟨⟨hlen, hc⟩, hn⟩ := hw
      by_cases ha : a.active v = true
      · simp only [reconcile, ha, ↓reduceIte]
        simp only [List.length_cons] at hlen
        simp [wellFormed, hlen, hc, hn]
      · have ha' : a.active v = false := by simpa using ha
        simp only [reconcile, ha', Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · rename_i b rest hr
          have hcont := rewind_contiguous v older (contiguous_tail a older hc)
          have hlen' := rewind_length v older
          rw [hr] at hcont hlen'
          simp only [List.length_cons] at hlen hlen'
          simp [wellFormed, hcont]
          omega

/-- A prefix of a contiguous list is contiguous. -/
@[req "WTC-13"]
theorem contiguous_take (n : Nat) (l : List Anchor) (h : contiguous l = true) :
    contiguous (l.take n) = true := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | [a] => simp [contiguous]
    | a :: b :: rest =>
      simp only [contiguous, Bool.and_eq_true] at h
      cases n with
      | zero => rfl
      | succ n =>
        have := ih (b :: rest) h.2
        simp only [List.take_succ_cons] at this ⊢
        simp only [contiguous, Bool.and_eq_true]
        exact ⟨h.1, this⟩

/-- Pushing a range onto a contiguous list whose head sits just below it is contiguous. -/
@[req "WTC-13"]
theorem pushAll_contiguous (bs : List Block) (h : Height) (acc : List Anchor)
    (hr : rangeFrom h bs = true) (hc : contiguous acc = true)
    (hj : ∀ a rest, acc = a :: rest → a.height + 1 = h) : contiguous (pushAll bs acc) = true := by
  induction bs generalizing h acc with
  | nil => exact hc
  | cons b rest ih =>
    simp only [rangeFrom, Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨hb, hr⟩ := hr
    simp only [pushAll]
    refine ih (h + 1) (b.anchor :: acc) hr ?_ ?_
    · cases acc with
      | nil => rfl
      | cons a rest' =>
        have := hj a rest' rfl
        simp only [contiguous, Bool.and_eq_true, beq_iff_eq, Block.anchor]
        simp only [Height] at *
        exact ⟨by omega, hc⟩
    · intro a rest' heq
      cases heq
      simp [Block.anchor, hb]

/-- The candidate a proven scan of a well-formed cursor's range yields is well-formed. Under
`bareHeight` the cursor's anchors are empty, the degenerate case of the invariant. -/
@[req "WTC-13"]
theorem candidate_wellFormed (sh : CursorShape) (c : Cursor) (s : Scan) (c' : Cursor)
    (hw : wellFormed c = true) (hb : sh = .bareHeight → c.anchors = [])
    (h : candidate sh c s = some c') : wellFormed c' = true := by
  unfold candidate at h
  split at h
  · rename_i hps
    simp only [Bool.and_eq_true] at hps
    simp only [Option.some.injEq] at h
    subst h
    split
    · exact hw
    · rename_i last hl
      cases sh with
      | bareHeight =>
        have hnil := hb rfl
        obtain ⟨anchors, next⟩ := c
        simp only at hnil
        subst hnil
        rfl
      | anchored =>
        simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨-, hc⟩, hn⟩ := hw
        have hcont : contiguous (pushAll s.blocks c.anchors) = true := by
          refine pushAll_contiguous s.blocks c.next c.anchors hps.2 hc ?_
          intro a rest heq
          rw [heq] at hn
          simp only [List.head?_cons, Option.all_some, beq_iff_eq] at hn
          exact hn.symm
        have hhead := pushAll_head s.blocks c.anchors last hl
        simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨?_, contiguous_take _ _ hcont⟩, ?_⟩
        · rw [List.length_take]; exact Nat.min_le_left _ _
        · rw [take_head _ _ (by decide), hhead]
          simp [Block.anchor]
  · cases h

/-- The pass preserves the invariant, under either shape. -/
@[req "WTC-13"]
theorem pass_wellFormed (sh : CursorShape) (tt : TipTest) (c : Cursor) (tip : Anchor)
    (o : Outcome) (hw : wellFormed c = true) (hb : sh = .bareHeight → c.anchors = []) :
    wellFormed (pass sh tt c tip o) = true := by
  cases o with
  | panicked => rfl
  | errored => exact hw
  | scanned s =>
    simp only [pass]
    split
    · exact hw
    · match hcand : candidate sh c s with
      | none => exact hw
      | some c' => exact candidate_wellFormed sh c s c' hw hb hcand

/-- Under `bareHeight` no anchor is ever held. -/
@[req "WTC-13"]
theorem bare_no_anchors (tt : TipTest) (c : Cursor) (hr : Reachable .bareHeight tt c) :
    c.anchors = [] := by
  induction hr with
  | init => rfl
  | next v o _ ih =>
    simp only [step, reconcile]
    cases o with
    | panicked => rfl
    | errored => exact ih
    | scanned s =>
      simp only [pass]
      split
      · exact ih
      · unfold candidate
        split
        · split
          · exact ih
          · exact ih
        · exact ih

/-- Bounded and contiguous: every reachable cursor, under either shape, holds the anchors
`WTC-13` bounds, "at most 101, contiguous", with the next height one above the newest. By
induction on `Reachable`. Under `bareHeight` the anchors are empty (`bare_no_anchors`), the
degenerate case. -/
@[req "WTC-13"]
theorem reachable_wellFormed (sh : CursorShape) (tt : TipTest) (c : Cursor)
    (hr : Reachable sh tt c) : wellFormed c = true := by
  induction hr with
  | init => rfl
  | next v o hr' ih =>
    refine pass_wellFormed sh tt _ _ o (reconcile_wellFormed sh v _ ih) ?_
    intro hsh
    subst hsh
    exact bare_no_anchors tt _ hr'

/-! ## `DEF-6`'s trace, and its half under the withdrawn shape

A chain `A` of six blocks, heights 0 to 5, hashes `100 + h`; the cursor scans all six from genesis
and stands at next height 6. A spend confirmed at height 4 on `A`, the one opaque spend id the
first pass binds; recognising or matching it is `Alerts.lean`'s (`WTC-17`–`WTC-22`). Then a
reorg drops `A`'s blocks at 3, 4 and 5 for a fork `B`, hashes `200 + h`, and the spend re-lands
at height 4 on `B` — below the cursor's next height. `DEF-6`: "a recovery-path or unrecognised
spend re-landing below it after a reorg was silently missed". The `anchored` half is in
`Exhibits.lean`. -/

/-- A chain view from its hashes by height: the hash at each height, the tip its last. -/
@[req "WTC-13"]
def chainOf (hashes : List Hash) : View :=
  { activeAt := fun h => hashes[h]?, tip := ⟨hashes.length - 1, hashes.getLast?.getD 0⟩ }

/-- The blocks of a chain from a given height, each linking to the hash before it. -/
@[req "WTC-12"]
def blocksOf (hashes : List Hash) (from_ : Height) (parent : Hash) : List Block :=
  match hashes with
  | [] => []
  | h :: rest => ⟨from_, h, parent⟩ :: blocksOf rest (from_ + 1) h

/-- Chain `A`, heights 0 to 5. -/
@[req "WTC-13"] def def6ChainA : List Hash := [100, 101, 102, 103, 104, 105]
/-- The chain after the reorg: `A` to height 2, then fork `B` at 3, 4 and 5. -/
@[req "WTC-13"] def def6ChainB : List Hash := [100, 101, 102, 203, 204, 205]
/-- The height the spend re-lands at on `B`, below the cursor's next height 6. -/
@[req "WTC-13"] def def6Relanded : Height := 4
/-- The first pass: chain `A` scanned from genesis, the spend confirmed at height 4 found, the
view after the loop still `A`. -/
@[req "WTC-13"]
def def6Scan : Scan :=
  { blocks := blocksOf def6ChainA 0 0, spends := [1], after := chainOf def6ChainA }
/-- The cursor after that pass, under a shape. The tip test is written at the value as it stands
and not read from the guard: this pass's view after the loop is `A` itself, on which both values
find no change, so the trace is `DEF-6`'s and says nothing about `WTC-14`'s tip test. -/
@[req "WTC-13"]
def def6Cursor (sh : CursorShape) : Cursor :=
  step sh .capturedHeight (chainOf def6ChainA) (.scanned def6Scan) genesis

/-- Under the withdrawn shape the next height is 6 after the pass, is 6 after reconciliation
against the reorged chain — "a bare monotonic height that never rewound" — and lies above the
re-landed height: the spend is never scanned again. -/
@[req "WTC-13"]
theorem def6_missed_with_withdrawn :
    (def6Cursor .bareHeight).next = 6 ∧
      (reconcile .bareHeight (chainOf def6ChainB) (def6Cursor .bareHeight)).next = 6 ∧
      def6Relanded < 6 := by
  decide

/-! ## `WTC-14`'s tip test, the same pass under each value

Chain `A` again, the cursor standing at next height 4 with anchors down to `(3, 103)`, and a pass
that scans heights 4 and 5 with the tip it captured, `(5, 105)`. While the loop ran, height 6
arrived: the view read after it is `A` plus `(6, 106)`, so its own tip is `(6, 106)` while the hash
at height 5 is still `105`. `WTC-14`: "a block arriving on top during the scan is not such a
change, and is the next pass's range". The `capturedHeight` half is in `Exhibits.lean`. -/

/-- Chain `A` with the block that arrived on top. -/
@[req "WTC-14"] def def14ChainGrown : List Hash := [100, 101, 102, 103, 104, 105, 106]

/-- The cursor the pass starts from: anchors down to `(3, 103)`, next height 4. -/
@[req "WTC-14"]
def def14Cursor : Cursor := { anchors := [⟨3, 103⟩, ⟨2, 102⟩], next := 4 }

/-- The pass: heights 4 and 5 read on `A`, linking to `103`, the view after the loop the grown
chain. -/
@[req "WTC-14"]
def def14Scan : Scan :=
  { blocks := blocksOf [104, 105] 4 103, spends := [], after := chainOf def14ChainGrown }

/-- The captured tip, `A`'s tip before the block arrived. -/
@[req "WTC-14"] def def14Tip : Anchor := ⟨5, 105⟩

/-- Under the withdrawn reading the arriving block is read as a change — the view's own tip hash is
`106`, not the captured `105` — and the pass discards its candidate, standing where it started at
next height 4. On mainnet a pass long enough to be overtaken is every pass of a `WTC-13` genesis
re-scan, so the cursor never advances. The `capturedHeight` half is
`Exhibits.WatchtowerCursor.block_on_top_kept_with_current`. -/
@[req "WTC-14"]
theorem def14_discarded_with_chainTip :
    tipChanged .chainTip def14Tip def14Scan.after = true ∧
      proven def14Cursor def14Scan = true ∧
      pass .anchored .chainTip def14Cursor def14Tip (.scanned def14Scan) = def14Cursor := by
  decide

/-- `WTC-12`'s proof with no block is vacuously proven: an empty scan binds its spends, and the
cursor it binds them with is the cursor as it was. -/
@[req "WTC-12"]
theorem empty_scan_binds_spends :
    result .anchored genesis { blocks := [], spends := [7], after := chainOf def6ChainA } =
      some (genesis, [7]) := by
  decide

end BtcPolicy.Watchtower
