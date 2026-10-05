import BtcPolicy.Chain
import BtcPolicy.Watchtower
import BtcPolicy.Coverage
/-! The vault-unspent cache, the wallet's completion markers and the import bracket
(`ADR-0024`; `DEF-21`). The vocabulary — heights, hashes, anchors,
the chain view and `previousblockhash` linkage — is `Chain.lean`'s; the scan, its two later checks
and the chain builders are `Watchtower.lean`'s; the coin and the coverage pass are
`Coverage.lean`'s. This is not the release cursor (`Cursor.lean`, `SPN-38`), which this module does
not import, and nothing here calls the watchtower cursor's reconciliation or pass: every proof
needs active-at-height and stable-snapshot facts only, never a cursor transition.

`WTC-5`: "A node MUST maintain a **vault-unspent cache** of the confirmed outputs paying the
vault script, anchored to the `(height, hash)` it was computed at, and MUST serve every fire-time
read from that cache: the coverage denominator (`DUR-22`) MUST refuse rather than scan the UTXO
set on the combine path, and MUST refuse if the cache's anchor is not the current tip."

`WTC-6` orders the three sources that serve the cache, `WTC-7` and `WTC-8` say what the
watch-only wallet is and when it is usable, `WTC-9` latches a repair when the wallet holds a
completion marker and no marker it holds has an anchor left on the active chain, and `WTC-10` takes
the one consistent snapshot the sweep consumes. Each is quoted where it is modelled. `WTC-11`'s
fourth site, the wallet, is here too, beside the cache it anchors; `Chain.lean` holds the other
three.

Seven guard parameters (`ADR-0023` decision 6). The import bracket is `DEF-21`'s and predates the
amendment of 2026-09-27..29 (`ADR-0024`), which moved what it re-proves to the settled block; the
marker anchor and the delta commit are that amendment's, two of the three guard parameters its
Consequences name, the third being `WTC-14`'s tip test, which `Watchtower.lean` owns; the walk
range and the chain tie came with the amendment of 2026-10-01 to `WTC-6` and `WTC-9`, as did the
latched base; the amendment of 2026-10-02 turned the chain tie over, brought the latch scope, and
brought the retry trigger, which takes the latched base in:

* the import bracket — `reProve` is `WTC-7` as it stands and `unbracketed` is the defect `DEF-21`
  records;
* the marker anchor — `settled` is `WTC-7`'s settled block, the settled depth below the scan
  anchor, and `scanTip` is the reference implementation's reading, the scan anchor itself with no
  walk below it, under which a reorg reaching no deeper than the settled depth below an import's
  own scan anchor unseats that import's own marker, at the tip it read, and costs a repair
  whenever it unseats every marker the wallet holds;
* the delta commit — `partialWalk` is `WTC-6`'s walk committed wherever it completes and `tipOnly`
  is the reading it withdraws, under which only a walk reaching the tip is committed. What
  completes a walk is the next parameter's, not this one's;
* the walk range — `whole` is `WTC-6`'s walk that covers its whole range (`coversRange`) and
  `asRead` is the reading it withdraws, under which a walk that passes its proofs is complete
  wherever it stops, the walk of no block included;
* the retry trigger — `neededScan` is `WTC-9` as it stands: a refresh that finds the latch set and
  no attempt in progress cold-scans of its own only until a cold scan has replaced the cache since
  the latch set, and after that a failed attempt is followed by another only at a cold scan
  `WTC-6`'s order reaches; `everyRefresh` is the rule of 2026-10-01 it withdraws, under which
  every such refresh cold-scans and starts an attempt; and `noFirstScan` is the reading that rule
  had withdrawn, under which the cache is the delta base whatever the latch;
* the chain tie — `untied` commits a walk on whichever branch `WTC-12`'s check on the view read
  after its loop finds it, and `tied`, the reading withdrawn, commits it only where its last block
  is also active on the view captured when the walk starts;
* the latch scope — `scoped` latches only a wallet that holds a completion marker, and `vacuous`,
  the reading withdrawn, latches a wallet holding none.

The delta commit, the walk range, the retry trigger and the chain tie reach `serve` and `refresh`
as one record, `Rules`, whose value as it stands is `currentRules`; the latch scope reaches
`observe`. The theorems here hold under every value or are stated with the guard they turn on
written at a literal value; `Exhibits.lean` holds every theorem over `current`, so a flip goes red
there and nowhere else. Beside the parameters sits each one's trace under its withdrawn value,
every guard written at a literal value so that a flip of one reaches only `Exhibits.lean`.

Block time is modelled by height: `WTC-7`'s birthday is "the lowest height among S and the blocks
that created every output the scan found live or the walk found spent", and `WTC-7`'s "a backend
that takes a birthday as a time MUST start its rescan no later than that height's block" is the
clause that makes a height the whole of it, since a height orders blocks on one chain the way
their times do.

**Spentness is modelled**, because the amended `WTC-7` reads it: the ledger holds both the vault
outputs a block creates and the ones it spends, each spend carrying the height of the block that
created the output it spends, and the cold scan yields what is live at the scan anchor. What is
still not modelled is `WTC-10`'s prevout re-validation, the opaque `keep` predicate, which is what
drops an output the delta walk carried and a later block spent: `WTC-6`'s delta walk adds the
outputs the walked blocks create and subtracts nothing, and `WTC-10`'s `keep` is where the sweep
drops the rest.

`WTC-10`'s "one consistent snapshot" is the **vault unspent** read the sweep consumes, from which
Coverage computes the protected value on a pass; it is not the protected value, which `DUR-22`
says to compute "on every pass from this node's current reads" and which is never a snapshot.
This module supplies what a pass reads and nothing of `DUR-22`'s arithmetic.

**Not modelled.** `WTC-6`'s signet measurement and `DEF-9`'s timing (a full scan on every warm
differs from `WTC-6` only in when it runs, and `Silence.lean` records that machine timing is not
claimed by the formal layer); the wallet's name hash and "not loaded on startup" (`WTC-7`),
operational facts the theorems never read; `SPN-33`'s authorized set, which reaches the snapshot
only as the opaque list of mempool additions; `WTC-2`'s backend operations and `WTC-4`'s timeouts;
the "loud message" and every alert; and wallet rescans. `WTC-7`'s "blank" and "descriptor-based"
are creation-time duties the `Wallet` record does not carry either. -/

namespace BtcPolicy.VaultUnspent
open BtcPolicy.Chain
open BtcPolicy.Watchtower (Scan firstLinksTo linked rangeFrom chainOf blocksOf)
open BtcPolicy.Coverage (Coin Outpoint Escape Pass sumValues)

/-! ## What the chain confirms, and what it spends -/

/-- The ground truth the sources read: the vault outputs the block with a given hash at a given
height creates, and the ones it spends, each spend carrying the height of the block that created
the output it spends — `WTC-7`'s "the blocks that created every output … the walk found spent".
Keyed by the hash as well as the height so that a fork's block at the same height confirms
different outputs, which is what every `DEF-21` fact turns on. A model parameter, not a global. -/
structure Ledger where
  vaultOutputs : Height → Hash → List Coin
  vaultSpends : Height → Hash → List (Height × Coin)

/-- The outputs the active block at a height creates on a view; none past the tip or where the
view has no block. -/
@[req "WTC-5"]
def confirmedAt (L : Ledger) (v : View) (h : Height) : List Coin :=
  match v.activeAt h with
  | some hash => L.vaultOutputs h hash
  | none => []

/-- The spends the active block at a height records on a view, each with the creating height. -/
@[req "WTC-7"]
def spentAt (L : Ledger) (v : View) (h : Height) : List (Height × Coin) :=
  match v.activeAt h with
  | some hash => L.vaultSpends h hash
  | none => []

/-- The outputs of the active blocks at `n` consecutive heights from `lo`, in height order. -/
@[req "WTC-5"]
def outputsIn (L : Ledger) (v : View) (lo : Height) : Nat → List Coin
  | 0 => []
  | n + 1 => confirmedAt L v lo ++ outputsIn L v (lo + 1) n

/-- The spends of the active blocks at `n` consecutive heights from `lo`, in height order. -/
@[req "WTC-7"]
def spendsIn (L : Ledger) (v : View) (lo : Height) : Nat → List (Height × Coin)
  | 0 => []
  | n + 1 => spentAt L v lo ++ spendsIn L v (lo + 1) n

/-- The outputs paying the vault created in every active block from `lo` to the tip's height on the
chain the view shows. -/
@[req "WTC-5"]
def confirmedFrom (L : Ledger) (v : View) (lo : Height) : List Coin :=
  outputsIn L v lo (v.tip.height + 1 - lo)

/-- The outputs spent in the active blocks at or below a height. -/
@[req "WTC-7"]
def spentUpTo (L : Ledger) (v : View) (H : Height) : List Coin :=
  (spendsIn L v 0 (H + 1)).map (·.2)

/-- `WTC-5`'s "the confirmed outputs paying the vault script", read as the amended `WTC-7` reads
them: created at or above `lo` and not spent at or below the tip. -/
@[req "WTC-5"]
def liveFrom (L : Ledger) (v : View) (lo : Height) : List Coin :=
  (confirmedFrom L v lo).filter fun x => !decide (x ∈ spentUpTo L v v.tip.height)

/-- `WTC-7`: "every output the scan found live" — every one the chain the view shows still has
unspent at its tip. -/
@[req "WTC-5"]
def live (L : Ledger) (v : View) : List Coin := liveFrom L v 0

/-- An output confirmed at a height inside the range is in the range's outputs. -/
@[req "WTC-5"]
theorem mem_outputsIn (L : Ledger) (v : View) (lo h : Height) (n : Nat) (x : Coin)
    (hx : x ∈ confirmedAt L v h) (hlo : lo ≤ h) (hn : h < lo + n) : x ∈ outputsIn L v lo n := by
  simp only [Height] at *
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    simp only [outputsIn, List.mem_append]
    by_cases heq : lo = h
    · subst heq; exact Or.inl hx
    · exact Or.inr (ih (lo + 1) (Nat.lt_of_le_of_ne hlo heq) (by rw [Nat.add_right_comm]; exact hn))

/-- And back: an output among a range's outputs was confirmed at a height inside the range. -/
@[req "WTC-5"]
theorem creator_of_mem_outputsIn (L : Ledger) (v : View) (lo : Height) (n : Nat) (x : Coin)
    (hx : x ∈ outputsIn L v lo n) : ∃ h, lo ≤ h ∧ h < lo + n ∧ x ∈ confirmedAt L v h := by
  simp only [Height] at *
  induction n generalizing lo with
  | zero => simp [outputsIn] at hx
  | succ n ih =>
    simp only [outputsIn, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨lo, Nat.le_refl _, by omega, hx⟩
    · obtain ⟨h, h1, h2, h3⟩ := ih (lo + 1) hx
      exact ⟨h, by omega, by omega, h3⟩

/-- A spend the active block at a height inside the range records is among the range's spends. -/
@[req "WTC-7"]
theorem mem_spendsIn (L : Ledger) (v : View) (lo h : Height) (n : Nat) (p : Height × Coin)
    (hp : p ∈ spentAt L v h) (hlo : lo ≤ h) (hn : h < lo + n) : p ∈ spendsIn L v lo n := by
  simp only [Height] at *
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    simp only [spendsIn, List.mem_append]
    by_cases heq : lo = h
    · subst heq; exact Or.inl hp
    · exact Or.inr (ih (lo + 1) (Nat.lt_of_le_of_ne hlo heq) (by omega))

/-- And back: a spend among a range's spends was recorded at a height inside the range. -/
@[req "WTC-7"]
theorem spender_of_mem_spendsIn (L : Ledger) (v : View) (lo : Height) (n : Nat)
    (p : Height × Coin) (hp : p ∈ spendsIn L v lo n) :
    ∃ h, lo ≤ h ∧ h < lo + n ∧ p ∈ spentAt L v h := by
  simp only [Height] at *
  induction n generalizing lo with
  | zero => simp [spendsIn] at hp
  | succ n ih =>
    simp only [spendsIn, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨lo, Nat.le_refl _, by omega, hp⟩
    · obtain ⟨h, h1, h2, h3⟩ := ih (lo + 1) hp
      exact ⟨h, by omega, by omega, h3⟩

/-- The output a spend at or below a height carries is among the outputs spent up to it. -/
@[req "WTC-7"]
theorem mem_spentUpTo (L : Ledger) (v : View) (H h : Height) (p : Height × Coin)
    (hp : p ∈ spentAt L v h) (hh : h ≤ H) : p.2 ∈ spentUpTo L v H := by
  simp only [spentUpTo, List.mem_map]
  exact ⟨p, mem_spendsIn L v 0 h (H + 1) p hp (Nat.zero_le _) (by simp only [Height] at *; omega),
    rfl⟩

/-- And back: an output spent up to a height was spent at some height at or below it. -/
@[req "WTC-7"]
theorem spender_of_mem_spentUpTo (L : Ledger) (v : View) (H : Height) (x : Coin)
    (hx : x ∈ spentUpTo L v H) : ∃ h p, h ≤ H ∧ p ∈ spentAt L v h ∧ p.2 = x := by
  simp only [spentUpTo, List.mem_map] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨h, -, hlt, hmem⟩ := spender_of_mem_spendsIn L v 0 (H + 1) p hp
  exact ⟨h, p, by simp only [Height] at *; omega, hmem, hpx⟩

/-- Two views that show the same block at a height confirm the same outputs there. -/
@[req "WTC-5"]
theorem confirmedAt_congr (L : Ledger) (v w : View) (h : Height)
    (ha : v.activeAt h = w.activeAt h) : confirmedAt L v h = confirmedAt L w h := by
  simp [confirmedAt, ha]

/-- And record the same spends there. -/
@[req "WTC-7"]
theorem spentAt_congr (L : Ledger) (v w : View) (h : Height)
    (ha : v.activeAt h = w.activeAt h) : spentAt L v h = spentAt L w h := by
  simp [spentAt, ha]

/-! ## The cache and the fire-time read (`WTC-5`) -/

/-- The vault-unspent cache: the outputs and the anchor. `WTC-5`: "anchored to the
`(height, hash)` it was computed at". -/
structure Cache where
  outputs : List Coin
  anchor : Anchor
  deriving DecidableEq, Repr

/-- The fire-time read, from the cache alone. `WTC-5`: "MUST serve every fire-time read from that
cache" and "MUST refuse if the cache's anchor is not the current tip". The read takes no ledger
and reads nothing but the tip and the cache: that is how "MUST refuse rather than scan the UTXO
set on the combine path" is stated, and `read_depends_on_tip_and_cache` says it. `WTC-6`: "a cache
whose anchor is not the current tip is refused at fire time (`WTC-5`)" — this is where the cache a
delta walk left below the tip is refused, and `served_read_iff_at_tip` says so. -/
@[req "WTC-5"]
def fireTimeRead (v : View) (c : Cache) : Option (List Coin) :=
  if c.anchor = v.tip then some c.outputs else none

/-- `WTC-5`'s refusal, both ways: the read yields outputs only when the cache's anchor is the
view's tip, and then the cache's own outputs, computed on the chain that tip names. -/
@[req "WTC-5"]
theorem read_some_iff (v : View) (c : Cache) (outs : List Coin) :
    fireTimeRead v c = some outs ↔ c.anchor = v.tip ∧ outs = c.outputs := by
  unfold fireTimeRead
  by_cases h : c.anchor = v.tip
  · simp [h, eq_comm]
  · simp [h]

/-- A cache anchored anywhere but the tip is refused. `WTC-5`: "MUST refuse if the cache's anchor
is not the current tip". A denominator from a stale cache is unreachable: the read that would
carry it is `none`. -/
@[req "WTC-5"]
theorem read_refused_when_stale (v : View) (c : Cache) (h : c.anchor ≠ v.tip) :
    fireTimeRead v c = none := by
  simp [fireTimeRead, h]

/-- The read depends on nothing but the tip and the cache: two views with the same tip read the
same, whatever else either shows. `WTC-5`: "MUST refuse rather than scan the UTXO set on the
combine path" — there is no UTXO set here to scan. -/
@[req "WTC-5"]
theorem read_depends_on_tip_and_cache (v w : View) (c : Cache) (h : v.tip = w.tip) :
    fireTimeRead v c = fireTimeRead w c := by
  simp [fireTimeRead, h]

/-! ## The wallet, its completion markers (`WTC-7`, `WTC-8`) and `WTC-11`'s fourth site -/

/-- `WTC-11`'s fourth site, one anchor at a time: the anchor is still active on the view.
`WTC-11`: "a wallet that holds completion markers none of whose anchors is still active (`WTC-8`)".
The wallet read's re-proof (`serve`), the latch (`observe`) and the import bracket
(`importBirthday`) all reach it, so the site is named once; at import the anchor is the settled
block, which the completion marker then carries. -/
@[req "WTC-11"]
def anchorStillActive (v : View) (a : Anchor) : Bool := a.active v

/-- The fourth site is refused whenever the anchor's block is not active at its height, whatever
the tip: the one-line shape of `Chain.header_refused_when_inactive`. -/
@[req "WTC-11"]
theorem anchor_refused_when_inactive (v : View) (a : Anchor)
    (hn : v.activeAt a.height ≠ some a.hash) : anchorStillActive v a = false := by
  simpa [anchorStillActive, Anchor.active] using hn

/-- A completion marker. `WTC-8`: "A **completion marker** — an inert `raw(OP_RETURN …)`
descriptor carrying the owner hash, the anchor height and hash of the import's settled block, and
the import's birthday (`WTC-7`)". The owner hash is a creation fact no theorem reads; the anchor
and the birthday are the two a theorem reads. -/
structure Marker where
  anchor : Anchor
  birthday : Height
  deriving DecidableEq, Repr

/-- The watch-only wallet as the theorems read it. `WTC-7`: "The wallet MUST be created with
private keys disabled, blank, descriptor-based, not loaded on startup, named from a hash of the
node's identity and the watched script set, and imported with the same `raw(<script>)` descriptors
the cold scan uses." The record carries what a theorem reads: private keys disabled, `WTC-8`: "A
wallet with private keys enabled is refused"; the descriptors' own birthday, as a height; the
completion markers the imports left; and whether the wallet holds every vault descriptor, `WTC-8`:
"it holds every vault descriptor". "Blank" and "descriptor-based" are creation-time duties of
`WTC-7` no theorem here reads, like the name hash and "not loaded on startup", so the record does
not carry them. -/
structure Wallet where
  privateKeysDisabled : Bool
  birthday : Height
  markers : List Marker
  holdsEveryVaultDescriptor : Bool
  deriving DecidableEq, Repr

/-- `WTC-7`: "the lowest birthday a held marker carries"; `none` when the wallet holds none. -/
@[req "WTC-7"]
def lowestBirthday : List Marker → Option Height
  | [] => none
  | m :: rest =>
    some (match lowestBirthday rest with
          | some lo => min m.birthday lo
          | none => m.birthday)

/-- What the wallet covers: the lowest birthday a held marker carries. -/
@[req "WTC-7"]
def Wallet.covers (w : Wallet) : Option Height := lowestBirthday w.markers

/-- Only a wallet holding no marker carries no lowest birthday. -/
@[req "WTC-7"]
theorem lowestBirthday_eq_none (ms : List Marker) (h : lowestBirthday ms = none) : ms = [] := by
  cases ms with
  | nil => rfl
  | cons a rest => simp [lowestBirthday] at h

/-- The lowest birthday is at or below every held marker's own. `WTC-7`: "the lowest birthday a
held marker carries". -/
@[req "WTC-7"]
theorem lowestBirthday_le_of_mem (ms : List Marker) (m : Marker) (lo : Height) (hm : m ∈ ms)
    (h : lowestBirthday ms = some lo) : lo ≤ m.birthday := by
  induction ms generalizing lo with
  | nil => cases hm
  | cons a rest ih =>
    cases hr : lowestBirthday rest with
    | none =>
      have hnil : rest = [] := lowestBirthday_eq_none rest hr
      subst hnil
      have hla : a.birthday = lo := by simpa [lowestBirthday] using h
      rcases List.mem_cons.mp hm with rfl | hmem
      · exact Nat.le_of_eq hla.symm
      · cases hmem
    | some l =>
      have hmin : min a.birthday l = lo := by
        simp only [lowestBirthday, hr, Option.some.injEq] at h
        exact h
      rcases List.mem_cons.mp hm with rfl | hmem
      · exact hmin ▸ Nat.min_le_left _ _
      · exact Nat.le_trans (hmin ▸ Nat.min_le_right _ _) (ih l hmem hr)

/-- `WTC-8`: "at least one marker whose anchor is still active", and `WTC-11`'s fourth site read
over the whole wallet. -/
@[req "WTC-8"]
def someMarkerActive (v : View) (w : Wallet) : Bool :=
  w.markers.any fun m => anchorStillActive v m.anchor

/-- `WTC-8`: "the wallet is usable only when it holds every vault descriptor, only markers
otherwise, and at least one marker whose anchor is still active" and "A wallet with private keys
enabled is refused". "Only markers otherwise" is a creation fact the record does not carry. -/
@[req "WTC-8"]
def usable (v : View) (w : Wallet) : Bool :=
  w.privateKeysDisabled && w.holdsEveryVaultDescriptor && someMarkerActive v w

/-- `WTC-8`: "A wallet with private keys enabled is refused" — never usable, on any view. -/
@[req "WTC-8"]
theorem keys_enabled_never_usable (v : View) (w : Wallet) (h : w.privateKeysDisabled = false) :
    usable v w = false := by
  simp [usable, h]

/-- A wallet none of whose markers is active is never usable. `WTC-8`: "at least one marker whose
anchor is still active". -/
@[req "WTC-8"]
theorem no_active_marker_never_usable (v : View) (w : Wallet)
    (h : someMarkerActive v w = false) : usable v w = false := by
  simp [usable, h]

/-- `WTC-8`: "at least one marker whose anchor is still active" and "Any such marker vouches for
the wallet" — one active marker is enough, whichever it is. -/
@[req "WTC-8"]
theorem any_active_marker_usable (v : View) (w : Wallet) (m : Marker) (hm : m ∈ w.markers)
    (ha : anchorStillActive v m.anchor = true) (hk : w.privateKeysDisabled = true)
    (hd : w.holdsEveryVaultDescriptor = true) : usable v w = true := by
  have hs : someMarkerActive v w = true := by
    unfold someMarkerActive
    exact List.any_eq_true.mpr ⟨m, hm, ha⟩
  simp [usable, hk, hd, hs]

/-- A wallet missing a vault descriptor is never usable. `WTC-8`: "usable only when it holds every
vault descriptor". -/
@[req "WTC-8"]
theorem missing_descriptor_never_usable (v : View) (w : Wallet)
    (h : w.holdsEveryVaultDescriptor = false) : usable v w = false := by
  simp [usable, h]

/-! ## The settled block, the walk above it, and the birthday (`WTC-7`) -/

/-- `WTC-7`: "the **settled block** S the block the **settled depth** — 10 blocks — below it".
Distinct from `WTC-13`'s 100-block cursor window (`Watchtower.window`), which bounds how far a
reorg may reach before the cursor re-scans from genesis and says nothing about a wallet import. -/
@[req "WTC-7"] def settledDepth : Nat := 10

/-- The settled block's height: the settled depth below the scan anchor, or genesis. `WTC-7`: "or
genesis when A's height is below the settled depth" — truncated subtraction is that clause. -/
@[req "WTC-7"]
def settledHeight (A : Anchor) : Height := A.height - settledDepth

/-- `WTC-7`'s settled block on a view: the block active at the settled height; `none` where the
view has none. -/
@[req "WTC-7"]
def settledBlock (v : View) (A : Anchor) : Option Anchor :=
  (v.activeAt (settledHeight A)).map fun hash => ⟨settledHeight A, hash⟩

/-- A settled block a view yields is at the settled height and active there. -/
@[req "WTC-7"]
theorem settledBlock_active (v : View) (A S : Anchor) (h : settledBlock v A = some S) :
    S.height = settledHeight A ∧ anchorStillActive v S = true := by
  unfold settledBlock at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨hash, ha, hs⟩ := h
  subst hs
  exact ⟨rfl, by simp [anchorStillActive, Anchor.active, ha]⟩

/-- `WTC-7`: "a walk of the blocks above S proven to end at A itself" — the last walked block is
the scan anchor, and a walk of no block only where the settled block is the scan anchor. -/
@[req "WTC-7"]
def endsAtScanAnchor (S A : Anchor) (bs : List Block) : Bool :=
  match bs.getLast? with
  | some b => decide (b.anchor = A)
  | none => decide (S = A)

/-- `WTC-7`: "The cold scan and a walk of the blocks above S proven to end at A itself (`WTC-12`)
form one result, and a walk that fails refuses the import." The three `WTC-12` checks
(`Watchtower.linked`) against the settled block as the expected parent, the range from one above
it, and the walk's end at `A`. -/
@[req "WTC-7"]
def settledWalkProven (S A : Anchor) (s : Scan) : Bool :=
  linked (some S.hash) s && rangeFrom (S.height + 1) s.blocks && endsAtScanAnchor S A s.blocks

/-- A consecutive walk with a last block contains every height from its start through that
block, including both endpoints. Used to derive the settled walk's coverage from its checks. -/
@[req "WTC-7"]
theorem rangeFrom_through_last (start : Height) (bs : List Block) (last : Block)
    (hr : rangeFrom start bs = true) (hl : bs.getLast? = some last) :
    start ≤ last.height ∧
      ∀ h, start ≤ h → h ≤ last.height → ∃ b ∈ bs, b.height = h := by
  induction bs generalizing start with
  | nil => simp at hl
  | cons b rest ih =>
    simp only [rangeFrom, Bool.and_eq_true, beq_iff_eq] at hr
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst last
      refine ⟨by simp only [Height] at *; omega, ?_⟩
      intro h hlo hhi
      exact ⟨b, by simp, by simp only [Height] at *; omega⟩
    | cons b' rest' =>
      obtain ⟨hle, hmem⟩ := ih (start + 1) hr.2
        (by simpa only [List.getLast?_cons_cons] using hl)
      refine ⟨by simp only [Height] at *; omega, ?_⟩
      intro h hlo hhi
      by_cases heq : h = start
      · exact ⟨b, by simp, by simp only [Height] at *; omega⟩
      · obtain ⟨a, ha, hah⟩ := hmem h (by simp only [Height] at *; omega) hhi
        exact ⟨a, List.mem_cons_of_mem b ha, hah⟩

/-- `WTC-7`: "a walk of the blocks above S proven to end at A itself". The operational checks
give the scan-anchor height bound and a block at every height in `(S, A]`. For an empty walk,
the end check gives `S = A`; no activity lookup or assumption about a view's tip is used. -/
@[req "WTC-7"]
theorem settledWalkProven_interval (S A : Anchor) (s : Scan)
    (hw : settledWalkProven S A s = true) :
    S.height ≤ A.height ∧
      ∀ h, S.height < h → h ≤ A.height → ∃ b ∈ s.blocks, b.height = h := by
  simp only [settledWalkProven, Bool.and_eq_true] at hw
  have hend := hw.2
  unfold endsAtScanAnchor at hend
  cases hl : s.blocks.getLast? with
  | none =>
    simp only [hl, decide_eq_true_eq] at hend
    subst A
    exact ⟨Nat.le_refl _, by intro h hlo hhi; simp only [Height] at *; omega⟩
  | some last =>
    simp only [hl, decide_eq_true_eq] at hend
    have hh : last.height = A.height := congrArg Anchor.height hend
    obtain ⟨hle, hmem⟩ := rangeFrom_through_last (S.height + 1) s.blocks last hw.1.2 hl
    refine ⟨by simp only [Height] at *; omega, ?_⟩
    intro h hlo hhi
    exact hmem h (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)

/-- The lowest of `n` consecutive heights from `lo` whose active block created one of `xs`. -/
@[req "WTC-7"]
def lowestCreator (L : Ledger) (v : View) (xs : List Coin) (lo : Height) : Nat → Option Height
  | 0 => none
  | n + 1 =>
    if (confirmedAt L v lo).any (fun x => decide (x ∈ xs)) then some lo
    else lowestCreator L v xs (lo + 1) n

/-- `WTC-7`: the lowest of "the blocks that created every output the scan found live"; `none` when
the scan found none live. -/
@[req "WTC-7"]
def liveCreator (L : Ledger) (v : View) : Option Height :=
  lowestCreator L v (live L v) 0 (v.tip.height + 1)

/-- The lowest creator of a list is found, and is at or below the creating height of any member
the range confirms. -/
@[req "WTC-7"]
theorem lowestCreator_le (L : Ledger) (v : View) (xs : List Coin) (lo c : Height) (n : Nat)
    (x : Coin) (hx : x ∈ confirmedAt L v c) (hxs : x ∈ xs) (hlo : lo ≤ c) (hn : c < lo + n) :
    ∃ h, lowestCreator L v xs lo n = some h ∧ h ≤ c := by
  simp only [Height] at *
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    by_cases hany : (confirmedAt L v lo).any (fun y => decide (y ∈ xs)) = true
    · exact ⟨lo, by simp [lowestCreator, hany], hlo⟩
    · have hne : lo ≠ c := by
        intro he
        subst he
        exact hany (List.any_eq_true.mpr ⟨x, hx, by simpa using hxs⟩)
      obtain ⟨h, hh, hle⟩ := ih (lo + 1) (Nat.lt_of_le_of_ne hlo hne) (by omega)
      exact ⟨h, by simp [lowestCreator, hany, hh], hle⟩

/-- The spends the walk above the settled block found, each with its creating height. -/
@[req "WTC-7"]
def walkSpends (L : Ledger) (s : Scan) : List (Height × Coin) :=
  s.blocks.flatMap fun b => L.vaultSpends b.height b.hash

/-- The lowest of a start and a list of heights. -/
@[req "WTC-7"]
def lowestOf (start : Height) : List Height → Height
  | [] => start
  | h :: rest => lowestOf (min start h) rest

/-- The lowest of a start and a list never rises above the start. -/
@[req "WTC-7"]
theorem lowestOf_le (start : Height) (hs : List Height) : lowestOf start hs ≤ start := by
  induction hs generalizing start with
  | nil => exact Nat.le_refl _
  | cons h rest ih => exact Nat.le_trans (ih (min start h)) (Nat.min_le_left _ _)

/-- Nor above any height the list holds. -/
@[req "WTC-7"]
theorem lowestOf_le_of_mem (start h : Height) (hs : List Height) (hm : h ∈ hs) :
    lowestOf start hs ≤ h := by
  induction hs generalizing start with
  | nil => cases hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with rfl | hr
    · exact Nat.le_trans (lowestOf_le (min start h) rest) (Nat.min_le_right _ _)
    · exact ih (min start a) hr

/-- `WTC-7`: "The import's **birthday** is the lowest height among S and the blocks that created
every output the scan found live or the walk found spent, so the import covers every output a
reorg that leaves S active can make live." -/
@[req "WTC-7"]
def settledBirthday (L : Ledger) (v : View) (S : Anchor) (s : Scan) : Height :=
  lowestOf S.height ((liveCreator L v).toList ++ (walkSpends L s).map (·.1))

/-- The birthday the withdrawn reading gives: the scan anchor and the creators of what the scan
found live, with no walk below it. -/
@[req "WTC-7"]
def scanTipBirthday (L : Ledger) (v : View) (A : Anchor) : Height :=
  lowestOf A.height (liveCreator L v).toList

/-- The birthday never rises above the settled block's height: `WTC-7`'s floor. -/
@[req "WTC-7"]
theorem settledBirthday_le (L : Ledger) (v : View) (S : Anchor) (s : Scan) :
    settledBirthday L v S s ≤ S.height := lowestOf_le S.height _

/-! ## The guard parameters (`ADR-0023` decision 6), and the import (`WTC-7`, `DEF-21`) -/

/-- The import bracket. `reProve` is `WTC-7` as it stands. `unbracketed` is `DEF-21`'s twin, the
import that reads no anchor again — `DEF-21`: "A reorg landing between the cold scan and the
wallet import could import a birthday proven on an abandoned fork, leaving an output permanently
unwatched and inflating apparent coverage." -/
inductive ImportBracket
  | reProve | unbracketed
  deriving DecidableEq, Repr

/-- `WTC-7` as it stands. `WTC-7`: "The import MUST be bracketed by re-proving S is still active,
before the descriptors are imported and again before the marker is (`WTC-8`); if it moved, the
import is refused rather than importing a birthday from another branch, which would leave an
output permanently unwatched and inflate apparent coverage." `DEF-21`: "the import MUST be
bracketed by re-proving the settled block, and the walk above it MUST end at the scan anchor
(`WTC-7`)." -/
@[req "WTC-7"]
def current : ImportBracket := .reProve

/-- What a completion marker anchors at, and what the birthday is floored by. `settled` is the
amended `WTC-7`. `scanTip` is the reference implementation's reading: the scan anchor itself, with
no walk of the settled depth below it, under which a reorg reaching no deeper than the settled
depth below an import's own scan anchor unseats that import's own marker, at the tip it read, and
costs a repair whenever the wallet holds no other marker whose anchor the reorg leaves active
(`ADR-0024`). While a held marker's anchor is still standing it leaves no output unwatched — the
floor rule closes that, and `scanTip_active_marker_watches_everything` is the fact, under its own
hypotheses; a reorg that unseats every held marker takes the wallet out of use and runs the repair
instead (`markerAnchor_repairs_with_scanTip`). -/
inductive MarkerAnchor
  | settled | scanTip
  deriving DecidableEq, Repr

/-- `WTC-7` as amended. `WTC-7`: "Let the **scan anchor** A be the block the cold scan read at, and
the **settled block** S the block the **settled depth** — 10 blocks — below it, or genesis when A's
height is below the settled depth." -/
@[req "WTC-7"]
def currentMarkerAnchor : MarkerAnchor := .settled

/-- What a delta walk commits. `partialWalk` is the amended `WTC-6`: a walk that completes is
committed even where it ends below the tip. `tipOnly` is the reading it withdraws, under which a
walk ending below the tip is thrown away and the cold scan runs instead. What completes a walk is
`WalkRange`'s to say, under either value of this one. -/
inductive DeltaCommit
  | partialWalk | tipOnly
  deriving DecidableEq, Repr

/-- `WTC-6` as amended. `WTC-6`: "A walk that completes becomes the cache even where it ends below
the tip, and any later delta walk starts from that cache; a cache whose anchor is not the current
tip is refused at fire time (`WTC-5`)". -/
@[req "WTC-6"]
def currentDeltaCommit : DeltaCommit := .partialWalk

/-- What completes a delta walk. `whole` is `WTC-6` as it stands since 2026-10-01: the walk covers
its whole range (`coversRange`) or is discarded. `asRead` is the reading that amendment withdraws,
under which a walk that passes its proofs is complete wherever it stops: a walk that stops short
of its range is committed, and so is a walk of no block, which every proof passes vacuously, so a
refresh can go on serving a cache below the tip without ever reading a block
(`short_and_empty_walk_committed_with_asRead`). -/
inductive WalkRange
  | whole | asRead
  deriving DecidableEq, Repr

/-- `WTC-6` as it stands. `WTC-6`: "The delta walk covers every height above the cache's anchor
through the lesser of the tip captured when the walk starts and 32 blocks above that anchor." And
`WTC-6`: "A walk that covers less is discarded whole". -/
@[req "WTC-6"]
def currentWalkRange : WalkRange := .whole

/-- When a refresh that finds the latch set and no attempt in progress cold-scans of its own, and
so what starts a repair again after one has failed. `neededScan` is `WTC-9` as it stands since
2026-10-02: such a refresh has no delta base, and so cold-scans and starts an attempt, only until a
cold scan has replaced the cache since the latch set (`State.scanned`); after that the cache is the
delta base, and an attempt that failed is followed by another only at a cold scan `WTC-6`'s own
order reaches. `everyRefresh` is the rule of 2026-10-01 that amendment withdraws: no delta base on
any refresh that finds the latch set and no attempt in progress, so a repair that keeps failing
costs a cold scan on every refresh (`failed_attempt_rescans_with_everyRefresh`). `noFirstScan` is
the reading the amendment of 2026-10-01 had itself withdrawn: the cache is the delta base whatever
the latch, so a refresh walks on from the cache it held when the latch set, which a wallet read may
have left (`latched_unscanned_walks_with_noFirstScan`).

This parameter takes in the latched base, the parameter the amendment of 2026-10-01 brought. Its
`coldScan` was `everyRefresh` and its `cache` is `noFirstScan`: both answer the one question this
parameter asks, what a latched refresh with no attempt in progress walks from, so a second
parameter would have carried values the first overrides. What the `cache` twin exhibited then — a
failed repair not started again while walks succeed — is no longer withdrawn: it is `WTC-9`'s
stated consequence, and `Exhibits.VaultUnspentCache.failed_attempt_not_retried_while_walks_succeed`
exhibits it under the value as it stands. What `noFirstScan` still withdraws is the walk from the
cache held when the latch set. -/
inductive RetryTrigger
  | neededScan | everyRefresh | noFirstScan
  deriving DecidableEq, Repr

/-- `WTC-9` as it stands. `WTC-9`: "the next attempt starts only from a cold scan `WTC-6` itself
reaches with none in progress, and starts no scan of its own". And `WTC-9`: "From the latch setting
until a cold scan has replaced the cache, every refresh with no attempt in progress starts a repair
attempt from a cold scan, whatever cache it holds". -/
@[req "WTC-9"]
def currentRetryTrigger : RetryTrigger := .neededScan

/-- Which chain a committed walk must end on. `untied` is the rule as it stands since 2026-10-02: a
walk that links from the cached anchor, covers its range by height and passes `WTC-12`'s checks on
the view read after its loop is committed, and no test is made against the view captured when the
walk starts. `tied` is the reading of 2026-10-01 that amendment withdraws, which no sentence of
`WTC-6` states: a walk is committed only where its last block is also active on the view captured
when the walk starts, so a walk read correctly on a branch the chain moved to after that view was
captured is discarded for a cold scan (`off_branch_walk_refused_with_tied`). -/
inductive ChainTie
  | tied | untied
  deriving DecidableEq, Repr

/-- The rule as it stands. `WTC-12`: "after the loop the hash at the last height still equals the
last scanned hash" — the walk's end is compared with the chain as it is after the walk, and that is
the whole of the test (`deltaWalk`, through `Watchtower.linked`). A cache the walk leaves anywhere
but the tip is refused at fire time — `WTC-5`: "MUST refuse if the cache's anchor is not the
current tip". -/
@[req "WTC-6"]
def currentChainTie : ChainTie := .untied

/-- Which wallets the latch applies to. `scoped` is `WTC-9` as it stands since 2026-10-02: only a
wallet that holds a completion marker, none of whose markers is active, is latched. `vacuous` is
the reading that amendment withdraws, under which a wallet holding no marker meets the condition
with nothing to check, so the wallet before its first build is latched and its build runs as a
repair, with a cold scan of its own (`unbuilt_wallet_latches_with_vacuous`). `observe` reads this
parameter; `serve` and `refresh` do not, so it is not one of `Rules`. -/
inductive LatchScope
  | scoped | vacuous
  deriving DecidableEq, Repr

/-- `WTC-9` as it stands. `WTC-9`: "If the wallet holds a completion marker and none it holds has
an anchor on the active chain the node MUST latch a repair". And `WTC-9`: "A wallet holding no
completion marker is not latched, `WTC-8` already keeping it out of use". -/
@[req "WTC-9"]
def currentLatchScope : LatchScope := .scoped

/-- The four guard parameters `serve` and `refresh` read, as one record: what a walk commits, what
completes it, when a latched refresh cold-scans of its own, and which chain a committed walk ends
on. -/
structure Rules where
  commit : DeltaCommit
  range : WalkRange
  retry : RetryTrigger
  chain : ChainTie
  deriving DecidableEq, Repr

/-- The four as they stand. -/
@[req "WTC-6"]
def currentRules : Rules :=
  { commit := currentDeltaCommit, range := currentWalkRange, retry := currentRetryTrigger,
    chain := currentChainTie }

/-- The bracket. Under `reProve` the settled block is re-proved at **both** points `WTC-7` names,
before the descriptors and again before the marker, and the import is refused when either read
finds it inactive — `DEF-21`: "the import MUST be bracketed by re-proving the settled block".
Under `unbracketed` the birthday is imported whatever either view shows. -/
@[req "WTC-7"]
def importBirthday (br : ImportBracket) (S : Anchor) (atDescriptors atMarker : View)
    (bday : Height) : Option Height :=
  match br with
  | .reProve =>
    if anchorStillActive atDescriptors S && anchorStillActive atMarker S then some bday else none
  | .unbracketed => some bday

/-- Under `reProve`, over every anchor, pair of views and birthday: a settled block that moved at
either bracket point refuses the import. `WTC-7`: "if it moved, the import is refused rather than
importing a birthday from another branch". -/
@[req "WTC-7"]
theorem import_refused_when_moved (S : Anchor) (atDescriptors atMarker : View) (b : Height)
    (h : anchorStillActive atDescriptors S = false ∨ anchorStillActive atMarker S = false) :
    importBirthday .reProve S atDescriptors atMarker b = none := by
  rcases h with h | h <;> simp [importBirthday, h]

/-- Under `reProve` a settled block active at both points imports the birthday: the bracket refuses
nothing a stable chain offers. -/
@[req "WTC-7"]
theorem import_accepted_when_active (S : Anchor) (atDescriptors atMarker : View) (b : Height)
    (hd : anchorStillActive atDescriptors S = true) (hm : anchorStillActive atMarker S = true) :
    importBirthday .reProve S atDescriptors atMarker b = some b := by
  simp [importBirthday, hd, hm]

/-- Under `unbracketed` every import goes through, moved settled block or not. -/
@[req "WTC-7"]
theorem unbracketed_imports_anything (S : Anchor) (atDescriptors atMarker : View) (b : Height) :
    importBirthday .unbracketed S atDescriptors atMarker b = some b := rfl

/-- The import `WTC-7` describes, as the marker `WTC-8` records it: the scan anchor is the scan
view's tip, the settled block is the settled depth below it, the walk above it must be proven to end
at the scan anchor, and the birthday is floored at the settled block. The bracket decides whether
the marker exists at all. -/
@[req "WTC-7"]
def settledImport (br : ImportBracket) (L : Ledger) (scanView atDescriptors atMarker : View)
    (s : Scan) : Option Marker :=
  match settledBlock scanView scanView.tip with
  | none => none
  | some S =>
    if settledWalkProven S scanView.tip s then
      (importBirthday br S atDescriptors atMarker (settledBirthday L scanView S s)).map
        fun b => { anchor := S, birthday := b }
    else none

/-- The same import under the withdrawn value: the marker anchors at the scan anchor, the birthday
reads the cold scan alone, and no walk of the settled depth is taken. -/
@[req "WTC-7"]
def scanTipImport (br : ImportBracket) (L : Ledger) (scanView atDescriptors atMarker : View) :
    Option Marker :=
  (importBirthday br scanView.tip atDescriptors atMarker
      (scanTipBirthday L scanView scanView.tip)).map
    fun b => { anchor := scanView.tip, birthday := b }

/-- The import, under the guard. -/
@[req "WTC-7"]
def importMarker (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) : Option Marker :=
  match ma with
  | .settled => settledImport br L scanView atDescriptors atMarker s
  | .scanTip => scanTipImport br L scanView atDescriptors atMarker

/-- Under `settled`, whatever the bracket: the marker the import leaves is anchored at the settled
block, and its birthday is at or below that block's height. `WTC-8`: "the anchor height and hash of
the import's settled block". -/
@[req "WTC-7"]
theorem marker_at_settled_block (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (m : Marker)
    (h : importMarker .settled br L scanView atDescriptors atMarker s = some m) :
    settledBlock scanView scanView.tip = some m.anchor ∧ m.birthday ≤ m.anchor.height := by
  simp only [importMarker] at h
  unfold settledImport at h
  split at h
  · cases h
  · rename_i S hS
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨b, hb, hm⟩ := h
      subst hm
      refine ⟨hS, ?_⟩
      cases br with
      | reProve =>
        simp only [importBirthday] at hb
        split at hb
        · simp only [Option.some.injEq] at hb
          subst hb
          exact settledBirthday_le L scanView S s
        · cases hb
      | unbracketed =>
        simp only [importBirthday, Option.some.injEq] at hb
        subst hb
        exact settledBirthday_le L scanView S s
    · cases h

/-- Under `settled`, whatever the bracket, a walk that fails any check refuses the import. `WTC-7`:
"a walk that fails refuses the import". -/
@[req "WTC-7"]
theorem import_refused_when_walk_fails (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (S : Anchor)
    (hS : settledBlock scanView scanView.tip = some S)
    (hw : settledWalkProven S scanView.tip s = false) :
    importMarker .settled br L scanView atDescriptors atMarker s = none := by
  simp [importMarker, settledImport, hS, hw]

/-- Under `scanTip`, whatever the bracket: the marker the import leaves is anchored at the scan
anchor — the scan view's own tip — and carries the birthday the cold scan alone gives. -/
@[req "WTC-7"]
theorem marker_at_scan_tip (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (m : Marker)
    (h : importMarker .scanTip br L scanView atDescriptors atMarker s = some m) :
    m.anchor = scanView.tip ∧ m.birthday = scanTipBirthday L scanView scanView.tip := by
  simp only [importMarker, scanTipImport, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, hm⟩ := h
  subst hm
  refine ⟨rfl, ?_⟩
  cases br with
  | reProve =>
    simp only [importBirthday] at hb
    split at hb
    · simpa using hb.symm
    · cases hb
  | unbracketed => simpa [importBirthday] using hb.symm

/-- The coupling the withdrawn value carries: under `scanTip` a marker's birthday is at most its
anchor's height, because the birthday is floored at the scan anchor and the marker anchors there
too. Under `settled` the floor is the settled block instead (`marker_at_settled_block`). -/
@[req "WTC-7"]
theorem scanTip_birthday_le_anchor (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (m : Marker)
    (h : importMarker .scanTip br L scanView atDescriptors atMarker s = some m) :
    m.birthday ≤ m.anchor.height := by
  obtain ⟨ha, hb⟩ := marker_at_scan_tip br L scanView atDescriptors atMarker s m h
  rw [ha, hb]
  exact lowestOf_le _ _

/-! ## What a wallet imported with a birthday watches (`WTC-7`) -/

/-- The outputs a wallet imported with a birthday watches on a view: the outputs live at the tip
that the blocks from the birthday up created. A wallet scans from its birthday up, so an output
created below it is never seen by that wallet: that is what "permanently unwatched" means here,
and nothing about wallet rescans is modelled. -/
@[req "WTC-7"]
def watched (L : Ledger) (v : View) (bday : Height) : List Coin := liveFrom L v bday

/-- The outputs such a wallet leaves unwatched: the outputs live on that view that the watched
list lacks. -/
@[req "WTC-7"]
def unwatched (L : Ledger) (v : View) (bday : Height) : List Coin :=
  (live L v).filter fun x => !decide (x ∈ watched L v bday)

/-- A wallet imported from genesis leaves nothing unwatched, on any view: the birthday is the whole
of what "unwatched" turns on. -/
@[req "WTC-7"]
theorem genesis_birthday_watches_everything (L : Ledger) (v : View) : unwatched L v 0 = [] := by
  simp [unwatched, watched, live]

/-- `WTC-7`: "so the import covers every output a reorg that leaves S active can make live".
This is a property of the formal model under the following named hypotheses, not runtime
conformance. `hwalk` is the operational proven walk, supplied separately from `scanView`;
`hblocks` ties every walked block to that view because the final activity check reads `s.after`.
`_hscanActive` and `_hlaterActive` identify the preserved settled block. The proof needs only the
stronger pointwise prefix agreement `hagree`, but the activity hypotheses retain the scope of
the quoted claim. Neither agreement nor `hlaterTip` follows from activity: `View` permits
arbitrary maps and independently supplied tips, even lookups above the tip. The scan-view bound
is instead derived from `hwalk`, including its empty case. `hcreators` requires recorded creating
heights to match every creation occurrence within the finite scan range: `Ledger` supplies
independent output and spend functions and enforces neither that consistency nor unique creation
occurrences. The later branch above S is unrestricted, and resurrection is permitted. -/
@[req "WTC-7"]
theorem settledBirthday_watches_everything (L : Ledger) (scanView v' : View) (S : Anchor)
    (s : Scan) (hwalk : settledWalkProven S scanView.tip s = true)
    (hblocks : ∀ b ∈ s.blocks, scanView.activeAt b.height = some b.hash)
    (_hscanActive : S.active scanView = true) (_hlaterActive : S.active v' = true)
    (hagree : ∀ h, h ≤ S.height → v'.activeAt h = scanView.activeAt h)
    (hlaterTip : S.height ≤ v'.tip.height)
    (hcreators : ∀ d, d ≤ scanView.tip.height → ∀ c, c ≤ scanView.tip.height →
      ∀ p ∈ spentAt L scanView d, p.2 ∈ confirmedAt L scanView c → p.1 = c) :
    unwatched L v' (settledBirthday L scanView S s) = [] := by
  obtain ⟨hscanTip, hwalkHeight⟩ := settledWalkProven_interval S scanView.tip s hwalk
  have hfloor := settledBirthday_le L scanView S s
  have key : ∀ x ∈ live L v', x ∈ watched L v' (settledBirthday L scanView S s) := by
    intro x hx
    simp only [live, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hx
    obtain ⟨hconf, hspent⟩ := hx
    obtain ⟨c, -, hclt, hc⟩ := creator_of_mem_outputsIn L v' 0 _ x hconf
    have hcle : c ≤ v'.tip.height := by simp only [Height] at *; omega
    have hbday : settledBirthday L scanView S s ≤ c := by
      by_cases hcs : S.height ≤ c
      · exact Nat.le_trans hfloor hcs
      have hcs' : c ≤ S.height := Nat.le_of_lt (Nat.lt_of_not_ge hcs)
      have hcscan : x ∈ confirmedAt L scanView c :=
        confirmedAt_congr L v' scanView c (hagree c hcs') ▸ hc
      have hcrange : c ≤ scanView.tip.height := Nat.le_trans hcs' hscanTip
      by_cases hsp : x ∈ spentUpTo L scanView scanView.tip.height
      · obtain ⟨d, p, hd, hp, hpx⟩ := spender_of_mem_spentUpTo L scanView _ x hsp
        have hds : S.height < d := by
          apply Nat.lt_of_not_ge
          intro hle
          have hp' : p ∈ spentAt L v' d :=
            spentAt_congr L v' scanView d (hagree d hle) ▸ hp
          exact hspent (hpx ▸ mem_spentUpTo L v' _ d p hp' (Nat.le_trans hle hlaterTip))
        obtain ⟨b, hb, hbd⟩ := hwalkHeight d hds hd
        have hpblock : p ∈ L.vaultSpends b.height b.hash := by
          have hpheight : p ∈ spentAt L scanView b.height := hbd.symm ▸ hp
          simpa only [spentAt, hblocks b hb] using hpheight
        have hpwalk : p ∈ walkSpends L s := List.mem_flatMap.mpr ⟨b, hb, hpblock⟩
        have hcreator : p.1 = c := hcreators d hd c hcrange p hp (hpx.symm ▸ hcscan)
        exact lowestOf_le_of_mem S.height c _
          (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hpwalk, hcreator⟩)))
      · have hlive : x ∈ live L scanView := by
          simp only [live, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
            Bool.not_true, decide_eq_false_iff_not]
          exact ⟨mem_outputsIn L scanView 0 c _ x hcscan (Nat.zero_le _)
            (by simp only [Height] at *; omega), hsp⟩
        obtain ⟨lo, hlo, hloc⟩ := lowestCreator_le L scanView (live L scanView) 0 c
          (scanView.tip.height + 1) x hcscan hlive (Nat.zero_le _)
          (by simp only [Height] at *; omega)
        unfold settledBirthday liveCreator
        rw [hlo]
        exact Nat.le_trans (lowestOf_le_of_mem _ lo _ (by simp)) hloc
    simp only [watched, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    exact ⟨mem_outputsIn L v' _ c _ x hc hbday (by simp only [Height] at *; omega), hspent⟩
  simp only [unwatched, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Decidable.not_not]
  exact key

/-- A successful settled import supplies the proven walk, the settled block's activity on the
scan view and the marker's birthday. Apply `settledBirthday_watches_everything` to that birthday,
under its remaining chain and ledger hypotheses. This holds for either import bracket; the later
view's preserved settled block is still an explicit hypothesis. -/
@[req "WTC-7"]
theorem settledImport_watches_everything (br : ImportBracket) (L : Ledger)
    (scanView v' atDescriptors atMarker : View) (s : Scan) (m : Marker)
    (hi : settledImport br L scanView atDescriptors atMarker s = some m)
    (hblocks : ∀ b ∈ s.blocks, scanView.activeAt b.height = some b.hash)
    (hlaterActive : m.anchor.active v' = true)
    (hagree : ∀ h, h ≤ m.anchor.height → v'.activeAt h = scanView.activeAt h)
    (hlaterTip : m.anchor.height ≤ v'.tip.height)
    (hcreators : ∀ d, d ≤ scanView.tip.height → ∀ c, c ≤ scanView.tip.height →
      ∀ p ∈ spentAt L scanView d, p.2 ∈ confirmedAt L scanView c → p.1 = c) :
    unwatched L v' m.birthday = [] := by
  unfold settledImport at hi
  split at hi
  · cases hi
  · rename_i S hS
    split at hi
    · rename_i hw
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨b, hb, hm⟩ := hi
      subst m
      have hbday : b = settledBirthday L scanView S s := by
        cases br with
        | reProve =>
          simp only [importBirthday] at hb
          split at hb
          · exact (Option.some.inj hb).symm
          · cases hb
        | unbracketed => exact (Option.some.inj hb).symm
      subst b
      exact settledBirthday_watches_everything L scanView v' S s hw hblocks
        (settledBlock_active scanView scanView.tip S hS).2 hlaterActive hagree hlaterTip hcreators
    · cases hi

/-- `WTC-7`'s floor closes the hole under the withdrawn marker anchor while a held marker's anchor
is still standing — this theorem's `hm` and `hagree`. It says nothing about the reorg that unseats
every held marker. Take a wallet whose descriptors start at the lowest birthday a held marker
carries — `WTC-7`: "A repair never starts later than the wallet already covers", the shape a first
import establishes and `applyImport` preserves (`birthday_never_rises`) — and a marker it holds that
some `scanTip` import left, on that import's own scan view `w`. Assume the reorg leaves that
marker's anchor standing, and assume as well (`hagree`) that the view `v` after it shows the same
block at every height at or below the anchor. The second does not follow from the first here:
`View` is an arbitrary map from heights to hashes and `Anchor.active` tests a single height, so a
view could keep the anchor's hash at the anchor's height and still change a block below it.
`hagree` is an assumption the model takes about the chain — a reorg that replaces a block replaces
every block above it — not something `Anchor.active` gives. Under both, and with `v`'s tip at or
above the anchor's height (`htip`), nothing live on `v` is unwatched: the output would have to be
created below the wallet's floor, and any such output live on `v` was live at that marker's own
import too, which floored its birthday at or below the output's creating height. So under `scanTip`
a reorg either unseats every held marker — and `WTC-9` latches a repair, which is what the value
costs (`markerAnchor_repairs_with_scanTip`) — or leaves one standing, and then, on that assumption,
there is nothing for the birthday to miss. -/
@[req "WTC-7"]
theorem scanTip_active_marker_watches_everything (br : ImportBracket) (L : Ledger)
    (v w atDescriptors atMarker : View) (s : Scan) (wl : Wallet) (m : Marker)
    (hi : importMarker .scanTip br L w atDescriptors atMarker s = some m)
    (hm : m ∈ wl.markers) (hfloor : wl.covers = some wl.birthday)
    (hagree : ∀ h, h ≤ m.anchor.height → v.activeAt h = w.activeAt h)
    (htip : m.anchor.height ≤ v.tip.height) :
    unwatched L v wl.birthday = [] := by
  obtain ⟨hanch, hbday⟩ := marker_at_scan_tip br L w atDescriptors atMarker s m hi
  have hba : m.birthday ≤ m.anchor.height :=
    scanTip_birthday_le_anchor br L w atDescriptors atMarker s m hi
  have hwl : wl.birthday ≤ m.birthday :=
    lowestBirthday_le_of_mem wl.markers m wl.birthday hm hfloor
  have hwtip : m.anchor.height = w.tip.height := by rw [hanch]
  have key : ∀ x ∈ live L v, x ∈ watched L v wl.birthday := by
    intro x hx
    simp only [live, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hx
    obtain ⟨hconf, hspent⟩ := hx
    obtain ⟨c, -, hclt, hc⟩ := creator_of_mem_outputsIn L v 0 _ x hconf
    have hcle : c ≤ v.tip.height := by simp only [Height] at *; omega
    have hfl : wl.birthday ≤ c := by
      rcases Nat.lt_or_ge c wl.birthday with hcb | hge
      case inr => exact hge
      have hcm : c < m.anchor.height := by simp only [Height] at *; omega
      have hcw : x ∈ confirmedAt L w c :=
        confirmedAt_congr L v w c (hagree c (Nat.le_of_lt hcm)) ▸ hc
      have hnotspent : x ∉ spentUpTo L w w.tip.height := by
        intro hsp
        obtain ⟨h0, q, hh0, hq, hqx⟩ := spender_of_mem_spentUpTo L w w.tip.height x hsp
        have hq' : q ∈ spentAt L v h0 :=
          spentAt_congr L v w h0 (hagree h0 (by simp only [Height] at *; omega)) ▸ hq
        exact hspent (hqx ▸ mem_spentUpTo L v v.tip.height h0 q hq'
          (by simp only [Height] at *; omega))
      have hlive : x ∈ live L w := by
        simp only [live, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not]
        exact ⟨mem_outputsIn L w 0 c _ x hcw (Nat.zero_le _) (by simp only [Height] at *; omega),
          hnotspent⟩
      obtain ⟨h1, hh1, hh1le⟩ := lowestCreator_le L w (live L w) 0 c (w.tip.height + 1) x hcw hlive
        (Nat.zero_le _) (by simp only [Height] at *; omega)
      have hmb : m.birthday ≤ c := by
        rw [hbday]
        unfold scanTipBirthday liveCreator
        rw [hh1]
        exact Nat.le_trans (lowestOf_le_of_mem _ h1 _ (by simp)) hh1le
      simp only [Height] at *; omega
    simp only [watched, liveFrom, confirmedFrom, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    exact ⟨mem_outputsIn L v wl.birthday c _ x hc hfl (by simp only [Height] at *; omega), hspent⟩
  simp only [unwatched, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Decidable.not_not]
  intro x hx
  exact key x hx

/-! ## The repair rule, and the birthday that never rises (`WTC-7`) -/

/-- `WTC-7`: "when its birthday is not below the lowest birthday a held marker carries, it imports
only a new marker". A first import, with no marker held, is never marker-only. -/
@[req "WTC-7"]
def markerOnly (w : Wallet) (m : Marker) : Bool :=
  match w.covers with
  | some lo => decide (lo ≤ m.birthday)
  | none => false

/-- Applying an import to the wallet. `WTC-7`: "A repair never starts later than the wallet already
covers: when its birthday is not below the lowest birthday a held marker carries, it imports only a
new marker, and otherwise it re-imports the descriptors from its own birthday." -/
@[req "WTC-7"]
def applyImport (w : Wallet) (m : Marker) : Wallet :=
  if markerOnly w m then { w with markers := m :: w.markers }
  else { w with birthday := m.birthday, markers := m :: w.markers,
                holdsEveryVaultDescriptor := true }

/-- Either way the marker is held, so what the wallet covers never rises. `WTC-8`: "a repair never
starts later than the wallet already covers and so never narrows what an earlier marker's import
covered". -/
@[req "WTC-8"]
theorem covers_never_rises (w : Wallet) (m : Marker) (lo : Height) (h : w.covers = some lo) :
    (applyImport w m).covers = some (min m.birthday lo) ∧ min m.birthday lo ≤ lo := by
  have hm : (applyImport w m).markers = m :: w.markers := by
    unfold applyImport; split <;> rfl
  refine ⟨?_, Nat.min_le_right _ _⟩
  simp only [Wallet.covers, hm, lowestBirthday]
  rw [show lowestBirthday w.markers = some lo from h]

/-- A marker-only import leaves the descriptors alone. `WTC-7`: "it imports only a new marker". -/
@[req "WTC-7"]
theorem marker_only_keeps_descriptors (w : Wallet) (m : Marker) (h : markerOnly w m = true) :
    (applyImport w m).birthday = w.birthday ∧
      (applyImport w m).holdsEveryVaultDescriptor = w.holdsEveryVaultDescriptor ∧
      (applyImport w m).markers = m :: w.markers := by
  simp [applyImport, h]

/-- Otherwise the descriptors are re-imported from the import's own birthday. `WTC-7`: "otherwise
it re-imports the descriptors from its own birthday". -/
@[req "WTC-7"]
theorem reimport_takes_own_birthday (w : Wallet) (m : Marker) (h : markerOnly w m = false) :
    (applyImport w m).birthday = m.birthday ∧
      (applyImport w m).holdsEveryVaultDescriptor = true := by
  simp [applyImport, h]

/-- The descriptors' birthday never rises either, and stays what the wallet covers: a marker-only
import leaves it, and a re-import lowers it. `WTC-7`: "A repair never starts later than the wallet
already covers." -/
@[req "WTC-7"]
theorem birthday_never_rises (w : Wallet) (m : Marker) (h : w.covers = some w.birthday) :
    (applyImport w m).birthday ≤ w.birthday ∧
      (applyImport w m).covers = some (applyImport w m).birthday := by
  obtain ⟨hc, -⟩ := covers_never_rises w m w.birthday h
  by_cases hle : w.birthday ≤ m.birthday
  · have h1 : markerOnly w m = true := by simp [markerOnly, h, hle]
    obtain ⟨hb, -, -⟩ := marker_only_keeps_descriptors w m h1
    rw [hb, hc, Nat.min_eq_right hle]
    exact ⟨Nat.le_refl _, rfl⟩
  · have h1 : markerOnly w m = false := by simp [markerOnly, h, hle]
    have hle' : m.birthday ≤ w.birthday := Nat.le_of_not_le hle
    obtain ⟨hb, -⟩ := reimport_takes_own_birthday w m h1
    rw [hb, hc, Nat.min_eq_left hle']
    exact ⟨hle', rfl⟩

/-! ## The three sources and their order (`WTC-6`) -/

/-- The three sources, in `WTC-6`'s order of preference. -/
inductive Source
  | wallet | deltaWalk | coldScan
  deriving DecidableEq, Repr

/-- `WTC-6`: "a bounded delta walk of at most 32 blocks from a cached anchor whose block is still
active". -/
@[req "WTC-6"] def deltaWindow : Nat := 32

/-- The wallet read: the outputs the wallet watches, anchored at the tip of the view the listing
was taken on. `WTC-6`: "a node-owned **watch-only descriptor wallet** read with one unspent listing
and a since-block reconciliation, discarded unless the tip captured before the listing is still the
tip when the reconciliation ends, and re-proving after the read that a completion marker's anchor
is still active (`WTC-8`)"; the tip bracket and the re-proof are `walletServed`'s. -/
@[req "WTC-6"]
def walletRead (L : Ledger) (v : View) (w : Wallet) : Cache :=
  { outputs := watched L v w.birthday, anchor := v.tip }

/-- The delta walk, from a cached anchor over the blocks a scan read above it: `WTC-12`'s three
checks against the cached anchor's hash as the expected parent (`Watchtower.linked`) — the first
block links to it, each later block to the previous, the last is active after the loop — the blocks
are the consecutive heights from the anchor's height plus one, and there are at most `deltaWindow`
of them; any failure yields `none` — `WTC-6`: "A walk that covers less is discarded whole, as is
one that fails any proof (`WTC-12`), and the refresh falls through to the cold scan". The result is
the old outputs plus those of the walked blocks, each looked up in the ledger by its height and
hash, anchored at the last block; a walk of no block is the cache as it was, which every check
passes vacuously, so whether such a walk is complete is `coversRange`'s to say and not this
function's. What a walked block spent is not subtracted here: `WTC-10`'s prevout re-validation is
what drops a spent output, and it is opaque in this module. -/
@[req "WTC-6"]
def deltaWalk (L : Ledger) (c : Cache) (s : Scan) : Option Cache :=
  match s.blocks.getLast? with
  | none => some c
  | some last =>
    if linked (some c.anchor.hash) s && rangeFrom (c.anchor.height + 1) s.blocks &&
        s.blocks.length ≤ deltaWindow then
      some { outputs := c.outputs ++ s.blocks.flatMap fun b => L.vaultOutputs b.height b.hash,
             anchor := last.anchor }
    else none

/-- The cold scan: the outputs live at the view's tip, anchored there. `WTC-6`: "a cold **full
UTXO-set scan** for the vault script, published to the cache BEFORE the slow wallet build that may
follow it on a background thread" — `refresh` publishes it, and `repair`, the build, does nothing
outside the attempt that refresh starts (`cold_scan_starts_attempt`). `WTC-7`: the scan
anchor "A" is this view's tip. -/
@[req "WTC-6"]
def coldScan (L : Ledger) (v : View) : Cache := { outputs := live L v, anchor := v.tip }

/-- The node's state the sources are served from: the wallet, the repair latch (`WTC-9`), whether a
cold scan has replaced the cache since the latch set, the cold scan the attempt in progress started
from — `none` when no attempt is in progress — and the cache. There is one cache: `WTC-5`'s
fire-time read takes it, every source replaces it (`refresh`) and every delta walk starts from it.
`WTC-6`: "A walk that completes becomes the cache even where it ends below the tip, and any later
delta walk starts from that cache". There is room for one attempt and no more — `WTC-9`: "At most
one attempt, whether a repair or a first build, is in progress at a time." An attempt is started by
a refresh that serves the cold scan with none in progress, under the latch or for a wallet holding
no marker, and that refresh records the scan it published (`refresh`); it is ended by the
re-import, whatever that yields (`repair`), or by a failure before the re-import (`endAsFailure`).
The scan is kept apart from the cache because delta walks advance the cache while the attempt runs,
and the re-import is of the scan, not of what the cache has become (`repair`). `scanned` is read
only while the latch is set: `State.observe` clears it where it sets the latch and `refresh` sets
it where it serves the cold scan, which makes it `WTC-9`'s "From the latch setting until a cold
scan has replaced the cache", as a state and not as a count of refreshes. -/
structure State where
  wallet : Wallet
  latched : Bool
  scanned : Bool
  repairScan : Option Cache
  cache : Option Cache
  deriving DecidableEq, Repr

/-- Whether an attempt, a repair or a first build, is in progress: the state holds the cold scan
one started from. -/
@[req "WTC-9"]
def State.attempting (st : State) : Bool := st.repairScan.isSome

/-- The delta base. Under `neededScan`, `WTC-9` as it stands, it is the cache except where the
latch is set, no cold scan has replaced the cache since it set, and no attempt is in progress,
where there is none and the refresh cold-scans (`latched_unscanned_serves_cold`). `WTC-9`: "From
the latch setting until a cold scan has replaced the cache, every refresh with no attempt in
progress starts a repair attempt from a cold scan, whatever cache it holds". Under `everyRefresh`
there is none wherever the latch is set and no attempt is in progress, a scan published since or
not, and under `noFirstScan` it is the cache whatever the latch. -/
@[req "WTC-9"]
def deltaBase (rt : RetryTrigger) (st : State) : Option Cache :=
  match rt with
  | .neededScan => if st.latched && !st.scanned && !st.attempting then none else st.cache
  | .everyRefresh => if st.latched && !st.attempting then none else st.cache
  | .noFirstScan => st.cache

/-- A delta base is the cache: the guard decides only whether there is one. -/
@[req "WTC-9"]
theorem deltaBase_cache (rt : RetryTrigger) (st : State) (c : Cache)
    (h : deltaBase rt st = some c) : st.cache = some c := by
  cases rt with
  | neededScan =>
    simp only [deltaBase] at h
    split at h
    · cases h
    · exact h
  | everyRefresh =>
    simp only [deltaBase] at h
    split at h
    · cases h
    · exact h
  | noFirstScan => exact h

/-- The wallet is the source when it is usable, the latch is not set, the tip captured before the
listing is still the tip when the reconciliation ends, and a completion marker's anchor is still
active on the view read after — `WTC-6`: "discarded unless the tip captured before the listing is
still the tip when the reconciliation ends, and re-proving after the read that a completion
marker's anchor is still active (`WTC-8`)" — so that, `WTC-9`: "a reorg deep enough to unseat the
last of them discards the result instead of installing an understated denominator; a shallower
reorg landing during a read is caught by the read's own tip bracket (`WTC-6`)". -/
@[req "WTC-6"]
def walletServed (st : State) (v after : View) : Bool :=
  !st.latched && usable v st.wallet && decide (after.tip = v.tip) &&
    someMarkerActive after st.wallet

/-- The height a delta walk from a cache must reach. `WTC-6`: "the lesser of the tip captured when
the walk starts and 32 blocks above that anchor". The view here is the walk's own, `serve`'s
`walk`: the one captured when the walk starts, which is after the wallet read has been given up, so
a block that landed during that read is inside the range. It is not `serve`'s `v`, which the
refresh captures before the wallet read; not `after`, which the wallet read's bracket reads when
the reconciliation ends; and not the scan's own `Scan.after`, which is read when the loop ends.
The reference implementation's `vault-node`, `chain::advance_confirmed_scan` reads the tip height
as the walk's first step. -/
@[req "WTC-6"]
def walkEnd (c : Cache) (w : View) : Height := min w.tip.height (c.anchor.height + deltaWindow)

/-- Whether a walk covers its range, on the view captured when the walk starts. `WTC-6`: "The delta
walk covers every height above the cache's anchor through the lesser of the tip captured when the
walk starts and 32 blocks above that anchor." `deltaWalk` holds the blocks to consecutive heights
from one above the anchor, so a walk of some block covers the range iff its last block is at
`walkEnd`, no lower and no higher. A walk of no block covers it only where the anchor already is
that tip: every `WTC-12` check holds vacuously on no block, so nothing but this refuses an empty
walk below the tip. -/
@[req "WTC-6"]
def coversRange (c : Cache) (w : View) (s : Scan) : Bool :=
  match s.blocks.getLast? with
  | some last => last.height == walkEnd c w
  | none => decide (c.anchor = w.tip)

/-- What completes a walk, under the walk range: its whole range under `whole`, nothing more than
its proofs under `asRead`. -/
@[req "WTC-6"]
def rangeHeld (wr : WalkRange) (c : Cache) (w : View) (s : Scan) : Bool :=
  match wr with
  | .whole => coversRange c w s
  | .asRead => true

/-- Which chain a walk's result must be on, under the chain tie: under `untied`, the rule as it
stands, anywhere `deltaWalk`'s own checks leave it, and under `tied` its anchor is active on the
view captured when the walk starts as well. -/
@[req "WTC-6"]
def endHeld (ct : ChainTie) (w : View) (c' : Cache) : Bool :=
  match ct with
  | .tied => c'.anchor.active w
  | .untied => true

/-- The delta walk from the delta base, on the view captured when the walk starts, when the base's
anchor is still active on it — `WTC-6`: "from a cached anchor whose block is still active". Under
the rules as they stand a walk is committed when it passes `deltaWalk`'s proofs and covers its
whole range (`coversRange`); the proofs hold its last block to the chain as it is after the loop,
and the range is measured by the tip captured when the walk starts, so a walk read on a branch the
chain moved to in between is committed where it covers that range by height. Anything else is
refused whole and the source falls through to the cold scan — `WTC-6`: "A walk that covers less is
discarded whole, as is one that fails any proof (`WTC-12`), and the refresh falls through to the
cold scan". Under `partialWalk` a walk that passes is committed even where its range ends below the
tip, which is the cache more than `deltaWindow` blocks behind — `WTC-6`: "A walk that completes
becomes the cache even where it ends below the tip" — and the cache it leaves is refused at fire
time (`WTC-5`), not here. Under `tipOnly`, the reading `ADR-0024` withdraws, a walk that does not
reach the tip is thrown away and the source falls through to the cold scan. -/
@[req "WTC-6"]
def deltaFrom (g : Rules) (L : Ledger) (st : State) (w : View) (s : Scan) : Option Cache :=
  match deltaBase g.retry st with
  | some c =>
    if c.anchor.active w then
      match deltaWalk L c s with
      | some c' =>
        if rangeHeld g.range c w s && endHeld g.chain w c' then
          match g.commit with
          | .partialWalk => some c'
          | .tipOnly => if c'.anchor = w.tip then some c' else none
        else none
      | none => none
    else none
  | none => none

/-- Serving the cache, in `WTC-6`'s order: "The cache MUST be served, in order of preference, by"
the wallet, the delta walk, the cold scan. Three views, in the order a refresh reads them: `v`,
captured before the wallet's listing; `after`, read when the wallet's reconciliation ends, which
the read's bracket compares with `v`; and `walk`, captured when the delta walk starts, which is
after a wallet read was discarded or passed over. The walk reads `walk` alone — its base's anchor
and its range are tested there — so a block that lands during the wallet read discards that read by
the bracket and is walked, not cold-scanned
(`Exhibits.VaultUnspentCache.block_during_wallet_read_is_walked`). The wallet read and the cold
scan are taken on `v`: the model gives the fallback scan no later view of its own, and a cache it
leaves behind a tip that moved meanwhile is refused at fire time (`WTC-5`). `WTC-6`: "While the
repair latch is set or a build or repair attempt is in progress, `WTC-9` restricts this order" —
the latch takes the wallet out of the order (`latched_never_wallet`) and, until a cold scan has
replaced the cache since it set, with no attempt in progress, the delta walk too
(`latched_unscanned_serves_cold`). -/
@[req "WTC-6"]
def serve (g : Rules) (L : Ledger) (st : State) (v after walk : View) (s : Scan) :
    Source × Cache :=
  if walletServed st v after then (.wallet, walletRead L v st.wallet)
  else
    match deltaFrom g L st walk s with
    | some c' => (.deltaWalk, c')
    | none => (.coldScan, coldScan L v)

/-- One refresh: what `serve` yields replaces the cache, whichever source it came from, and a cold
scan served is recorded as having replaced it (`State.scanned`). An attempt already in progress
stays the one in progress, latch set or clear — `WTC-9`: "At most one attempt, whether a repair or
a first build, is in progress at a time." Where none is, one starts only where this refresh served
the cold scan, and only under the latch or for a wallet holding no marker, and it records that
scan (`cold_scan_starts_attempt`, `attempt_starts_only_at_cold_scan`) — `WTC-9`: "the next attempt
starts only from a cold scan `WTC-6` itself reaches with none in progress, and starts no scan of
its own", and of the wallet holding no marker, `WTC-9`: "its first build, and any retry after a
failed one, starts the same way". Whether the cold scan is served is `serve`'s to say: under the
latch, with no scan published since it set and no attempt in progress, it always is
(`latched_unscanned_serves_cold`), and otherwise only as `WTC-6`'s fallback. `WTC-9`: "thereafter,
while the latch holds, the cache is advanced by delta walks or their cold-scan fallback (`WTC-6`),
and a wallet read never replaces it". The latch itself is `observe`'s; the state a refresh is
given carries what it found. -/
@[req "WTC-9"]
def refresh (g : Rules) (L : Ledger) (st : State) (v after walk : View) (s : Scan) : State :=
  { st with
    cache := some (serve g L st v after walk s).2,
    scanned := st.scanned || decide ((serve g L st v after walk s).1 = .coldScan),
    repairScan :=
      match st.repairScan with
      | some a => some a
      | none =>
        if (serve g L st v after walk s).1 = .coldScan ∧
            (st.latched || st.wallet.markers.isEmpty) = true then
          some (serve g L st v after walk s).2
        else none }

/-- The wallet is served only when usable, unlatched, read between one tip and the same tip, and
re-proved active after the read, and then the cache is the wallet read. -/
@[req "WTC-6"]
theorem served_wallet_only_when (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (h : (serve g L st v after walk s).1 = .wallet) :
    st.latched = false ∧ usable v st.wallet = true ∧ after.tip = v.tip ∧
      someMarkerActive after st.wallet = true ∧
      (serve g L st v after walk s).2 = walletRead L v st.wallet := by
  by_cases hw : walletServed st v after = true
  · have hw' := hw
    simp only [walletServed, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw'
    exact ⟨hw'.1.1.1, hw'.1.1.2, hw'.1.2, hw'.2, by simp [serve, hw]⟩
  · exfalso
    simp only [serve, hw, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> simp at h

/-- A walk that succeeds ends anchored at the last walked block, or, walking nothing, where it
began. -/
@[req "WTC-6"]
theorem deltaWalk_anchor (L : Ledger) (c c' : Cache) (s : Scan) (h : deltaWalk L c s = some c') :
    (s.blocks = [] ∧ c' = c) ∨ ∃ last, s.blocks.getLast? = some last ∧ c'.anchor = last.anchor := by
  unfold deltaWalk at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨List.getLast?_eq_none_iff.mp hl, h.symm⟩
  · rename_i last hl
    split at h
    · simp only [Option.some.injEq] at h
      exact Or.inr ⟨last, hl, by rw [← h]⟩
    · cases h

/-- A walk of no block covers its range iff the cache's anchor already is the tip captured when the
walk starts. `WTC-6`: "The delta walk covers every height above the cache's anchor through the
lesser of the tip captured when the walk starts and 32 blocks above that anchor." -/
@[req "WTC-6"]
theorem coversRange_empty (c : Cache) (w : View) (s : Scan) (h : s.blocks = []) :
    coversRange c w s = true ↔ c.anchor = w.tip := by
  simp [coversRange, h]

/-- A walk that succeeds and covers its range leaves a cache anchored at or below the tip captured
when it started: at `walkEnd`, or, walking nothing, at the tip itself. -/
@[req "WTC-6"]
theorem covered_walk_at_or_below_tip (L : Ledger) (c c' : Cache) (w : View) (s : Scan)
    (hw : deltaWalk L c s = some c') (hc : coversRange c w s = true) :
    c'.anchor.height ≤ w.tip.height := by
  rcases deltaWalk_anchor L c c' s hw with ⟨hnil, rfl⟩ | ⟨last, hl, ha⟩
  · rw [(coversRange_empty c' w s hnil).mp hc]
    exact Nat.le_refl _
  · simp only [coversRange, hl, beq_iff_eq] at hc
    rw [ha, Block.anchor]
    simp only [walkEnd, Height] at hc ⊢
    omega

/-- A delta walk served came from a delta base whose anchor is still active on the view captured
when the walk started and succeeded from it. Under `whole` it covered its whole range and left a
cache at or below that view's tip, which the withdrawn `asRead` does not promise. Under `tied`, the
chain tie withdrawn, that cache's anchor is active on that view as well, which the rule as it
stands does not ask. -/
@[req "WTC-6"]
theorem deltaFrom_some (g : Rules) (L : Ledger) (st : State) (w : View) (s : Scan)
    (c' : Cache) (h : deltaFrom g L st w s = some c') :
    ∃ c, deltaBase g.retry st = some c ∧ c.anchor.active w = true ∧ deltaWalk L c s = some c' ∧
      (g.range = .whole → coversRange c w s = true ∧ c'.anchor.height ≤ w.tip.height) ∧
      (g.chain = .tied → c'.anchor.active w = true) := by
  unfold deltaFrom at h
  split at h
  · rename_i c hc
    split at h
    · rename_i ha
      split at h
      · rename_i c'' hd
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true] at hb
          have hrange : g.range = .whole →
              coversRange c w s = true ∧ c''.anchor.height ≤ w.tip.height := by
            intro hr
            have hcov : coversRange c w s = true := by simpa [rangeHeld, hr] using hb.1
            exact ⟨hcov, covered_walk_at_or_below_tip L c c'' w s hd hcov⟩
          have htied : g.chain = .tied → c''.anchor.active w = true := by
            intro ht
            simpa [endHeld, ht] using hb.2
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨c, hc, ha, hd, hrange, htied⟩
          · split at h
            · simp only [Option.some.injEq] at h
              subst h
              exact ⟨c, hc, ha, hd, hrange, htied⟩
            · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Under `partialWalk`, whatever the other three: a walk that succeeds from a still-active base,
covers its whole range, and ends on a block active on the view captured when it started is
committed, wherever that range ends. `WTC-6`: "A walk that completes becomes the cache even where
it ends below the tip". The last hypothesis is what `tied` asks; under `untied` the walk is
committed without it (`delta_commits_walk_on_any_branch`). -/
@[req "WTC-6"]
theorem delta_commits_completed_walk (wr : WalkRange) (rt : RetryTrigger) (ct : ChainTie)
    (L : Ledger) (st : State) (w : View) (s : Scan) (c c' : Cache)
    (hb : deltaBase rt st = some c) (ha : c.anchor.active w = true)
    (hw : deltaWalk L c s = some c') (hc : coversRange c w s = true)
    (ht : c'.anchor.active w = true) :
    deltaFrom ⟨.partialWalk, wr, rt, ct⟩ L st w s = some c' := by
  cases wr <;> cases ct <;> simp [deltaFrom, rangeHeld, endHeld, hb, ha, hw, hc, ht]

/-- Under `partialWalk` and `untied`, whatever the other two: a walk that succeeds from a
still-active base and covers its whole range is committed, whichever branch its last block is on.
`deltaWalk` has already held that block to the chain as it is after the loop — `WTC-12`: "after the
loop the hash at the last height still equals the last scanned hash" — and no test is made against
the view captured when the walk starts. -/
@[req "WTC-6"]
theorem delta_commits_walk_on_any_branch (wr : WalkRange) (rt : RetryTrigger)
    (L : Ledger) (st : State) (w : View) (s : Scan) (c c' : Cache)
    (hb : deltaBase rt st = some c) (ha : c.anchor.active w = true)
    (hw : deltaWalk L c s = some c') (hc : coversRange c w s = true) :
    deltaFrom ⟨.partialWalk, wr, rt, .untied⟩ L st w s = some c' := by
  cases wr <;> simp [deltaFrom, rangeHeld, endHeld, hb, ha, hw, hc]

/-- Under `tipOnly`, whatever the other three, only a walk reaching the tip is committed. -/
@[req "WTC-6"]
theorem delta_tipOnly_refuses_below_tip (wr : WalkRange) (rt : RetryTrigger) (ct : ChainTie)
    (L : Ledger) (st : State) (w : View) (s : Scan) (c c' : Cache)
    (hb : deltaBase rt st = some c) (hw : deltaWalk L c s = some c') (ht : c'.anchor ≠ w.tip) :
    deltaFrom ⟨.tipOnly, wr, rt, ct⟩ L st w s = none := by
  simp [deltaFrom, hb, hw, ht]

/-- Under `whole`, whatever the other three: a walk that covers less than its range from the cache
is discarded, however well it proves. `WTC-6`: "A walk that covers less is discarded whole". The
hypothesis is over the cache because a delta base is the cache or nothing (`deltaBase_cache`). -/
@[req "WTC-6"]
theorem delta_refuses_uncovered_walk (dc : DeltaCommit) (rt : RetryTrigger) (ct : ChainTie)
    (L : Ledger) (st : State) (w : View) (s : Scan)
    (hc : ∀ c, st.cache = some c → coversRange c w s = false) :
    deltaFrom ⟨dc, .whole, rt, ct⟩ L st w s = none := by
  unfold deltaFrom
  split
  · rename_i c hb
    have hcov := hc c (deltaBase_cache rt st c hb)
    simp only [rangeHeld, hcov, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · split <;> rfl
    · rfl
  · rfl

/-- Under `tied`, the chain tie withdrawn, whatever the other three: a walk from the cache that
ends on a block not active on the view captured when it started is discarded, though it links from
the anchor and covers its range. -/
@[req "WTC-6"]
theorem delta_refuses_off_branch_walk (dc : DeltaCommit) (wr : WalkRange) (rt : RetryTrigger)
    (L : Ledger) (st : State) (w : View) (s : Scan)
    (ht : ∀ c c', st.cache = some c → deltaWalk L c s = some c' → c'.anchor.active w = false) :
    deltaFrom ⟨dc, wr, rt, .tied⟩ L st w s = none := by
  unfold deltaFrom
  split
  · rename_i c hb
    split
    · split
      · rename_i c' hd
        have hoff := ht c c' (deltaBase_cache rt st c hb) hd
        simp [endHeld, hoff]
      · rfl
    · rfl
  · rfl

/-- The delta walk is served only from a delta base whose anchor is still active on the view
captured when the walk started, and then the walk from it succeeded with the served cache. Under
`whole` it covered its whole range and the served cache is at or below that view's tip: under the
rules as they stand a reader of this model cannot conclude that a served cache may be anchored
above the tip its walk was measured against. Under `tied`, the chain tie withdrawn, the served
cache's anchor is active on that view too; under the rule as it stands it may be on another branch
than that view's, the one the chain had moved to when the walk's loop ended. -/
@[req "WTC-6"]
theorem served_delta_only_when (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (h : (serve g L st v after walk s).1 = .deltaWalk) :
    ∃ c, deltaBase g.retry st = some c ∧ c.anchor.active walk = true ∧
      deltaWalk L c s = some (serve g L st v after walk s).2 ∧
      (g.range = .whole → coversRange c walk s = true ∧
        (serve g L st v after walk s).2.anchor.height ≤ walk.tip.height) ∧
      (g.chain = .tied → (serve g L st v after walk s).2.anchor.active walk = true) := by
  by_cases hw : walletServed st v after = true
  · simp [serve, hw] at h
  · simp only [serve, hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
    match hd : deltaFrom g L st walk s with
    | some c' => exact deltaFrom_some g L st walk s c' hd
    | none => simp [hd] at h

/-- Otherwise the cold scan, anchored at the tip of the view the refresh captured first. -/
@[req "WTC-6"]
theorem served_cold_otherwise (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (hw : (serve g L st v after walk s).1 ≠ .wallet)
    (hd : (serve g L st v after walk s).1 ≠ .deltaWalk) :
    serve g L st v after walk s = (.coldScan, coldScan L v) := by
  by_cases hws : walletServed st v after = true
  · exact absurd (by simp [serve, hws]) hw
  · simp only [serve, hws, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    match hdf : deltaFrom g L st walk s with
    | some c' => rw [hdf] at hd; simp at hd
    | none => rfl

/-- Under `whole`, where the wallet is not the source, a walk that covers less than its range falls
through to the cold scan. `WTC-6`: "A walk that covers less is discarded whole, as is one that
fails any proof (`WTC-12`), and the refresh falls through to the cold scan". -/
@[req "WTC-6"]
theorem uncovered_walk_serves_cold (dc : DeltaCommit) (rt : RetryTrigger) (ct : ChainTie)
    (L : Ledger) (st : State) (v after walk : View) (s : Scan)
    (hw : walletServed st v after = false)
    (hc : ∀ c, st.cache = some c → coversRange c walk s = false) :
    serve ⟨dc, .whole, rt, ct⟩ L st v after walk s = (.coldScan, coldScan L v) := by
  simp [serve, hw, delta_refuses_uncovered_walk dc rt ct L st walk s hc]

/-- Under `tied`, the chain tie withdrawn, where the wallet is not the source, a walk that ends on
a block not active on the view captured when it started falls through to the cold scan. -/
@[req "WTC-6"]
theorem off_branch_walk_serves_cold (dc : DeltaCommit) (wr : WalkRange) (rt : RetryTrigger)
    (L : Ledger) (st : State) (v after walk : View) (s : Scan)
    (hw : walletServed st v after = false)
    (ht : ∀ c c', st.cache = some c → deltaWalk L c s = some c' → c'.anchor.active walk = false) :
    serve ⟨dc, wr, rt, .tied⟩ L st v after walk s = (.coldScan, coldScan L v) := by
  simp [serve, hw, delta_refuses_off_branch_walk dc wr rt L st walk s ht]

/-- What the fire-time read makes of a served cache: it is read iff it is anchored at the tip of
the view the read is taken on. `WTC-6`: "a cache whose anchor is not the current tip is refused at
fire time (`WTC-5`)" — the amended walk may commit below the tip, and `WTC-5` is where that cache
is refused, not `WTC-6`. Over every guard value, ledger, state, view read at fire time, the three
views of the refresh and scan, with no hypothesis. -/
@[req "WTC-5"]
theorem served_read_iff_at_tip (g : Rules) (L : Ledger) (st : State) (t v after walk : View)
    (s : Scan) :
    fireTimeRead t (serve g L st v after walk s).2 =
        some (serve g L st v after walk s).2.outputs ↔
      (serve g L st v after walk s).2.anchor = t.tip := by
  rw [read_some_iff]
  simp

/-- The wallet read and the cold scan are anchored at the tip of the view the refresh captured
first, by construction; only the delta walk is anchored by what it read. -/
@[req "WTC-6"]
theorem served_at_tip_unless_delta (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (h : (serve g L st v after walk s).1 ≠ .deltaWalk) :
    (serve g L st v after walk s).2.anchor = v.tip := by
  by_cases hw : walletServed st v after = true
  · simp [serve, hw, walletRead]
  · simp only [serve, hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
    match hd : deltaFrom g L st walk s with
    | some c' => rw [hd] at h; simp at h
    | none => rfl

/-- `WTC-5`'s completeness for the cold scan: its cache holds every output the chain it scanned
created at or below its tip and has not spent. -/
@[req "WTC-5"]
theorem coldScan_complete (L : Ledger) (v : View) (h : Height) (hash : Hash) (x : Coin)
    (hh : h ≤ v.tip.height) (ha : v.activeAt h = some hash) (hx : x ∈ L.vaultOutputs h hash)
    (hs : x ∉ spentUpTo L v v.tip.height) : x ∈ (coldScan L v).outputs := by
  simp only [coldScan, live, liveFrom, List.mem_filter, confirmedFrom,
    decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨?_, by simpa using hs⟩
  refine mem_outputsIn L v 0 h _ x ?_ (Nat.zero_le _) (by simp only [Height] at *; omega)
  simp [confirmedAt, ha, hx]

/-- `WTC-5`'s completeness for the delta walk, over the walked blocks: a walk that succeeds keeps
every old output and holds every output the ledger confirms in a walked block. -/
@[req "WTC-5"]
theorem deltaWalk_complete (L : Ledger) (c c' : Cache) (s : Scan)
    (h : deltaWalk L c s = some c') :
    (∀ x ∈ c.outputs, x ∈ c'.outputs) ∧
      ∀ b ∈ s.blocks, ∀ x ∈ L.vaultOutputs b.height b.hash, x ∈ c'.outputs := by
  unfold deltaWalk at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun x hx => hx, fun b hb => ?_⟩
    rw [List.getLast?_eq_none_iff] at hl
    simp [hl] at hb
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => by simp [hx], fun b hb x hx => ?_⟩
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨b, hb, hx⟩
    · cases h

/-- A walk longer than `deltaWindow` blocks, or one whose first block does not link to the cached
anchor, is refused: the source falls through. -/
@[req "WTC-6"]
theorem deltaWalk_refused (L : Ledger) (c : Cache) (s : Scan)
    (h : deltaWindow < s.blocks.length ∨ firstLinksTo c.anchor.hash s.blocks = false) :
    deltaWalk L c s = none := by
  unfold deltaWalk
  split
  · rename_i hl
    rw [List.getLast?_eq_none_iff] at hl
    rcases h with h | h
    · simp [hl] at h
    · simp [hl, firstLinksTo] at h
  · rcases h with h | h
    · have : ¬ s.blocks.length ≤ deltaWindow := by omega
      simp [this]
    · simp [linked, h]

/-! ## The repair latch and the attempt (`WTC-9`) -/

/-- The latch after observing a view: set if it was set, or, under `scoped`, if the wallet holds a
completion marker and none it holds has an anchor on the active chain. `WTC-9`: "If the wallet
holds a completion marker and none it holds has an anchor on the active chain the node MUST latch a
repair, keep the wallet out of use until a cold scan and re-import have rebuilt it, and re-prove
after every read that a marker's anchor is still active, so a reorg deep enough to unseat the last
of them discards the result instead of installing an understated denominator". Under `vacuous`, the
reading withdrawn, holding a marker is not asked. Sticky: nothing here clears it. -/
@[req "WTC-9"]
def observe (ls : LatchScope) (v : View) (w : Wallet) (latched : Bool) : Bool :=
  latched ||
    match ls with
    | .scoped => !w.markers.isEmpty && !someMarkerActive v w
    | .vacuous => !someMarkerActive v w

/-- The observation as the state carries it. Where it sets a latch that was clear, no cold scan has
replaced the cache since, so `scanned` is cleared: `WTC-9`: "From the latch setting until a cold
scan has replaced the cache". Under a latch already set it changes nothing. -/
@[req "WTC-9"]
def State.observe (ls : LatchScope) (v : View) (st : State) : State :=
  { st with latched := VaultUnspent.observe ls v st.wallet st.latched,
            scanned := st.latched && st.scanned }

/-- Set stays set through every observation, under either scope. -/
@[req "WTC-9"]
theorem latch_sticky (ls : LatchScope) (v : View) (w : Wallet) : observe ls v w true = true := rfl

/-- Under `scoped` the latch after is the latch before, or a marker held and none active,
exactly. -/
@[req "WTC-9"]
theorem latch_iff (v : View) (w : Wallet) (l : Bool) :
    observe .scoped v w l = true ↔
      l = true ∨ (w.markers ≠ [] ∧ someMarkerActive v w = false) := by
  simp [observe]

/-- A view on which a held marker's anchor is active does not latch, under either scope, so a reorg
that leaves one standing sets nothing: `WTC-9`'s "a shallower reorg landing during a read is caught
by the read's own tip bracket (`WTC-6`)" is the rule that the latch is not what catches it. -/
@[req "WTC-9"]
theorem marker_active_never_latches (ls : LatchScope) (v : View) (w : Wallet) (m : Marker)
    (hm : m ∈ w.markers) (ha : anchorStillActive v m.anchor = true) :
    observe ls v w false = false := by
  have hs : someMarkerActive v w = true := by
    unfold someMarkerActive
    exact List.any_eq_true.mpr ⟨m, hm, ha⟩
  cases ls <;> simp [observe, hs]

/-- (iii) An unbuilt wallet never latches. Under `scoped`, a wallet holding no marker leaves the
latch as it was on every view: observing sets nothing. That is the wallet before its first build
and the one a first build that failed leaves. `WTC-9`: "A wallet holding no completion marker is
not latched, `WTC-8` already keeping it out of use" — `no_active_marker_never_usable` is the
`WTC-8` half. The reference implementation's `vault-node`,
`chain::refresh_vault_unspent_cache_mode` reads it the same way: it latches only a wallet that
holds an anchor. -/
@[req "WTC-9"]
theorem unbuilt_wallet_never_latches (v : View) (w : Wallet) (l : Bool) (h : w.markers = []) :
    observe .scoped v w l = l := by
  simp [observe, h]

/-- Under `vacuous`, the reading withdrawn, a wallet holding no marker is latched on every view,
whatever the latch was: "none it holds has an anchor on the active chain" holds of it with nothing
to check. -/
@[req "WTC-9"]
theorem unbuilt_wallet_latches_under_vacuous (v : View) (w : Wallet) (l : Bool)
    (h : w.markers = []) : observe .vacuous v w l = true := by
  simp [observe, someMarkerActive, h]

/-- A latch that an observation sets finds no cold scan published since: whatever `scanned` held
while the latch was clear, the state leaves the observation with it cleared, so under `neededScan`
the next refresh with no attempt in progress cold-scans (`latched_unscanned_serves_cold`). -/
@[req "WTC-9"]
theorem newly_latched_awaits_scan (ls : LatchScope) (v : View) (st : State)
    (h : st.latched = false) : (st.observe ls v).scanned = false := by
  simp [State.observe, h]

/-- While the latch is set the wallet is not the source served, over every view, wallet and state.
`WTC-9`: "keep the wallet out of use until a cold scan and re-import have rebuilt it". -/
@[req "WTC-9"]
theorem latched_never_wallet (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (h : st.latched = true) : (serve g L st v after walk s).1 ≠ .wallet := by
  intro hw
  have := (served_wallet_only_when g L st v after walk s hw).1
  rw [h] at this
  cases this

/-- (i) Under `neededScan`, whatever the other three: a refresh that finds the latch set, no cold
scan published since it set and no attempt in progress serves the cold scan, whatever the cache
holds and whatever the walk offered, over every ledger, state, view and scan. `WTC-9`: "From the
latch setting until a cold scan has replaced the cache, every refresh with no attempt in progress
starts a repair attempt from a cold scan, whatever cache it holds". The hypothesis is the state,
not the count of refreshes since the latch set: a refresh after a first scan that failed to
publish finds the same state and cold-scans again. -/
@[req "WTC-9"]
theorem latched_unscanned_serves_cold (dc : DeltaCommit) (wr : WalkRange) (ct : ChainTie)
    (L : Ledger) (st : State) (v after walk : View) (s : Scan) (hl : st.latched = true)
    (hs : st.scanned = false) (hn : st.attempting = false) :
    serve ⟨dc, wr, .neededScan, ct⟩ L st v after walk s = (.coldScan, coldScan L v) := by
  simp [serve, walletServed, deltaFrom, deltaBase, hl, hs, hn]

/-- Under `everyRefresh`, whatever the other three: a refresh that finds the latch set and no
attempt in progress serves the cold scan, a scan published since the latch set or not. That is the
rule of 2026-10-01 the retry trigger as it stands withdraws, and what the reference
implementation's `vault-node`, `chain::refresh_vault_unspent_cache_mode` does: it refuses the slot
as a delta base in that state on every pass. -/
@[req "WTC-9"]
theorem latched_no_attempt_serves_cold (dc : DeltaCommit) (wr : WalkRange) (ct : ChainTie)
    (L : Ledger) (st : State) (v after walk : View) (s : Scan) (hl : st.latched = true)
    (hn : st.attempting = false) :
    serve ⟨dc, wr, .everyRefresh, ct⟩ L st v after walk s = (.coldScan, coldScan L v) := by
  simp [serve, walletServed, deltaFrom, deltaBase, hl, hn]

/-- A cold scan served with no attempt in progress starts one, under the latch or for a wallet
holding no marker, whatever the rules: afterwards the attempt in progress is the one that began at
that cold scan, which is the cache, and a cold scan has replaced the cache. This is the repair's
first scan, the retry at a fallback scan and the first build alike. `WTC-9`: "the next attempt
starts only from a cold scan `WTC-6` itself reaches with none in progress", and `WTC-9`: "its
first build, and any retry after a failed one, starts the same way, from a cold scan `WTC-6`
reaches with no attempt in progress". -/
@[req "WTC-9"]
theorem cold_scan_starts_attempt (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (hc : (serve g L st v after walk s).1 = .coldScan) (hn : st.attempting = false)
    (hw : st.latched = true ∨ st.wallet.markers = []) :
    (refresh g L st v after walk s).repairScan = some (coldScan L v) ∧
      (refresh g L st v after walk s).cache = some (coldScan L v) ∧
      (refresh g L st v after walk s).scanned = true ∧
      (refresh g L st v after walk s).latched = st.latched := by
  have hn' : st.repairScan = none := by
    cases hr : st.repairScan with
    | none => rfl
    | some a => simp [State.attempting, hr] at hn
  have hsv := served_cold_otherwise g L st v after walk s (by rw [hc]; decide) (by rw [hc]; decide)
  have hw' : (st.latched || st.wallet.markers.isEmpty) = true := by
    rcases hw with h | h <;> simp [h]
  simp [refresh, hn', hsv, hw']

/-- And the refresh (i) describes starts the attempt: afterwards the attempt in progress is the one
that began at that cold scan, the latch is still set, the cache is that cold scan, and a cold scan
has replaced the cache since the latch set, so the refreshes that follow walk from it. -/
@[req "WTC-9"]
theorem latched_unscanned_starts_attempt (dc : DeltaCommit) (wr : WalkRange) (ct : ChainTie)
    (L : Ledger) (st : State) (v after walk : View) (s : Scan) (hl : st.latched = true)
    (hs : st.scanned = false) (hn : st.attempting = false) :
    (refresh ⟨dc, wr, .neededScan, ct⟩ L st v after walk s).repairScan = some (coldScan L v) ∧
      (refresh ⟨dc, wr, .neededScan, ct⟩ L st v after walk s).latched = true ∧
      (refresh ⟨dc, wr, .neededScan, ct⟩ L st v after walk s).scanned = true ∧
      (refresh ⟨dc, wr, .neededScan, ct⟩ L st v after walk s).cache = some (coldScan L v) := by
  have hsv := latched_unscanned_serves_cold dc wr ct L st v after walk s hl hs hn
  obtain ⟨h1, h2, h3, h4⟩ := cold_scan_starts_attempt ⟨dc, wr, .neededScan, ct⟩ L st v after walk
    s (by rw [hsv]) hn (Or.inl hl)
  exact ⟨h1, h4.trans hl, h3, h2⟩

/-- An attempt starts only at a cold scan, whatever the rules: a refresh that finds none in
progress and leaves one served the cold scan, the attempt began at that scan, and the state was
latched or its wallet held no marker. A refresh that serves the wallet or a delta walk starts
nothing. `WTC-9`: "the next attempt starts only from a cold scan `WTC-6` itself reaches with none
in progress, and starts no scan of its own". -/
@[req "WTC-9"]
theorem attempt_starts_only_at_cold_scan (g : Rules) (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (hn : st.attempting = false)
    (h : (refresh g L st v after walk s).attempting = true) :
    serve g L st v after walk s = (.coldScan, coldScan L v) ∧
      (refresh g L st v after walk s).repairScan = some (coldScan L v) ∧
      (st.latched = true ∨ st.wallet.markers = []) := by
  have hn' : st.repairScan = none := by
    cases hr : st.repairScan with
    | none => rfl
    | some a => simp [State.attempting, hr] at hn
  by_cases hc : (serve g L st v after walk s).1 = .coldScan
  · have hsv := served_cold_otherwise g L st v after walk s (by rw [hc]; decide)
      (by rw [hc]; decide)
    by_cases hw : (st.latched || st.wallet.markers.isEmpty) = true
    · have hw' : st.latched = true ∨ st.wallet.markers = [] := by
        simpa [List.isEmpty_iff] using hw
      exact ⟨hsv, (cold_scan_starts_attempt g L st v after walk s hc hn hw').1, hw'⟩
    · simp [refresh, State.attempting, hn', hsv, hw] at h
  · simp [refresh, State.attempting, hn', hc] at h

/-- (b) While the latch is set no wallet read replaces the cache. The cache a refresh leaves is the
cold scan or a walk from the delta base, and it is the same cache whatever wallet the state holds
and whatever the view after the listing shows: nothing the wallet read turns on reaches it.
`WTC-9`: "a wallet read never replaces it". `WTC-9`: "the cache does not depend on the wallet". A
`refresh` that served the wallet under the latch would fail both halves. -/
@[req "WTC-9"]
theorem latched_refresh_never_wallet_read (g : Rules) (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (hl : st.latched = true) :
    ((refresh g L st v after walk s).cache = some (coldScan L v) ∨
      ∃ c c', deltaBase g.retry st = some c ∧ deltaWalk L c s = some c' ∧
        (refresh g L st v after walk s).cache = some c') ∧
    ∀ (w' : Wallet) (after' : View),
      (refresh g L { st with wallet := w' } v after' walk s).cache =
        (refresh g L st v after walk s).cache := by
  have hnw := latched_never_wallet g L st v after walk s hl
  refine ⟨?_, fun w' after' => ?_⟩
  · by_cases hd : (serve g L st v after walk s).1 = .deltaWalk
    · obtain ⟨c, hb, -, hw, -, -⟩ := served_delta_only_when g L st v after walk s hd
      exact Or.inr ⟨c, _, hb, hw, rfl⟩
    · have hc := served_cold_otherwise g L st v after walk s hnw hd
      exact Or.inl (by simp [refresh, hc])
  · have h1 : walletServed st v after = false := by simp [walletServed, hl]
    have h2 : walletServed { st with wallet := w' } v after' = false := by simp [walletServed, hl]
    have h3 : deltaFrom g L { st with wallet := w' } walk s = deltaFrom g L st walk s := by
      cases hg : g.retry <;> simp [deltaFrom, deltaBase, State.attempting, hg]
    simp [refresh, serve, h1, h2, h3]

/-- While an attempt is in progress, latch set or not, the delta base is the cache, under every
retry trigger; under the latch a refresh then serves a delta walk from it or the cold scan, never
the wallet (`latched_never_wallet`). `WTC-9`: "the cache is advanced by delta walks or their
cold-scan fallback (`WTC-6`)". -/
@[req "WTC-9"]
theorem attempt_in_progress_walks_from_cache (rt : RetryTrigger) (st : State)
    (ha : st.attempting = true) : deltaBase rt st = st.cache := by
  cases rt <;> simp [deltaBase, ha]

/-- Once a cold scan has replaced the cache since the latch set, the delta base under `neededScan`
is the cache, an attempt in progress or not. `WTC-9`: "thereafter, while the latch holds, the cache
is advanced by delta walks or their cold-scan fallback (`WTC-6`)". -/
@[req "WTC-9"]
theorem scanned_base_is_cache (st : State) (hs : st.scanned = true) :
    deltaBase .neededScan st = st.cache := by
  simp [deltaBase, hs]

/-- With the latch clear the delta base is the cache under every retry trigger: a wallet holding no
marker is not latched under `scoped` (`unbuilt_wallet_never_latches`), so the refreshes of a node
whose first build has not succeeded take `WTC-6`'s order as it is, and start no scan of their
own. `WTC-9`: "A wallet holding no completion marker is not latched, `WTC-8` already keeping it out
of use". -/
@[req "WTC-9"]
theorem unlatched_base_is_cache (rt : RetryTrigger) (st : State) (hl : st.latched = false) :
    deltaBase rt st = st.cache := by
  cases rt <;> simp [deltaBase, hl]

/-- `WTC-9`: "At most one attempt, whether a repair or a first build, is in progress at a time." A
refresh that finds one in progress starts no other, latch set or clear: the attempt in progress
afterwards is the one that was, begun at the same cold scan, whatever this refresh served. -/
@[req "WTC-9"]
theorem attempt_in_progress_not_restarted (g : Rules) (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (a : Cache)
    (ha : st.repairScan = some a) : (refresh g L st v after walk s).repairScan = some a := by
  simp [refresh, ha]

/-- The one cache: after a refresh the cache is what was served, so the fire-time read takes what
the refresh left iff that is anchored at the tip it reads (`served_read_iff_at_tip`), and the next
delta walk starts from it — under `neededScan` a refresh never leaves the latch set with no scan
published since and no attempt in progress, under `everyRefresh` it never leaves the latch set with
no attempt in progress, and under `noFirstScan` the latch does not matter. `WTC-6`: "any later
delta walk starts from that cache". -/
@[req "WTC-6"]
theorem refresh_installs_served (g : Rules) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) :
    (refresh g L st v after walk s).cache = some (serve g L st v after walk s).2 ∧
      deltaBase g.retry (refresh g L st v after walk s) =
        some (serve g L st v after walk s).2 := by
  refine ⟨rfl, ?_⟩
  obtain ⟨dc, wr, rt, ct⟩ := g
  cases rt with
  | noFirstScan => rfl
  | neededScan =>
    cases hl : st.latched with
    | false => simp [refresh, deltaBase, hl]
    | true =>
      cases hs : st.scanned with
      | true => simp [refresh, deltaBase, hl, hs]
      | false =>
        cases hr : st.repairScan with
        | some a => simp [refresh, deltaBase, State.attempting, hl, hs, hr]
        | none =>
          have hn : st.attempting = false := by simp [State.attempting, hr]
          simp [refresh, deltaBase, State.attempting, hl, hs, hr,
            latched_unscanned_serves_cold dc wr ct L st v after walk s hl hs hn]
  | everyRefresh =>
    cases hl : st.latched with
    | false => simp [refresh, deltaBase, hl]
    | true =>
      cases hr : st.repairScan with
      | some a => simp [refresh, deltaBase, State.attempting, hl, hr]
      | none =>
        have hn : st.attempting = false := by simp [State.attempting, hr]
        simp [refresh, deltaBase, State.attempting, hl, hr,
          latched_no_attempt_serves_cold dc wr ct L st v after walk s hl hn]

/-- The rebuild: the import under the marker-anchor guard (`importMarker`) — under `settled`, the
walk above the scan view's settled block and the bracket at its two points — applied to the wallet;
`none` when the import yields no marker. -/
@[req "WTC-9"]
def rebuild (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (w : Wallet) : Option Wallet :=
  (importMarker ma br L scanView atDescriptors atMarker s).map (applyImport w)

/-- An attempt that stops without rebuilding the wallet: no attempt is in progress afterwards, and
the latch, the wallet and the cache are as they were. `WTC-9`: "a cold scan or wallet call that
fails or overruns its `WTC-4` timeout ends it as a failure". What failed and why is not modelled —
`WTC-4`'s timeouts are outside this module — only that the attempt stopped before its re-import:
this is the step an attempt takes when a wallet call ahead of the re-import fails. A cold scan
that fails is a refresh that published nothing, and the state it leaves is the one it found, with
no attempt in progress, which is this function's result too. -/
@[req "WTC-9"]
def endAsFailure (st : State) : State := { st with repairScan := none }

/-- The re-import that ends an attempt, a repair or a first build. It runs only inside an attempt,
which only a refresh starts and only from a cold scan that has already replaced the cache —
`WTC-9`: "the scan replacing the cache before the re-import begins (`WTC-6`)" — and outside one it
does nothing. `scanView` is the view that cold scan read at, `WTC-7`'s scan anchor its tip, and the
re-import is held to it: the scan read on `scanView` must be the one the attempt recorded when it
started (`State.repairScan`), anchor and outputs, and a re-import offered any other scan rebuilds
nothing. A view is a map from heights to hashes and the recorded scan pins its tip and what was
live there, not every block below, so the tie reaches the settled block only under the premise
that a block's hash fixes the chain beneath it (`Chain.Ancestry`,
`rebuild_reads_the_attempts_settled_block`). `atDescriptors` and `atMarker` stay free: they are the
two later reads `WTC-7`'s bracket makes, and what they show is the chain's to decide. The attempt
ends whatever happens — `WTC-9`: "An attempt ends however it stops, whether or not its re-import
began" — a rebuild that yields a wallet clears the latch, and anything else is `endAsFailure`,
`WTC-9`: "one that ends without rebuilding the wallet leaves any latch set"
(`failed_attempt_keeps_latch`). The cache is not touched here, and neither is `scanned`. -/
@[req "WTC-9"]
def repair (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) : State :=
  match st.repairScan with
  | none => st
  | some a =>
    if coldScan L scanView = a then
      match rebuild ma br L scanView atDescriptors atMarker s st.wallet with
      | some w' => { st with wallet := w', latched := false, repairScan := none }
      | none => endAsFailure st
    else endAsFailure st

/-- The latch is cleared only by a rebuild inside an attempt, from that attempt's own cold scan: a
repair that leaves it clear from set ran with an attempt in progress whose recorded scan is the
one read on `scanView`, its rebuild yielded a wallet, that wallet holds the import's marker newest,
and the attempt is over. `WTC-9`: "keep the wallet out of use until a cold scan and re-import have
rebuilt it". -/
@[req "WTC-9"]
theorem cleared_only_by_rebuild (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) (hl : st.latched = true)
    (hc : (repair ma br L scanView atDescriptors atMarker s st).latched = false) :
    st.repairScan = some (coldScan L scanView) ∧
    ∃ w' m, rebuild ma br L scanView atDescriptors atMarker s st.wallet = some w' ∧
      importMarker ma br L scanView atDescriptors atMarker s = some m ∧
      w'.markers.head? = some m ∧
      (repair ma br L scanView atDescriptors atMarker s st).wallet = w' ∧
      (repair ma br L scanView atDescriptors atMarker s st).attempting = false := by
  cases hr : st.repairScan with
  | none => simp [repair, hr, hl] at hc
  | some a =>
    by_cases heq : coldScan L scanView = a
    · cases hw : rebuild ma br L scanView atDescriptors atMarker s st.wallet with
      | none => simp [repair, hr, heq, hw, endAsFailure, hl] at hc
      | some w' =>
        refine ⟨by rw [heq], w', ?_⟩
        have hw2 := hw
        unfold rebuild at hw2
        simp only [Option.map_eq_some_iff] at hw2
        obtain ⟨m, hm, hw'⟩ := hw2
        refine ⟨m, rfl, hm, ?_, by simp [repair, hr, heq, hw],
          by simp [repair, hr, heq, hw, State.attempting]⟩
        rw [← hw']
        unfold applyImport
        split <;> rfl
    · simp [repair, hr, heq, endAsFailure, hl] at hc

/-- A repair never touches the cache: only a refresh replaces it. -/
@[req "WTC-9"]
theorem repair_keeps_cache (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) :
    (repair ma br L scanView atDescriptors atMarker s st).cache = st.cache := by
  unfold repair
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- `WTC-9`: "An attempt ends however it stops, whether or not its re-import began". After a
repair no attempt is in progress, whatever the state held and whatever the re-import yielded, and
after `endAsFailure` none is either, with the latch, the wallet and the cache as they were. -/
@[req "WTC-9"]
theorem attempt_ends_however_it_stops (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) :
    (repair ma br L scanView atDescriptors atMarker s st).attempting = false ∧
      (endAsFailure st).attempting = false ∧ (endAsFailure st).latched = st.latched ∧
      (endAsFailure st).wallet = st.wallet ∧ (endAsFailure st).cache = st.cache := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  unfold repair
  split
  · rename_i hn
    simp [State.attempting, hn]
  · split
    · split <;> rfl
    · rfl

/-- A repair never touches `scanned` either: only a refresh that serves a cold scan sets it and
only `State.observe` clears it. -/
@[req "WTC-9"]
theorem repair_keeps_scanned (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) :
    (repair ma br L scanView atDescriptors atMarker s st).scanned = st.scanned := by
  unfold repair
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- An attempt that ends without rebuilding leaves the latch set and no attempt in progress.
Whatever the state held, a repair whose rebuild yields no wallet, or which is offered another scan
than the one its attempt started from, clears nothing. `WTC-9`: "one that ends without rebuilding
the wallet leaves any latch set". -/
@[req "WTC-9"]
theorem failed_attempt_keeps_latch (ma : MarkerAnchor) (br : ImportBracket)
    (L : Ledger) (scanView atDescriptors atMarker : View) (s : Scan) (st : State)
    (hl : st.latched = true)
    (hf : rebuild ma br L scanView atDescriptors atMarker s st.wallet = none ∨
      st.repairScan ≠ some (coldScan L scanView)) :
    (repair ma br L scanView atDescriptors atMarker s st).latched = true ∧
      (repair ma br L scanView atDescriptors atMarker s st).attempting = false := by
  have hlat : (repair ma br L scanView atDescriptors atMarker s st).latched = true := by
    cases hr : st.repairScan with
    | none => simp [repair, hr, hl]
    | some a =>
      by_cases heq : coldScan L scanView = a
      · rcases hf with hf | hf
        · simp [repair, hr, heq, hf, endAsFailure, hl]
        · exact absurd (by rw [hr, heq]) hf
      · simp [repair, hr, heq, endAsFailure, hl]
  exact ⟨hlat, (attempt_ends_however_it_stops ma br L scanView atDescriptors atMarker s st).1⟩

/-- (ii) A failed attempt starts no scan of its own. Once a cold scan has replaced the cache since
the latch set, the state a repair leaves — whatever the re-import yielded — and the state a
failure before the re-import leaves both have the cache as their delta base under `neededScan`, the
cache the attempt left untouched: the next refresh walks from it, and cold-scans only where
`WTC-6`'s own order falls through to the cold scan. `WTC-9`: "the next attempt starts only from a
cold scan `WTC-6` itself reaches with none in progress, and starts no scan of its own". -/
@[req "WTC-9"]
theorem failed_attempt_starts_no_scan (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) (hs : st.scanned = true) :
    deltaBase .neededScan (repair ma br L scanView atDescriptors atMarker s st) = st.cache ∧
      deltaBase .neededScan (endAsFailure st) = st.cache := by
  refine ⟨?_, scanned_base_is_cache (endAsFailure st) hs⟩
  rw [scanned_base_is_cache _
    ((repair_keeps_scanned ma br L scanView atDescriptors atMarker s st).trans hs)]
  exact repair_keeps_cache ma br L scanView atDescriptors atMarker s st

/-- The paired attempt invariant of the formal model. A latched running attempt has published
its scan; an unlatched running attempt has no completion marker. `WTC-9`: "the scan replacing
the cache before the re-import begins (`WTC-6`)" and "A wallet holding no completion marker is
not latched, `WTC-8` already keeping it out of use: its first build, and any retry after a failed
one, starts the same way, from a cold scan `WTC-6` reaches with no attempt in progress."

`attemptInvariant_reachable` lifts the base and one-step preservation lemmas to every finite
composition of `refresh`, `repair`, `endAsFailure` and `State.observe .scoped` from any
no-attempt state, with arbitrary operation inputs and rule values. `Reachable` excludes
arbitrary external replacement of record fields. The marker-free half excludes the unlatched,
running, already-built records whose observation could otherwise set the latch while clearing
`scanned`. -/
@[req "WTC-9"]
def attemptInvariant (st : State) : Bool :=
  decide ((st.latched = true → st.attempting = true → st.scanned = true) ∧
    (st.latched = false → st.attempting = true → st.wallet.markers = []))

/-- Any no-attempt state satisfies the paired model invariant, whatever its other fields. -/
@[req "WTC-9"]
theorem attemptInvariant_of_no_attempt (st : State) (hn : st.attempting = false) :
    attemptInvariant st = true := by
  simp [attemptInvariant, hn]

/-- The scan-published half, exposed without an extra scan premise. -/
@[req "WTC-9"]
theorem attemptInvariant_scanned (st : State) (hi : attemptInvariant st = true)
    (hl : st.latched = true) (ha : st.attempting = true) : st.scanned = true :=
  (of_decide_eq_true hi).1 hl ha

/-- The marker-free half is needed when observing a running first build. -/
@[req "WTC-9"]
theorem attemptInvariant_markers (st : State) (hi : attemptInvariant st = true)
    (hl : st.latched = false) (ha : st.attempting = true) : st.wallet.markers = [] :=
  (of_decide_eq_true hi).2 hl ha

/-- Every refresh preserves both halves, under every rule value. An existing attempt retains
its scan state; a new attempt starts only where the refresh publishes a cold scan. -/
@[req "WTC-9"]
theorem attemptInvariant_refresh (g : Rules) (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (hi : attemptInvariant st = true) :
    attemptInvariant (refresh g L st v after walk s) = true := by
  apply decide_eq_true
  constructor
  · intro hl ha
    cases hn : st.attempting with
    | true => simp [refresh, attemptInvariant_scanned st hi hl hn]
    | false =>
      obtain ⟨hc, -, -⟩ := attempt_starts_only_at_cold_scan g L st v after walk s hn ha
      simp [refresh, hc]
  · intro hl ha
    cases hn : st.attempting with
    | true => exact attemptInvariant_markers st hi hl hn
    | false =>
      obtain ⟨-, -, hw⟩ := attempt_starts_only_at_cold_scan g L st v after walk s hn ha
      change st.wallet.markers = []
      change st.latched = false at hl
      simpa [hl] using hw

/-- A repair establishes both halves without an input-invariant premise: it ends the attempt,
under either marker anchor and either import bracket. -/
@[req "WTC-9"]
theorem attemptInvariant_repair (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) :
    attemptInvariant (repair ma br L scanView atDescriptors atMarker s st) = true :=
  attemptInvariant_of_no_attempt _
    (attempt_ends_however_it_stops ma br L scanView atDescriptors atMarker s st).1

/-- Failure before re-import also establishes both halves by ending the attempt. -/
@[req "WTC-9"]
theorem attemptInvariant_endAsFailure (st : State) :
    attemptInvariant (endAsFailure st) = true :=
  attemptInvariant_of_no_attempt _ rfl

/-- Scoped observation preserves the pair for a latched repair and an unlatched first build.
The latter needs the marker-free half: it prevents a new latch while `scanned` is cleared.
The literal scope is essential; observation under `.vacuous` can latch a running first build
(`running_first_build_breaks_invariant_with_vacuous`). -/
@[req "WTC-9"]
theorem attemptInvariant_observe (v : View) (st : State) (hi : attemptInvariant st = true) :
    attemptInvariant (st.observe .scoped v) = true := by
  apply decide_eq_true
  constructor
  · intro hl ha
    change st.attempting = true at ha
    cases hb : st.latched with
    | true => simp [State.observe, hb, attemptInvariant_scanned st hi hb ha]
    | false =>
      have hm := attemptInvariant_markers st hi hb ha
      change observe .scoped v st.wallet st.latched = true at hl
      rw [unbuilt_wallet_never_latches v st.wallet st.latched hm, hb] at hl
      cases hl
  · intro hl ha
    have hb : st.latched = false := by
      simpa [State.observe, observe] using (Bool.or_eq_false_iff.mp hl).1
    exact attemptInvariant_markers st hi hb ha

/-- Finite operation histories from any state with no attempt in progress, whatever its other
fields. Each refresh and repair may use any rule values and inputs; observation is scoped and
may read any view. External record replacement is not an operation in this boundary. -/
@[req "WTC-9"]
inductive Reachable : State → Prop
  | init (st : State) (hn : st.attempting = false) : Reachable st
  | refresh (g : Rules) (L : Ledger) (st : State) (v after walk : View) (s : Scan)
      (hr : Reachable st) : Reachable (VaultUnspent.refresh g L st v after walk s)
  | repair (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger)
      (scanView atDescriptors atMarker : View) (s : Scan) (st : State)
      (hr : Reachable st) :
      Reachable (VaultUnspent.repair ma br L scanView atDescriptors atMarker s st)
  | endAsFailure (st : State) (hr : Reachable st) : Reachable (VaultUnspent.endAsFailure st)
  | observe (v : View) (st : State) (hr : Reachable st) : Reachable (st.observe .scoped v)

/-- The paired attempt invariant holds after every admitted finite operation history. -/
@[req "WTC-9"]
theorem attemptInvariant_reachable (st : State) (hr : Reachable st) :
    attemptInvariant st = true := by
  induction hr with
  | init st hn => exact attemptInvariant_of_no_attempt st hn
  | refresh g L st v after walk s _ ih =>
    exact attemptInvariant_refresh g L st v after walk s ih
  | repair ma br L scanView atDescriptors atMarker s st _ _ =>
    exact attemptInvariant_repair ma br L scanView atDescriptors atMarker s st
  | endAsFailure st _ _ => exact attemptInvariant_endAsFailure st
  | observe v st _ ih => exact attemptInvariant_observe v st ih

/-- `WTC-9`: "the next attempt starts only from a cold scan `WTC-6` itself reaches with none
in progress, and starts no scan of its own". For a latched running attempt the paired model
invariant discharges the scan premise of `failed_attempt_starts_no_scan`. The delta base here
is specifically `.neededScan`; the other retry values are not asserted. -/
@[req "WTC-9"]
theorem invariant_failed_attempt_starts_no_scan (ma : MarkerAnchor) (br : ImportBracket)
    (L : Ledger) (scanView atDescriptors atMarker : View) (s : Scan) (st : State)
    (hi : attemptInvariant st = true) (hl : st.latched = true) (ha : st.attempting = true) :
    deltaBase .neededScan (repair ma br L scanView atDescriptors atMarker s st) = st.cache ∧
      deltaBase .neededScan (endAsFailure st) = st.cache :=
  failed_attempt_starts_no_scan ma br L scanView atDescriptors atMarker s st
    (attemptInvariant_scanned st hi hl ha)

/-- Reachability discharges the paired invariant and its scan premise for a latched running
attempt. Both ways of ending it retain the original cache as the `.neededScan` delta base;
the caller supplies neither an invariant nor a `scanned` premise. -/
@[req "WTC-9"]
theorem reachable_failed_attempt_starts_no_scan (ma : MarkerAnchor) (br : ImportBracket)
    (L : Ledger) (scanView atDescriptors atMarker : View) (s : Scan) (st : State)
    (hr : Reachable st) (hl : st.latched = true) (ha : st.attempting = true) :
    deltaBase .neededScan (repair ma br L scanView atDescriptors atMarker s st) = st.cache ∧
      deltaBase .neededScan (endAsFailure st) = st.cache :=
  invariant_failed_attempt_starts_no_scan ma br L scanView atDescriptors atMarker s st
    (attemptInvariant_reachable st hr) hl ha

/-- And the refresh that follows such a failure, offered a walk that completes from the cache,
serves that walk and starts no attempt: under `partialWalk` and `neededScan`, whatever the other
two, over every ledger, state with a cold scan published since its latch set, view and scan.
`WTC-9`: "A failed build or repair is therefore not retried while delta walks succeed". The walk's
end is taken active on the view captured when the walk starts (`ht`) so that the statement holds
under `tied` too; under `untied` it is not needed (`delta_commits_walk_on_any_branch`). -/
@[req "WTC-9"]
theorem scanned_walk_starts_no_attempt (wr : WalkRange) (ct : ChainTie) (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (c c' : Cache) (hl : st.latched = true)
    (hs : st.scanned = true) (hc : st.cache = some c) (ha : c.anchor.active walk = true)
    (hw : deltaWalk L c s = some c') (hcov : coversRange c walk s = true)
    (ht : c'.anchor.active walk = true) :
    serve ⟨.partialWalk, wr, .neededScan, ct⟩ L st v after walk s = (.deltaWalk, c') ∧
      (refresh ⟨.partialWalk, wr, .neededScan, ct⟩ L st v after walk s).repairScan =
        st.repairScan := by
  have hb : deltaBase .neededScan st = some c := by rw [scanned_base_is_cache st hs, hc]
  have hd := delta_commits_completed_walk wr .neededScan ct L st walk s c c' hb ha hw hcov ht
  have hsv : serve ⟨.partialWalk, wr, .neededScan, ct⟩ L st v after walk s = (.deltaWalk, c') := by
    simp [serve, walletServed, hl, hd]
  refine ⟨hsv, ?_⟩
  cases hr : st.repairScan <;> simp [refresh, hsv, hr]

/-- The re-import is tied to the cold scan its attempt started from, whatever the rules. A refresh
that finds the latch set and no attempt in progress, followed by a repair that clears the latch,
started an attempt, and the scan read on the repair's `scanView` is the cold scan that refresh
published: the same anchor and the same outputs. `WTC-9`: "starts a repair attempt from a cold
scan, whatever cache it holds, the scan replacing the cache before the re-import begins (`WTC-6`)",
and `WTC-7`: "The cold scan and a walk of the blocks above S proven to end at A itself (`WTC-12`)
form one result". Refreshes in between do not loosen it: they keep the recorded scan
(`attempt_in_progress_not_restarted`). What the equality pins is the scan's tip and what was live
there, not the blocks beneath; `rebuild_reads_the_attempts_settled_block` is the settled block,
under the premise that reaches it. -/
@[req "WTC-9"]
theorem rebuild_is_of_the_attempts_scan (g : Rules)
    (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (scanView atDescriptors atMarker : View) (s' : Scan) (hl : st.latched = true)
    (hn : st.attempting = false)
    (hc : (repair ma br L scanView atDescriptors atMarker s'
      (refresh g L st v after walk s)).latched = false) :
    coldScan L scanView = coldScan L v := by
  have h2 : (refresh g L st v after walk s).latched = true := hl
  obtain ⟨h, -⟩ := cleared_only_by_rebuild ma br L scanView atDescriptors atMarker s' _ h2 hc
  have ha : (refresh g L st v after walk s).attempting = true := by
    simp [State.attempting, h]
  obtain ⟨-, h1, -⟩ := attempt_starts_only_at_cold_scan g L st v after walk s hn ha
  rw [h1] at h
  exact (Option.some.inj h).symm

/-- The settled block `rebuild` reads is the attempt's. `rebuild` reads the settled block off the
view the repair is given, and `rebuild_is_of_the_attempts_scan` pins that view's tip and live
outputs only: a `View` is a map from heights to hashes, and nothing in it makes a tip fix the block
ten below. Under `Chain.Ancestry` — each view's tip active in it, and two views that share an
active block agreeing at every height at or below it, which is what a block hash's commitment to
its ancestry gives — the repair's scan view and the view the attempt's cold scan read at have the
same settled block. The premise is a hypothesis of this theorem and of nothing else here. Without
it the conclusion fails (`mismatched_scan_view_excluded_by_ancestry`). -/
@[req "WTC-9"]
theorem rebuild_reads_the_attempts_settled_block (g : Rules)
    (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (scanView atDescriptors atMarker : View) (s' : Scan) (hl : st.latched = true)
    (hn : st.attempting = false)
    (hc : (repair ma br L scanView atDescriptors atMarker s'
      (refresh g L st v after walk s)).latched = false)
    (ha : Ancestry scanView v) :
    settledBlock scanView scanView.tip = settledBlock v v.tip := by
  have h := rebuild_is_of_the_attempts_scan g ma br L st v after walk s scanView atDescriptors
    atMarker s' hl hn hc
  have ht : scanView.tip = v.tip := congrArg Cache.anchor h
  unfold settledBlock
  rw [ha.below_shared_tip ht (settledHeight scanView.tip) (Nat.sub_le _ _), ht]

/-- First-build sibling of `rebuild_is_of_the_attempts_scan`. `WTC-9`: "its first build, and any
retry after a failed one, starts the same way, from a cold scan `WTC-6` reaches with no attempt
in progress". Marker gain proves success even when the latch was already clear. No initial
latch premise is needed. The no-attempt premise excludes completion of an older attempt;
the refresh walk and import walk remain independent. -/
@[req "WTC-9"]
theorem first_build_is_of_the_attempts_scan (g : Rules)
    (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (scanView atDescriptors atMarker : View) (s' : Scan)
    (hm : st.wallet.markers = []) (hn : st.attempting = false)
    (hc : (repair ma br L scanView atDescriptors atMarker s'
      (refresh g L st v after walk s)).wallet.markers ≠ []) :
    coldScan L scanView = coldScan L v := by
  have h : (refresh g L st v after walk s).repairScan = some (coldScan L scanView) := by
    cases hr : (refresh g L st v after walk s).repairScan with
    | none =>
      simp only [repair, hr] at hc
      exact False.elim (hc hm)
    | some a =>
      by_cases heq : coldScan L scanView = a
      · rw [heq]
      · simp only [repair, hr, heq, ↓reduceIte, endAsFailure] at hc
        exact False.elim (hc hm)
  have ha : (refresh g L st v after walk s).attempting = true := by
    simp [State.attempting, h]
  obtain ⟨-, h1, -⟩ := attempt_starts_only_at_cold_scan g L st v after walk s hn ha
  rw [h1] at h
  exact (Option.some.inj h).symm

/-- The first build reads its attempt's settled block under the explicit ancestry premise.
Equal cold scans fix the tip and live outputs, not every block beneath the tip: the same
representation boundary as `mismatched_scan_view_excluded_by_ancestry` applies here.
`Chain.Ancestry` supplies agreement below the shared tip. This equates settled blocks on the
views; it makes no imported-marker anchor claim under arbitrary `MarkerAnchor` values. -/
@[req "WTC-9"]
theorem first_build_reads_the_attempts_settled_block (g : Rules)
    (ma : MarkerAnchor) (br : ImportBracket) (L : Ledger) (st : State) (v after walk : View)
    (s : Scan) (scanView atDescriptors atMarker : View) (s' : Scan)
    (hm : st.wallet.markers = []) (hn : st.attempting = false)
    (hc : (repair ma br L scanView atDescriptors atMarker s'
      (refresh g L st v after walk s)).wallet.markers ≠ [])
    (ha : Ancestry scanView v) :
    settledBlock scanView scanView.tip = settledBlock v v.tip := by
  have h := first_build_is_of_the_attempts_scan g ma br L st v after walk s scanView
    atDescriptors atMarker s' hm hn hc
  have ht : scanView.tip = v.tip := congrArg Cache.anchor h
  unfold settledBlock
  rw [ha.below_shared_tip ht (settledHeight scanView.tip) (Nat.sub_le _ _), ht]

/-- The scan view of the review probe: hashes `100` and `101`, tip `(1, 101)`. -/
@[req "WTC-9"] def probeScanView : View := chainOf [100, 101]

/-- The view the probe's repair is offered: the same tip over another block at height 0. No chain
of blocks has this shape beside `probeScanView` — the block `101` commits to one parent — but a
`View` can. -/
@[req "WTC-9"] def probeOfferedView : View := chainOf [200, 101]

/-- A ledger with no vault output, so that the two views' cold scans are equal. -/
@[req "WTC-9"]
def probeLedger : Ledger := { vaultOutputs := fun _ _ => [], vaultSpends := fun _ _ => [] }

/-- A latched node with one marker neither view has, no scan since the latch and no cache. -/
@[req "WTC-9"]
def probeLatched : State :=
  { wallet := { privateKeysDisabled := true, birthday := 0, markers := [⟨⟨0, 300⟩, 0⟩],
                holdsEveryVaultDescriptor := true },
    latched := true, scanned := false, repairScan := none, cache := none }

/-- The review probe, kept as the case the premise excludes. The refresh records a cold scan read
on hashes `[100, 101]`; the repair is offered the view `[200, 101]`, whose cold scan is equal —
same tip, same live outputs — so the tie passes, the latch clears, and the marker the rebuild
leaves is anchored at `(0, 200)`, a settled block the attempt's scan view never had: its own is
`(0, 100)`. So `rebuild_is_of_the_attempts_scan`'s conclusion holds here and
`rebuild_reads_the_attempts_settled_block`'s does not, and the pair of views is not one
`Chain.Ancestry` admits: they share the tip and differ beneath it. Every guard is written at a
literal value. -/
@[req "WTC-9"]
theorem mismatched_scan_view_excluded_by_ancestry :
    (let st' := refresh ⟨.partialWalk, .whole, .neededScan, .untied⟩ probeLedger probeLatched
        probeScanView probeScanView probeScanView
        { blocks := [], spends := [], after := probeScanView }
      let done := repair .settled .reProve probeLedger probeOfferedView probeOfferedView
        probeOfferedView
        { blocks := blocksOf [101] 1 200, spends := [], after := probeOfferedView } st'
      st'.repairScan = some (coldScan probeLedger probeScanView) ∧
        coldScan probeLedger probeOfferedView = coldScan probeLedger probeScanView ∧
        done.latched = false ∧ done.wallet.markers.head? = some ⟨⟨0, 200⟩, 0⟩ ∧
        settledBlock probeScanView probeScanView.tip = some ⟨0, 100⟩ ∧
        settledBlock probeOfferedView probeOfferedView.tip = some ⟨0, 200⟩) ∧
      ¬ Ancestry probeOfferedView probeScanView := by
  refine ⟨by decide, fun a => ?_⟩
  exact absurd (a.below_shared_tip (by decide) 0 (by decide)) (by decide)

/-- Under `settled` and `reProve` a rebuild whose bracket does not hold the settled block at either
point yields no wallet, so the latch stays set: the repair that keeps failing. -/
@[req "WTC-9"]
theorem rebuild_refused_when_moved (L : Ledger) (scanView atDescriptors atMarker : View)
    (s : Scan) (w : Wallet) (S : Anchor) (hS : settledBlock scanView scanView.tip = some S)
    (h : anchorStillActive atDescriptors S = false ∨ anchorStillActive atMarker S = false) :
    rebuild .settled .reProve L scanView atDescriptors atMarker s w = none := by
  unfold rebuild importMarker settledImport
  simp only [hS]
  split
  · simp [import_refused_when_moved S atDescriptors atMarker _ h]
  · rfl

/-! ## The snapshot (`WTC-10`) and what a coverage pass reads -/

/-- The snapshot: the tip and mempool sequence captured, and the read. -/
structure Snapshot where
  tip : Anchor
  sequence : Nat
  read : List Coin
  deriving DecidableEq, Repr

/-- One attempt at the snapshot. `WTC-10`: "capture the mempool txid set and its sequence number;
read confirmed candidates from the cache at the current tip; re-validate each with a batched
prevout read keeping only watched, confirmed outputs; add every output paying a watched script
from mempool transactions in the authorized set whose prevout is unconfirmed; then require the
tip and the mempool sequence to be unchanged". The cache is read through `fireTimeRead`, so a
cache whose anchor is not the tip is refused before any snapshot; `keep` is the prevout
re-validation, opaque; `additions` are the mempool outputs, from the authorized set by their
argument's definition, which is how "Unconfirmed external deposits are excluded by construction":
the authorized set is `SPN-33`'s and is not modelled. The attempt yields the snapshot when the
tip and the sequence read after are the ones captured, and `none` otherwise. -/
@[req "WTC-10"]
def attempt (v : View) (c : Cache) (sequence : Nat) (keep : Coin → Bool) (additions : List Coin)
    (tipAfter : Anchor) (sequenceAfter : Nat) : Option Snapshot :=
  match fireTimeRead v c with
  | none => none
  | some cached =>
    if v.tip = tipAfter ∧ sequence = sequenceAfter then
      some { tip := v.tip, sequence, read := cached.filter keep ++ additions }
    else none

/-- An attempt that yields a snapshot did so with the tip and the sequence unchanged between
capture and check, and its read is the read taken at capture: the cache's outputs at the tip,
re-validated, plus the additions. So the value the sweep sees is a function of the captured
`(tip, sequence, read)` alone. -/
@[req "WTC-10"]
theorem attempt_some (v : View) (c : Cache) (sequence : Nat) (keep : Coin → Bool)
    (additions : List Coin) (tipAfter : Anchor) (sequenceAfter : Nat) (snap : Snapshot)
    (h : attempt v c sequence keep additions tipAfter sequenceAfter = some snap) :
    v.tip = tipAfter ∧ sequence = sequenceAfter ∧ c.anchor = v.tip ∧
      snap = { tip := v.tip, sequence, read := c.outputs.filter keep ++ additions } := by
  unfold attempt at h
  split at h
  · cases h
  · rename_i outs hr
    obtain ⟨ha, rfl⟩ := (read_some_iff v c outs).mp hr
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      exact ⟨hs.1, hs.2, ha, h.symm⟩
    · cases h

/-- A chain advance between capture and use is one the attempt refuses. `WTC-10`: "require the
tip and the mempool sequence to be unchanged". -/
@[req "WTC-10"]
theorem attempt_refused_when_moved (v : View) (c : Cache) (sequence : Nat) (keep : Coin → Bool)
    (additions : List Coin) (tipAfter : Anchor) (sequenceAfter : Nat)
    (h : v.tip ≠ tipAfter ∨ sequence ≠ sequenceAfter) :
    attempt v c sequence keep additions tipAfter sequenceAfter = none := by
  unfold attempt
  split
  · rfl
  · have : ¬ (v.tip = tipAfter ∧ sequence = sequenceAfter) := by
      rcases h with h | h <;> exact fun hc => h (by simp [hc])
    simp [this]

/-- A stale cache is refused before any snapshot: no capture, no read. -/
@[req "WTC-10"]
theorem attempt_refused_when_stale (v : View) (c : Cache) (sequence : Nat) (keep : Coin → Bool)
    (additions : List Coin) (tipAfter : Anchor) (sequenceAfter : Nat) (h : c.anchor ≠ v.tip) :
    attempt v c sequence keep additions tipAfter sequenceAfter = none := by
  simp [attempt, read_refused_when_stale v c h]

/-- The sweep's read: two attempts, the second taken only when the first refused. `WTC-10`:
"retrying once and failing closed otherwise". -/
@[req "WTC-10"]
def readWithRetry (first second : Option Snapshot) : Option Snapshot :=
  match first with
  | some snap => some snap
  | none => second

/-- Fails closed: both attempts refused, nothing is read. -/
@[req "WTC-10"]
theorem retry_fails_closed : readWithRetry none none = none := rfl

/-- The first attempt's snapshot when the first succeeds, whatever the second. -/
@[req "WTC-10"]
theorem retry_takes_first (snap : Snapshot) (second : Option Snapshot) :
    readWithRetry (some snap) second = some snap := rfl

/-- What the sweep reads from a snapshot: the **vault unspent** read, whole. -/
@[req "WTC-10"]
def Snapshot.vaultUnspent (snap : Snapshot) : List Coin := snap.read

/-- The coverage pass built from a snapshot: its read is the snapshot's; the selected set, the
resident rungs and the unconfirmed-external list are the pass's own. Coverage owns the
denominator (`DUR-22`); this module supplies what it reads. -/
@[req "WTC-10"]
def passOf (snap : Snapshot) (selected : List Escape)
    (residentRungs unconfirmedExternal : List Outpoint) : Pass :=
  { read := snap.vaultUnspent, selected, residentRungs, unconfirmedExternal }

/-- The pass reads exactly the snapshot's read. -/
@[req "WTC-10"]
theorem passOf_read (snap : Snapshot) (selected : List Escape)
    (residentRungs unconfirmedExternal : List Outpoint) :
    (passOf snap selected residentRungs unconfirmedExternal).read = snap.read := rfl

/-! ## The chains and the ledger the traces run on

Chain `A` is thirteen blocks, heights 0 to 12, hashes `100 + h`, so the scan anchor `A` is
`(12, 112)` and the settled block `S` is ten below it, `(2, 102)`. Chain `B` forks at height 2,
hashes `200 + h` from there: a reorg deeper than the settled depth, which unseats `S`. Chain `C`
forks at height 5: a reorg no deeper than the settled depth, which leaves `S` standing. The
marker-anchor twin below runs `C` against a wallet holding one marker, which is what a fresh import
and a cold start leave and where the repair cost lands; a wallet also holding a scan-tip marker
whose anchor `C` leaves active — one anchored below the fork at height 5 — is the other case, and
`ADR-0024` carries it.

The ledger holds three vault outputs and two spends:

* `X = (1, 50)`, created in the shared block at height 0 and spent at height 2 — **at** `S`, so
  neither the scan (which finds it spent) nor the walk of `(S, A]` (which starts above `S`) sees
  its creating height on `A`. On `B` the block at height 2 spends nothing, so `X` is live there:
  that is `DEF-21`'s permanently unwatched output.
* `Z = (4, 60)`, created in the shared block at height 1 and spent at height 7 — **inside** the
  settled depth, so the walk of `(S, A]` reports its creating height 1 and the amended birthday
  covers it. On `C` the block at height 7 spends nothing, so `Z` is live there: the output a reorg
  no deeper than the settled depth resurrects, which the settled block's marker is still standing
  to cover.
* `Y = (2, 40)`, created at height 11 on `A` alone and live at `A`: what the cold scan finds. -/

/-- Chain `A`: thirteen blocks, the scan anchor `(12, 112)` and the settled block `(2, 102)`. -/
@[req "WTC-7"]
def vaultChainA : List Hash := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]

/-- Chain `B`: the reorg deeper than the settled depth, forking at height 2. -/
@[req "WTC-7"]
def vaultChainB : List Hash := [100, 101, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]

/-- Chain `C`: the reorg no deeper than the settled depth, forking at height 5. -/
@[req "WTC-7"]
def vaultChainC : List Hash := [100, 101, 102, 103, 104, 205, 206, 207, 208, 209, 210, 211, 212]

/-- The ledger of the traces, keyed by height and hash. -/
@[req "WTC-7"]
def vaultLedger : Ledger :=
  { vaultOutputs := fun h hash =>
      if h == 0 && hash == 100 then [(1, 50)]
      else if h == 1 && hash == 101 then [(4, 60)]
      else if h == 11 && hash == 111 then [(2, 40)]
      else [],
    vaultSpends := fun h hash =>
      if h == 2 && hash == 102 then [(0, (1, 50))]
      else if h == 7 && hash == 107 then [(1, (4, 60))]
      else [] }

/-- The walk of `(S, A]` on `A`: heights 3 to 12, the first linking to `S`'s hash `102`, the last
the scan anchor itself. -/
@[req "WTC-7"]
def vaultWalkA : Scan :=
  { blocks := blocksOf [103, 104, 105, 106, 107, 108, 109, 110, 111, 112] 3 102, spends := [],
    after := chainOf vaultChainA }

/-- The same walk on `B`, for the repair that scans there. -/
@[req "WTC-7"]
def vaultWalkB : Scan :=
  { blocks := blocksOf [203, 204, 205, 206, 207, 208, 209, 210, 211, 212] 3 202, spends := [],
    after := chainOf vaultChainB }

/-- `S` on `A`: `(2, 102)`. -/
@[req "WTC-7"] def vaultSettledA : Anchor := ⟨2, 102⟩

/-- The birthday the import on `A` computes under the amended rule: `S`'s height 2 lowered to 1 by
the creating height the walk's spend of `Z` carries. -/
@[req "WTC-7"] def def21Birthday : Height := 1

/-! ### `DEF-21`'s trace, and its half under the withdrawn bracket

The import on `A`, with the reorg to `B` landing between the scan and the import. The `reProve`
half is in `Exhibits.lean`. "Permanently" is the birthday's definition — a wallet scans from its
birthday up, so an output created below it is never seen by that wallet — and nothing about wallet
rescans is modelled. -/

/-- Under the withdrawn bracket the import goes through on `B` with `A`'s birthday 1; `X`, created
at height 0 and live on `B`, is unwatched — `DEF-21`: "leaving an output permanently unwatched" —
and the outputs the wallet watches sum to less than the outputs live on `B` — "inflating apparent
coverage": the denominator understated. -/
@[req "WTC-7"]
theorem def21_unwatched_with_unbracketed :
    importMarker .settled .unbracketed vaultLedger (chainOf vaultChainA)
        (chainOf vaultChainB) (chainOf vaultChainB) vaultWalkA =
      some ⟨vaultSettledA, def21Birthday⟩ ∧
      unwatched vaultLedger (chainOf vaultChainB) def21Birthday ≠ [] ∧
      sumValues (watched vaultLedger (chainOf vaultChainB) def21Birthday) <
        sumValues (live vaultLedger (chainOf vaultChainB)) := by
  decide

/-! ### The marker anchor's trace, and its half under the withdrawn value

The same import on `A`, then the reorg to `C` — no deeper than the settled depth. The `settled`
half is in `Exhibits.lean`.

What the two values differ in, on a history the model can reach, is the repair: `C` leaves the
settled block standing and unseats the scan anchor, the only anchor `scanTipWallet` holds. So the
wallet goes out of use and `WTC-9` latches a repair (`markerAnchor_repairs_with_scanTip`), and the
output `C` resurrects sits below that wallet's birthday, unwatched until the repair completes.
`scanTip_active_marker_watches_everything` does not apply here: its `hagree` takes the view after
the reorg to show the same block as the import's scan view at every height at or below the marker's
anchor, and `C` shows a different one at height 12, the anchor's own height. Its `hm` holds — the
wallet does hold that marker — but the standing-anchor scoping is `hm` and `hagree` together, and
`C` leaves this wallet no anchor left standing. What closes the gap is the repair's own cold scan,
which reads at `C`'s tip where the output is live, so `scanTipBirthday` floors the re-import at or
below that output's creating height —
`WTC-7`: "A repair never starts later than the wallet already covers". Both — that the output is
unwatched until the repair completes, and that the repair's cold scan closes it — are read off the
definitions and neither is exhibited: no declaration reads `unwatched` on this wallet, and no
exhibit evaluates `repair` at `.scanTip` on it — `cleared_only_by_rebuild` and
`failed_attempt_keeps_latch` take the marker anchor as a variable and so say something
of `repair .scanTip` too, but nothing about what this wallet's birthday becomes. Where a held marker
does stand through the reorg,
`scanTip_active_marker_watches_everything` is the coverage fact, under its own hypotheses. -/

/-- The wallet the import leaves under the withdrawn value: one marker, at the scan anchor
`(12, 112)`, with the birthday 11 the descriptors took. -/
@[req "WTC-7"]
def scanTipWallet : Wallet :=
  { privateKeysDisabled := true, birthday := 11, markers := [⟨⟨12, 112⟩, 11⟩],
    holdsEveryVaultDescriptor := true }

/-- The wallet the same import leaves under the value as it stands: the marker at `S = (2, 102)`,
with the birthday the walk of `(S, A]` lowered to 1. -/
@[req "WTC-7"]
def settledWallet : Wallet :=
  { privateKeysDisabled := true, birthday := def21Birthday,
    markers := [⟨vaultSettledA, def21Birthday⟩], holdsEveryVaultDescriptor := true }

/-- Under the withdrawn value the marker anchors at the scan anchor and the birthday is 11, the
creating height of the one output the scan found live: the walk of the settled depth is not taken,
so the spend of `Z` at height 7 contributes nothing. The reorg to `C` — no deeper than the settled
depth — unseats that anchor, and it is the only anchor the wallet holds: no held marker is left
active, the wallet is out of use, and `WTC-9` latches a repair, a cold scan and a re-import for a
reorg that left the settled block standing. That cost is what the value as it stands avoids: its
marker anchors at `S`, which `C` leaves active, so the wallet stays in use and nothing latches
(`Exhibits.VaultUnspentCache.settled_covers_resurrection_with_current`). -/
@[req "WTC-7"]
theorem markerAnchor_repairs_with_scanTip :
    importMarker .scanTip .reProve vaultLedger (chainOf vaultChainA) (chainOf vaultChainA)
        (chainOf vaultChainA) vaultWalkA = some ⟨⟨12, 112⟩, 11⟩ ∧
      anchorStillActive (chainOf vaultChainC) ⟨12, 112⟩ = false ∧
      usable (chainOf vaultChainC) scanTipWallet = false ∧
      observe .scoped (chainOf vaultChainC) scanTipWallet false = true := by
  decide

/-! ### The delta walk's traces, and their halves under the withdrawn values

One delta base: the cache anchored at `(0, 100)`, held under the latch, a cold scan having replaced
the cache since the latch set, with a repair attempt in progress, which is the state `WTC-9`
advances by delta walks. The latch keeps the wallet out of play, so its value is immaterial. Two
views of the chain `100 + h`: the short one, heights 0 to 2, on which a walk that covers its range
reaches the tip, and the long one, heights 0 to 34, whose tip is two blocks further than
`deltaWindow` blocks above the base. Each trace below writes all four of `Rules` at literal values,
three as they stand and one withdrawn; the halves under the values as they stand are in
`Exhibits.lean`. -/

/-- The delta base and the state it is held in: the latch set, a cold scan published since, and an
attempt in progress whose recorded scan is the cache at `(0, 100)`. Both hold no output: they stand
in for a scan and are not `vaultLedger`'s cold scan there, and no exhibit runs `repair` on this
state. -/
@[req "WTC-6"]
def deltaState : State :=
  { wallet := { privateKeysDisabled := true, birthday := 0, markers := [⟨⟨0, 100⟩, 0⟩],
                holdsEveryVaultDescriptor := true },
    latched := true, scanned := true, repairScan := some { outputs := [], anchor := ⟨0, 100⟩ },
    cache := some { outputs := [], anchor := ⟨0, 100⟩ } }

/-- The same cache under the latch after the attempt has failed: none in progress. -/
@[req "WTC-9"]
def deltaFailedState : State := endAsFailure deltaState

/-- The same cache under a latch that has just set: no cold scan has replaced the cache since, and
no attempt is in progress. The cache is the one the node held before the latch. -/
@[req "WTC-9"]
def deltaUnscannedState : State := { deltaFailedState with scanned := false }

/-- The short view: heights 0 to 2, tip `(2, 102)`. -/
@[req "WTC-6"] def deltaView : View := chainOf [100, 101, 102]

/-- The long view: heights 0 to 34, tip `(34, 134)`. -/
@[req "WTC-6"] def deltaLongView : View := chainOf ((List.range 35).map (100 + ·))

/-- The walk from the base that covers its whole range on the short view: the two blocks above the
anchor, each linking to the one before it, the last still active after the loop. -/
@[req "WTC-6"]
def deltaTipWalk : Scan :=
  { blocks := blocksOf [101, 102] 1 100, spends := [], after := deltaView }

/-- The walk that stops one short of its range on the short view: block 1 alone. -/
@[req "WTC-6"]
def deltaShortWalk : Scan :=
  { blocks := blocksOf [101] 1 100, spends := [], after := deltaView }

/-- The walk of no block. -/
@[req "WTC-6"]
def deltaEmptyWalk : Scan := { blocks := [], spends := [], after := deltaView }

/-- The branch the chain moves to after the short view is captured: the same block at height 0,
then hashes `201` and `202`. -/
@[req "WTC-6"] def deltaForkView : View := chainOf [100, 201, 202]

/-- The walk read on that branch: two blocks at heights 1 and 2 that link from the base's hash
`100` and to each other, hashes `201` and `202`, the last active on the view read after the loop,
which is that branch. It covers heights 1 to 2, the short view's whole range, and passes every
`WTC-12` check; what it is not is on the short view's chain. -/
@[req "WTC-6"]
def deltaForkWalk : Scan :=
  { blocks := blocksOf [201, 202] 1 100, spends := [], after := deltaForkView }

/-- The walk from the base that covers its whole range on the long view: the `deltaWindow` blocks
at heights 1 to 32, ending at `(32, 132)`, two below the tip. -/
@[req "WTC-6"]
def deltaWindowWalk : Scan :=
  { blocks := blocksOf ((List.range 32).map (101 + ·)) 1 100, spends := [], after := deltaLongView }

/-- The wallet before its first build: no descriptor imported and no completion marker. -/
@[req "WTC-9"]
def unbuiltWallet : Wallet :=
  { privateKeysDisabled := true, birthday := 0, markers := [], holdsEveryVaultDescriptor := false }

/-- A node whose first wallet build has failed: the wallet still unbuilt, no attempt in progress,
and the cache the cold scan published, at the short view's tip. -/
@[req "WTC-9"]
def unbuiltState : State :=
  { wallet := unbuiltWallet, latched := false, scanned := false, repairScan := none,
    cache := some (coldScan vaultLedger deltaView) }

/-- The delta commit, withdrawn value. The walk that covers its whole range and ends two below the
tip is thrown away, and the cold scan runs instead — on every refresh of a node more than
`deltaWindow` blocks behind. Under the value as it stands it is committed
(`Exhibits.VaultUnspentCache.delta_walk_below_tip_committed`). -/
@[req "WTC-6"]
theorem delta_below_tip_falls_through_with_tipOnly :
    coversRange { outputs := [], anchor := ⟨0, 100⟩ } deltaLongView deltaWindowWalk = true ∧
      (serve ⟨.tipOnly, .whole, .neededScan, .untied⟩ vaultLedger deltaState deltaLongView
        deltaLongView deltaLongView deltaWindowWalk).1 = .coldScan ∧
      (serve ⟨.tipOnly, .whole, .neededScan, .untied⟩ vaultLedger deltaState deltaLongView
        deltaLongView deltaLongView deltaWindowWalk).2.anchor = ⟨34, 134⟩ := by
  decide

/-- The walk range, withdrawn value. The walk that stops one short of its range is committed and
leaves the cache at `(1, 101)`; the walk of no block is committed too and leaves the cache where it
was, two below the tip, which the fire-time read refuses — and nothing makes the next refresh do
otherwise, so a node can serve that cache refresh after refresh without reading a block. Under the
value as it stands both fall through to the cold scan
(`Exhibits.VaultUnspentCache.delta_walk_short_falls_through`,
`Exhibits.VaultUnspentCache.delta_walk_empty_below_tip_falls_through`). -/
@[req "WTC-6"]
theorem short_and_empty_walk_committed_with_asRead :
    serve ⟨.partialWalk, .asRead, .neededScan, .untied⟩ vaultLedger deltaState deltaView deltaView
        deltaView deltaShortWalk = (.deltaWalk, { outputs := [(4, 60)], anchor := ⟨1, 101⟩ }) ∧
      serve ⟨.partialWalk, .asRead, .neededScan, .untied⟩ vaultLedger deltaState deltaView
        deltaView deltaView deltaEmptyWalk =
          (.deltaWalk, { outputs := [], anchor := ⟨0, 100⟩ }) ∧
      fireTimeRead deltaView { outputs := [], anchor := ⟨0, 100⟩ } = none := by
  decide

/-- The retry trigger, the value the amendment of 2026-10-02 withdraws. With the latch set, a cold
scan published since and the attempt failed, the refresh is offered a walk that covers its whole
range from the cache and passes it over: it cold-scans of its own and starts another attempt from
that scan, and so does every refresh after a failure, however well the walks would have done.
Under the value as it stands the walk is served and no attempt starts
(`Exhibits.VaultUnspentCache.failed_attempt_not_retried_while_walks_succeed`). -/
@[req "WTC-9"]
theorem failed_attempt_rescans_with_everyRefresh :
    coversRange { outputs := [], anchor := ⟨0, 100⟩ } deltaView deltaTipWalk = true ∧
      serve ⟨.partialWalk, .whole, .everyRefresh, .untied⟩ vaultLedger deltaFailedState deltaView
        deltaView deltaView deltaTipWalk = (.coldScan, coldScan vaultLedger deltaView) ∧
      (refresh ⟨.partialWalk, .whole, .everyRefresh, .untied⟩ vaultLedger deltaFailedState
        deltaView deltaView deltaView deltaTipWalk).repairScan =
          some (coldScan vaultLedger deltaView) := by
  decide

/-- The retry trigger, the value the amendment of 2026-10-01 had withdrawn. The latch has just set
and no cold scan has replaced the cache since, yet the refresh walks on from the cache it held
before the latch: the delta walk is the source, no cold scan runs, and afterwards the latch is
still set with no attempt in progress and still no scan since it set — so no repair starts while
such walks succeed, and the cache a wallet read may have left is never replaced by a scan. Under
the value as it stands the same refresh cold-scans and starts an attempt
(`Exhibits.VaultUnspentCache.latched_unscanned_cold_scans`). -/
@[req "WTC-9"]
theorem latched_unscanned_walks_with_noFirstScan :
    serve ⟨.partialWalk, .whole, .noFirstScan, .untied⟩ vaultLedger deltaUnscannedState deltaView
        deltaView deltaView deltaTipWalk =
          (.deltaWalk, { outputs := [(4, 60)], anchor := ⟨2, 102⟩ }) ∧
      (refresh ⟨.partialWalk, .whole, .noFirstScan, .untied⟩ vaultLedger deltaUnscannedState
        deltaView deltaView deltaView deltaTipWalk).latched = true ∧
      (refresh ⟨.partialWalk, .whole, .noFirstScan, .untied⟩ vaultLedger deltaUnscannedState
        deltaView deltaView deltaView deltaTipWalk).scanned = false ∧
      (refresh ⟨.partialWalk, .whole, .noFirstScan, .untied⟩ vaultLedger deltaUnscannedState
        deltaView deltaView deltaView deltaTipWalk).attempting = false := by
  decide

/-- The chain tie, withdrawn value. The chain moves to another branch after the short view is
captured, and the walk reads that branch: it links from the cache's anchor, covers heights 1 to 2,
the whole range the short view sets, and its last block `(2, 202)` is active on the view read after
its loop, so it passes every `WTC-12` check. Under `tied` it is refused all the same, because
`(2, 202)` is not the block the short view has at height 2, and the refresh falls through to a cold
scan read on the short view, the chain that was left. Under the value as it stands the walk is
committed (`Exhibits.VaultUnspentCache.off_branch_walk_committed`). -/
@[req "WTC-6"]
theorem off_branch_walk_refused_with_tied :
    deltaWalk vaultLedger { outputs := [], anchor := ⟨0, 100⟩ } deltaForkWalk =
        some { outputs := [], anchor := ⟨2, 202⟩ } ∧
      coversRange { outputs := [], anchor := ⟨0, 100⟩ } deltaView deltaForkWalk = true ∧
      Anchor.active deltaView ⟨2, 202⟩ = false ∧
      serve ⟨.partialWalk, .whole, .neededScan, .tied⟩ vaultLedger deltaState deltaView deltaView
        deltaView deltaForkWalk = (.coldScan, coldScan vaultLedger deltaView) := by
  decide

/-- The latch scope, withdrawn value. The unbuilt wallet meets the latch condition with nothing to
check, so observing any view latches it; and the refresh that follows, offered a walk of no block
from a cache already at the tip — which covers its range and would be served — has no delta base
and cold-scans of its own, to start as a repair the build `WTC-8` was already keeping the wallet
out of use for. Under the value as it stands the wallet is not latched and the walk is served
(`Exhibits.VaultUnspentCache.unbuilt_wallet_not_latched`). -/
@[req "WTC-9"]
theorem unbuilt_wallet_latches_with_vacuous :
    observe .vacuous deltaView unbuiltWallet false = true ∧
      (unbuiltState.observe .vacuous deltaView).latched = true ∧
      serve ⟨.partialWalk, .whole, .neededScan, .untied⟩ vaultLedger
        (unbuiltState.observe .vacuous deltaView) deltaView deltaView deltaView deltaEmptyWalk =
          (.coldScan, coldScan vaultLedger deltaView) ∧
      (refresh ⟨.partialWalk, .whole, .neededScan, .untied⟩ vaultLedger
        (unbuiltState.observe .vacuous deltaView) deltaView deltaView deltaView
        deltaEmptyWalk).repairScan = some (coldScan vaultLedger deltaView) := by
  decide

/-- A refresh starts a first build from a marker-free, no-attempt state and establishes the
paired invariant. Observation under `.vacuous` then latches that running build, clears its
published-scan flag and leaves the attempt running, breaking the invariant. This is the concrete
counterexample to extending `attemptInvariant_observe` beyond `.scoped`. -/
@[req "WTC-9"]
theorem running_first_build_breaks_invariant_with_vacuous :
    let initial := { unbuiltState with cache := none }
    let running := refresh ⟨.partialWalk, .whole, .neededScan, .untied⟩ vaultLedger initial
      deltaView deltaView deltaView deltaEmptyWalk
    let observed := running.observe .vacuous deltaView
    initial.wallet.markers = [] ∧ initial.attempting = false ∧
      running.repairScan = some (coldScan vaultLedger deltaView) ∧
      running.wallet.markers = [] ∧ running.latched = false ∧
      running.scanned = true ∧ running.attempting = true ∧
      attemptInvariant running = true ∧
      observed.latched = true ∧ observed.scanned = false ∧ observed.attempting = true ∧
      attemptInvariant observed = false := by
  decide

end BtcPolicy.VaultUnspent
