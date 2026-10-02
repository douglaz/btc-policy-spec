import BtcPolicy.Req
/-! The backend view the watchtower binds results to (`ADR-0023` decision 10 item 8, milestone 8):
heights and block hashes, `WTC-13`'s `(height, hash)` anchor, the active-chain read with the
captured tip, and `previousblockhash` linkage. Defined once, here, and shared: the watchtower
cursor, its reconciliation and the scan proof (`WTC-12`–`WTC-14`, `Watchtower.lean`) import it,
and so do the vault-unspent cache and the wallet's completion markers (`WTC-5`–`WTC-10`,
`VaultUnspent.lean`), so that height → hash is stated in one place and `WTC-6`'s delta walk reuses
the one linkage predicate.

`WTC-11`: "A node MUST detect a reorg at every point where it binds a result to a chain: a block
hash at a height that no longer matches; a header height accepted only if that block is still
active at it; a delta walk whose block's `previousblockhash` is not the cached parent; a wallet
that holds completion markers none of whose anchors is still active (`WTC-8`)." The first site is
`Anchor.active`, the read reconciliation makes; the second is `headerAccepted`; the third is
`Block.linksTo`, which `WTC-12`'s first two checks use too. The fourth site, the wallet, is
`VaultUnspent.lean`'s with the cache it anchors, and is not stated here.

This is not the kernel's chain view (`{mtp, seen}`, an environment input), not the refresh age's
(`tip`, `confirmed`, `mtp`) and not the coverage pass: none of those carries height → hash, and
none is enlarged. It is not the release cursor either (`Cursor.lean`, `SPN-38`), which this module
does not import. -/

namespace BtcPolicy.Chain

/-- A block height, and a block hash; hashes are compared for equality and nothing else. -/
abbrev Height := Nat
abbrev Hash := Nat

/-- The anchor. `WTC-13`: "the `(height, hash)` anchors of the top of its scanned range". -/
structure Anchor where
  height : Height
  hash : Hash
  deriving DecidableEq, Repr

/-- The chain as the watchtower reads it: the hash active at each height (`none` past the tip)
and the tip captured before a pass, the one whose hash `WTC-14` tests: "captured tip's hash". -/
structure View where
  activeAt : Height → Option Hash
  tip : Anchor

/-- What a block hash commits to, as a premise on a pair of views: each view's tip is active in
that view, and two views that share an active block at a height show the same block at every height
at or below it. A `View` is an arbitrary map from heights to hashes and `Anchor.active` tests a
single height, so neither follows from the structure; Bitcoin is what makes both hold, a block's
hash committing to its `previousblockhash` and so to every block beneath it. A hypothesis a theorem
takes where it needs it (`VaultUnspent.rebuild_reads_the_attempts_settled_block`), never an axiom
and never a field of `View`. -/
structure Ancestry (v w : View) : Prop where
  tipLeft : v.activeAt v.tip.height = some v.tip.hash
  tipRight : w.activeAt w.tip.height = some w.tip.hash
  agree : ∀ h hash, v.activeAt h = some hash → w.activeAt h = some hash →
    ∀ k, k ≤ h → v.activeAt k = w.activeAt k

/-- Under the premise, two views with one tip show the same block at every height at or below it:
the tip is the shared active block. -/
@[req "WTC-11"]
theorem Ancestry.below_shared_tip {v w : View} (a : Ancestry v w) (ht : v.tip = w.tip) (k : Height)
    (hk : k ≤ v.tip.height) : v.activeAt k = w.activeAt k :=
  a.agree v.tip.height v.tip.hash a.tipLeft (by rw [ht]; exact a.tipRight) k hk

/-- `WTC-11`'s first site. `WTC-11`: "a block hash at a height that no longer matches" — the
anchor's hash is what the chain now has at its height. -/
@[req "WTC-11"]
def Anchor.active (v : View) (a : Anchor) : Bool := v.activeAt a.height == some a.hash

/-- `WTC-11`'s second site. `WTC-11`: "a header height accepted only if that block is still active
at it". -/
@[req "WTC-11"]
def headerAccepted (v : View) (h : Height) (hash : Hash) : Bool := v.activeAt h == some hash

/-- A header is refused whenever its block is not active at that height, whatever the tip. -/
@[req "WTC-11"]
theorem header_refused_when_inactive (v : View) (h : Height) (hash : Hash)
    (hn : v.activeAt h ≠ some hash) : headerAccepted v h hash = false := by
  simpa [headerAccepted] using hn

/-- A scanned block: its height, its hash, and its `previousblockhash`. -/
structure Block where
  height : Height
  hash : Hash
  prev : Hash
  deriving DecidableEq, Repr

/-- `WTC-11`'s third site, as the predicate it negates: the block links to the parent hash given.
`WTC-11`: "a delta walk whose block's `previousblockhash` is not the cached parent". `WTC-12`'s
first two checks are this predicate against the expected parent and against the previous scanned
hash. -/
@[req "WTC-11"]
def Block.linksTo (b : Block) (parent : Hash) : Bool := b.prev == parent

/-- The anchor a scanned block leaves behind. -/
@[req "WTC-13"]
def Block.anchor (b : Block) : Anchor := ⟨b.height, b.hash⟩

end BtcPolicy.Chain
