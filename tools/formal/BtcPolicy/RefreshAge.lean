import BtcPolicy.Req
/-! `SPN-46`'s refresh age, with where it is read as a guard parameter (`ADR-0019`, `F52`).

"A refresh MUST be refused `REFRESH_TOO_SOON` / `refresh_min_interval` unless EVERY input's coin
is at least `refresh_min_interval_secs` old **by the chain's own clock**: with `confirming` the
block in which the input's creating transaction confirmed on the active chain, `tip` the node's
current tip, and `MTP` BIP113 median-time-past, `MTP(tip) − MTP(confirming) ≥
refresh_min_interval_secs` with equality passing … An input whose creating transaction is not
confirmed on the active chain has no age and MUST be refused the same way".

The withdrawn design recorded in `ADR-0019` latched on each node's own accepted refreshes
(`F52`); it is modelled as each node's own accepted set, so the theorems here take the
source as an argument and `Exhibits.lean` holds the ones over `current`. Time is in days, block
heights are days, and `refresh_min_interval_secs` is a sealed value, so the interval is an
argument, never a constant. -/

namespace BtcPolicy.RefreshAge

/-- Where a coin's age is read. `chainMtp` is `SPN-46` as it stands; `perNodeLog` is the 2026-09-12
defect `F52` records. -/
inductive Source
  | chainMtp | perNodeLog
  deriving DecidableEq, Repr

/-- `SPN-46` as it stands. -/
@[req "SPN-46"]
def current : Source := .chainMtp

/-- A coin is named by its creating transaction; a block by its height. -/
abbrev TxId := Nat
abbrev Block := Nat

/-- What the chain rule reads: the tip, which block confirmed each transaction on the active
chain (`none`: not confirmed there), and each block's median-time-past. -/
structure ChainView where
  tip : Block
  confirmed : List (TxId × Block)
  mtp : Block → Nat

/-- What the withdrawn rule read: this node's own accepted refreshes, each as the day it was
accepted and every coin it touched — its inputs and its outputs (`ADR-0019`'s withdrawn
refresh log). -/
abbrev Log := List (Nat × List TxId)

/-- `MTP(tip) − MTP(confirming)`, or `none` for a coin whose creating transaction is not confirmed
on the active chain. `Nat` subtraction saturates, and a confirming block's MTP never exceeds the
tip's. -/
@[req "SPN-46"]
def age (cv : ChainView) (coin : TxId) : Option Nat :=
  (cv.confirmed.lookup coin).map fun b => cv.mtp cv.tip - cv.mtp b

/-- One input's verdict. Under `chainMtp` the log is not read; under `perNodeLog` the chain is
not read: a coin any refresh this node accepted touched inside the interval is refused. -/
@[req "SPN-46"]
def admit (src : Source) (interval : Nat) (cv : ChainView) (log : Log) (now : Nat) (coin : TxId) :
    Bool :=
  match src with
  | .chainMtp =>
    match age cv coin with
    | none => false
    | some a => interval ≤ a
  | .perNodeLog => !log.any fun (day, touched) => touched.contains coin && now < day + interval

/-- "unless EVERY input's coin is at least `refresh_min_interval_secs` old". -/
@[req "SPN-46"]
def admitAll (src : Source) (interval : Nat) (cv : ChainView) (log : Log) (now : Nat)
    (coins : List TxId) : Bool :=
  coins.all (admit src interval cv log now)

/-- Under the chain rule, for every view and every coin: admitted iff the coin has an age and the
age reaches the interval, "with equality passing". -/
@[req "SPN-46"]
theorem chain_admits_iff (interval : Nat) (cv : ChainView) (log : Log) (now coin : Nat) :
    admit .chainMtp interval cv log now coin = true ↔
      ∃ a, age cv coin = some a ∧ interval ≤ a := by
  unfold admit
  cases age cv coin <;> simp

/-- A coin whose creating transaction is not on the active chain is refused, whatever the tip. -/
@[req "SPN-46"]
theorem unconfirmed_refused (interval : Nat) (cv : ChainView) (log : Log) (now coin : Nat)
    (h : cv.confirmed.lookup coin = none) : admit .chainMtp interval cv log now coin = false := by
  simp [admit, age, h]

/-! ## `F52`'s alternation, as data

2-of-3, nodes `A = 0`, `B = 1` honest and `M = 2` compromised. The coin `X` is transaction `0`,
confirmed at day 0; the table's day `d` is day `30 + d` here, so `X` is thirty days old when the
attack starts against a thirty-day interval. Each link is `(day, refresh, coin it spends, honest
nodes it is presented to)`; the seed is presented to `B` alone and never confirms, and every later
link confirms on the day it is presented. Seven links in fifteen days. -/

structure Link where
  day : Nat
  tx : TxId
  spends : TxId
  honest : List Nat
  deriving Repr

@[req "SPN-46"] def interval : Nat := 30

/-- The seed and the seven links. -/
@[req "SPN-46"]
def alternation : List Link :=
  [ { day := 31, tx := 1, spends := 0, honest := [1] },        -- seed over X, B only, no quorum
    { day := 33, tx := 2, spends := 0, honest := [0] },        -- X→Y: A, M
    { day := 35, tx := 3, spends := 2, honest := [1] },        -- Y→Z: B, M
    { day := 37, tx := 4, spends := 3, honest := [0] },        -- Z→W: A, M
    { day := 39, tx := 5, spends := 4, honest := [1] },
    { day := 41, tx := 6, spends := 5, honest := [0] },
    { day := 43, tx := 7, spends := 6, honest := [1] },
    { day := 45, tx := 8, spends := 7, honest := [0] } ]

/-- The chain as the honest nodes all read it at `tip`: `X` at day 0, every confirmed link at its
day; the seed never confirms. -/
def chainAt (tip : Nat) : ChainView :=
  { tip := tip,
    confirmed := (0, 0) :: (alternation.filter (·.tx ≠ 1)).map fun l => (l.tx, l.day),
    mtp := fun b => b }

/-- Node `node`'s own log before `day`: every earlier link it accepted, with the coin spent and
the coin created. -/
def logOf (node day : Nat) : Log :=
  (alternation.filter fun l => l.day < day && l.honest.contains node).map
    fun l => (l.day, [l.spends, l.tx])

/-- A link's verdict on an honest node it is presented to, under a source. -/
def verdict (src : Source) (node : Nat) (l : Link) : Bool :=
  admit src interval (chainAt l.day) (logOf node l.day) l.day l.spends

/-- The links after the seed. -/
def links : List Link := alternation.filter (·.tx ≠ 1)

/-- Under the withdrawn rule every honest node admits every link it is presented to: no honest
node ever saw two consecutive links, so no log held the coin. -/
@[req "SPN-46"]
theorem perNodeLog_admits_every_link :
    ∀ l ∈ links, ∀ node ∈ l.honest, verdict .perNodeLog node l = true := by decide

/-- Under the chain rule the first link is admitted — `X` is thirty days old — and the second is
refused on EVERY honest node, presented to it or not: `Y` is two days old on the chain they all
read. -/
@[req "SPN-46"]
theorem chainMtp_refuses_second_link :
    links.length = 7 ∧
    (∀ l ∈ links.take 1, ∀ node ∈ [0, 1], verdict .chainMtp node l = true) ∧
    (∀ l ∈ (links.drop 1).take 1, ∀ node ∈ [0, 1], verdict .chainMtp node l = false) := by
  decide

/-! ## `WTC-25`'s bump path

"Without this clause a refresh could never be fee-bumped: its first attempt, resident, would make
its own inputs read as spent on every node." `SPN-46`: "A refresh that is signed but never
confirms leaves no trace on the chain". A node accepted a refresh `R1` over `X` at day 40; it
did not confirm; the higher-fee replacement `R2` over the same `X` is presented at day 41. This
is the ingress half of the bump path, the age; the fire-time half — `WTC-25`'s ordered-outpoints
rule and the walk over the resident — is `Package.lean`'s. -/

@[req "WTC-25"] def bumpDay : Nat := 41
@[req "WTC-25"] def bumpChain : ChainView := { tip := bumpDay, confirmed := [(0, 0)], mtp := fun b => b }
/-- The log after accepting `R1` (transaction `9`) over `X` at day 40. -/
@[req "WTC-25"] def bumpLog : Log := [(40, [0, 9])]

/-- The replacement's verdict under each source. -/
@[req "WTC-25"]
def bumpVerdict (src : Source) : Bool := admit src interval bumpChain bumpLog bumpDay 0

/-- Under the withdrawn rule the replacement is refused for the rest of the interval: the log
holds `X`. -/
@[req "WTC-25"]
theorem perNodeLog_refuses_replacement : bumpVerdict .perNodeLog = false := by decide

end BtcPolicy.RefreshAge
