import BtcPolicy.Encode
import BtcPolicy.Kernel
import BtcPolicy.Delivery
import BtcPolicy.Watchtower
import BtcPolicy.VaultUnspent
import BtcPolicy.Alerts
import BtcPolicy.Package
/-! The language-neutral trace format that `btc-policy-lean` — and any other implementation —
replays against the formal model (`ADR-0023` decision 10 item 8: "implementation trace adapters —
the boundary at which `btc-policy-lean`'s runtime evidence meets the model"). The repository
already owns encoders (`WIR-18`, `Encode.lean`); this is one more codec plus fixtures: a versioned
alphabet that is the union of the events the milestone-8 modules and the kernel step on, each
entry with its explicit mapping to a model input, a kernel entry carrying the effects its step
emitted; `encode` and `decode` in `Encode.lean`'s pattern with the round trip, injectivity and the
length theorem; one published synthetic trace over the kernel alphabet with its verdict decided over
a replay; and the malformed shapes `decode` refuses and the misplaced effect the replay refuses, as
negative exhibits.

**What is not here.** No adapter, runner or collector, no schema and no decoder in any other
language: `ADR-0023` decision 8 says "No implementation, verifier or shadow node ever lives here."
The replay adapter — the code that turns an implementation's runtime evidence into entries of this
alphabet, replays them through the formal layer and compares its own verdict — is implementation
and lives in `btc-policy-lean`, against `15-conformance-checklist.md`'s rows for it.

**Synthetic traces only.** Every trace this repository publishes, and every trace an adapter's
corpus holds, is synthetic: composed from model identifiers, clock samples, flags and counts, never
captured from a node holding a secret. That is the project's rule, stronger than `STO-11`
requires, and it is not attributed to `STO-11`; what `STO-11` requires the alphabet holds by
construction, said on `Entry` below. No `@[req "STO-11"]` declaration exists here: the kernel
checks no proposition about secrets in a trace whose alphabet cannot carry one, and a field list
is not a proposition.

**Widths.** Every model identifier, height, hash, count and clock sample is `u32`; the two satoshi
amounts, `Tx.outflow` and a `Coin`'s value, are `u64`; a flag is `u8`, `0` or `1`; an `Option` is
`u8` `0`, or `u8` `1` and the value; a closed type is one `u8` tag; every list is `list`; no field
is a byte string. A kernel entry carries the effects its step emitted, so the published trace
carries what the kernel must emit on the step that emits it, and the decided verdict is stated
over a replay that refuses an effect on any other step. -/

namespace BtcPolicy.Trace
open BtcPolicy.Encode (Bytes u8 u32 u64 var list le readLE readList
  readLE_le readList_list var_length le_length)
open BtcPolicy.Clocks
open BtcPolicy.Chain (Height Hash Anchor Block View)
open BtcPolicy.Coverage (Coin)

/-! ## The reading side of `WIR-18`'s moves, as this format uses them -/

theorem read32_u32 (v : Nat) (h : v < 256 ^ 4) (r : Bytes) : readLE 4 (u32 v ++ r) = some (v, r) :=
  readLE_le 4 v h r

theorem read64_u64 (v : Nat) (h : v < 256 ^ 8) (r : Bytes) : readLE 8 (u64 v ++ r) = some (v, r) :=
  readLE_le 8 v h r

/-- A `var`-framed item is read whole: `dec` must consume every byte the length prefix framed. -/
def whole {α : Type} (dec : Bytes → Option (α × Bytes)) (bs : Bytes) : Option α :=
  match dec bs with
  | some (x, []) => some x
  | _ => none

/-- Every item of a `list`, each read whole. -/
def decAll {α : Type} (dec : Bytes → Option (α × Bytes)) : List Bytes → Option (List α)
  | [] => some []
  | b :: bs => do
    let x ← whole dec b
    let xs ← decAll dec bs
    pure (x :: xs)

/-- `WIR-18`'s `list` over an item encoder. -/
def encList {α : Type} (enc : α → Bytes) (xs : List α) : Bytes := list (xs.map enc)

def decList {α : Type} (dec : Bytes → Option (α × Bytes)) (bs : Bytes) :
    Option (List α × Bytes) := do
  let (items, bs) ← readList bs
  let xs ← decAll dec items
  pure (xs, bs)

/-- The domain of a `list`: the count under `u32`, and each item well formed and under the
`u32` length prefix `var` gives it. -/
abbrev ListWF {α : Type} (WF : α → Prop) (enc : α → Bytes) (xs : List α) : Prop :=
  xs.length < 256 ^ 4 ∧ ∀ x ∈ xs, WF x ∧ (enc x).length < 256 ^ 4

theorem whole_enc {α : Type} (dec : Bytes → Option (α × Bytes)) (enc : α → Bytes) (x : α)
    (h : ∀ r, dec (enc x ++ r) = some (x, r)) : whole dec (enc x) = some x := by
  have := h []
  simp only [List.append_nil] at this
  simp [whole, this]

theorem decAll_enc {α : Type} (dec : Bytes → Option (α × Bytes)) (enc : α → Bytes) (xs : List α)
    (h : ∀ x ∈ xs, ∀ r, dec (enc x ++ r) = some (x, r)) : decAll dec (xs.map enc) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [decAll, whole_enc dec enc x (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]

theorem decList_encList {α : Type} (dec : Bytes → Option (α × Bytes)) (enc : α → Bytes)
    (WF : α → Prop) (xs : List α) (hw : ListWF WF enc xs)
    (h : ∀ x, WF x → ∀ r, dec (enc x ++ r) = some (x, r)) (rest : Bytes) :
    decList dec (encList enc xs ++ rest) = some (xs, rest) := by
  obtain ⟨hk, hx⟩ := hw
  have hl : ∀ b ∈ xs.map enc, b.length < 256 ^ 4 := by
    intro b hb
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hb
    exact (hx x hx').2
  have hk' : (xs.map enc).length < 256 ^ 4 := by simpa using hk
  simp [decList, encList, readList_list (xs.map enc) hk' hl rest,
    decAll_enc dec enc xs (fun x hx' => h x (hx x hx').1)]

/-- A flag: `u8` `1` or `0`; any other byte is refused. -/
def encBool (b : Bool) : Bytes := u8 (if b then 1 else 0)

def decBool : Bytes → Option (Bool × Bytes)
  | 0 :: bs => some (false, bs)
  | 1 :: bs => some (true, bs)
  | _ => none

theorem decBool_enc (b : Bool) (r : Bytes) : decBool (encBool b ++ r) = some (b, r) := by
  cases b <;> rfl

/-- An `Option`: `u8` `0`, or `u8` `1` and the value. -/
def encOpt {α : Type} (enc : α → Bytes) : Option α → Bytes
  | none => u8 0
  | some x => u8 1 ++ enc x

def decOpt {α : Type} (dec : Bytes → Option (α × Bytes)) : Bytes → Option (Option α × Bytes)
  | 0 :: bs => some (none, bs)
  | 1 :: bs => (dec bs).map fun (x, bs) => (some x, bs)
  | _ => none

theorem decOpt_enc {α : Type} (dec : Bytes → Option (α × Bytes)) (enc : α → Bytes) (o : Option α)
    (h : ∀ x, o = some x → ∀ r, dec (enc x ++ r) = some (x, r)) (r : Bytes) :
    decOpt dec (encOpt enc o ++ r) = some (o, r) := by
  cases o with
  | none => rfl
  | some x => simp [encOpt, decOpt, u8, h x rfl r]

/-! ## Integers, pairs, coins -/

abbrev NatsWF (xs : List Nat) : Prop := ListWF (· < 256 ^ 4) u32 xs

theorem decList_u32 (xs : List Nat) (h : NatsWF xs) (r : Bytes) :
    decList (readLE 4) (encList u32 xs ++ r) = some (xs, r) :=
  decList_encList (readLE 4) u32 (· < 256 ^ 4) xs h (fun x hx r => read32_u32 x hx r) r

abbrev OptNatWF (o : Option Nat) : Prop := ∀ n, o = some n → n < 256 ^ 4

theorem decOpt_u32 (o : Option Nat) (h : OptNatWF o) (r : Bytes) :
    decOpt (readLE 4) (encOpt u32 o ++ r) = some (o, r) :=
  decOpt_enc (readLE 4) u32 o (fun n hn r => read32_u32 n (h n hn) r) r

/-- Two identifiers: a sighash message `(tx, input)` or an outpoint `(txid, vout)`. -/
def encPair (p : Nat × Nat) : Bytes := u32 p.1 ++ u32 p.2

def decPair (bs : Bytes) : Option ((Nat × Nat) × Bytes) := do
  let (a, bs) ← readLE 4 bs
  let (b, bs) ← readLE 4 bs
  pure ((a, b), bs)

abbrev PairWF (p : Nat × Nat) : Prop := p.1 < 256 ^ 4 ∧ p.2 < 256 ^ 4

theorem decPair_enc (p : Nat × Nat) (h : PairWF p) (r : Bytes) :
    decPair (encPair p ++ r) = some (p, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decPair, encPair, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2]

/-- A `Coverage.Coin`: the outpoint and its `witness_utxo` value in satoshis. -/
def encCoin (c : Coin) : Bytes := u32 c.1 ++ u64 c.2

def decCoin (bs : Bytes) : Option (Coin × Bytes) := do
  let (o, bs) ← readLE 4 bs
  let (v, bs) ← readLE 8 bs
  pure ((o, v), bs)

abbrev CoinWF (c : Coin) : Prop := c.1 < 256 ^ 4 ∧ c.2 < 256 ^ 8

theorem decCoin_enc (c : Coin) (h : CoinWF c) (r : Bytes) : decCoin (encCoin c ++ r) = some (c, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decCoin, encCoin, List.append_assoc, read32_u32 _ h1, read64_u64 _ h2]

theorem decList_coin (xs : List Coin) (h : ListWF CoinWF encCoin xs) (r : Bytes) :
    decList decCoin (encList encCoin xs ++ r) = some (xs, r) :=
  decList_encList decCoin encCoin CoinWF xs h decCoin_enc r

/-! ## The kernel alphabet (`Kernel.Env × Kernel.Event`, `Kernel.Effect`) -/

/-- `Kernel.Tx` as it stands: `id`, `inputs`, `outflow`. -/
def encTx (t : Kernel.Tx) : Bytes := u32 t.id ++ encList u32 t.inputs ++ u64 t.outflow

def decTx (bs : Bytes) : Option (Kernel.Tx × Bytes) := do
  let (id, bs) ← readLE 4 bs
  let (inputs, bs) ← decList (readLE 4) bs
  let (outflow, bs) ← readLE 8 bs
  pure ({ id, inputs, outflow }, bs)

abbrev TxWF (t : Kernel.Tx) : Prop := t.id < 256 ^ 4 ∧ NatsWF t.inputs ∧ t.outflow < 256 ^ 8

theorem decTx_enc (t : Kernel.Tx) (h : TxWF t) (r : Bytes) : decTx (encTx t ++ r) = some (t, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decTx, encTx, List.append_assoc, read32_u32 _ h1, decList_u32 _ h2, read64_u64 _ h3]

theorem decList_tx (xs : List Kernel.Tx) (h : ListWF TxWF encTx xs) (r : Bytes) :
    decList decTx (encList encTx xs ++ r) = some (xs, r) :=
  decList_encList decTx encTx TxWF xs h decTx_enc r

/-- Candidate input to a kernel acceptance, with wall instants as raw samples. `toKernel`
applies `Wall.sample` and leaves the registration-owned pair identity absent: `Kernel.register`
derives role and sibling from the two request positions, never from input metadata. This is not
a codec for resident candidate snapshots. Pair registration changes no field of this candidate
input layout; the event alphabet's version is recorded below.
`Entry` owns what an entry carries beside a candidate. -/
structure Cand where
  id : Nat
  tx : Kernel.Tx
  hot : Bool
  quorum : Bool
  frozen : Bool
  terminal : Bool
  settled : Bool
  broadcast : Bool
  released : Bool
  packageOk : Bool
  heldSigners : List Nat
  fireAt : Option Nat
  windowClose : Option Nat
  expiry : Nat
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Cand.toKernel (c : Cand) : Kernel.Cand :=
  { id := c.id, tx := c.tx, hot := c.hot, quorum := c.quorum, frozen := c.frozen,
    terminal := c.terminal, settled := c.settled, broadcast := c.broadcast, released := c.released,
    packageOk := c.packageOk, heldSigners := c.heldSigners, fireAt := c.fireAt.map Wall.sample,
    windowClose := c.windowClose.map Wall.sample, expiry := Wall.sample c.expiry, pair := none }

def encCand (c : Cand) : Bytes :=
  u32 c.id ++ encTx c.tx ++ encBool c.hot ++ encBool c.quorum ++ encBool c.frozen ++
  encBool c.terminal ++ encBool c.settled ++ encBool c.broadcast ++ encBool c.released ++
  encBool c.packageOk ++ encList u32 c.heldSigners ++ encOpt u32 c.fireAt ++
  encOpt u32 c.windowClose ++ u32 c.expiry

def decCand (bs : Bytes) : Option (Cand × Bytes) := do
  let (id, bs) ← readLE 4 bs
  let (tx, bs) ← decTx bs
  let (hot, bs) ← decBool bs
  let (quorum, bs) ← decBool bs
  let (frozen, bs) ← decBool bs
  let (terminal, bs) ← decBool bs
  let (settled, bs) ← decBool bs
  let (broadcast, bs) ← decBool bs
  let (released, bs) ← decBool bs
  let (packageOk, bs) ← decBool bs
  let (heldSigners, bs) ← decList (readLE 4) bs
  let (fireAt, bs) ← decOpt (readLE 4) bs
  let (windowClose, bs) ← decOpt (readLE 4) bs
  let (expiry, bs) ← readLE 4 bs
  pure ({ id, tx, hot, quorum, frozen, terminal, settled, broadcast, released, packageOk,
          heldSigners, fireAt, windowClose, expiry }, bs)

abbrev CandWF (c : Cand) : Prop :=
  c.id < 256 ^ 4 ∧ TxWF c.tx ∧ NatsWF c.heldSigners ∧ OptNatWF c.fireAt ∧
  OptNatWF c.windowClose ∧ c.expiry < 256 ^ 4

theorem decCand_enc (c : Cand) (h : CandWF c) (r : Bytes) : decCand (encCand c ++ r) = some (c, r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp [decCand, encCand, List.append_assoc, read32_u32 _ h1, decTx_enc _ h2, decBool_enc,
    decList_u32 _ h3, decOpt_u32 _ h4, decOpt_u32 _ h5, read32_u32 _ h6]

/-- `Kernel.Env`, with each clock sample raw and the chain view flattened: `wall`, `hw`, `mono`,
`chain.mtp` and `chain.seen`. `Ledger.envOf` is the precedent for an environment built from raw
samples. -/
structure Env where
  wall : Nat
  hw : Nat
  mono : Nat
  mtp : Nat
  seen : List Kernel.Tx
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Env.toKernel (e : Env) : Kernel.Env :=
  { wall := Wall.sample e.wall, hw := HighWater.sample e.hw, mono := Mono.sample e.mono,
    chain := { mtp := Mtp.sample e.mtp, seen := e.seen } }

def encEnv (e : Env) : Bytes :=
  u32 e.wall ++ u32 e.hw ++ u32 e.mono ++ u32 e.mtp ++ encList encTx e.seen

def decEnv (bs : Bytes) : Option (Env × Bytes) := do
  let (wall, bs) ← readLE 4 bs
  let (hw, bs) ← readLE 4 bs
  let (mono, bs) ← readLE 4 bs
  let (mtp, bs) ← readLE 4 bs
  let (seen, bs) ← decList decTx bs
  pure ({ wall, hw, mono, mtp, seen }, bs)

abbrev EnvWF (e : Env) : Prop :=
  e.wall < 256 ^ 4 ∧ e.hw < 256 ^ 4 ∧ e.mono < 256 ^ 4 ∧ e.mtp < 256 ^ 4 ∧ ListWF TxWF encTx e.seen

theorem decEnv_enc (e : Env) (h : EnvWF e) (r : Bytes) : decEnv (encEnv e ++ r) = some (e, r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp [decEnv, encEnv, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2, read32_u32 _ h3,
    read32_u32 _ h4, decList_tx _ h5]

/-- Refusal codes use `Policy.Code.all`'s order, with an unknown tag refused. -/
def encCode (code : Policy.Code) : Bytes := u8 (Policy.Code.all.idxOf code)
def decCode : Bytes → Option (Policy.Code × Bytes)
  | tag :: rest => (Policy.Code.all[tag]?).map fun code => (code, rest)
  | [] => none

theorem decCode_enc (code : Policy.Code) (rest : Bytes) :
    decCode (encCode code ++ rest) = some (code, rest) := by
  cases code <;> rfl

/-- `Kernel.Event`, constructor for constructor, with `accept`'s `E` a raw sample and its two
candidates the record above. -/
inductive KernelEvent
  | accept (cid : Nat) (duress : Bool) (E : Nat) (spend escape : Cand)
  | refuse (cid : Nat) (duress : Bool) (E : Nat) (pair : Option (Nat × Nat))
      (code : Policy.Code := .BAD_PIN)
  | receipt (cid sender : Nat)
  | firePass
  | packageAccepted (cand : Nat)
  | send (cand : Nat)
  | settle (tx : Kernel.Tx)
  | prune
  | tick
  | panic
  | adversaryExposes (msg : Nat × Nat) (input signer cid : Nat)
  | receivePartial (msg : Nat × Nat) (input signer cid : Nat)
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def KernelEvent.toKernel : KernelEvent → Kernel.Event
  | .accept cid d E sp es => .accept cid d (Wall.sample E) sp.toKernel es.toKernel
  | .refuse cid d E pair code => .refuse cid d (Wall.sample E) pair code
  | .receipt cid s => .receipt cid s
  | .firePass => .firePass
  | .packageAccepted c => .packageAccepted c
  | .send c => .send c
  | .settle tx => .settle tx
  | .prune => .prune
  | .tick => .tick
  | .panic => .panic
  | .adversaryExposes m i s c => .adversaryExposes m i s c
  | .receivePartial m i s c => .receivePartial m i s c

def encKernelEvent : KernelEvent → Bytes
  | .accept cid d E sp es => u8 1 ++ u32 cid ++ encBool d ++ u32 E ++ encCand sp ++ encCand es
  | .refuse cid d E pair code =>
    u8 12 ++ u32 cid ++ encBool d ++ u32 E ++ encOpt encPair pair ++ encCode code
  | .receipt cid s => u8 2 ++ u32 cid ++ u32 s
  | .firePass => u8 3
  | .packageAccepted c => u8 4 ++ u32 c
  | .send c => u8 5 ++ u32 c
  | .settle tx => u8 6 ++ encTx tx
  | .prune => u8 7
  | .tick => u8 8
  | .panic => u8 9
  | .adversaryExposes m i s c => u8 10 ++ encPair m ++ u32 i ++ u32 s ++ u32 c
  | .receivePartial m i s c => u8 11 ++ encPair m ++ u32 i ++ u32 s ++ u32 c

def decKernelEvent : Bytes → Option (KernelEvent × Bytes)
  | 1 :: bs => do
    let (cid, bs) ← readLE 4 bs
    let (d, bs) ← decBool bs
    let (E, bs) ← readLE 4 bs
    let (sp, bs) ← decCand bs
    let (es, bs) ← decCand bs
    pure (.accept cid d E sp es, bs)
  | 2 :: bs => do
    let (cid, bs) ← readLE 4 bs
    let (s, bs) ← readLE 4 bs
    pure (.receipt cid s, bs)
  | 3 :: bs => some (.firePass, bs)
  | 4 :: bs => (readLE 4 bs).map fun (c, bs) => (.packageAccepted c, bs)
  | 5 :: bs => (readLE 4 bs).map fun (c, bs) => (.send c, bs)
  | 6 :: bs => (decTx bs).map fun (tx, bs) => (.settle tx, bs)
  | 7 :: bs => some (.prune, bs)
  | 8 :: bs => some (.tick, bs)
  | 9 :: bs => some (.panic, bs)
  | 10 :: bs => do
    let (m, bs) ← decPair bs
    let (i, bs) ← readLE 4 bs
    let (s, bs) ← readLE 4 bs
    let (c, bs) ← readLE 4 bs
    pure (.adversaryExposes m i s c, bs)
  | 11 :: bs => do
    let (m, bs) ← decPair bs
    let (i, bs) ← readLE 4 bs
    let (s, bs) ← readLE 4 bs
    let (c, bs) ← readLE 4 bs
    pure (.receivePartial m i s c, bs)
  | 12 :: bs => do
    let (cid, bs) ← readLE 4 bs
    let (d, bs) ← decBool bs
    let (E, bs) ← readLE 4 bs
    let (pair, bs) ← decOpt decPair bs
    let (code, bs) ← decCode bs
    pure (.refuse cid d E pair code, bs)
  | _ => none

def KernelEvent.WF : KernelEvent → Prop
  | .accept cid _ E sp es => cid < 256 ^ 4 ∧ E < 256 ^ 4 ∧ CandWF sp ∧ CandWF es
  | .refuse cid _ E pair _ => cid < 256 ^ 4 ∧ E < 256 ^ 4 ∧ ∀ p, pair = some p → PairWF p
  | .receipt cid s => cid < 256 ^ 4 ∧ s < 256 ^ 4
  | .firePass => True
  | .packageAccepted c => c < 256 ^ 4
  | .send c => c < 256 ^ 4
  | .settle tx => TxWF tx
  | .prune => True
  | .tick => True
  | .panic => True
  | .adversaryExposes m i s c => PairWF m ∧ i < 256 ^ 4 ∧ s < 256 ^ 4 ∧ c < 256 ^ 4
  | .receivePartial m i s c => PairWF m ∧ i < 256 ^ 4 ∧ s < 256 ^ 4 ∧ c < 256 ^ 4

theorem decKernelEvent_enc (ev : KernelEvent) (h : ev.WF) (r : Bytes) :
    decKernelEvent (encKernelEvent ev ++ r) = some (ev, r) := by
  cases ev with
  | accept cid d E sp es =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [encKernelEvent, decKernelEvent, u8, List.append_assoc, read32_u32 _ h1, decBool_enc,
      read32_u32 _ h2, decCand_enc _ h3, decCand_enc _ h4]
  | refuse cid d E pair code =>
    obtain ⟨h1, h2, hp⟩ := h
    have hpair := decOpt_enc decPair encPair pair (fun p he r => decPair_enc p (hp p he) r)
    simp [encKernelEvent, decKernelEvent, u8, List.append_assoc, read32_u32 _ h1,
      decBool_enc, read32_u32 _ h2, hpair, decCode_enc]
  | receipt cid s =>
    obtain ⟨h1, h2⟩ := h
    simp [encKernelEvent, decKernelEvent, u8, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2]
  | firePass => simp [encKernelEvent, decKernelEvent, u8]
  | packageAccepted c =>
    simp [encKernelEvent, decKernelEvent, u8, read32_u32 _ h]
  | send c => simp [encKernelEvent, decKernelEvent, u8, read32_u32 _ h]
  | settle tx => simp [encKernelEvent, decKernelEvent, u8, decTx_enc _ h]
  | prune => simp [encKernelEvent, decKernelEvent, u8]
  | tick => simp [encKernelEvent, decKernelEvent, u8]
  | panic => simp [encKernelEvent, decKernelEvent, u8]
  | adversaryExposes m i s c =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [encKernelEvent, decKernelEvent, u8, List.append_assoc, decPair_enc _ h1,
      read32_u32 _ h2, read32_u32 _ h3, read32_u32 _ h4]
  | receivePartial m i s c =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [encKernelEvent, decKernelEvent, u8, List.append_assoc, decPair_enc _ h1,
      read32_u32 _ h2, read32_u32 _ h3, read32_u32 _ h4]

/-- `Kernel.Effect` as it stands: it carries only identifiers and a flag, so the trace holds the
kernel's own type. -/
def encEffect : Kernel.Effect → Bytes
  | .queuePartial m i h c => u8 1 ++ encPair m ++ u32 i ++ encBool h ++ u32 c
  | .broadcast tx => u8 2 ++ u32 tx

def decEffect : Bytes → Option (Kernel.Effect × Bytes)
  | 1 :: bs => do
    let (m, bs) ← decPair bs
    let (i, bs) ← readLE 4 bs
    let (h, bs) ← decBool bs
    let (c, bs) ← readLE 4 bs
    pure (.queuePartial m i h c, bs)
  | 2 :: bs => (readLE 4 bs).map fun (tx, bs) => (.broadcast tx, bs)
  | _ => none

def EffectWF : Kernel.Effect → Prop
  | .queuePartial m i _ c => PairWF m ∧ i < 256 ^ 4 ∧ c < 256 ^ 4
  | .broadcast tx => tx < 256 ^ 4

theorem decEffect_enc (e : Kernel.Effect) (h : EffectWF e) (r : Bytes) :
    decEffect (encEffect e ++ r) = some (e, r) := by
  cases e with
  | queuePartial m i hot c =>
    obtain ⟨h1, h2, h3⟩ := h
    simp [encEffect, decEffect, u8, List.append_assoc, decPair_enc _ h1, read32_u32 _ h2,
      decBool_enc, read32_u32 _ h3]
  | broadcast tx => simp [encEffect, decEffect, u8, read32_u32 _ h]

theorem decList_effect (xs : List Kernel.Effect) (h : ListWF EffectWF encEffect xs) (r : Bytes) :
    decList decEffect (encList encEffect xs ++ r) = some (xs, r) :=
  decList_encList decEffect encEffect EffectWF xs h decEffect_enc r

/-! ## The delivery alphabet (`Delivery.Outcome`) -/

/-- `Delivery.Failure`, one tag each, in declaration order. -/
def encFailure : Delivery.Failure → Bytes
  | .timeout => u8 1
  | .partialWrite => u8 2
  | .read => u8 3
  | .framing => u8 4
  | .capCrossed => u8 5

def decFailure : Bytes → Option (Delivery.Failure × Bytes)
  | 1 :: bs => some (.timeout, bs)
  | 2 :: bs => some (.partialWrite, bs)
  | 3 :: bs => some (.read, bs)
  | 4 :: bs => some (.framing, bs)
  | 5 :: bs => some (.capCrossed, bs)
  | _ => none

theorem decFailure_enc (f : Delivery.Failure) (r : Bytes) : decFailure (encFailure f ++ r) = some (f, r) := by
  cases f <;> rfl

/-- `Delivery.Outcome`, constructor for constructor; it too carries only identifiers. -/
def encOutcome : Delivery.Outcome → Bytes
  | .notSent => u8 1
  | .accepted cid => u8 2 ++ u32 cid
  | .nonceReplayed => u8 3
  | .badRequest => u8 4
  | .tooLarge => u8 5
  | .otherStatus code => u8 6 ++ u32 code
  | .failed f => u8 7 ++ encFailure f

def decOutcome : Bytes → Option (Delivery.Outcome × Bytes)
  | 1 :: bs => some (.notSent, bs)
  | 2 :: bs => (readLE 4 bs).map fun (cid, bs) => (.accepted cid, bs)
  | 3 :: bs => some (.nonceReplayed, bs)
  | 4 :: bs => some (.badRequest, bs)
  | 5 :: bs => some (.tooLarge, bs)
  | 6 :: bs => (readLE 4 bs).map fun (code, bs) => (.otherStatus code, bs)
  | 7 :: bs => (decFailure bs).map fun (f, bs) => (.failed f, bs)
  | _ => none

def OutcomeWF : Delivery.Outcome → Prop
  | .accepted cid => cid < 256 ^ 4
  | .otherStatus code => code < 256 ^ 4
  | _ => True

theorem decOutcome_enc (o : Delivery.Outcome) (h : OutcomeWF o) (r : Bytes) :
    decOutcome (encOutcome o ++ r) = some (o, r) := by
  cases o with
  | accepted cid => simp [encOutcome, decOutcome, u8, read32_u32 _ h]
  | otherStatus code => simp [encOutcome, decOutcome, u8, read32_u32 _ h]
  | failed f => simp [encOutcome, decOutcome, u8, decFailure_enc]
  | _ => rfl

theorem decList_outcome (xs : List Delivery.Outcome) (h : ListWF OutcomeWF encOutcome xs) (r : Bytes) :
    decList decOutcome (encList encOutcome xs ++ r) = some (xs, r) :=
  decList_encList decOutcome encOutcome OutcomeWF xs h decOutcome_enc r

/-! ## The chain alphabet (`Chain.View`, `Watchtower.Scan`, `Watchtower.Outcome`) -/

/-- `Chain.Anchor`: `height`, `hash`. -/
def encAnchor (a : Anchor) : Bytes := u32 a.height ++ u32 a.hash

def decAnchor (bs : Bytes) : Option (Anchor × Bytes) := do
  let (height, bs) ← readLE 4 bs
  let (hash, bs) ← readLE 4 bs
  pure ({ height, hash }, bs)

abbrev AnchorWF (a : Anchor) : Prop := a.height < 256 ^ 4 ∧ a.hash < 256 ^ 4

theorem decAnchor_enc (a : Anchor) (h : AnchorWF a) (r : Bytes) : decAnchor (encAnchor a ++ r) = some (a, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decAnchor, encAnchor, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2]

theorem decList_anchor (xs : List Anchor) (h : ListWF AnchorWF encAnchor xs) (r : Bytes) :
    decList decAnchor (encList encAnchor xs ++ r) = some (xs, r) :=
  decList_encList decAnchor encAnchor AnchorWF xs h decAnchor_enc r

/-- `Chain.Block`: `height`, `hash`, `prev`. -/
def encBlock (b : Block) : Bytes := u32 b.height ++ u32 b.hash ++ u32 b.prev

def decBlock (bs : Bytes) : Option (Block × Bytes) := do
  let (height, bs) ← readLE 4 bs
  let (hash, bs) ← readLE 4 bs
  let (prev, bs) ← readLE 4 bs
  pure ({ height, hash, prev }, bs)

abbrev BlockWF (b : Block) : Prop := b.height < 256 ^ 4 ∧ b.hash < 256 ^ 4 ∧ b.prev < 256 ^ 4

theorem decBlock_enc (b : Block) (h : BlockWF b) (r : Bytes) : decBlock (encBlock b ++ r) = some (b, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decBlock, encBlock, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2, read32_u32 _ h3]

theorem decList_block (xs : List Block) (h : ListWF BlockWF encBlock xs) (r : Bytes) :
    decList decBlock (encList encBlock xs ++ r) = some (xs, r) :=
  decList_encList decBlock encBlock BlockWF xs h decBlock_enc r

/-- A chain view is carried as the hashes by height, `Watchtower.chainOf`'s argument: `View.activeAt`
is a function, and `chainOf` is the mapping that states the value outside the list, `none`. -/
abbrev Hashes := List Hash

/-- `Watchtower.Scan`, with its view after the loop as hashes. `Watchtower.Scan` and
`Watchtower.Outcome` derive nothing, because a `View` is a function; the trace's records do. -/
structure Scan where
  blocks : List Block
  spends : List Nat
  after : Hashes
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Scan.toWatchtower (s : Scan) : Watchtower.Scan :=
  { blocks := s.blocks, spends := s.spends, after := Watchtower.chainOf s.after }

def encScan (s : Scan) : Bytes := encList encBlock s.blocks ++ encList u32 s.spends ++ encList u32 s.after

def decScan (bs : Bytes) : Option (Scan × Bytes) := do
  let (blocks, bs) ← decList decBlock bs
  let (spends, bs) ← decList (readLE 4) bs
  let (after, bs) ← decList (readLE 4) bs
  pure ({ blocks, spends, after }, bs)

abbrev ScanWF (s : Scan) : Prop := ListWF BlockWF encBlock s.blocks ∧ NatsWF s.spends ∧ NatsWF s.after

theorem decScan_enc (s : Scan) (h : ScanWF s) (r : Bytes) : decScan (encScan s ++ r) = some (s, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decScan, encScan, List.append_assoc, decList_block _ h1, decList_u32 _ h2, decList_u32 _ h3]

/-- `Watchtower.Outcome`, constructor for constructor. -/
inductive WatchOutcome
  | scanned (s : Scan)
  | errored
  | panicked
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def WatchOutcome.toWatchtower : WatchOutcome → Watchtower.Outcome
  | .scanned s => .scanned s.toWatchtower
  | .errored => .errored
  | .panicked => .panicked

def encWatchOutcome : WatchOutcome → Bytes
  | .scanned s => u8 1 ++ encScan s
  | .errored => u8 2
  | .panicked => u8 3

def decWatchOutcome : Bytes → Option (WatchOutcome × Bytes)
  | 1 :: bs => (decScan bs).map fun (s, bs) => (.scanned s, bs)
  | 2 :: bs => some (.errored, bs)
  | 3 :: bs => some (.panicked, bs)
  | _ => none

def WatchOutcome.WF : WatchOutcome → Prop
  | .scanned s => ScanWF s
  | _ => True

theorem decWatchOutcome_enc (o : WatchOutcome) (h : o.WF) (r : Bytes) :
    decWatchOutcome (encWatchOutcome o ++ r) = some (o, r) := by
  cases o with
  | scanned s => simp [encWatchOutcome, decWatchOutcome, u8, decScan_enc _ h]
  | _ => rfl

/-- `Watchtower.Cursor`: `anchors`, `next`. -/
def encCursor (c : Watchtower.Cursor) : Bytes := encList encAnchor c.anchors ++ u32 c.next

def decCursor (bs : Bytes) : Option (Watchtower.Cursor × Bytes) := do
  let (anchors, bs) ← decList decAnchor bs
  let (next, bs) ← readLE 4 bs
  pure ({ anchors, next }, bs)

abbrev CursorWF (c : Watchtower.Cursor) : Prop := ListWF AnchorWF encAnchor c.anchors ∧ c.next < 256 ^ 4

theorem decCursor_enc (c : Watchtower.Cursor) (h : CursorWF c) (r : Bytes) :
    decCursor (encCursor c ++ r) = some (c, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decCursor, encCursor, List.append_assoc, decList_anchor _ h1, read32_u32 _ h2]

/-! ## The vault-unspent alphabet (`VaultUnspent.serve`, `repair`, `endAsFailure`, `attempt`) -/

/-- One vault output a block spent, with the height of the block that created it (`WTC-7`). -/
def encSpentCoin (p : Height × Coin) : Bytes := u32 p.1 ++ encCoin p.2

def decSpentCoin (bs : Bytes) : Option ((Height × Coin) × Bytes) := do
  let (height, bs) ← readLE 4 bs
  let (coin, bs) ← decCoin bs
  pure ((height, coin), bs)

abbrev SpentCoinWF (p : Height × Coin) : Prop := p.1 < 256 ^ 4 ∧ CoinWF p.2

theorem decSpentCoin_enc (x : Height × Coin) (h : SpentCoinWF x) (r : Bytes) :
    decSpentCoin (encSpentCoin x ++ r) = some (x, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decSpentCoin, encSpentCoin, List.append_assoc, read32_u32 _ h1, decCoin_enc _ h2]

theorem decList_spentCoin (xs : List (Height × Coin)) (h : ListWF SpentCoinWF encSpentCoin xs)
    (r : Bytes) : decList decSpentCoin (encList encSpentCoin xs ++ r) = some (xs, r) :=
  decList_encList decSpentCoin encSpentCoin SpentCoinWF xs h decSpentCoin_enc r

/-- One row of a `VaultUnspent.Ledger`: the vault outputs the block with this hash at this height
creates, and the ones it spends. The ledger is a pair of functions; `ledgerOf` states the value
outside the list, `[]`. -/
structure LedgerRow where
  height : Height
  hash : Hash
  vaultOutputs : List Coin
  vaultSpends : List (Height × Coin)
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def ledgerOf (rows : List LedgerRow) : VaultUnspent.Ledger :=
  { vaultOutputs := fun h hash =>
      ((rows.find? fun r => r.height == h && r.hash == hash).map (·.vaultOutputs)).getD [],
    vaultSpends := fun h hash =>
      ((rows.find? fun r => r.height == h && r.hash == hash).map (·.vaultSpends)).getD [] }

def encLedgerRow (r : LedgerRow) : Bytes :=
  u32 r.height ++ u32 r.hash ++ encList encCoin r.vaultOutputs ++ encList encSpentCoin r.vaultSpends

def decLedgerRow (bs : Bytes) : Option (LedgerRow × Bytes) := do
  let (height, bs) ← readLE 4 bs
  let (hash, bs) ← readLE 4 bs
  let (vaultOutputs, bs) ← decList decCoin bs
  let (vaultSpends, bs) ← decList decSpentCoin bs
  pure ({ height, hash, vaultOutputs, vaultSpends }, bs)

abbrev LedgerRowWF (r : LedgerRow) : Prop :=
  r.height < 256 ^ 4 ∧ r.hash < 256 ^ 4 ∧ ListWF CoinWF encCoin r.vaultOutputs ∧
    ListWF SpentCoinWF encSpentCoin r.vaultSpends

theorem decLedgerRow_enc (x : LedgerRow) (h : LedgerRowWF x) (r : Bytes) :
    decLedgerRow (encLedgerRow x ++ r) = some (x, r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [decLedgerRow, encLedgerRow, List.append_assoc, read32_u32 _ h1, read32_u32 _ h2,
    decList_coin _ h3, decList_spentCoin _ h4]

theorem decList_ledger (xs : List LedgerRow) (h : ListWF LedgerRowWF encLedgerRow xs) (r : Bytes) :
    decList decLedgerRow (encList encLedgerRow xs ++ r) = some (xs, r) :=
  decList_encList decLedgerRow encLedgerRow LedgerRowWF xs h decLedgerRow_enc r

/-- `VaultUnspent.Cache`: `outputs`, `anchor`. -/
def encCache (c : VaultUnspent.Cache) : Bytes := encList encCoin c.outputs ++ encAnchor c.anchor

def decCache (bs : Bytes) : Option (VaultUnspent.Cache × Bytes) := do
  let (outputs, bs) ← decList decCoin bs
  let (anchor, bs) ← decAnchor bs
  pure ({ outputs, anchor }, bs)

abbrev CacheWF (c : VaultUnspent.Cache) : Prop := ListWF CoinWF encCoin c.outputs ∧ AnchorWF c.anchor

theorem decCache_enc (c : VaultUnspent.Cache) (h : CacheWF c) (r : Bytes) :
    decCache (encCache c ++ r) = some (c, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decCache, encCache, List.append_assoc, decList_coin _ h1, decAnchor_enc _ h2]

abbrev OptCacheWF (o : Option VaultUnspent.Cache) : Prop := ∀ c, o = some c → CacheWF c

theorem decOpt_cache (o : Option VaultUnspent.Cache) (h : OptCacheWF o) (r : Bytes) :
    decOpt decCache (encOpt encCache o ++ r) = some (o, r) :=
  decOpt_enc decCache encCache o (fun c hc r => decCache_enc c (h c hc) r) r

/-- `VaultUnspent.Marker`: `anchor`, `birthday` (`WTC-8`). -/
def encMarker (m : VaultUnspent.Marker) : Bytes := encAnchor m.anchor ++ u32 m.birthday

def decMarker (bs : Bytes) : Option (VaultUnspent.Marker × Bytes) := do
  let (anchor, bs) ← decAnchor bs
  let (birthday, bs) ← readLE 4 bs
  pure ({ anchor, birthday }, bs)

abbrev MarkerWF (m : VaultUnspent.Marker) : Prop := AnchorWF m.anchor ∧ m.birthday < 256 ^ 4

theorem decMarker_enc (m : VaultUnspent.Marker) (h : MarkerWF m) (r : Bytes) :
    decMarker (encMarker m ++ r) = some (m, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decMarker, encMarker, List.append_assoc, decAnchor_enc _ h1, read32_u32 _ h2]

theorem decList_marker (xs : List VaultUnspent.Marker) (h : ListWF MarkerWF encMarker xs)
    (r : Bytes) : decList decMarker (encList encMarker xs ++ r) = some (xs, r) :=
  decList_encList decMarker encMarker MarkerWF xs h decMarker_enc r

/-- `VaultUnspent.Wallet`: `privateKeysDisabled`, `birthday`, `markers`,
`holdsEveryVaultDescriptor`. -/
def encWallet (w : VaultUnspent.Wallet) : Bytes :=
  encBool w.privateKeysDisabled ++ u32 w.birthday ++ encList encMarker w.markers ++
    encBool w.holdsEveryVaultDescriptor

def decWallet (bs : Bytes) : Option (VaultUnspent.Wallet × Bytes) := do
  let (privateKeysDisabled, bs) ← decBool bs
  let (birthday, bs) ← readLE 4 bs
  let (markers, bs) ← decList decMarker bs
  let (holdsEveryVaultDescriptor, bs) ← decBool bs
  pure ({ privateKeysDisabled, birthday, markers, holdsEveryVaultDescriptor }, bs)

abbrev WalletWF (w : VaultUnspent.Wallet) : Prop :=
  w.birthday < 256 ^ 4 ∧ ListWF MarkerWF encMarker w.markers

theorem decWallet_enc (w : VaultUnspent.Wallet) (h : WalletWF w) (r : Bytes) :
    decWallet (encWallet w ++ r) = some (w, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decWallet, encWallet, List.append_assoc, decBool_enc, read32_u32 _ h1, decList_marker _ h2]

/-- `VaultUnspent.State`: `wallet`, `latched`, `scanned`, `repairScan`, `cache` (`WTC-9`). The cold
scan the attempt in progress started from is an `Option` of the cache's own layout. -/
def encState (st : VaultUnspent.State) : Bytes :=
  encWallet st.wallet ++ encBool st.latched ++ encBool st.scanned ++
    encOpt encCache st.repairScan ++ encOpt encCache st.cache

def decState (bs : Bytes) : Option (VaultUnspent.State × Bytes) := do
  let (wallet, bs) ← decWallet bs
  let (latched, bs) ← decBool bs
  let (scanned, bs) ← decBool bs
  let (repairScan, bs) ← decOpt decCache bs
  let (cache, bs) ← decOpt decCache bs
  pure ({ wallet, latched, scanned, repairScan, cache }, bs)

abbrev StateWF (st : VaultUnspent.State) : Prop :=
  WalletWF st.wallet ∧ OptCacheWF st.repairScan ∧ OptCacheWF st.cache

theorem decState_enc (st : VaultUnspent.State) (h : StateWF st) (r : Bytes) :
    decState (encState st ++ r) = some (st, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decState, encState, List.append_assoc, decWallet_enc _ h1, decBool_enc, decOpt_cache _ h2,
    decOpt_cache _ h3]

/-- `VaultUnspent.Snapshot`: `tip`, `sequence`, `read`. -/
def encSnapshot (s : VaultUnspent.Snapshot) : Bytes := encAnchor s.tip ++ u32 s.sequence ++ encList encCoin s.read

def decSnapshot (bs : Bytes) : Option (VaultUnspent.Snapshot × Bytes) := do
  let (tip, bs) ← decAnchor bs
  let (sequence, bs) ← readLE 4 bs
  let (read, bs) ← decList decCoin bs
  pure ({ tip, sequence, read }, bs)

abbrev SnapshotWF (s : VaultUnspent.Snapshot) : Prop :=
  AnchorWF s.tip ∧ s.sequence < 256 ^ 4 ∧ ListWF CoinWF encCoin s.read

theorem decSnapshot_enc (s : VaultUnspent.Snapshot) (h : SnapshotWF s) (r : Bytes) :
    decSnapshot (encSnapshot s ++ r) = some (s, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decSnapshot, encSnapshot, List.append_assoc, decAnchor_enc _ h1, read32_u32 _ h2, decList_coin _ h3]

/-- `VaultUnspent.attempt`'s `keep` is a predicate; the trace carries the coins it keeps, and the
mapping states the value outside the list, `false`. -/
@[req "ADR-0023"]
def keepOf (kept : List Coin) : Coin → Bool := (kept.contains ·)

/-! ## The recognition alphabet (`Alerts.duty`) -/

/-- What `Alerts.classify` reads of a witness: the class `Alerts.selector` yields. `CHN-9`: "The
selector is the second-to-last element: a single `0x01` byte for the Normal (`OP_IF`) branch, an
**empty** push for the Recovery (`OP_ELSE`) branch"; `WTC-19`: "A witness with fewer than two
elements reads as non-recovery". The trace carries the class and never the stack: a `List Bytes`
field is an unrestricted carrier whatever its docstring says, and the class is all the model reads
of it. What the replay therefore does not check is the implementation's own reading of the
selector from a real witness (`CHN-9`); that reading is the adapter's, and
`15-conformance-checklist.md`'s row for the adapter says so. -/
@[req "ADR-0023"]
inductive WitnessClass
  /-- The empty push: the Recovery branch. -/
  | recovery
  /-- The single `0x01` byte: the Normal branch. -/
  | normal
  /-- A selector `CHN-9` names for neither branch. -/
  | other
  /-- A stack with fewer than two elements: no selector. -/
  | short
  deriving DecidableEq, Repr

/-- The class's reading: Recovery for `recovery` and nothing else. -/
@[req "ADR-0023"]
def WitnessClass.isRecovery : WitnessClass → Bool
  | .recovery => true
  | _ => false

/-- A witness whose selector, `0x02`, is a byte `CHN-9` names for neither branch. -/
@[req "ADR-0023"]
def otherWitness : List Bytes := [[0x30], [0x02], [0x63]]

/-- One fixed witness per class: `Alerts.recoveryWitness`, `Alerts.normalWitness`, `otherWitness`
and `Alerts.shortWitness`. -/
@[req "ADR-0023"]
def WitnessClass.toWitness : WitnessClass → List Bytes
  | .recovery => Alerts.recoveryWitness
  | .normal => Alerts.normalWitness
  | .other => otherWitness
  | .short => Alerts.shortWitness

/-- `Alerts.isRecovery` of the mapped witness is the class's reading, decided over the closed
type. -/
@[req "ADR-0023"]
theorem toWitness_isRecovery (c : WitnessClass) : Alerts.isRecovery c.toWitness = c.isRecovery := by
  cases c <;> decide

def encWitnessClass : WitnessClass → Bytes
  | .recovery => u8 1
  | .normal => u8 2
  | .other => u8 3
  | .short => u8 4

def decWitnessClass : Bytes → Option (WitnessClass × Bytes)
  | 1 :: bs => some (.recovery, bs)
  | 2 :: bs => some (.normal, bs)
  | 3 :: bs => some (.other, bs)
  | 4 :: bs => some (.short, bs)
  | _ => none

theorem decWitnessClass_enc (c : WitnessClass) (r : Bytes) :
    decWitnessClass (encWitnessClass c ++ r) = some (c, r) := by
  cases c <;> rfl

/-- A script as an identifier, mapped to fixed bytes by its `u32` encoding: total, and the one map
for a spend's script and for an alert's, so the alert in the queue carries the identifier its
spend carried. -/
@[req "ADR-0023"]
def scriptOf (i : Nat) : Bytes := u32 i

/-- `Alerts.Spend` with its two byte strings replaced: `txid` and `outpoint` as they are, the script
an identifier through `scriptOf`, the witness its `WitnessClass`, whose docstring says what the
replay does not check of the selector. -/
@[req "ADR-0023"]
structure Spend where
  txid : Nat
  outpoint : Nat × Nat
  script : Nat
  witness : WitnessClass
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Spend.toAlerts (s : Spend) : Alerts.Spend :=
  { txid := s.txid, outpoint := s.outpoint, script := scriptOf s.script, witness := s.witness.toWitness }

def encSpend (s : Spend) : Bytes :=
  u32 s.txid ++ encPair s.outpoint ++ u32 s.script ++ encWitnessClass s.witness

def decSpend (bs : Bytes) : Option (Spend × Bytes) := do
  let (txid, bs) ← readLE 4 bs
  let (outpoint, bs) ← decPair bs
  let (script, bs) ← readLE 4 bs
  let (witness, bs) ← decWitnessClass bs
  pure ({ txid, outpoint, script, witness }, bs)

abbrev SpendWF (s : Spend) : Prop := s.txid < 256 ^ 4 ∧ PairWF s.outpoint ∧ s.script < 256 ^ 4

theorem decSpend_enc (s : Spend) (h : SpendWF s) (r : Bytes) : decSpend (encSpend s ++ r) = some (s, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decSpend, encSpend, List.append_assoc, read32_u32 _ h1, decPair_enc _ h2, read32_u32 _ h3,
    decWitnessClass_enc]

/-- `Alerts.duty`'s `spendOf` is a function; the trace carries it as rows keyed by the scan's
spend id, and the mapping states the value outside the list: a spend with a short witness, which
`Alerts.classify` reads as no selector. -/
def encSpendRow (p : Nat × Spend) : Bytes := u32 p.1 ++ encSpend p.2

def decSpendRow (bs : Bytes) : Option ((Nat × Spend) × Bytes) := do
  let (i, bs) ← readLE 4 bs
  let (s, bs) ← decSpend bs
  pure ((i, s), bs)

abbrev SpendRowWF (p : Nat × Spend) : Prop := p.1 < 256 ^ 4 ∧ SpendWF p.2

theorem decSpendRow_enc (p : Nat × Spend) (h : SpendRowWF p) (r : Bytes) :
    decSpendRow (encSpendRow p ++ r) = some (p, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decSpendRow, encSpendRow, List.append_assoc, read32_u32 _ h1, decSpend_enc _ h2]

theorem decList_spendRow (xs : List (Nat × Spend)) (h : ListWF SpendRowWF encSpendRow xs) (r : Bytes) :
    decList decSpendRow (encList encSpendRow xs ++ r) = some (xs, r) :=
  decList_encList decSpendRow encSpendRow SpendRowWF xs h decSpendRow_enc r

def noSpend : Spend := { txid := 0, outpoint := (0, 0), script := 0, witness := .short }

@[req "ADR-0023"]
def spendOfRows (rows : List (Nat × Spend)) : Nat → Alerts.Spend :=
  fun i => (((rows.find? (·.1 == i)).map (·.2)).getD noSpend).toAlerts

/-- `Alerts.Kind`, one tag each. -/
def encKind : Alerts.Kind → Bytes
  | .recoveryPathSpend => u8 1
  | .unrecognizedSpend => u8 2

def decKind : Bytes → Option (Alerts.Kind × Bytes)
  | 1 :: bs => some (.recoveryPathSpend, bs)
  | 2 :: bs => some (.unrecognizedSpend, bs)
  | _ => none

theorem decKind_enc (k : Alerts.Kind) (r : Bytes) : decKind (encKind k ++ r) = some (k, r) := by
  cases k <;> rfl

/-- `Alerts.Alert` with its script an identifier through `scriptOf`: `kind`, `spendTxid`,
`outpoint`, `script`. -/
@[req "ADR-0023"]
structure Alert where
  kind : Alerts.Kind
  spendTxid : Nat
  outpoint : Nat × Nat
  script : Nat
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Alert.toAlerts (a : Alert) : Alerts.Alert :=
  { kind := a.kind, spendTxid := a.spendTxid, outpoint := a.outpoint, script := scriptOf a.script }

def encAlert (a : Alert) : Bytes := encKind a.kind ++ u32 a.spendTxid ++ encPair a.outpoint ++ u32 a.script

def decAlert (bs : Bytes) : Option (Alert × Bytes) := do
  let (kind, bs) ← decKind bs
  let (spendTxid, bs) ← readLE 4 bs
  let (outpoint, bs) ← decPair bs
  let (script, bs) ← readLE 4 bs
  pure ({ kind, spendTxid, outpoint, script }, bs)

abbrev AlertWF (a : Alert) : Prop := a.spendTxid < 256 ^ 4 ∧ PairWF a.outpoint ∧ a.script < 256 ^ 4

theorem decAlert_enc (a : Alert) (h : AlertWF a) (r : Bytes) : decAlert (encAlert a ++ r) = some (a, r) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decAlert, encAlert, List.append_assoc, decKind_enc, read32_u32 _ h1, decPair_enc _ h2, read32_u32 _ h3]

/-- `Alerts.Event`: `seq`, `alert`, as a pair. -/
def encAlertEvent (e : Nat × Alert) : Bytes := u32 e.1 ++ encAlert e.2

def decAlertEvent (bs : Bytes) : Option ((Nat × Alert) × Bytes) := do
  let (seq, bs) ← readLE 4 bs
  let (alert, bs) ← decAlert bs
  pure ((seq, alert), bs)

abbrev AlertEventWF (e : Nat × Alert) : Prop := e.1 < 256 ^ 4 ∧ AlertWF e.2

theorem decAlertEvent_enc (e : Nat × Alert) (h : AlertEventWF e) (r : Bytes) :
    decAlertEvent (encAlertEvent e ++ r) = some (e, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decAlertEvent, encAlertEvent, List.append_assoc, read32_u32 _ h1, decAlert_enc _ h2]

theorem decList_alertEvent (xs : List (Nat × Alert)) (h : ListWF AlertEventWF encAlertEvent xs) (r : Bytes) :
    decList decAlertEvent (encList encAlertEvent xs ++ r) = some (xs, r) :=
  decList_encList decAlertEvent encAlertEvent AlertEventWF xs h decAlertEvent_enc r

/-- `Alerts.Queue`: `events`, `next`, each event's alert through `Alert.toAlerts`. -/
@[req "ADR-0023"]
structure Queue where
  events : List (Nat × Alert)
  next : Nat
  deriving DecidableEq, Repr

@[req "ADR-0023"]
def Queue.toAlerts (q : Queue) : Alerts.Queue :=
  { events := q.events.map fun (seq, a) => { seq := seq, alert := a.toAlerts }, next := q.next }

def encQueue (q : Queue) : Bytes := encList encAlertEvent q.events ++ u32 q.next

def decQueue (bs : Bytes) : Option (Queue × Bytes) := do
  let (events, bs) ← decList decAlertEvent bs
  let (next, bs) ← readLE 4 bs
  pure ({ events, next }, bs)

abbrev QueueWF (q : Queue) : Prop := ListWF AlertEventWF encAlertEvent q.events ∧ q.next < 256 ^ 4

theorem decQueue_enc (q : Queue) (h : QueueWF q) (r : Bytes) : decQueue (encQueue q ++ r) = some (q, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decQueue, encQueue, List.append_assoc, decList_alertEvent _ h1, read32_u32 _ h2]

/-! ## The package alphabet (`Package.validate`) -/

/-- `Package.Candidate`: `txid`, `inputs`. -/
def encCandidate (c : Package.Candidate) : Bytes := u32 c.txid ++ encList u32 c.inputs

def decCandidate (bs : Bytes) : Option (Package.Candidate × Bytes) := do
  let (txid, bs) ← readLE 4 bs
  let (inputs, bs) ← decList (readLE 4) bs
  pure ({ txid, inputs }, bs)

abbrev CandidateWF (c : Package.Candidate) : Prop := c.txid < 256 ^ 4 ∧ NatsWF c.inputs

theorem decCandidate_enc (c : Package.Candidate) (h : CandidateWF c) (r : Bytes) :
    decCandidate (encCandidate c ++ r) = some (c, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decCandidate, encCandidate, List.append_assoc, read32_u32 _ h1, decList_u32 _ h2]

/-- One row of `Package.MempoolRead`: a resident txid and its ordered inputs. -/
def encMemRow (p : Nat × List Nat) : Bytes := u32 p.1 ++ encList u32 p.2

def decMemRow (bs : Bytes) : Option ((Nat × List Nat) × Bytes) := do
  let (t, bs) ← readLE 4 bs
  let (ins, bs) ← decList (readLE 4) bs
  pure ((t, ins), bs)

abbrev MemRowWF (p : Nat × List Nat) : Prop := p.1 < 256 ^ 4 ∧ NatsWF p.2

theorem decMemRow_enc (p : Nat × List Nat) (h : MemRowWF p) (r : Bytes) : decMemRow (encMemRow p ++ r) = some (p, r) := by
  obtain ⟨h1, h2⟩ := h
  simp [decMemRow, encMemRow, List.append_assoc, read32_u32 _ h1, decList_u32 _ h2]

theorem decList_memRow (xs : List (Nat × List Nat)) (h : ListWF MemRowWF encMemRow xs) (r : Bytes) :
    decList decMemRow (encList encMemRow xs ++ r) = some (xs, r) :=
  decList_encList decMemRow encMemRow MemRowWF xs h decMemRow_enc r

theorem decList_pair (xs : List (Nat × Nat)) (h : ListWF PairWF encPair xs) (r : Bytes) :
    decList decPair (encList encPair xs ++ r) = some (xs, r) :=
  decList_encList decPair encPair PairWF xs h decPair_enc r

/-- `Package.Creator` is a function; the trace carries it as `(outpoint, creating txid)` rows,
and the mapping states the value outside the list, `0`, as `Package.twinCreator` does. -/
@[req "ADR-0023"]
def creatorOf (rows : List (Nat × Nat)) : Package.Creator :=
  fun o => ((rows.find? (·.1 == o)).map (·.2)).getD 0

/-! ## The alphabet, versioned -/

/-- The format's version. The encoding starts with it and `decode` refuses any other value before
reading anything else, as `Manifest.encode_refuses_other_revisions` refuses a revision. Version 5
adds refused-but-staged kernel ingress, tag 12, with an optional pair binding. Version 4
is the vault-unspent alphabet as it stands. Over version 3 it moves one thing: the state carries
whether a cold scan has replaced the cache since the latch set (`VaultUnspent.State.scanned`), one
`bool` after the latch, because `VaultUnspent.refresh` reads it. Version 3 had moved three things
over version 2, each because the model function the entry maps to moved: the `vaultServe` entry
carries a third view, the one captured when the delta walk starts (`VaultUnspent.serve`'s `walk`);
the state carries the cold scan the attempt in progress started from, as an `Option` of a cache,
where version 2 carried a flag (`VaultUnspent.State.repairScan`); and the `vaultRepairFailed`
entry is new, for the attempt that stops before its re-import (`VaultUnspent.endAsFailure`).
Version 2 had itself moved the layout over version 1: a ledger row carries the vault outputs its
block spends (`LedgerRow.vaultSpends`), the wallet its list of completion markers, the
`vaultRepair` entry its second bracket view and the walk above the settled block, and the state
one cache. A string of any other version is refused (`decode_refuses_other_versions`);
`wrong_version_refused` is the exhibit at version 4, the version this one supersedes,
`third_version_refused` the one at version 3, `second_version_refused` the one at version 2
and `first_version_refused` the one at version 1. -/
@[req "ADR-0023"]
def version : Nat := 5

/-- One entry: what one module steps on, with the arguments its step takes, and for the kernel
the effects the step emitted. Each constructor names the model function it maps to; the mappings
below are the definitions an adapter targets.

**Secrets by construction.** `STO-11` says the secrets it lists "MUST never appear in a log line,
trace, metric, crash dump, alert, replay entry or disk write". No field of any constructor here,
or of any record a constructor carries, is a PIN, a preimage, a key, a KDF output or matrix, a
padded payload or a request body, and none has type `Bytes` or `List Bytes`: every field is a
model identifier, a clock sample, a flag, a count or a value of a closed type, a spend's witness
is carried as the class `Alerts.selector` yields (`WitnessClass`) and its script as an identifier
(`Spend`), and the entry that carries a candidate carries what `Kernel.accept` reads and nothing
the wire's `SpendRequest` carried beside it. `STO-12`: "No fast digest, MAC, full signature or
retained request body MAY exist that would let later process-memory capture cheaply test the
plaintext PIN" — no synthetic identifier in the published trace is derived from anything; they
are small integers chosen by hand. -/
@[req "ADR-0023"]
inductive Entry
  /-- `Kernel.step`: one environment, one event, and the effects the step emitted, in order. They
  nest here rather than following the step as entries of their own because they are the step's own
  result: an entry of its own could sit anywhere, and a projection over the entries could not tell
  a misplaced one from a placed one (`misplaced_effect_refused`). -/
  | kernel (env : Env) (event : KernelEvent) (effects : List Kernel.Effect)
  /-- `Delivery.run`: the expected commitment id and every endpoint's outcome. -/
  | delivery (expected : Nat) (outcomes : List Delivery.Outcome)
  /-- `Watchtower.step`: the view captured before the pass and the pass's outcome. -/
  | watchtower (view : Hashes) (outcome : WatchOutcome)
  /-- `VaultUnspent.serve`, and `VaultUnspent.refresh`, which takes the same arguments: the
  ledger, the state, the view captured before the wallet's listing, the view read when its
  reconciliation ends, the view captured when the delta walk starts, the scan (`WTC-6`). -/
  | vaultServe (ledger : List LedgerRow) (st : VaultUnspent.State) (view after walk : Hashes)
      (scan : Scan)
  /-- `VaultUnspent.repair`: the ledger, the scan view, the two views the bracket re-proves the
  settled block on, the walk above it, and the state (`WTC-7`). -/
  | vaultRepair (ledger : List LedgerRow) (scanView atDescriptors atMarker : Hashes) (scan : Scan)
      (st : VaultUnspent.State)
  /-- `VaultUnspent.endAsFailure`: the state of a repair attempt that stops before its re-import
  (`WTC-9`). -/
  | vaultRepairFailed (st : VaultUnspent.State)
  /-- `VaultUnspent.attempt`: the view, the cache, the sequence, the coins kept, the additions,
  the tip and the sequence read after. -/
  | vaultAttempt (view : Hashes) (cache : VaultUnspent.Cache) (sequence : Nat) (keep additions : List Coin)
      (tipAfter : Anchor) (sequenceAfter : Nat)
  /-- `Alerts.duty`: the snapshot, the latch, the cursor, the tip, the outcome, the spends by id,
  the queue. -/
  | alerts (snap : List Nat) (lockedDown : Bool) (cursor : Watchtower.Cursor) (tip : Anchor)
      (outcome : WatchOutcome) (spends : List (Nat × Spend)) (queue : Queue)
  /-- `Package.validate`: the creator rows, the snapshot, the mempool read, the authorized set,
  the candidate, the txid it replaces. -/
  | package (creator : List (Nat × Nat)) (snap : VaultUnspent.Snapshot) (mem : List (Nat × List Nat))
      (authorized : List Nat) (candidate : Package.Candidate) (replaces : Option Nat)
  deriving DecidableEq, Repr

/-- A trace: its entries, in order. The version is the format's, not the trace's. -/
@[req "ADR-0023"]
structure Trace where
  entries : List Entry
  deriving DecidableEq, Repr

/-! ### The mappings, one per module

A guard parameter (`ImportBracket`, `MarkerAnchor`, `CursorShape`, `TipTest`,
`ReplacementAncestry`), `VaultUnspent.Rules`, `Delivery.Rules` and `Kernel.Rules` are the formal
model's, supplied as `current` by whoever replays: a trace never carries which requirement it is
replayed against. -/

/-- What the kernel is fed: every `kernel` entry, in order, as `Kernel.run`'s argument; what each
step must emit is checked by `replayKernel`, not projected. -/
@[req "ADR-0023"]
def kernelInputs (t : Trace) : List (Kernel.Env × Kernel.Event) :=
  t.entries.filterMap fun
    | .kernel env ev _ => some (env.toKernel, ev.toKernel)
    | _ => none

/-- The replay: `Kernel.step` on each `kernel` entry in order, refused when the effects the step
emitted are not the entry's, so an effect on any step but its own is refused where it sits. The
kernel is the only module the replay runs; every other entry is passed over, because the other
modules' entries are mapped by the projections below and not stepped. -/
@[req "ADR-0023"]
def replayKernel (r : Kernel.Rules) : Kernel.World → List Entry → Option Kernel.World
  | w, [] => some w
  | w, .kernel env ev effs :: rest =>
    let (w', effs') := Kernel.step r env.toKernel w ev.toKernel
    if effs' = effs then replayKernel r w' rest else none
  | w, _ :: rest => replayKernel r w rest

/-- Every `Delivery.run`, its arguments after `Delivery.Rules`: the expected id and the outcomes. -/
@[req "ADR-0023"]
def deliveryRuns (t : Trace) : List (Nat × List Delivery.Outcome) :=
  t.entries.filterMap fun
    | .delivery e os => some (e, os)
    | _ => none

/-- Every `Watchtower.step`: the view and the outcome; the cursor is the fold's state from
`Watchtower.genesis`. -/
@[req "ADR-0023"]
def watchtowerPasses (t : Trace) : List (View × Watchtower.Outcome) :=
  t.entries.filterMap fun
    | .watchtower v o => some (Watchtower.chainOf v, o.toWatchtower)
    | _ => none

/-- Every `VaultUnspent.serve` and `VaultUnspent.refresh`, the arguments after the rules, in
order. -/
@[req "ADR-0023"]
def vaultServes (t : Trace) :
    List (VaultUnspent.Ledger × VaultUnspent.State × View × View × View × Watchtower.Scan) :=
  t.entries.filterMap fun
    | .vaultServe L st v after walk s =>
      some (ledgerOf L, st, Watchtower.chainOf v, Watchtower.chainOf after, Watchtower.chainOf walk,
        s.toWatchtower)
    | _ => none

/-- Every `VaultUnspent.repair`, its arguments after the marker anchor and the import bracket, in
order. -/
@[req "ADR-0023"]
def vaultRepairs (t : Trace) :
    List (VaultUnspent.Ledger × View × View × View × Watchtower.Scan × VaultUnspent.State) :=
  t.entries.filterMap fun
    | .vaultRepair L sv ad am s st =>
      some (ledgerOf L, Watchtower.chainOf sv, Watchtower.chainOf ad, Watchtower.chainOf am,
        s.toWatchtower, st)
    | _ => none

/-- Every `VaultUnspent.endAsFailure`, its one argument, in order. -/
@[req "ADR-0023"]
def vaultRepairFailures (t : Trace) : List VaultUnspent.State :=
  t.entries.filterMap fun
    | .vaultRepairFailed st => some st
    | _ => none

/-- Every `VaultUnspent.attempt`, its seven arguments in order. -/
@[req "ADR-0023"]
def vaultAttempts (t : Trace) :
    List (View × VaultUnspent.Cache × Nat × (Coin → Bool) × List Coin × Anchor × Nat) :=
  t.entries.filterMap fun
    | .vaultAttempt v c seq keep adds tip seq' => some (Watchtower.chainOf v, c, seq, keepOf keep, adds, tip, seq')
    | _ => none

/-- Every `Alerts.duty`, its arguments after the cursor shape and the tip test, in order. -/
@[req "ADR-0023"]
def alertDuties (t : Trace) :
    List (List Nat × Bool × Watchtower.Cursor × Anchor × Watchtower.Outcome × (Nat → Alerts.Spend) × Alerts.Queue) :=
  t.entries.filterMap fun
    | .alerts snap l c tip o spends q => some (snap, l, c, tip, o.toWatchtower, spendOfRows spends, q.toAlerts)
    | _ => none

/-- Every `Package.validate`, its arguments after the replacement-ancestry guard, in order. -/
@[req "ADR-0023"]
def packageValidations (t : Trace) :
    List (Package.Creator × VaultUnspent.Snapshot × Package.MempoolRead × List Nat × Package.Candidate × Option Nat) :=
  t.entries.filterMap fun
    | .package cr snap mem auth c rep => some (creatorOf cr, snap, mem, auth, c, rep)
    | _ => none

/-! ## The codec -/

/-- One entry: a tag byte, then its fields, each field with the move its width names. -/
@[req "ADR-0023"]
def encEntry : Entry → Bytes
  | .kernel env ev effs => u8 1 ++ encEnv env ++ encKernelEvent ev ++ encList encEffect effs
  | .delivery e os => u8 2 ++ u32 e ++ encList encOutcome os
  | .watchtower v o => u8 3 ++ encList u32 v ++ encWatchOutcome o
  | .vaultServe L st v after walk s =>
    u8 4 ++ encList encLedgerRow L ++ encState st ++ encList u32 v ++ encList u32 after ++
      encList u32 walk ++ encScan s
  | .vaultRepair L sv ad am s st =>
    u8 5 ++ encList encLedgerRow L ++ encList u32 sv ++ encList u32 ad ++ encList u32 am ++
      encScan s ++ encState st
  | .vaultAttempt v c seq keep adds tip seq' =>
    u8 6 ++ encList u32 v ++ encCache c ++ u32 seq ++ encList encCoin keep ++ encList encCoin adds ++
      encAnchor tip ++ u32 seq'
  | .alerts snap l c tip o spends q =>
    u8 7 ++ encList u32 snap ++ encBool l ++ encCursor c ++ encAnchor tip ++ encWatchOutcome o ++
      encList encSpendRow spends ++ encQueue q
  | .package cr snap mem auth c rep =>
    u8 8 ++ encList encPair cr ++ encSnapshot snap ++ encList encMemRow mem ++ encList u32 auth ++
      encCandidate c ++ encOpt u32 rep
  | .vaultRepairFailed st => u8 9 ++ encState st

/-- One entry read back; a tag no constructor carries is refused. -/
@[req "ADR-0023"]
def decEntry : Bytes → Option (Entry × Bytes)
  | 1 :: bs => do
    let (env, bs) ← decEnv bs
    let (ev, bs) ← decKernelEvent bs
    let (effs, bs) ← decList decEffect bs
    pure (.kernel env ev effs, bs)
  | 2 :: bs => do
    let (e, bs) ← readLE 4 bs
    let (os, bs) ← decList decOutcome bs
    pure (.delivery e os, bs)
  | 3 :: bs => do
    let (v, bs) ← decList (readLE 4) bs
    let (o, bs) ← decWatchOutcome bs
    pure (.watchtower v o, bs)
  | 4 :: bs => do
    let (L, bs) ← decList decLedgerRow bs
    let (st, bs) ← decState bs
    let (v, bs) ← decList (readLE 4) bs
    let (after, bs) ← decList (readLE 4) bs
    let (walk, bs) ← decList (readLE 4) bs
    let (s, bs) ← decScan bs
    pure (.vaultServe L st v after walk s, bs)
  | 5 :: bs => do
    let (L, bs) ← decList decLedgerRow bs
    let (sv, bs) ← decList (readLE 4) bs
    let (ad, bs) ← decList (readLE 4) bs
    let (am, bs) ← decList (readLE 4) bs
    let (s, bs) ← decScan bs
    let (st, bs) ← decState bs
    pure (.vaultRepair L sv ad am s st, bs)
  | 6 :: bs => do
    let (v, bs) ← decList (readLE 4) bs
    let (c, bs) ← decCache bs
    let (seq, bs) ← readLE 4 bs
    let (keep, bs) ← decList decCoin bs
    let (adds, bs) ← decList decCoin bs
    let (tip, bs) ← decAnchor bs
    let (seq', bs) ← readLE 4 bs
    pure (.vaultAttempt v c seq keep adds tip seq', bs)
  | 7 :: bs => do
    let (snap, bs) ← decList (readLE 4) bs
    let (l, bs) ← decBool bs
    let (c, bs) ← decCursor bs
    let (tip, bs) ← decAnchor bs
    let (o, bs) ← decWatchOutcome bs
    let (spends, bs) ← decList decSpendRow bs
    let (q, bs) ← decQueue bs
    pure (.alerts snap l c tip o spends q, bs)
  | 8 :: bs => do
    let (cr, bs) ← decList decPair bs
    let (snap, bs) ← decSnapshot bs
    let (mem, bs) ← decList decMemRow bs
    let (auth, bs) ← decList (readLE 4) bs
    let (c, bs) ← decCandidate bs
    let (rep, bs) ← decOpt (readLE 4) bs
    pure (.package cr snap mem auth c rep, bs)
  | 9 :: bs => do
    let (st, bs) ← decState bs
    pure (.vaultRepairFailed st, bs)
  | _ => none

/-- Every integer under its width, every list under `256 ^ 4`. -/
@[req "ADR-0023"]
def Entry.WF : Entry → Prop
  | .kernel env ev effs => EnvWF env ∧ ev.WF ∧ ListWF EffectWF encEffect effs
  | .delivery e os => e < 256 ^ 4 ∧ ListWF OutcomeWF encOutcome os
  | .watchtower v o => NatsWF v ∧ o.WF
  | .vaultServe L st v after walk s =>
    ListWF LedgerRowWF encLedgerRow L ∧ StateWF st ∧ NatsWF v ∧ NatsWF after ∧ NatsWF walk ∧
      ScanWF s
  | .vaultRepair L sv ad am s st =>
    ListWF LedgerRowWF encLedgerRow L ∧ NatsWF sv ∧ NatsWF ad ∧ NatsWF am ∧ ScanWF s ∧ StateWF st
  | .vaultAttempt v c seq keep adds tip seq' =>
    NatsWF v ∧ CacheWF c ∧ seq < 256 ^ 4 ∧ ListWF CoinWF encCoin keep ∧ ListWF CoinWF encCoin adds ∧
      AnchorWF tip ∧ seq' < 256 ^ 4
  | .alerts snap _ c tip o spends q =>
    NatsWF snap ∧ CursorWF c ∧ AnchorWF tip ∧ o.WF ∧ ListWF SpendRowWF encSpendRow spends ∧ QueueWF q
  | .package cr snap mem auth c rep =>
    ListWF PairWF encPair cr ∧ SnapshotWF snap ∧ ListWF MemRowWF encMemRow mem ∧ NatsWF auth ∧
      CandidateWF c ∧ OptNatWF rep
  | .vaultRepairFailed st => StateWF st

theorem decEntry_enc (e : Entry) (h : e.WF) (r : Bytes) : decEntry (encEntry e ++ r) = some (e, r) := by
  cases e with
  | kernel env ev effs =>
    obtain ⟨h1, h2, h3⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decEnv_enc _ h1, decKernelEvent_enc _ h2,
      decList_effect _ h3]
  | delivery e os =>
    obtain ⟨h1, h2⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, read32_u32 _ h1, decList_outcome _ h2]
  | watchtower v o =>
    obtain ⟨h1, h2⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_u32 _ h1, decWatchOutcome_enc _ h2]
  | vaultServe L st v after walk s =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_ledger _ h1, decState_enc _ h2,
      decList_u32 _ h3, decList_u32 _ h4, decList_u32 _ h5, decScan_enc _ h6]
  | vaultRepair L sv ad am s st =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_ledger _ h1, decList_u32 _ h2,
      decList_u32 _ h3, decList_u32 _ h4, decScan_enc _ h5, decState_enc _ h6]
  | vaultAttempt v c seq keep adds tip seq' =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_u32 _ h1, decCache_enc _ h2,
      read32_u32 _ h3, decList_coin _ h4, decList_coin _ h5, decAnchor_enc _ h6, read32_u32 _ h7]
  | alerts snap l c tip o spends q =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_u32 _ h1, decBool_enc, decCursor_enc _ h2,
      decAnchor_enc _ h3, decWatchOutcome_enc _ h4, decList_spendRow _ h5, decQueue_enc _ h6]
  | package cr snap mem auth c rep =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    simp [encEntry, decEntry, u8, List.append_assoc, decList_pair _ h1, decSnapshot_enc _ h2,
      decList_memRow _ h3, decList_u32 _ h4, decCandidate_enc _ h5, decOpt_u32 _ h6]
  | vaultRepairFailed st =>
    simp [encEntry, decEntry, u8, decState_enc _ h]

/-- The trace's domain: `Entry.WF` on every entry, the count and each entry's bytes under
`u32`. -/
@[req "ADR-0023"]
abbrev Trace.WF (t : Trace) : Prop := ListWF Entry.WF encEntry t.entries

/-- The encoding: the version as `u8`, then the entries as `list`. `WIR-18`: "`u32` little-endian
count, then each item as `var`", and a `var` is "`u32` little-endian length prefix, then the
bytes"; each item is a tag byte and its fields. `WIR-18` owns the moves, not the trace: `WIR-18`
says "Every signed or hashed byte string except the commitment" is built with them, and this
string is neither signed nor hashed by the protocol; it is hashed by `check_vectors.py` alone. -/
@[req "ADR-0023"]
def encode (t : Trace) : Bytes := u8 version ++ encList encEntry t.entries

/-- The decoder, in `Encode.decode`'s shape: "consumes the whole string or refuses". It refuses, in
this order: a version other than `version`, before reading anything else; then it reads the count
and every `var` frame, refusing a frame whose length prefix overruns the string before any tag is
inspected; then each item in turn, a tag no constructor carries, an item shorter than its fields, or
an item with bytes left after its fields; and last, bytes after the last frame. -/
@[req "ADR-0023"]
def decode : Bytes → Option Trace
  | v :: bs =>
    if v == version then
      match decList decEntry bs with
      | some (entries, []) => some { entries }
      | _ => none
    else none
  | [] => none

theorem decList_entries (es : List Entry) (h : ListWF Entry.WF encEntry es) (r : Bytes) :
    decList decEntry (encList encEntry es ++ r) = some (es, r) :=
  decList_encList decEntry encEntry Entry.WF es h decEntry_enc r

theorem decList_entries_nil (es : List Entry) (h : ListWF Entry.WF encEntry es) :
    decList decEntry (encList encEntry es) = some (es, []) := by
  simpa using decList_entries es h []

/-- On the admitted domain the encoding reads back exactly. -/
@[req "ADR-0023"]
theorem decode_encode (t : Trace) (h : t.WF) : decode (encode t) = some t := by
  simp [decode, encode, u8, version, decList_entries_nil t.entries h]

/-- Two well-formed traces with one encoding are one trace, as `Encode.encode_injective` follows
from `Encode.decode_encode`. -/
@[req "ADR-0023"]
theorem encode_injective (a b : Trace) (ha : a.WF) (hb : b.WF) (h : encode a = encode b) : a = b := by
  have := decode_encode a ha
  rw [h, decode_encode b hb] at this
  exact (Option.some.inj this).symm

/-- The widths add up: 5 fixed bytes — the version and the count — then 4 plus the entry's own
bytes per entry. -/
@[req "ADR-0023"]
theorem encode_length (t : Trace) :
    (encode t).length = 5 + (t.entries.map fun e => 4 + (encEntry e).length).sum := by
  simp [encode, encList, Encode.list, u8, le_length, var_length, List.map_map, Function.comp_def]
  omega

/-- A version other than `version` is refused whatever follows, as
`Manifest.encode_refuses_other_revisions` refuses a revision other than `Manifest.revision`. -/
@[req "ADR-0023"]
theorem decode_refuses_other_versions (v : Nat) (bs : Bytes) (h : v ≠ version) :
    decode (v :: bs) = none := by
  simp [decode, h]

/-! ## The published synthetic trace -/

/-- The world `BtcPolicy.Exhibits.ReleaseKernel` starts from: one honest node, `t = 2`, nothing
accepted, nothing armed. Restated here because `Exhibits.lean` imports everything and this
module must not import it. -/
def node0 : Kernel.Node :=
  { id := 0, t := 2, armed := false, poisoned := false, lockedDown := false, carriers := [],
    cands := [], T := Wall.sample 0, sweepActive := false, selected := [], duressDelay := 200,
    epsilon := 5, combineSlack := 40 }

def w0 : Kernel.World := { node := node0, exposure := [] }

/-- A candidate as it is handed to `accept`, where `Kernel.born` writes the flags. -/
def cand (id : Nat) (tx : Kernel.Tx) (hot : Bool) (fireAt : Option Nat) (expiry : Nat) : Cand :=
  { id := id, tx := tx, hot := hot, quorum := false, frozen := false, terminal := false,
    settled := false, broadcast := false, released := false, packageOk := false,
    heldSigners := [], fireAt := fireAt, windowClose := none, expiry := expiry }

/-- The hot spend over input 0 and its Escape; every identifier a small integer chosen by hand. -/
def tx1 : Kernel.Tx := { id := 100, inputs := [0], outflow := 100 }
def txE : Kernel.Tx := { id := 101, inputs := [0, 1], outflow := 0 }

/-- A raw wall sample, a HotClock sample, no high-water advance, an empty chain view. -/
def envAt (wall mono : Nat) : Env := { wall := wall, hw := 0, mono := mono, mtp := 0, seen := [] }

/-- The trace: accepted at wall 50 with `E = 200`; peer 1's relay reaches `t = 2` and opens the
pair; the fire pass at wall 120 finds the hot candidate due and queues its partial; peer 1's
partial arrives and completes possession; the package test passes; the send re-authorizes and
broadcasts. The two effects the kernel emits sit on the steps that emit them. -/
@[req "ADR-0023"]
def published : Trace :=
  { entries :=
    [ .kernel (envAt 50 5) (.accept 10 false 200 (cand 1 tx1 true (some 100) 200) (cand 2 txE false none 200)) [],
      .kernel (envAt 50 5) (.receipt 10 1) [],
      .kernel (envAt 120 60) .firePass [.queuePartial (100, 0) 0 true 1],
      .kernel (envAt 120 60) (.receivePartial (100, 0) 0 1 1) [],
      .kernel (envAt 120 60) (.packageAccepted 1) [],
      .kernel (envAt 120 60) (.send 1) [.broadcast 100] ] }

/-- A refused normal Carrier names the closed resident pair; a later unbound duress refusal
arms. Each reaches a live holder decision and every step emits nothing. -/
def refusalTrace : Trace :=
  { entries := [
    .kernel (envAt 50 5) (.accept 10 false 200 (cand 1 tx1 true (some 100) 200)
      (cand 2 txE false none 200)) [],
    .kernel (envAt 50 5) (.refuse 11 false 200 (some (1, 2)) .EXPIRY_TOO_SHORT) [],
    .kernel (envAt 60 20) (.receipt 11 1) [],
    .kernel (envAt 120 60) .firePass [],
    .kernel (envAt 120 60) (.refuse 12 true 200 none .BAD_PIN) [],
    .kernel (envAt 130 70) (.receipt 12 1) [] ] }

/-- The published trace's kernel inputs, written out: what `kernelInputs` yields. -/
def publishedInputs : List (Kernel.Env × Kernel.Event) :=
  [ ((envAt 50 5).toKernel, .accept 10 false (Wall.sample 200) (cand 1 tx1 true (some 100) 200).toKernel
      (cand 2 txE false none 200).toKernel),
    ((envAt 50 5).toKernel, .receipt 10 1),
    ((envAt 120 60).toKernel, .firePass),
    ((envAt 120 60).toKernel, .receivePartial (100, 0) 0 1 1),
    ((envAt 120 60).toKernel, .packageAccepted 1),
    ((envAt 120 60).toKernel, .send 1) ]

/-- The world the published trace ends in: `Kernel.run` over `publishedInputs` under `current`. -/
def finalWorld : Kernel.World := (Kernel.run Kernel.current w0 publishedInputs).1

/-- The frame entry by entry: the version and the count, then each entry as `var`. What
`Render.traceVector` prints, each entry from a new line and 32 bytes to a line; `framed_flatten`
says it is `encode`. -/
def framed (t : Trace) : List Bytes :=
  (u8 version ++ le 4 t.entries.length) :: t.entries.map fun e => var (encEntry e)

set_option maxRecDepth 100000 in
/-- The bytes `Render.traceVector` prints are the encoding. -/
@[req "ADR-0023"]
theorem framed_flatten : (framed published).flatten = encode published := by decide +kernel

set_option maxRecDepth 100000 in
/-- The decided verdict: the fire pass carried through to `SPN-39`'s broadcast. `SPN-39`: "assemble
the package (`WTC-24`); test it for mempool acceptance; re-check the slot, the freeze and the
window under the store lock as the linearization point between arming and sending; then
broadcast". The published bytes decode to the trace; the trace maps to `publishedInputs`; the
replay under `current` accepts every step's effects and ends in `finalWorld`, where the hot
candidate is released and broadcast with its `packageOk` consumed by `Kernel.send`, its Escape
opened with it but neither released nor broadcast, the Carrier retired by the holder decision, the
node unarmed, and this node's and peer 1's authority exposed. -/
@[req "SPN-39"]
theorem published_replays_with_current :
    decode (encode published) = some published ∧
    kernelInputs published = publishedInputs ∧
    replayKernel Kernel.current w0 published.entries = some finalWorld ∧
    finalWorld.node.cands.map (fun c => (c.id, c.quorum, c.released, c.packageOk, c.broadcast)) =
      [(1, true, true, false, true), (2, true, false, false, false)] ∧
    finalWorld.node.carriers = [] ∧
    finalWorld.node.armed = false ∧
    finalWorld.exposure.map (fun e => (e.signer, e.cid)) = [(0, 1), (1, 1)] := by
  decide +kernel

/-! ## Negative exhibits: the malformed shapes `decode` refuses -/

/-- The published bytes with their version byte set to 4, the version this format supersedes. -/
@[req "ADR-0023"]
def wrongVersion : Bytes := u8 4 ++ (encode published).drop 1

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem wrong_version_refused : decode wrongVersion = none := by decide +kernel

/-- The preceding vault-unspent revision is also refused. -/
@[req "ADR-0023"]
theorem third_version_refused : decode (u8 3 ++ (encode published).drop 1) = none := by
  decide +kernel

/-- The published bytes with their version byte set to 2, the version before that one. -/
@[req "ADR-0023"]
def secondVersion : Bytes := u8 2 ++ (encode published).drop 1

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem second_version_refused : decode secondVersion = none := by decide +kernel

/-- The published bytes with their version byte set to 1, the version first published. -/
@[req "ADR-0023"]
def firstVersion : Bytes := u8 1 ++ (encode published).drop 1

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem first_version_refused : decode firstVersion = none := by decide +kernel

/-- The offset of entry `k + 1`'s tag byte in `encode published`: the version and the count, then
`k` framed entries, then the frame's own length prefix. -/
def tagOffset (k : Nat) : Nat :=
  5 + ((published.entries.take k).map fun e => 4 + (encEntry e).length).sum + 4

/-- The published bytes with entry 2's tag byte set to 255, a tag no constructor carries, inside
an otherwise good trace. -/
@[req "ADR-0023"]
def unknownTag : Bytes := (encode published).set (tagOffset 1) 255

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem unknown_tag_refused : decode unknownTag = none := by decide +kernel

/-- The published bytes with their last byte dropped: the last entry's frame promises one byte
more than there is, refused before any tag is read. -/
@[req "ADR-0023"]
def truncated : Bytes := (encode published).dropLast

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem truncated_refused : decode truncated = none := by decide +kernel

/-- The published bytes with one byte appended after the last entry. -/
@[req "ADR-0023"]
def trailing : Bytes := encode published ++ u8 0

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem trailing_refused : decode trailing = none := by decide +kernel

/-! ## Negative exhibit: the misplaced effect `replayKernel` refuses -/

/-- The published trace with the fire pass's `queuePartial` moved one entry later, onto the
`receivePartial` step. -/
@[req "ADR-0023"]
def effectLater : Trace :=
  { entries := (published.entries.set 2 (.kernel (envAt 120 60) .firePass [])).set 3
      (.kernel (envAt 120 60) (.receivePartial (100, 0) 0 1 1) [.queuePartial (100, 0) 0 true 1]) }

/-- The published trace with the fire pass's `queuePartial` moved one entry earlier, onto the
`receipt` step. -/
@[req "ADR-0023"]
def effectEarlier : Trace :=
  { entries := (published.entries.set 2 (.kernel (envAt 120 60) .firePass [])).set 1
      (.kernel (envAt 50 5) (.receipt 10 1) [.queuePartial (100, 0) 0 true 1]) }

set_option maxRecDepth 100000 in
/-- Both decode, both map to `publishedInputs` — a projection cannot tell them from the published
trace — and the replay refuses each at the step whose effects are not the entry's. -/
@[req "ADR-0023"]
theorem misplaced_effect_refused :
    decode (encode effectLater) = some effectLater ∧ decode (encode effectEarlier) = some effectEarlier ∧
    kernelInputs effectLater = publishedInputs ∧ kernelInputs effectEarlier = publishedInputs ∧
    replayKernel Kernel.current w0 effectLater.entries = none ∧
    replayKernel Kernel.current w0 effectEarlier.entries = none := by
  decide +kernel

end BtcPolicy.Trace
