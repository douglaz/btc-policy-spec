import BtcPolicy.Sweep
import BtcPolicy.Witness
/-! Fast-exit feasibility: whether a request exists that meets the size and ancestry bounds and
`DUR-24`'s coverage at once (`F1`, `F2`, `F48`). Research and counterexamples over existing rules.
No selection rule, reserve topology, proof carrier or `F48` answer is chosen here, and `DUR-22`'s
denominator is read as it stands: `DUR-22` says "What the coordinator composes over (`OPR-33`) never
changes this denominator."

**Three questions, kept apart.** They are nested and neither inclusion reverses.

* `nodeOk`: would a node take this request and pass it at the sweep's reads? The bytes it measures
  (`API-4`, `API-6`), `WTC-24`'s ancestry, `DUR-23`'s fee and `DUR-24`'s coverage.
* `bounded`: also inside the bounds every composer and signer are held to whatever coins they pick:
  `F1` says whatever is chosen MUST "stay inside the size bounds of `OPR-35`", and `CHN-22` requires
  each input's "full previous transaction".
* `composeEvery`: does the composer as specified build it? `OPR-33` says it spends "**every** coin
  of the stable confirmed inventory", `OPR-34` says a coin absent from the UTXO set "MUST refuse the
  WHOLE inventory", and `OPR-39` keeps it "**confirmed-only**".

`compose_bounded` is the inclusion: a composed request is bounded, given no unconfirmed
vault-authorized value at the read. Over one read, `feasible_iff_best` answers the second question
in closed form under `CountOnly`, and `no_request_of_value_bound` is the general refutation.

**The denominator stays whole.** A request drawn from a canonical read with agreeing values is measured
against every coin of it, whichever it omits (`denominator_request`). With other Escapes selected the
denominator is at least the read less `DUR-22`'s excluded outputs, given distinct outpoints and agreement
on the coins they share (`base_le_denominator`). No theorem here drops a coin from the protected value to make a request
pass; `Exhibits.Feasibility.omitting_admits_two` is what that repair would cost.

**The size assumptions, by name.** `Parent.inDomain` is the assumed consensus transaction-size domain.
`Limits` carries the shape and the wire sizes, which this set fixes nowhere per input and which are
therefore assumptions of each exhibit, never deployment figures. `Vault.parentOf` is whether a
creating transaction can be obtained at all. `Vault.admissible` is what an exhibit's state satisfies. `Vault.retained` counts each input once per PSBT input
map: this module reads `OPR-35`'s "parent size × candidate multiplicity × both PSBT input maps" with
multiplicity as the number of inventory coins the parent creates. A reading that also multiplies by
rungs only raises the projection, so a refutation here stands under it.

**`F48` stays open.** `ParentRule` holds its three readings and no `current` value; `F48` says "The
node-side rule — refuse, ignore, or verify when present — is unstated". `Request.carried` says whether
a request carries full parents on the wire. The node has no reason to refuse a stripped request under
`ignore` or `verify`, and under `refuse` no composed request passes (`refuse_refuses_composed`).

**Not modelled.** The primary spend and the pair's policy checks: a request here is its Escape's
inputs, fee and wire size. `CHN-16`'s ladder enters only as `Limits.psbts`. `DUR-26`'s rung selection
and `DUR-21`'s check before release, as in `Sweep`. `WTC-26`'s acceptance verdict and relay policy:
`OPR-35`'s vsize bound is the composer's, and what a backend would relay is not read. Coinbase
maturity, which `Sweep.Backend` does not carry. Exact PSBT framing and base64 expansion. Whether a
confirmation ever happens. A request's own outputs: it is measured before it is resident, so they
are not in the read. -/

namespace BtcPolicy.Feasibility
open BtcPolicy.Coverage (Coin Outpoint sumValues dedupCoins insertCoin)

/-! ## The bounds -/

/-- `API-4`: "`/sign` MUST refuse a body larger than 1 048 576 bytes". -/
@[req "API-4"] def bodyCap : Nat := 1048576
/-- `OPR-35`: retained full parents "at most 64 MiB, equality passing". -/
@[req "OPR-35"] def retainedCap : Nat := 64 * 1024 * 1024
/-- `OPR-35`: "each composed shape's maximum finalized vsize at most 100 000 vB". -/
@[req "OPR-35"] def vsizeCap : Nat := 100000
/-- `OPR-35`'s "both PSBT input maps". -/
@[req "OPR-35"] def inputMaps : Nat := 2

/-- The size of a creating transaction: its bytes without the witness and its witness bytes. -/
structure Parent where
  base : Nat
  wit : Nat
  deriving DecidableEq, Repr

def Parent.bytes (p : Parent) : Nat := p.base + p.wit
def Parent.weight (p : Parent) : Nat := 4 * p.base + p.wit

/-- The block weight limit, an assumption about the chain and not a requirement of this set. -/
def consensusWeight : Nat := 4000000

/-- The assumed consensus transaction-size domain: `F1`'s "consensus-valid very large parent" is at
most the block weight limit, which a witness-heavy transaction can nearly fill. -/
def Parent.inDomain (p : Parent) : Bool := p.weight ≤ consensusWeight

/-- A parent in the domain is at most the limit in bytes. -/
theorem Parent.bytes_le {p : Parent} (h : p.inDomain = true) : p.bytes ≤ consensusWeight := by
  simp only [Parent.inDomain, Parent.weight, decide_eq_true_eq] at h
  simp only [Parent.bytes]
  omega

/-- The shape and the wire sizes a request is measured with. `psbts` counts the primary, the Escape
and the rungs. `shell` is `OPR-46`'s worst-case request shell. `perInput` is one input in one PSBT
with its parent stripped. `envelope` is the channel expansion `API-6` adds, and `msg` is `NCH-10`'s
`max_msg_bytes`. `outBytes` is the legacy serialization's output section, count prefix included. -/
structure Limits where
  t : Nat
  n : Nat
  outBytes : Nat
  psbts : Nat
  shell : Nat
  perInput : Nat
  envelope : Nat
  msg : Nat
  deriving DecidableEq, Repr

/-- The length of `Witness.compactSize` at the tiers it has. -/
def csLen (k : Nat) : Nat := if k < 253 then 1 else if k < 65536 then 3 else 5

theorem csLen_eq (k : Nat) : (Witness.compactSize k).length = csLen k := by
  unfold Witness.compactSize csLen
  split
  · rfl
  · split <;> simp [Encode.le_length]

theorem csLen_mono {a b : Nat} (h : a ≤ b) : csLen a ≤ csLen b := by
  unfold csLen; split <;> split <;> (try split) <;> (try split) <;> omega

/-- `CHN-34`'s `B` for a transaction of `k` inputs: version, input count, 41 bytes per input (an
outpoint, an empty `scriptSig` with its length prefix, a sequence), the output section, lock time. -/
@[req "CHN-34"]
def legacyLen (outBytes k : Nat) : Nat := 4 + csLen k + 41 * k + outBytes + 4

/-- A transaction's output section as `Witness.legacy` writes it. -/
def outSection (tx : Witness.Tx) : Nat :=
  (Witness.compactSize tx.outputs.length ++ tx.outputs.flatMap (fun o =>
    Encode.le 8 o.amount ++ Witness.compactSize o.script.length ++ o.script)).length

/-- `legacyLen` is `Witness.legacy`'s length, for every transaction whose inputs name 32-byte txids. -/
@[req "CHN-34"]
theorem legacyLen_measures (tx : Witness.Tx) (h : ∀ i ∈ tx.inputs, i.txid.length = 32) :
    (Witness.legacy tx).length = legacyLen (outSection tx) tx.inputs.length := by
  have hin : ∀ l : List Encode.Input, (∀ i ∈ l, i.txid.length = 32) →
      (l.flatMap fun i => i.txid ++ Encode.le 4 i.vout ++ [0] ++ Encode.le 4 i.sequence).length =
        41 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro hl
      have h1 := hl x List.mem_cons_self
      have h2 := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
        Encode.le_length, h1, h2]
      omega
  have hi := hin _ h
  simp only [Witness.legacy, outSection, legacyLen, List.length_append, Encode.le_length, csLen_eq] at *
  omega

/-- `CHN-34`'s maximum finalized vsize of a `k`-input Escape, by `Witness.maxVsize`. -/
@[req "CHN-34"]
def vsizeOf (lim : Limits) (k : Nat) : Nat :=
  Witness.maxVsize (legacyLen lim.outBytes k) k lim.t lim.n

theorem vsizeOf_mono (lim : Limits) {a b : Nat} (h : a ≤ b) : vsizeOf lim a ≤ vsizeOf lim b := by
  have hm : a * Witness.W lim.t lim.n ≤ b * Witness.W lim.t lim.n := Nat.mul_le_mul_right _ h
  have hc := csLen_mono h
  unfold vsizeOf Witness.maxVsize Witness.maxWeight legacyLen
  exact Nat.div_le_div_right (by omega)

/-! ## The state and the request -/

/-- A vault state at one backend instant. `cfg` holds the guards, the coverage, `witness_utxo` values
and each outpoint's creator. `parentOf` is a transaction's size by txid, `none` when its full bytes
cannot be obtained, so coins of one creator share one parent. `floor` is `escape_feerate_floor`. -/
structure Vault where
  cfg : Sweep.Cfg
  A : List Nat
  b : Sweep.Backend
  parentOf : Nat → Option Parent
  floor : Nat

/-- A request: its inputs in order, the fee, and whether full parents travel on the wire. -/
structure Request where
  txid : Nat
  inputs : List Outpoint
  fee : Nat
  carried : Bool := false
  deriving DecidableEq, Repr

/-- `F48`'s three readings. No `current`: the finding is open. -/
inductive ParentRule
  | refuse | ignore | verify
  deriving DecidableEq, Repr

/-- `CHN-18`'s "canonical outpoint order (sorted by txid then vout, no duplicates)" over the model's
outpoint order. -/
@[req "CHN-18"]
def ascending : List Nat → Bool
  | a :: b :: t => decide (a < b) && ascending (b :: t)
  | _ => true

namespace Vault

/-- `WTC-10`'s snapshot of the instant. -/
def snap (s : Vault) : VaultUnspent.Snapshot := Sweep.snapshot s.A s.b
/-- The read a request is measured against. -/
def read (s : Vault) : List Coin := s.snap.read
/-- `DUR-22`'s protected value at a read nothing is excluded from. -/
def total (s : Vault) : Nat := sumValues s.read
/-- The size of the transaction that created this outpoint. -/
def parent (s : Vault) (o : Outpoint) : Option Parent := s.parentOf (s.cfg.creator o)
/-- Inputs as coins at their `witness_utxo` values. -/
def coins (s : Vault) (r : List Outpoint) : List Coin := r.map fun o => (o, s.cfg.book.value o)
def inSum (s : Vault) (r : List Outpoint) : Nat := sumValues (s.coins r)
def parentBytes (s : Vault) (o : Outpoint) : Nat := ((s.parent o).map Parent.bytes).getD 0

/-- The request's raw bytes: the shell plus each input in each PSBT, its parent only if carried. -/
@[req "OPR-46"]
def wire (s : Vault) (lim : Limits) (r : List Outpoint) (carried : Bool) : Nat :=
  lim.shell + (r.map fun o => lim.psbts * (lim.perInput + if carried then s.parentBytes o else 0)).sum

/-- `OPR-35`'s projected total of retained full parents. -/
@[req "OPR-35"]
def retained (s : Vault) (r : List Outpoint) : Nat := (r.map fun o => inputMaps * s.parentBytes o).sum

/-- The request's Escape as the denominator sees it: not resident, so no output of its in the read. -/
def escape (s : Vault) (q : Request) : Coverage.Escape :=
  { id := q.txid, inputs := s.coins q.inputs, outputs := [], delivered := s.inSum q.inputs - q.fee }

/-- `DUR-22`'s pass with this request selected, measured alone. -/
def pass (s : Vault) (q : Request) : Coverage.Pass :=
  VaultUnspent.passOf s.snap [s.escape q] [] (Sweep.unconfirmedExternal s.A s.b)

/-- `DUR-22`'s denominator at that pass, under the state's guard values. -/
@[req "DUR-22"]
def denominator (s : Vault) (q : Request) : Nat :=
  Coverage.denominator s.cfg.denominator s.cfg.external (s.pass q) (s.escape q)

/-- What the exhibits call an admissible state, a Boolean so each one is decided: the read canonical;
`SPN-25`'s agreement on values; every known parent inside the consensus domain; a confirmed coin's creator
not itself resident; each unconfirmed output's creator what the mempool read says; and a coverage
`MAN-9` can seal. A state's reachability by any party's actions is a separate question. -/
@[req "MAN-9"]
def admissible (s : Vault) : Bool :=
  ascending (s.read.map (·.1)) && s.read.all (fun c => s.cfg.book.value c.1 == c.2) &&
    s.read.all (fun c => match s.parent c.1 with
      | some p => p.inDomain
      | none => true) &&
    s.b.confirmed.all (fun c => (s.b.mempool.lookup (s.cfg.creator c.1)).isNone) &&
    s.b.pending.all (fun p => s.cfg.creator p.2.1 == p.1 && (s.b.mempool.lookup p.1).isSome) &&
    decide (Coverage.floorPct ≤ s.cfg.pct) && decide (s.cfg.pct ≤ Coverage.ceilingPct)

/-! ### Validating a request that exists -/

/-- The bytes a node measures: `API-4`'s body cap, `API-6`'s envelope against `NCH-10`, and under
`F48`'s `refuse` reading a parent on every input. -/
@[req "API-4"]
def wireOk (s : Vault) (lim : Limits) (rule : ParentRule) (r : List Outpoint) (carried : Bool) : Bool :=
  decide (s.wire lim r carried ≤ bodyCap) && decide (s.wire lim r carried + lim.envelope ≤ lim.msg) &&
    (rule != .refuse || carried)

/-- `WTC-24` on these inputs, read through `Package.validate` with no resident named. -/
@[req "WTC-24"]
def ancestryOk (s : Vault) (r : List Outpoint) : Bool :=
  (Package.validate s.cfg.ancestry s.cfg.creator s.snap s.b.mempool s.A ⟨0, r⟩ none).isAdmitted

/-- `DUR-23`'s floor at the maximum finalized vsize, paid from the inputs. -/
@[req "DUR-23"]
def feeOk (s : Vault) (lim : Limits) (q : Request) : Bool :=
  decide (s.floor * vsizeOf lim q.inputs.length ≤ q.fee) && decide (q.fee ≤ s.inSum q.inputs)

/-- `DUR-24` against `DUR-22`'s denominator. -/
@[req "DUR-24"]
def coverOk (s : Vault) (q : Request) : Bool :=
  Coverage.covers (s.escape q).delivered (s.denominator q) s.cfg.pct

/-- The first question: a node takes this request and passes it at this read. -/
@[req "DUR-24"]
def nodeOk (s : Vault) (lim : Limits) (rule : ParentRule) (q : Request) : Bool :=
  !q.inputs.isEmpty && ascending q.inputs && s.wireOk lim rule q.inputs q.carried &&
    s.ancestryOk q.inputs && s.feeOk lim q && s.coverOk q

/-- `OPR-35`'s two bounds and `CHN-22`'s full parent on every input, whichever coins are picked. -/
@[req "OPR-35"]
def boundOk (s : Vault) (lim : Limits) (r : List Outpoint) : Bool :=
  decide (vsizeOf lim r.length ≤ vsizeCap) && r.all (fun o => (s.parent o).isSome) &&
    decide (s.retained r ≤ retainedCap)

/-- The second question: also inside the composer's and the signer's bounds. -/
@[req "OPR-35"]
def bounded (s : Vault) (lim : Limits) (rule : ParentRule) (q : Request) : Bool :=
  s.nodeOk lim rule q && s.boundOk lim q.inputs

end Vault

/-! ### Constructing one: the composer as specified -/

/-- Why the composer refuses. -/
inductive Refusal
  | empty | vsizeOver | mempoolSpent (o : Outpoint) | noParent (o : Outpoint) | retainedOver
  | wireOver | feeOver | underCovered
  deriving DecidableEq, Repr

/-- The request `OPR-33` names: every confirmed coin in order, stripped, at the floor's fee. -/
def everyRequest (lim : Limits) (txid : Nat) (s : Vault) : Request :=
  { txid := txid, inputs := s.b.confirmed.map (·.1),
    fee := s.floor * vsizeOf lim (s.b.confirmed.map (·.1)).length }

/-- `OPR-33`'s composer: every confirmed coin in order, in `OPR-33`'s order of reads: the empty set,
the zero-amount preflight, each candidate (`OPR-34`), the parents and their retention (`OPR-35`),
the stripped wire (`OPR-46`), then the Escape's own `CHN-21`, "`sweep × 100 ≥ total_in ×
escape_coverage_pct`", at the feerate floor (`OPR-38`'s lowest case). `OPR-39`: unconfirmed value is
not an input. -/
@[req "OPR-33"]
def composeEvery (lim : Limits) (txid : Nat) (s : Vault) : Except Refusal Request :=
  let inv := s.b.confirmed
  let r := inv.map (·.1)
  let fee := s.floor * vsizeOf lim r.length
  if inv.isEmpty then .error .empty
  else if vsizeCap < vsizeOf lim r.length then .error .vsizeOver
  else match r.find? (Sweep.spentInMempool s.b) with
    | some o => .error (.mempoolSpent o)
    | none =>
      match r.find? (fun o => (s.parent o).isNone) with
      | some o => .error (.noParent o)
      | none =>
        if retainedCap < s.retained r then .error .retainedOver
        else if !s.wireOk lim .ignore r false then .error .wireOver
        else if sumValues inv < fee then .error .feeOver
        else if !Coverage.covers (sumValues inv - fee) (sumValues inv) s.cfg.pct then
          .error .underCovered
        else .ok (everyRequest lim txid s)

/-! ## List facts -/

theorem ascending_iff : ∀ l : List Nat, ascending l = true ↔ l.Pairwise (· < ·)
  | [] => by simp [ascending]
  | [a] => by simp [ascending]
  | a :: b :: t => by
    have ih := ascending_iff (b :: t)
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hab, hp⟩
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, hp⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact Nat.lt_trans hab ((List.pairwise_cons.1 hp).1 x hx)
    · intro h
      obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
      exact ⟨h1 b List.mem_cons_self, h2⟩

/-- A sorted request over a sorted read, with values that agree, is a sublist of it. -/
theorem coins_sublist (v : Outpoint → Nat) : ∀ (read : List Coin) (r : List Outpoint),
    (read.map (·.1)).Pairwise (· < ·) → r.Pairwise (· < ·) → (∀ o ∈ r, o ∈ read.map (·.1)) →
    (∀ c ∈ read, v c.1 = c.2) → (r.map fun o => (o, v o)).Sublist read
  | [], r, _, _, hs, _ => by
    cases r with
    | nil => exact List.Sublist.refl _
    | cons o os => simpa using hs o List.mem_cons_self
  | c :: cs, r, hk, hr, hs, hv => by
    cases r with
    | nil => exact List.nil_sublist _
    | cons o os =>
      have hk' := List.pairwise_cons.1 (by simpa using hk :
        (c.1 :: cs.map (·.1)).Pairwise (· < ·))
      have hr' := List.pairwise_cons.1 hr
      have hvc : ∀ x ∈ cs, v x.1 = x.2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
      by_cases he : o = c.1
      · have hc : (o, v o) = c := by
          apply Prod.ext
          · exact he
          · simpa [he] using hv c List.mem_cons_self
        simp only [List.map_cons, hc]
        refine List.Sublist.cons_cons _ (coins_sublist v cs os hk'.2 hr'.2 (fun x hx => ?_) hvc)
        have hx' := hs x (List.mem_cons_of_mem _ hx)
        simp only [List.map_cons, List.mem_cons] at hx'
        rcases hx' with he' | hx'
        · have hox : o < x := hr'.1 x hx
          exact (Nat.ne_of_lt hox (he.trans he'.symm)).elim
        · exact hx'
      · have ho : o ∈ cs.map (·.1) := by
          have := hs o List.mem_cons_self
          simp only [List.map_cons, List.mem_cons] at this
          exact this.resolve_left he
        have hlt := hk'.1 _ ho
        refine List.Sublist.cons _ (coins_sublist v cs (o :: os) hk'.2 hr (fun x hx => ?_) hvc)
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ho
        · have hx' := hs x (List.mem_cons_of_mem _ hx)
          simp only [List.map_cons, List.mem_cons] at hx'
          rcases hx' with he' | hx'
          · have hox : o < x := hr'.1 x hx
            have hco : c.1 < o := hk'.1 o ho
            rw [he'] at hox
            exact (Nat.lt_asymm hox hco).elim
          · exact hx'

theorem insertCoin_absent (c : Coin) : ∀ ds : List Coin, (∀ d ∈ ds, d.1 ≠ c.1) →
    insertCoin c ds = ds ++ [c]
  | [], _ => rfl
  | d :: ds, h => by
    have h1 := h d List.mem_cons_self
    simp [insertCoin, h1, insertCoin_absent c ds fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem any_insert (c : Coin) (o : Nat) : ∀ ds : List Coin,
    (insertCoin c ds).any (fun d => d.1 == o) = (c.1 == o || ds.any fun d => d.1 == o)
  | [] => by simp [insertCoin]
  | d :: ds => by
    have ih := any_insert c o ds
    simp only [insertCoin]
    split
    · rename_i h
      have : d.1 = c.1 := by simpa using h
      simp [this]
    · simp only [List.any_cons, ih]
      cases (d.1 == o) <;> cases (c.1 == o) <;> simp

theorem any_dedup (o : Nat) : ∀ l : List Coin,
    (dedupCoins l).any (fun d => d.1 == o) = l.any fun d => d.1 == o
  | [] => rfl
  | c :: cs => by simp [dedupCoins, any_insert, any_dedup o cs]

theorem mem_key_of_any {l : List Coin} {o : Nat} : l.any (fun d => d.1 == o) = true ↔ o ∈ l.map (·.1) := by
  simp only [List.any_eq_true, beq_iff_eq, List.mem_map]

theorem sumValues_cons (c : Coin) (l : List Coin) : sumValues (c :: l) = c.2 + sumValues l := by
  simp [sumValues]

theorem sumValues_append (a b : List Coin) : sumValues (a ++ b) = sumValues a + sumValues b := by
  simp [sumValues, List.sum_append]

/-- With distinct outpoints the set construction adds each coin once at its own value. -/
theorem sum_dedup : ∀ l : List Coin, (l.map (·.1)).Nodup → sumValues (dedupCoins l) = sumValues l
  | [], _ => rfl
  | c :: cs, h => by
    have h' := List.nodup_cons.1 (by simpa using h : (c.1 :: cs.map (·.1)).Nodup)
    have habs : ∀ d ∈ dedupCoins cs, d.1 ≠ c.1 := by
      intro d hd he
      apply h'.1
      rw [← he, ← mem_key_of_any, ← any_dedup, mem_key_of_any]
      exact List.mem_map_of_mem hd
    simp only [dedupCoins, insertCoin_absent c _ habs, sumValues_append, sum_dedup cs h'.2,
      sumValues_cons]
    simp [sumValues]
    omega

/-- A sublist and what the read holds beside it add up to the read. -/
theorem sum_complement {r read : List Coin} (hs : r.Sublist read) (hn : (read.map (·.1)).Nodup) :
    sumValues r + sumValues (read.filter fun c => !(r.any fun d => d.1 == c.1)) = sumValues read := by
  induction hs with
  | slnil => rfl
  | @cons l₁ l₂ a hs ih =>
    have h' := List.nodup_cons.1 (by simpa using hn : (a.1 :: l₂.map (·.1)).Nodup)
    have hna : (l₁.any fun d => d.1 == a.1) = false := by
      rw [← Bool.not_eq_true, mem_key_of_any]
      exact fun hm => h'.1 (hs.map _ |>.subset hm)
    simp only [List.filter_cons, hna, Bool.not_false, if_true, sumValues_cons]
    have := ih h'.2
    omega
  | @cons_cons l₁ l₂ a hs ih =>
    have h' := List.nodup_cons.1 (by simpa using hn : (a.1 :: l₂.map (·.1)).Nodup)
    have hf : (l₂.filter fun c => !(a.1 == c.1 || l₁.any fun d => d.1 == c.1)) =
        l₂.filter fun c => !(l₁.any fun d => d.1 == c.1) := by
      apply List.filter_congr
      intro c hc
      have hne : (a.1 == c.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact h'.1 (he ▸ List.mem_map_of_mem hc)
      simp [hne]
    simp only [List.filter_cons, List.any_cons, beq_self_eq_true, Bool.true_or, Bool.not_true,
      if_false, reduceCtorEq, sumValues_cons, hf]
    have := ih h'.2
    omega

theorem sum_filter_split (l : List Coin) (p q : Coin → Bool) :
    sumValues (l.filter p) =
      sumValues (l.filter fun c => p c && q c) + sumValues (l.filter fun c => p c && !q c) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.filter_cons]
    cases hp : p c <;> cases hq : q c <;> simp [sumValues_cons, ih] <;> omega

theorem sum_le_of_witness : ∀ (l D : List Coin), (l.map (·.1)).Nodup →
    (∀ c ∈ l, ∃ d ∈ D, d.1 = c.1 ∧ c.2 ≤ d.2) → sumValues l ≤ sumValues D
  | [], _, _, _ => Nat.zero_le _
  | c :: cs, D, hn, hw => by
    have h' := List.nodup_cons.1 (by simpa using hn : (c.1 :: cs.map (·.1)).Nodup)
    obtain ⟨d, hd, hk, hv⟩ := hw c List.mem_cons_self
    have hp : (D.map (·.2)).Perm ((d :: D.erase d).map (·.2)) := (List.perm_cons_erase hd).map _
    have hs : sumValues D = d.2 + sumValues (D.erase d) := by
      have := hp.sum_nat
      simpa [sumValues] using this
    have ih := sum_le_of_witness cs (D.erase d) h'.2 (fun x hx => by
      obtain ⟨y, hy, hk', hv'⟩ := hw x (List.mem_cons_of_mem _ hx)
      refine ⟨y, ?_, hk', hv'⟩
      refine (List.mem_erase_of_ne ?_).2 hy
      intro he
      apply h'.1
      rw [← hk, ← he, hk']
      exact List.mem_map_of_mem hx)
    rw [sumValues_cons, hs]
    omega

theorem insert_witness_new (c : Coin) : ∀ ds : List Coin,
    ∃ d ∈ insertCoin c ds, d.1 = c.1 ∧ c.2 ≤ d.2
  | [] => ⟨c, by simp [insertCoin], rfl, Nat.le_refl _⟩
  | x :: ds => by
    simp only [insertCoin]
    split
    · rename_i h
      exact ⟨_, List.mem_cons_self, by simpa using h, Nat.le_max_right _ _⟩
    · obtain ⟨d, hd, h1, h2⟩ := insert_witness_new c ds
      exact ⟨d, List.mem_cons_of_mem _ hd, h1, h2⟩

theorem insert_witness_old (c : Coin) : ∀ ds : List Coin, ∀ e ∈ ds,
    ∃ d ∈ insertCoin c ds, d.1 = e.1 ∧ e.2 ≤ d.2
  | [], _, h => by cases h
  | x :: ds, e, he => by
    simp only [insertCoin]
    split
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, List.mem_cons_self, rfl, Nat.le_max_left _ _⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, rfl, Nat.le_refl _⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨e, List.mem_cons_self, rfl, Nat.le_refl _⟩
      · obtain ⟨d, hd, h1, h2⟩ := insert_witness_old c ds e he
        exact ⟨d, List.mem_cons_of_mem _ hd, h1, h2⟩

theorem dedup_witness : ∀ l : List Coin, ∀ e ∈ l, ∃ d ∈ dedupCoins l, d.1 = e.1 ∧ e.2 ≤ d.2
  | [], _, h => by cases h
  | c :: cs, e, he => by
    simp only [dedupCoins]
    rcases List.mem_cons.1 he with rfl | he
    · exact insert_witness_new _ _
    · obtain ⟨d, hd, h1, h2⟩ := dedup_witness cs e he
      obtain ⟨d', hd', h1', h2'⟩ := insert_witness_old c _ d hd
      exact ⟨d', hd', h1'.trans h1, Nat.le_trans h2 h2'⟩

/-! ## The denominator stays whole -/

/-- `DUR-22`'s denominator is at least the read less the outputs it excludes, whichever Escapes are
selected, given `SPN-25`'s agreement on the coins they share. Nothing a request omits leaves it. -/
@[req "DUR-22"]
theorem base_le_denominator (p : Coverage.Pass) (under : Coverage.Escape)
    (hn : (p.read.map (·.1)).Nodup)
    (hv : ∀ c ∈ p.read, ∀ d ∈ p.selected.flatMap Coverage.Escape.inputs, d.1 = c.1 → c.2 ≤ d.2) :
    sumValues (p.read.filter fun c =>
        !((p.selected.flatMap Coverage.Escape.outputs ++ p.residentRungs).contains c.1)) ≤
      Coverage.denominator .restoreAll .countedWhenSpent p under := by
  have hraw := dedup_witness (p.selected.flatMap Coverage.Escape.inputs)
  unfold Coverage.denominator Coverage.countedInputs
  simp only
  rw [sum_filter_split _ _ fun c =>
    (dedupCoins (p.selected.flatMap Coverage.Escape.inputs)).any fun d => d.1 == c.1]
  refine Nat.add_le_add ?_ (Nat.le_refl _)
  apply sum_le_of_witness
  · exact (List.filter_sublist.map _).nodup hn
  · intro c hc
    obtain ⟨hr, hany⟩ := List.mem_filter.1 hc
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hany
    obtain ⟨d, hd, he⟩ := hany.2
    have hsel : c.1 ∈ (p.selected.flatMap Coverage.Escape.inputs).map (·.1) := by
      rw [← mem_key_of_any, ← any_dedup, mem_key_of_any, ← he]
      exact List.mem_map_of_mem hd
    obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hsel
    obtain ⟨d', hd', h1, h2⟩ := hraw x hx
    exact ⟨d', hd', h1.trans hxk, Nat.le_trans (hv c hr x hx hxk) h2⟩

namespace Vault

theorem read_pass (s : Vault) (q : Request) : (s.pass q).read = s.read := rfl

/-- A request drawn from the read is measured against the whole read, whichever coins it omits. -/
@[req "DUR-22"]
theorem denominator_request (s : Vault) (q : Request)
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hc : (s.coins q.inputs).Sublist s.read) (hn : (s.read.map (·.1)).Nodup) :
    s.denominator q = s.total := by
  have hnc : ((s.coins q.inputs).map (·.1)).Nodup := (hc.map _).nodup hn
  have hsum := sum_complement hc hn
  have hdd := sum_dedup _ hnc
  have hfil : (s.read.filter fun c => !(dedupCoins (s.coins q.inputs)).any fun d => d.1 == c.1) =
      s.read.filter fun c => !((s.coins q.inputs).any fun d => d.1 == c.1) :=
    List.filter_congr fun c _ => by rw [any_dedup]
  simp only [denominator, hd, hx, Coverage.denominator, Coverage.countedInputs, pass,
    VaultUnspent.passOf, VaultUnspent.Snapshot.vaultUnspent, escape, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, total, read] at *
  simp only [hdd, List.contains_nil, Bool.not_false, Bool.true_and]
  rw [hfil]
  exact hsum

/-! ## What a valid request establishes -/

theorem shown_of_ancestry {s : Vault} {r : List Outpoint} (h : s.ancestryOk r = true) :
    ∀ o ∈ r, o ∈ s.read.map (·.1) := by
  intro o ho
  simp only [ancestryOk, Package.validate, Package.residentRead] at h
  split at h
  · rename_i hm
    simp [Package.Verdict.isAdmitted] at h
  · rename_i hm
    have hf := List.find?_eq_none.1 hm o ho
    simp only [List.contains_nil, Bool.or_false, Bool.not_eq_true', Bool.not_eq_true,
      Package.shown, Bool.not_eq_false] at hf
    exact mem_key_of_any.1 hf

/-- An accepted request's coins are a sublist of a sorted read with agreeing values. -/
theorem coins_of_nodeOk {s : Vault} {lim : Limits} {rule : ParentRule} {q : Request}
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (h : s.nodeOk lim rule q = true) : (s.coins q.inputs).Sublist s.read := by
  simp only [nodeOk, Bool.and_eq_true] at h
  exact coins_sublist _ _ _ ((ascending_iff _).1 hs) ((ascending_iff _).1 h.1.1.1.1.2)
    (shown_of_ancestry h.1.1.2) hv

/-- An accepted request covers the whole read from its own inputs. -/
@[req "DUR-24"]
theorem covers_of_nodeOk {s : Vault} {lim : Limits} {rule : ParentRule} {q : Request}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (h : s.nodeOk lim rule q = true) : s.total * s.cfg.pct ≤ (s.inSum q.inputs - q.fee) * 100 := by
  have hc := coins_of_nodeOk hs hv h
  have hn : (s.read.map (·.1)).Nodup :=
    ((ascending_iff _).1 hs).imp fun hlt => Nat.ne_of_lt hlt
  have hde := denominator_request s q hd hx hc hn
  simp only [nodeOk, Bool.and_eq_true] at h
  have hcv := h.2
  simp only [coverOk, Coverage.covers, hde, decide_eq_true_eq, escape] at hcv
  exact hcv

/-! ## The refutation -/

/-- If every accepted request carries at most `K`, and `K` does not reach the required share of the
whole read, there is no accepted request at all. -/
@[req "DUR-24"]
theorem no_nodeOk_of_value_bound {s : Vault} {lim : Limits} {rule : ParentRule} {K : Nat}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hK : ∀ q, s.nodeOk lim rule q = true → s.inSum q.inputs ≤ K)
    (hlt : K * 100 < s.total * s.cfg.pct) (q : Request) : s.nodeOk lim rule q = false := by
  rw [← Bool.not_eq_true]
  intro h
  have h1 := covers_of_nodeOk hd hx hs hv h
  have h2 : (s.inSum q.inputs - q.fee) * 100 ≤ K * 100 :=
    Nat.mul_le_mul_right 100 (Nat.le_trans (Nat.sub_le _ _) (hK q h))
  omega

/-- The same over bounded requests: the general form every shape below instantiates. -/
@[req "DUR-24"]
theorem no_request_of_value_bound {s : Vault} {lim : Limits} {rule : ParentRule} {K : Nat}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hK : ∀ q, s.bounded lim rule q = true → s.inSum q.inputs ≤ K)
    (hlt : K * 100 < s.total * s.cfg.pct) (q : Request) : s.bounded lim rule q = false := by
  rw [← Bool.not_eq_true]
  intro h
  have hn : s.nodeOk lim rule q = true := by
    simp only [bounded, Bool.and_eq_true] at h; exact h.1
  have h1 := covers_of_nodeOk hd hx hs hv hn
  have h2 : (s.inSum q.inputs - q.fee) * 100 ≤ K * 100 :=
    Nat.mul_le_mul_right 100 (Nat.le_trans (Nat.sub_le _ _) (hK q h))
  omega

/-- `OPR-35`'s vsize bound limits the input count: above the first count over the cap, no request. -/
@[req "OPR-35"]
theorem inputs_le_of_vsize {s : Vault} {lim : Limits} {rule : ParentRule} {N : Nat}
    (hover : vsizeCap < vsizeOf lim (N + 1)) {q : Request} (h : s.bounded lim rule q = true) :
    q.inputs.length ≤ N := by
  simp only [bounded, boundOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hv := h.2.1.1
  refine Nat.le_of_not_lt fun hne => ?_
  have := vsizeOf_mono lim (show N + 1 ≤ q.inputs.length by omega)
  omega

theorem retained_ge {s : Vault} {m : Nat} : ∀ r : List Outpoint, (∀ o ∈ r, m ≤ s.parentBytes o) →
    r.length * (inputMaps * m) ≤ s.retained r
  | [], _ => by simp [retained]
  | o :: os, h => by
    have ih := retained_ge (s := s) os fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h1 := Nat.mul_le_mul_left inputMaps (h o List.mem_cons_self)
    simp only [retained, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      at *
    omega

/-- `OPR-35`'s retention bound limits how many coins with parents of at least `m` bytes a request
holds. -/
@[req "OPR-35"]
theorem inputs_le_of_retained {s : Vault} {lim : Limits} {rule : ParentRule} {N m : Nat}
    (hm : ∀ c ∈ s.read, m ≤ s.parentBytes c.1) (hover : retainedCap < (N + 1) * (inputMaps * m))
    {q : Request} (h : s.bounded lim rule q = true) : q.inputs.length ≤ N := by
  simp only [bounded, nodeOk, boundOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hshown := shown_of_ancestry h.1.1.1.2
  have hret : s.retained q.inputs ≤ retainedCap := h.2.2
  have hge := retained_ge (s := s) (m := m) q.inputs fun o ho => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (hshown o ho)
    exact hm c hc
  refine Nat.le_of_not_lt fun hne => ?_
  have := Nat.mul_le_mul_right (inputMaps * m) (show N + 1 ≤ q.inputs.length by omega)
  omega

/-- Inside the domain, eight inputs fit `OPR-35`'s retention bound whatever their parents: a large
parent breaks that bound only with multiplicity. -/
@[req "OPR-35"]
theorem eight_inputs_always_retained (s : Vault) (hdom : ∀ o p, s.parent o = some p → p.inDomain = true)
    (r : List Outpoint) (hk : r.length ≤ 8) : s.retained r ≤ retainedCap := by
  have hb : ∀ o, s.parentBytes o ≤ consensusWeight := by
    intro o
    simp only [parentBytes]
    cases hp : s.parent o with
    | none => simp
    | some p => simpa using Parent.bytes_le (hdom o p hp)
  have hgen : ∀ l : List Outpoint, s.retained l ≤ l.length * (inputMaps * consensusWeight) := by
    intro l
    induction l with
    | nil => simp [retained]
    | cons o os ih =>
      have h1 := Nat.mul_le_mul_left inputMaps (hb o)
      simp only [retained, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        at *
      omega
  have h1 := Nat.mul_le_mul_right (inputMaps * consensusWeight) hk
  have h3 : 8 * (inputMaps * consensusWeight) ≤ retainedCap := by decide +kernel
  exact Nat.le_trans (hgen r) (Nat.le_trans h1 h3)

theorem inSum_le_count {s : Vault} {v : Nat} (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hle : ∀ c ∈ s.read, c.2 ≤ v) : ∀ r : List Outpoint, (∀ o ∈ r, o ∈ s.read.map (·.1)) →
    s.inSum r ≤ r.length * v
  | [], _ => by simp [inSum, coins, sumValues]
  | o :: os, h => by
    have ih := inSum_le_count hv hle os fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (h o List.mem_cons_self)
    have h1 := hv c hc
    have h2 := hle c hc
    simp only [inSum, coins, List.map_cons, sumValues_cons, List.length_cons, Nat.add_mul,
      Nat.one_mul] at *
    omega

/-- **Fragmentation.** At most `N` inputs, no coin above `v`: if `N` coins of `v` don't reach the
required share of the whole read, no bounded request exists. -/
@[req "DUR-24"]
theorem fragmented_infeasible {s : Vault} {lim : Limits} {rule : ParentRule} {N v : Nat}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hle : ∀ c ∈ s.read, c.2 ≤ v)
    (hN : ∀ q, s.bounded lim rule q = true → q.inputs.length ≤ N)
    (hlt : N * v * 100 < s.total * s.cfg.pct) (q : Request) : s.bounded lim rule q = false := by
  refine no_request_of_value_bound hd hx hs hv (K := N * v) (fun q hq => ?_) hlt q
  have hb := hq
  simp only [bounded, nodeOk, Bool.and_eq_true] at hq
  exact Nat.le_trans (inSum_le_count hv hle _ (shown_of_ancestry hq.1.1.1.2))
    (Nat.mul_le_mul_right v (hN q hb))

/-- A sublist's value is at most the whole's. -/
theorem sumValues_sublist {a b : List Coin} (h : a.Sublist b) : sumValues a ≤ sumValues b := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons x _ ih => rw [sumValues_cons]; omega
  | cons_cons x _ ih => rw [sumValues_cons, sumValues_cons]; omega

/-- A request all of whose coins pass a test is not accepted if what the read's passing coins carry
does not reach the required share of the whole read. -/
@[req "DUR-24"]
theorem not_nodeOk_of_usable {s : Vault} {lim : Limits} {rule : ParentRule} {usable : Coin → Bool}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hlt : sumValues (s.read.filter usable) * 100 < s.total * s.cfg.pct) {q : Request}
    (hu : ∀ c ∈ s.coins q.inputs, usable c = true) : s.nodeOk lim rule q = false := by
  rw [← Bool.not_eq_true]
  intro hn
  have hc := coins_of_nodeOk hs hv hn
  have hf := hc.filter usable
  rw [List.filter_eq_self.2 hu] at hf
  have h1 := covers_of_nodeOk hd hx hs hv hn
  have h2 : (s.inSum q.inputs - q.fee) * 100 ≤ sumValues (s.read.filter usable) * 100 :=
    Nat.mul_le_mul_right 100 (Nat.le_trans (Nat.sub_le _ _) (sumValues_sublist hf))
  omega

/-- **Value out of reach.** If no bounded request can hold a coin outside `usable`, what the usable
coins carry must reach the required share of the whole read, the unusable coins included. -/
@[req "DUR-24"]
theorem unreachable_infeasible {s : Vault} {lim : Limits} {rule : ParentRule} {usable : Coin → Bool}
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (hu : ∀ q, s.bounded lim rule q = true → ∀ c ∈ s.coins q.inputs, usable c = true)
    (hlt : sumValues (s.read.filter usable) * 100 < s.total * s.cfg.pct) (q : Request) :
    s.bounded lim rule q = false := by
  rw [← Bool.not_eq_true]
  intro h
  have hn : s.nodeOk lim rule q = false := not_nodeOk_of_usable hd hx hs hv hlt (hu q h)
  simp [bounded, hn] at h

theorem le_sum_of_mem {f : Outpoint → Nat} : ∀ {r : List Outpoint} {o : Outpoint}, o ∈ r →
    f o ≤ (r.map f).sum
  | x :: xs, o, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_mem (f := f) h
      omega

/-- With parents on the wire, a parent larger than the body cap once per PSBT is in no accepted
request, whatever else the request holds. -/
@[req "API-4"]
theorem carried_parent_over_body {s : Vault} {lim : Limits} {rule : ParentRule} {r : List Outpoint}
    {o : Outpoint} (ho : o ∈ r) (hover : bodyCap < lim.psbts * s.parentBytes o) :
    s.wireOk lim rule r true = false := by
  have h1 := le_sum_of_mem (f := fun o => lim.psbts * (lim.perInput + s.parentBytes o)) ho
  have h2 : lim.psbts * s.parentBytes o ≤ lim.psbts * (lim.perInput + s.parentBytes o) :=
    Nat.mul_le_mul_left _ (by omega)
  have hnot : ¬ s.wire lim r true ≤ bodyCap := by
    simp only [wire, if_true]
    simp only at h1
    omega
  simp [wireOk, hnot]

end Vault

/-! ## The closed form under a count bound -/

/-- The most value `k` coins of a list carry. -/
def best : Nat → List Coin → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, c :: cs => max (best (k + 1) cs) (c.2 + best k cs)

theorem best_ge : ∀ (l r : List Coin) (k : Nat), r.Sublist l → r.length ≤ k → sumValues r ≤ best k l
  | [], r, k, hs, _ => by
    have := List.sublist_nil.1 hs
    subst this
    simp [sumValues]
  | c :: cs, r, k, hs, hk => by
    cases k with
    | zero =>
      have := List.length_eq_zero_iff.1 (Nat.le_zero.1 hk)
      subst this
      simp [sumValues, best]
    | succ k =>
      simp only [best]
      cases hs with
      | cons _ h => exact Nat.le_trans (best_ge cs r (k + 1) h hk) (Nat.le_max_left _ _)
      | cons_cons _ h =>
        rw [sumValues_cons]
        refine Nat.le_trans ?_ (Nat.le_max_right _ _)
        exact Nat.add_le_add_left (best_ge cs _ k h (by simpa using hk)) _

theorem best_attained : ∀ (l : List Coin) (k : Nat),
    ∃ r : List Coin, r.Sublist l ∧ r.length ≤ k ∧ sumValues r = best k l
  | [], k => by
    refine ⟨[], List.Sublist.refl _, by simp, ?_⟩
    cases k <;> simp [sumValues, best]
  | c :: cs, 0 => ⟨[], List.nil_sublist _, by simp, by simp [sumValues, best]⟩
  | c :: cs, k + 1 => by
    simp only [best]
    by_cases h : c.2 + best k cs ≤ best (k + 1) cs
    · obtain ⟨r, h1, h2, h3⟩ := best_attained cs (k + 1)
      exact ⟨r, h1.cons _, h2, by omega⟩
    · obtain ⟨r, h1, h2, h3⟩ := best_attained cs k
      refine ⟨c :: r, h1.cons_cons _, by simpa using h2, ?_⟩
      rw [sumValues_cons]
      omega

/-- The named assumption of the closed form: over canonical inputs drawn from the read, the size
bounds and the ancestry walk reduce to a count bound `N` and a per-coin usable test. It holds only
when no additive bound binds before `N`, and each exhibit that uses it discharges it. -/
structure CountOnly (s : Vault) (lim : Limits) (rule : ParentRule) (carried : Bool)
    (usable : Coin → Bool) (N : Nat) : Prop where
  shape : ∀ r : List Outpoint, r ≠ [] → (s.coins r).Sublist s.read →
    ((s.wireOk lim rule r carried && s.ancestryOk r && s.boundOk lim r) = true ↔
      r.length ≤ N ∧ ∀ c ∈ s.coins r, usable c = true)

/-- **Feasibility characterized under a count bound.** A bounded request exists exactly when, for
some count within `N`, the most valuable usable coins of that count, less the floor's fee at that
count, reach the required share of the WHOLE read. The usable test narrows the numerator; nothing
narrows `s.total`. -/
@[req "DUR-24"]
theorem feasible_iff_best (s : Vault) (lim : Limits) (rule : ParentRule) (carried : Bool)
    (usable : Coin → Bool) (N : Nat)
    (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.read.map (·.1)) = true) (hv : ∀ c ∈ s.read, s.cfg.book.value c.1 = c.2)
    (htotal : 0 < s.total) (hpct : 0 < s.cfg.pct) (hc : CountOnly s lim rule carried usable N) :
    (∃ q, q.carried = carried ∧ s.bounded lim rule q = true) ↔
      ∃ k, k ≤ N ∧ s.total * s.cfg.pct ≤
        (best k (s.read.filter usable) - s.floor * vsizeOf lim k) * 100 := by
  have hpos : 0 < s.total * s.cfg.pct := Nat.mul_pos htotal hpct
  have hnk : (s.read.map (·.1)).Pairwise (· < ·) := (ascending_iff _).1 hs
  constructor
  · rintro ⟨q, rfl, h⟩
    have hn : s.nodeOk lim rule q = true := by
      simp only [Vault.bounded, Bool.and_eq_true] at h; exact h.1
    have hcs := Vault.coins_of_nodeOk hs hv hn
    have hcov := Vault.covers_of_nodeOk hd hx hs hv hn
    simp only [Vault.bounded, Vault.nodeOk, Bool.and_eq_true] at h
    have hne : q.inputs ≠ [] := by
      intro he
      have := h.1.1.1.1.1.1
      simp [he] at this
    obtain ⟨hN, hu⟩ := (hc.shape q.inputs hne hcs).1 (by
      simp only [Bool.and_eq_true]
      exact ⟨⟨h.1.1.1.1.2, h.1.1.1.2⟩, h.2⟩)
    refine ⟨q.inputs.length, hN, Nat.le_trans hcov (Nat.mul_le_mul_right 100 ?_)⟩
    have hfee : s.floor * vsizeOf lim q.inputs.length ≤ q.fee := by
      have := h.1.1.2
      simp only [Vault.feeOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hf := hcs.filter usable
    rw [List.filter_eq_self.2 hu] at hf
    have hb := best_ge _ _ q.inputs.length hf (by simp [Vault.coins])
    have : s.inSum q.inputs ≤ best q.inputs.length (s.read.filter usable) := hb
    omega
  · rintro ⟨k, hkN, hcov⟩
    obtain ⟨r', hr', hlen, hsum⟩ := best_attained (s.read.filter usable) k
    rw [← hsum] at hcov
    have hrr : r'.Sublist s.read := hr'.trans List.filter_sublist
    let r := r'.map (·.1)
    have hcoins : s.coins r = r' := by
      simp only [Vault.coins, r, List.map_map]
      conv => rhs; rw [← List.map_id r']
      apply List.map_congr_left
      intro c hc'
      exact Prod.ext rfl (hv c (hrr.subset hc'))
    have hrl : r.length = r'.length := by simp [r]
    have hne : r ≠ [] := by
      intro he
      have : r' = [] := by simpa [r] using he
      subst this
      simp [sumValues] at hcov
      omega
    have hpw : r.Pairwise (· < ·) := List.Pairwise.sublist (hrr.map _) hnk
    have hshape := (hc.shape r hne (by rw [hcoins]; exact hrr)).2
      ⟨by omega, by
        rw [hcoins]
        intro c hc'
        exact (List.mem_filter.1 (hr'.subset hc')).2⟩
    simp only [Bool.and_eq_true] at hshape
    have hvm := Nat.mul_le_mul_left s.floor (vsizeOf_mono lim hlen)
    have hin : s.inSum r = sumValues r' := by simp [Vault.inSum, hcoins]
    let q : Request := { txid := 0, inputs := r, fee := s.floor * vsizeOf lim r.length, carried }
    have hdel : s.total * s.cfg.pct ≤ (s.inSum r - q.fee) * 100 := by
      refine Nat.le_trans hcov (Nat.mul_le_mul_right 100 ?_)
      show _ ≤ s.inSum r - s.floor * vsizeOf lim r.length
      rw [hin, hrl]
      omega
    have hde : s.denominator q = s.total :=
      Vault.denominator_request s q hd hx (by simp only [q]; rw [hcoins]; exact hrr)
        (hnk.imp fun hlt => Nat.ne_of_lt hlt)
    refine ⟨q, rfl, ?_⟩
    simp only [Vault.bounded, Vault.nodeOk, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, hshape.1.1⟩, hshape.1.2⟩, ?_⟩, ?_⟩, hshape.2⟩
    · simp [q, hne]
    · exact (ascending_iff _).2 hpw
    · simp only [Vault.feeOk, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨Nat.le_refl _, ?_⟩
      show q.fee ≤ s.inSum r
      refine Nat.le_of_not_lt fun hlt => ?_
      have h0 : s.inSum r - q.fee = 0 := by omega
      rw [h0] at hdel
      omega
    · simp only [Vault.coverOk, Coverage.covers, hde, decide_eq_true_eq, Vault.escape]
      exact hdel

theorem ancestors_of_no_unconfirmed {creator : Package.Creator} {mem : Package.MempoolRead}
    {ins : List Outpoint} (h : ∀ o ∈ ins, mem.lookup (creator o) = none) :
    Package.ancestors creator mem ins = [] := by
  have hp : Package.unconfirmedParents creator mem ins = [] := by
    simp only [Package.unconfirmedParents, List.filter_eq_nil_iff, List.mem_map]
    rintro _ ⟨o, ho, rfl⟩
    simp [h o ho]
  have hstep : ∀ n : Nat, Nat.repeat (Package.expand creator mem) n [] = [] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [Nat.repeat, ih, Package.expand, Package.insertAll]
  simp [Package.ancestors, hp, Package.insertAll, hstep]

theorem sum_const (w : Nat) : ∀ r : List Outpoint, (r.map fun _ => w).sum = r.length * w
  | [] => by simp
  | _ :: os => by
    have := sum_const w os
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- `CountOnly` holds where no additive bound binds before the vsize bound does: nothing
unconfirmed, every parent present and small, and the wire slack at `N` stripped inputs. -/
@[req "DUR-24"]
theorem countOnly_of_slack (s : Vault) (lim : Limits) (rule : ParentRule) (N m : Nat)
    (hrule : rule ≠ .refuse) (hover : vsizeCap < vsizeOf lim (N + 1)) (hin : vsizeOf lim N ≤ vsizeCap)
    (hwire : lim.shell + N * (lim.psbts * lim.perInput) ≤ bodyCap)
    (hmsg : lim.shell + N * (lim.psbts * lim.perInput) + lim.envelope ≤ lim.msg)
    (hpar : ∀ c ∈ s.read, (s.parent c.1).isSome = true) (hbytes : ∀ c ∈ s.read, s.parentBytes c.1 ≤ m)
    (hret : N * (inputMaps * m) ≤ retainedCap)
    (hconf : ∀ c ∈ s.read, s.b.mempool.lookup (s.cfg.creator c.1) = none) :
    CountOnly s lim rule false (fun _ => true) N := by
  refine ⟨fun r _ hsub => ?_⟩
  have hmem : ∀ o ∈ r, ∃ c ∈ s.read, c.1 = o := by
    intro o ho
    have : (o, s.cfg.book.value o) ∈ s.coins r := List.mem_map.2 ⟨o, ho, rfl⟩
    exact ⟨_, hsub.subset this, rfl⟩
  constructor
  · intro h
    simp only [Bool.and_eq_true, Vault.boundOk, decide_eq_true_eq] at h
    refine ⟨Nat.le_of_not_lt fun hne => ?_, fun _ _ => rfl⟩
    have := vsizeOf_mono lim (show N + 1 ≤ r.length by omega)
    have := h.2.1.1
    omega
  · rintro ⟨hN, -⟩
    have hsum : (r.map fun o => lim.psbts * (lim.perInput + if false = true then s.parentBytes o else 0)).sum
        = r.length * (lim.psbts * lim.perInput) := by
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact sum_const _ r
    have hmul := Nat.mul_le_mul_right (lim.psbts * lim.perInput) hN
    have hW : s.wire lim r false ≤ lim.shell + N * (lim.psbts * lim.perInput) := by
      simp only [Vault.wire]
      rw [hsum]
      omega
    have hgen : ∀ l : List Outpoint, (∀ o ∈ l, ∃ c ∈ s.read, c.1 = o) →
        s.retained l ≤ l.length * (inputMaps * m) := by
      intro l
      induction l with
      | nil => simp [Vault.retained]
      | cons o os ih =>
        intro hl
        have h0 := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
        obtain ⟨c, hc, rfl⟩ := hl o List.mem_cons_self
        have h1 := Nat.mul_le_mul_left inputMaps (hbytes c hc)
        simp only [Vault.retained, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at *
        omega
    simp only [Bool.and_eq_true, Vault.boundOk, decide_eq_true_eq, Vault.wireOk, List.all_eq_true]
    refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, ⟨Nat.le_trans (vsizeOf_mono lim hN) hin, ?_⟩, ?_⟩
    · cases rule with
      | refuse => exact absurd rfl hrule
      | ignore => rfl
      | verify => rfl
    · have hanc : Package.ancestors s.cfg.creator s.b.mempool r = [] := by
        apply ancestors_of_no_unconfirmed
        intro o ho
        obtain ⟨c, hc, rfl⟩ := hmem o ho
        exact hconf c hc
      have hnone : Package.missingPrevout s.snap [] r = none := by
        simp only [Package.missingPrevout]
        apply List.find?_eq_none.2
        intro o ho
        obtain ⟨c, hc, rfl⟩ := hmem o ho
        have := mem_key_of_any.2 (List.mem_map_of_mem hc : c.1 ∈ s.read.map (·.1))
        simpa [Package.shown, Vault.read] using this
      simp [Vault.ancestryOk, Package.validate, Package.residentRead, hnone, hanc,
        Package.ancestryVerdict, Package.Verdict.isAdmitted, Package.ancestorLimit]
    · intro o ho
      obtain ⟨c, hc, rfl⟩ := hmem o ho
      exact hpar c hc
    · exact Nat.le_trans (hgen r hmem) (Nat.le_trans (Nat.mul_le_mul_right _ hN) hret)

/-! ## The composer against the request -/

theorem composeEvery_carried {lim : Limits} {txid : Nat} {s : Vault} {q : Request}
    (h : composeEvery lim txid s = .ok q) : q.carried = false := by
  simp only [composeEvery] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rfl

/-- `OPR-46` strips every parent, so under `F48`'s `refuse` reading a composed request never passes:
that reading and the stripped wire cannot both stand. -/
@[req "OPR-46"]
theorem refuse_refuses_composed {lim : Limits} {txid : Nat} {s : Vault} {q : Request}
    (h : composeEvery lim txid s = .ok q) : s.bounded lim .refuse q = false := by
  have hc := composeEvery_carried h
  simp [Vault.bounded, Vault.nodeOk, Vault.wireOk, hc]

/-- **What the composer builds validates.** With no unconfirmed vault-authorized value at the read
and every confirmed coin's creator outside the mempool, a composed request is bounded under `F48`'s
`ignore` and `verify` readings. The converse fails: `Exhibits.Feasibility.dust_stops_composer_only` and
`Exhibits.Feasibility.prior_spend_composer_refuses` hold bounded requests at states the composer refuses. -/
@[req "OPR-33"]
theorem compose_bounded {lim : Limits} {txid : Nat} {s : Vault} {q : Request} (rule : ParentRule)
    (hrule : rule ≠ .refuse) (hd : s.cfg.denominator = .restoreAll)
    (hx : s.cfg.external = .countedWhenSpent)
    (hs : ascending (s.b.confirmed.map (·.1)) = true)
    (hv : ∀ c ∈ s.b.confirmed, s.cfg.book.value c.1 = c.2)
    (hadd : Sweep.additions s.A s.b = [])
    (hconf : ∀ c ∈ s.b.confirmed, s.b.mempool.lookup (s.cfg.creator c.1) = none)
    (h : composeEvery lim txid s = .ok q) : s.bounded lim rule q = true := by
  have hcar := composeEvery_carried h
  simp only [composeEvery] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hempty hvs
  split at h
  · cases h
  rename_i hsp
  split at h
  · cases h
  rename_i hpar
  split at h
  · cases h
  rename_i hret
  split at h
  · cases h
  rename_i hwire
  split at h
  · cases h
  rename_i hfee
  split at h
  · cases h
  rename_i hcov
  cases h
  have hEi : (everyRequest lim txid s).inputs = s.b.confirmed.map (·.1) := rfl
  have hEf : (everyRequest lim txid s).fee = s.floor * vsizeOf lim (s.b.confirmed.map (·.1)).length := rfl
  have hread : s.read = s.b.confirmed := by
    have hnone := List.find?_eq_none.1 hsp
    simp only [Vault.read, Vault.snap, Sweep.snapshot, hadd, List.append_nil]
    apply List.filter_eq_self.2
    intro c hc
    simpa using hnone c.1 (List.mem_map_of_mem hc)
  have hcoins : s.coins (s.b.confirmed.map (·.1)) = s.b.confirmed := by
    simp only [Vault.coins, List.map_map]
    conv => rhs; rw [← List.map_id s.b.confirmed]
    apply List.map_congr_left
    intro c hc
    exact Prod.ext rfl (hv c hc)
  have hnk : (s.b.confirmed.map (·.1)).Pairwise (· < ·) := (ascending_iff _).1 hs
  have hde := Vault.denominator_request s (everyRequest lim txid s) hd hx
    (by rw [hEi, hcoins, hread]; exact List.Sublist.refl _)
    (by rw [hread]; exact hnk.imp fun hlt => Nat.ne_of_lt hlt)
  have hempty' : (s.b.confirmed.map (·.1)).isEmpty = false := by
    cases hc : s.b.confirmed with
    | nil => simp [hc] at hempty
    | cons _ _ => rfl
  have hanc : s.ancestryOk (s.b.confirmed.map (·.1)) = true := by
    have hempty'' : Package.ancestors s.cfg.creator s.b.mempool (s.b.confirmed.map (·.1)) = [] := by
      apply ancestors_of_no_unconfirmed
      intro o ho
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact hconf c hc
    simp only [Vault.ancestryOk, Package.validate, Package.residentRead, hempty'',
      Package.ancestryVerdict]
    have hnone : Package.missingPrevout s.snap [] (s.b.confirmed.map (·.1)) = none := by
      simp only [Package.missingPrevout]
      apply List.find?_eq_none.2
      intro o ho
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      have hm : c.1 ∈ s.read.map (·.1) := by rw [hread]; exact List.mem_map_of_mem hc
      have := mem_key_of_any.2 hm
      simpa [Package.shown, Vault.read] using this
    simp [hnone, Package.ancestorLimit, Package.Verdict.isAdmitted]
  simp only [Vault.bounded, Vault.nodeOk, Bool.and_eq_true, hEi]
  have hw : s.wireOk lim .ignore (s.b.confirmed.map (·.1)) false = true := by
    simpa using hwire
  refine ⟨⟨⟨⟨⟨⟨by simp [hempty'], hs⟩, ?_⟩, hanc⟩, ?_⟩, ?_⟩, ?_⟩
  · have hc0 : (everyRequest lim txid s).carried = false := rfl
    rw [hc0]
    simp only [Vault.wireOk, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
    refine ⟨hw.1, ?_⟩
    cases rule with
    | refuse => exact absurd rfl hrule
    | ignore => rfl
    | verify => rfl
  · simp only [Vault.feeOk, Bool.and_eq_true, decide_eq_true_eq, hEi, hEf, Vault.inSum, hcoins]
    exact ⟨Nat.le_refl _, by omega⟩
  · simp only [Vault.coverOk, hde, Vault.escape, hEi, hEf, Vault.inSum, hcoins, Vault.total, hread]
    simpa using hcov
  · simp only [Vault.boundOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨by omega, fun o ho => ?_⟩, by omega⟩
    have := List.find?_eq_none.1 hpar o ho
    simpa [Option.isSome_iff_ne_none] using this

/-! ## No way around a deep coin -/

theorem mem_insertAll_left (ts acc : List Nat) (t : Nat) (h : t ∈ acc) : t ∈ Package.insertAll ts acc := by
  induction ts generalizing acc with
  | nil => exact h
  | cons x xs ih =>
    simp only [Package.insertAll, List.foldl_cons]
    apply ih
    simp only [Package.insertNew]
    split
    · exact h
    · exact List.mem_cons_of_mem _ h

theorem mem_insertAll_right (ts acc : List Nat) (t : Nat) (h : t ∈ ts) : t ∈ Package.insertAll ts acc := by
  induction ts generalizing acc with
  | nil => cases h
  | cons x xs ih =>
    simp only [Package.insertAll, List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · apply mem_insertAll_left
      simp only [Package.insertNew]
      split
      · assumption
      · exact List.mem_cons_self
    · exact ih _ h

theorem expand_mono (creator : Package.Creator) (mem : Package.MempoolRead) {a b : List Nat}
    (h : a ⊆ b) : Package.expand creator mem a ⊆ Package.expand creator mem b := by
  intro t ht
  rcases Package.mem_insertAll _ _ t ht with hl | hr
  · apply mem_insertAll_right
    obtain ⟨x, hx, hxt⟩ := List.mem_flatMap.1 hl
    exact List.mem_flatMap.2 ⟨x, h hx, hxt⟩
  · exact mem_insertAll_left _ _ _ (h hr)

theorem nodup_length_le : ∀ {a b : List Nat}, a.Nodup → a ⊆ b → a.length ≤ b.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, b, hn, hs => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 hn
    have hx : x ∈ b := hs List.mem_cons_self
    have hsub : xs ⊆ b.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun (he : y = x) => h1 (he ▸ hy))).2 (hs (List.mem_cons_of_mem _ hy))
    have := nodup_length_le h2 hsub
    have hl := List.length_erase_of_mem hx
    have hp : 0 < b.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- The walk grows with its inputs. -/
theorem ancestors_mono (creator : Package.Creator) (mem : Package.MempoolRead) {a b : List Outpoint}
    (h : a ⊆ b) : Package.ancestors creator mem a ⊆ Package.ancestors creator mem b := by
  unfold Package.ancestors
  have hbase : Package.insertAll (Package.unconfirmedParents creator mem a) [] ⊆
      Package.insertAll (Package.unconfirmedParents creator mem b) [] := by
    intro t ht
    rcases Package.mem_insertAll _ _ t ht with hl | hr
    · apply mem_insertAll_right
      simp only [Package.unconfirmedParents, List.mem_filter, List.mem_map] at hl ⊢
      obtain ⟨⟨o, ho, rfl⟩, hk⟩ := hl
      exact ⟨⟨o, h ho, rfl⟩, hk⟩
    · cases hr
  generalize mem.length = n
  induction n with
  | zero => exact hbase
  | succ n ih => exact expand_mono creator mem ih

/-- **A coin whose own ancestry is over the limit is in no request.** `WTC-24`'s walk only grows with
the inputs, so no selection around it brings the count back inside the limit, and adding coins to the
request never helps. -/
@[req "WTC-24"]
theorem deep_coin_excluded {s : Vault} {r : List Outpoint} {o : Outpoint} (ho : o ∈ r)
    (hdeep : Package.ancestorLimit < (Package.ancestors s.cfg.creator s.b.mempool [o]).length)
    : s.ancestryOk r = false := by
  have hsub := ancestors_mono s.cfg.creator s.b.mempool (a := [o]) (b := r) (by simpa using ho)
  have hnd := Package.ancestors_nodup s.cfg.creator s.b.mempool [o]
  have hle : (Package.ancestors s.cfg.creator s.b.mempool [o]).length ≤
      (Package.ancestors s.cfg.creator s.b.mempool r).length :=
    nodup_length_le hnd hsub
  simp only [Vault.ancestryOk, Package.validate, Package.residentRead]
  split
  · rfl
  · simp only [Package.ancestryVerdict]
    split
    · rfl
    · have : ¬ (Package.ancestors s.cfg.creator s.b.mempool r).length ≤ Package.ancestorLimit := by
        omega
      simp [this, Package.Verdict.isAdmitted]

/-! ## The bridge to the sweep -/

/-- What `Sweep.covered` reads at a node, whichever Escapes it has selected: if this candidate
delivers at most `K` and `K` does not reach the required share of the read less the excluded outputs,
it does not cover. -/
@[req "DUR-24"]
theorem covered_false_of_value_bound (cfg : Sweep.Cfg) (A : List Nat) (n : Kernel.Node)
    (b : Sweep.Backend) (c : Kernel.Cand) (K : Nat)
    (hd : cfg.denominator = .restoreAll) (hx : cfg.external = .countedWhenSpent)
    (hn : (((Sweep.snapshot A b).read).map (·.1)).Nodup)
    (hv : ∀ x ∈ (Sweep.snapshot A b).read, cfg.book.value x.1 = x.2)
    (hdel : cfg.book.delivered c.tx.id ≤ K)
    (hlt : K * 100 < sumValues ((Sweep.passAt cfg A n b).read.filter fun x =>
        !(((Sweep.passAt cfg A n b).selected.flatMap Coverage.Escape.outputs ++
          (Sweep.passAt cfg A n b).residentRungs).contains x.1)) * cfg.pct) :
    Sweep.covered cfg A n b c = false := by
  have hbase := base_le_denominator (Sweep.passAt cfg A n b) (Sweep.escapeOf cfg.book c.tx) hn (by
    intro x hx' d hd' hk
    obtain ⟨e, he, hde⟩ := List.mem_flatMap.1 hd'
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 he
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 hde
    have h1 := hv x hx'
    have hk' : o = x.1 := hk
    have h2 : cfg.book.value o = x.2 := by rw [hk']; exact h1
    exact Nat.le_of_eq h2.symm)
  rw [← Bool.not_eq_true]
  intro h
  simp only [Sweep.covered, hd, hx, Coverage.covers, decide_eq_true_eq] at h
  have h1 := Nat.mul_le_mul_right cfg.pct hbase
  have h2 := Nat.mul_le_mul_right 100 hdel
  omega

/-- So the assembly of that candidate's commitment is not admitted at the read: the sweep takes the
coverage verdict and no step goes around it. -/
@[req "DUR-29"]
theorem assembly_refused {cfg : Sweep.Cfg} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Kernel.Env} {b : Sweep.Backend} {c : Kernel.Cand}
    (hobs : st.obs i = some b) (hc : c ∈ (st.fed.worlds i).node.cands) (he : c.isEscape = true)
    (hcov : Sweep.covered cfg (Sweep.authorizedAt st T i) (st.fed.worlds i).node b c = false) :
    Sweep.assemblyOk cfg st T (.process i env (.packageAccepted c.id)) = false := by
  simp only [Sweep.assemblyOk, List.all_eq_false, Bool.not_eq_true]
  refine ⟨c, hc, ?_⟩
  simp [he, Sweep.check, hobs, hcov]

/-- `Sweep.submitted_in_order`'s other direction: the assembly is the only road to an Escape's
submission, so if at every assembly step of the history the node's read left the candidate uncovered,
that Escape is never submitted. The premise is per assembly step because a node reads a different
instant at each. -/
@[req "DUR-29"]
theorem no_submission_of_uncovered {cfg : Sweep.Cfg} {r : Kernel.Rules} {honest : List Nat}
    {T : Sweep.Trace} {st : Sweep.State} (hr : r.reauth = .beforeSend)
    (hx : Sweep.Execution cfg r honest T st) {i : Nat} {env : Kernel.Env} {cid x : Nat}
    (hes : ∀ c ∈ (st.fed.worlds i).node.cands, c.id = cid → c.isEscape = true)
    (hall : ∀ T₁ T₂ st₁ env₁ b, T = T₂ ++ (st₁, .fed (.process i env₁ (.packageAccepted cid))) :: T₁ →
      st₁.obs i = some b → ∀ d ∈ (st₁.fed.worlds i).node.cands, d.id = cid →
        Sweep.covered cfg (Sweep.authorizedAt st₁ T₁ i) (st₁.fed.worlds i).node b d = false)
    (ha : Sweep.admits cfg honest st T (.fed (.process i env (.send cid))) = true)
    (hs : x ∈ Sweep.submits r st (.fed (.process i env (.send cid)))) : False := by
  obtain ⟨c, hc, hid, -, -, -, -, hasm⟩ := Sweep.submitted_in_order hr hx ha hs
  obtain ⟨T₁, T₂, st₁, env₁, d, hT, hd, hdi, -, -, hchk, -⟩ := hasm (hes c hc hid)
  subst hid
  simp only [Sweep.check] at hchk
  cases hobs : st₁.obs i with
  | none => simp [hobs] at hchk
  | some b =>
    have hbad := hall T₁ T₂ st₁ env₁ b hT hobs d hd hdi
    simp [hobs, hbad] at hchk

/-! ## Bounded-selection ideas, compared and not chosen

`F1` lists "deterministic bounded input selection" among its candidates. These two are that family's
simplest members, there to be measured by `bounded`: neither is a rule of this set. -/

/-- A request over these inputs at the floor's fee, parents stripped. -/
def requestOver (s : Vault) (lim : Limits) (txid : Nat) (r : List Outpoint) : Request :=
  { txid := txid, inputs := r, fee := s.floor * vsizeOf lim r.length }

/-- The first `N` coins in canonical order. -/
def byPrefix (s : Vault) (lim : Limits) (txid N : Nat) : Request :=
  requestOver s lim txid ((s.read.take N).map (·.1))

def insertAsc (o : Nat) : List Nat → List Nat
  | [] => [o]
  | x :: xs => if o ≤ x then o :: x :: xs else x :: insertAsc o xs

def insertDesc (c : Coin) : List Coin → List Coin
  | [] => [c]
  | x :: xs => if x.2 < c.2 then c :: x :: xs else x :: insertDesc c xs

/-- The `N` most valuable coins, back in canonical order. -/
def byLargest (s : Vault) (lim : Limits) (txid N : Nat) : Request :=
  requestOver s lim txid
    ((((s.read.foldr insertDesc []).take N).map (·.1)).foldr insertAsc [])

end BtcPolicy.Feasibility
