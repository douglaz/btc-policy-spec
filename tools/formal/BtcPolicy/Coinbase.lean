import BtcPolicy.Feasibility
import BtcPolicy.Watchtower
import BtcPolicy.Formula
/-! The composer's immature coinbase (`OPR-33`, `OPR-38`, `OPR-65`, `OPR-68`, `WTC-28`): selection,
the additional coverage check, its report, and what a reorganization does to them. This formalizes the
adopted rules; it decides nothing about `F69`'s deployment question, and no theorem here says that
waiting is an adequate response.

**The backend stays whole.** The scan is the backend's own confirmed list, `Sweep.Backend.confirmed`, so
an immature coinbase the scan returns stays in the node's read and in `DUR-22`'s denominator, as
`WTC-6` requires ("Every path MUST serve an immature coinbase output paying the vault script, since
`DUR-22` counts it"). `accept` validates every scanned coin, then partitions the scan into the
stable confirmed inventory `U` and the immature coinbases it leaves out. The spend composer reads
`U` through `view`, the same instant with its confirmed list narrowed; the node reads the instant
itself. Nothing is deleted from a backend to filter it.

**Coinbase identity is read, not supplied.** `OPR-33`: "Whether a coin is a coinbase's output is read
from the creating transaction `OPR-82` already obtains." `Record.tx` is that transaction as `OPR-82`
obtains it: its inputs as `WTC-12` reads them (`Watchtower.Input`), the referenced output's value and
script, and its confirming header's height. `kind` derives the classification from the inputs; the
caller supplies no classification. The named boundary: that a creating transaction's bytes hash to
the txid it was fetched by, and the header checks, are the symbolic chain boundary — `Creating.active`
stands for `OPR-82`'s "matching hash, active-chain `confirmations >= 1`", and is not derived.

**Maturity is a height condition.** `mature` counts confirmations at the accepted tip. It is kept
apart from the Recovery path's relative lock and its MTP age (`Recovery.matured`), and from refresh's
MTP age, which `refresh` takes as a parameter.

**Not modelled.** `OPR-82`'s brackets and retries; sorting (the scan is taken in canonical order, so
a duplicate shows as an out-of-order outpoint); the primary spend's outputs, dust and fee bounds
beyond `Feasibility.composeEvery`'s; refresh's age order and its partition into batches of `SPN-44`'s
input limit, its fee cap and its watch; the claw-back's fee, dust and output checks; a cache
implementation, which is runtime conformance. -/

namespace BtcPolicy.Coinbase
open BtcPolicy.Coverage (Coin Outpoint sumValues)
open BtcPolicy.Feasibility (Vault Request Limits composeEvery everyRequest vsizeOf)

/-! ## Maturity -/

/-- `OPR-33`: an immature coinbase has "fewer than 100 confirmations at the accepted tip". -/
@[req "OPR-33"] def maturity : Nat := 100

/-- Confirmations at tip height `tip` of a coin confirmed at height `h`: the block at `h` is the first.
`Nat` subtraction makes a height above the tip zero. -/
@[req "OPR-33"] def confirmations (tip h : Nat) : Nat := tip + 1 - h

/-- A coinbase output confirmed at `h` is mature at `tip` when it has at least `maturity` confirmations. -/
@[req "OPR-33"]
def mature (tip h : Nat) : Bool := maturity ≤ confirmations tip h

/-- `OPR-33`: "one confirmed at height `h` has 100 at tip height `h + 99`". -/
@[req "OPR-33"] def clearOffset : Nat := maturity - 1

/-- Property 1, for every tip and height: mature exactly from tip `h + 99`, equality included. -/
@[req "OPR-33"]
theorem mature_iff (tip h : Nat) : mature tip h = true ↔ h + clearOffset ≤ tip := by
  simp only [mature, confirmations, clearOffset, maturity, decide_eq_true_eq]
  omega

/-! ## The evidence -/

/-- The block-qualified creating transaction `OPR-82` obtains for one scanned coin: its inputs as
`WTC-12` reads them, its referenced output's value and script, its confirming header's height, and
whether that header passed `OPR-82`'s hash and active-chain checks. -/
structure Creating where
  inputs : List Watchtower.Input
  value : Nat
  script : Nat
  height : Nat
  active : Bool
  deriving DecidableEq, Repr

/-- One scanned coin's record beside the coin itself: `OPR-82`'s caller-supplied "confirmation height,
value and script" (the value is the coin's own), and the creating transaction. -/
structure Record where
  height : Nat
  script : Nat
  tx : Creating
  deriving DecidableEq, Repr

/-- One inventory pass: the sealed vault script, and a record for each scanned outpoint. -/
structure Pass where
  script : Nat
  records : List (Outpoint × Record)
  deriving DecidableEq, Repr

/-- A creating transaction's class. -/
inductive Kind
  | ordinary | coinbase
  deriving DecidableEq, Repr

def isPrevout : Watchtower.Input → Bool
  | .prevout _ => true
  | _ => false

/-- The class read from the creating transaction's inputs: a coinbase has exactly the one coinbase
input; an ordinary transaction has inputs that each carry a prevout. Anything else is inconsistent
evidence, `none`, which `accept` refuses and never reads as immaturity. -/
@[req "OPR-33"]
def kind : List Watchtower.Input → Option Kind
  | [.coinbase] => some .coinbase
  | ins => if !ins.isEmpty && ins.all isPrevout then some .ordinary else none

/-- `OPR-82`'s checks on one coin: on the vault script, the creating transaction's referenced output
equal to the scanned value and script, its header at the scanned height and active, at least one
confirmation, and a consistent class. -/
@[req "OPR-33"]
def recordOk (tip script : Nat) (c : Coin) (r : Record) : Bool :=
  r.script == script && r.tx.script == r.script && r.tx.value == c.2 && r.tx.height == r.height &&
    r.tx.active && decide (r.height ≤ tip) && (kind r.tx.inputs).isSome

def recordOf (p : Pass) (o : Outpoint) : Option Record := p.records.lookup o

/-- A scanned coin passes its reads and evidence; a coin with no record fails. -/
@[req "OPR-33"]
def valid (tip : Nat) (p : Pass) (c : Coin) : Bool :=
  match recordOf p c.1 with
  | some r => recordOk tip p.script c r
  | none => false

/-- A coinbase output short of maturity at the tip. An ordinary coin is never one, whatever its height. -/
@[req "OPR-33"]
def immatureAt (tip : Nat) (r : Record) : Bool :=
  kind r.tx.inputs == some .coinbase && !mature tip r.height

/-- `WTC-28`'s inventory is "every confirmed, mature (at least 100 confirmations for a coinbase),
mempool-unspent output paying the vault script": this is the coin it leaves out. -/
@[req "WTC-28"]
def leftOut (tip : Nat) (p : Pass) (c : Coin) : Bool :=
  match recordOf p c.1 with
  | some r => immatureAt tip r
  | none => false

def heightOf (p : Pass) (o : Outpoint) : Nat := ((recordOf p o).map Record.height).getD 0

/-! ## The accepted pass -/

/-- Why a whole inventory is refused: `OPR-33`'s empty set and duplicates, a failed read or evidence
check (`OPR-82`), and `OPR-34`'s mempool-spent coin. None names a coin (`OPR-8`). -/
inductive Refusal
  | empty | duplicate | evidence | mempoolSpent
  deriving DecidableEq, Repr

/-- An accepted pass: its tip, the inventory `U` in scan order, and each immature coinbase left out
with its confirmation height. -/
structure Accepted where
  tip : Nat
  inventory : List Coin
  immature : List (Coin × Nat)
  deriving DecidableEq, Repr

/-- `OPR-33`'s whole-inventory validation, then the partition. Every scanned coin is validated, the
immature ones included: "a failure in its reads or evidence refuses the whole inventory as any coin's
does; only a coin that passes is left out." -/
@[req "OPR-33"]
def accept (s : Vault) (p : Pass) : Except Refusal Accepted :=
  if s.b.confirmed.isEmpty then .error .empty
  else if !Feasibility.ascending (s.b.confirmed.map (·.1)) then .error .duplicate
  else if !s.b.confirmed.all (valid s.b.tip.height p) then .error .evidence
  else if s.b.confirmed.any (fun c => Sweep.spentInMempool s.b c.1) then .error .mempoolSpent
  else .ok { tip := s.b.tip.height,
             inventory := s.b.confirmed.filter (fun c => !leftOut s.b.tip.height p c),
             immature := (s.b.confirmed.filter (leftOut s.b.tip.height p)).map
               fun c => (c, heightOf p c.1) }

/-- `OPR-38`'s `I`: "the sum of their values read in that pass". -/
@[req "OPR-38"]
def Accepted.value (a : Accepted) : Nat := (a.immature.map (·.1.2)).sum

def maxHeight : List Nat → Nat
  | [] => 0
  | h :: hs => max h (maxHeight hs)

/-- `OPR-38`'s reported height: "`h + 99` for the highest confirmation height `h` among them". -/
@[req "OPR-38"]
def Accepted.clear (a : Accepted) : Nat := maxHeight (a.immature.map (·.2)) + clearOffset

/-! ## `OPR-38`'s additional check -/

/-- `OPR-38`: "the composer additionally requires `sweep × 100 ≥ (total_in + I) × escape_coverage_pct`,
widened, equality passing". It is `DUR-24`'s own predicate at the widened amount: one arithmetic
definition, `Coverage.covers`, in unbounded `Nat`. -/
@[req "OPR-38"]
def extraCovers (sweep totalIn I pct : Nat) : Bool := Coverage.covers sweep (totalIn + I) pct

open Formula in
def sweepSide : Expr := .mul (.var "sweep") (.lit 100)
open Formula in
def requiredSide : Expr := .mul (.paren (.add (.var "total_in") (.var "I"))) (.var "escape_coverage_pct")

/-- The check as `OPR-38` writes it, rendered from the two expressions; the copies gate finds it
verbatim in `OPR-38`. -/
@[req "OPR-38"]
def extraFormula : String := s!"{Formula.renderNat sweepSide} ≥ {Formula.renderNat requiredSide}"

@[req "OPR-38"]
theorem extra_renders : extraFormula = "sweep × 100 ≥ (total_in + I) × escape_coverage_pct" := by
  decide

/-- The rendered inequality IS `extraCovers`, for every value of its variables. -/
@[req "OPR-38"]
theorem extra_expr_agrees (sweep totalIn I pct : Nat) :
    extraCovers sweep totalIn I pct =
      decide (Formula.evalNat (fun x => if x = "total_in" then totalIn else if x = "I" then I
          else if x = "escape_coverage_pct" then pct else 0) requiredSide ≤
        Formula.evalNat (fun x => if x = "sweep" then sweep else 0) sweepSide) := by
  simp [extraCovers, Coverage.covers, Formula.evalNat, sweepSide, requiredSide]

/-- With nothing left out the check is `CHN-21`'s, unchanged. -/
@[req "OPR-38"]
theorem extra_zero (sweep totalIn pct : Nat) :
    extraCovers sweep totalIn 0 pct = Coverage.covers sweep totalIn pct := by
  simp [extraCovers]

/-! ## Spend -/

/-- Why a spend refuses: the inventory, `Feasibility.composeEvery`'s own reasons, or `OPR-38`'s
additional check, which reports `I` and the clearing height and names no outpoint. -/
inductive SpendRefusal
  | inventory (e : Refusal)
  | compose (e : Feasibility.Refusal)
  | immature (I clear : Nat)
  deriving DecidableEq, Repr

/-- The instant as the composer reads it: the confirmed list narrowed to `U`. Only the composer reads
this; the node's read and denominator are taken from the instant itself. -/
def view (s : Vault) (U : List Coin) : Vault := { s with b := { s.b with confirmed := U } }

/-- The spend composer: `Feasibility.composeEvery` over `U`, then the additional check. When leaving
the immature coinbases out empties the inventory, `OPR-33`: "a spend refuses with that check's
report". Every refusal is before a request exists, so before signing. -/
@[req "OPR-38"]
def composeSpend (lim : Limits) (txid : Nat) (s : Vault) (p : Pass) :
    Except SpendRefusal Request :=
  match accept s p with
  | .error e => .error (.inventory e)
  | .ok acc =>
    if acc.inventory.isEmpty then .error (.immature acc.value acc.clear)
    else match composeEvery lim txid (view s acc.inventory) with
      | .error e => .error (.compose e)
      | .ok q =>
        if extraCovers (sumValues acc.inventory - q.fee) (sumValues acc.inventory) acc.value s.cfg.pct then .ok q
        else .error (.immature acc.value acc.clear)

/-! ## Claw-back -/

/-- `OPR-67`'s three selection modes. -/
inductive Selection
  | outpoints (T : List Outpoint)
  | all
  | replace (recorded : List Outpoint)
  deriving DecidableEq, Repr

/-- `OPR-68`'s refusals that this module reads. -/
inductive ClawRefusal
  | inventory (e : Refusal)
  | emptyTarget | duplicate | immatureTarget | notInventory
  deriving DecidableEq, Repr

/-- A composed claw-back: its inputs, exactly `T`, and for `--all` the count of immature coinbases it
left out (`OPR-68`: "`--all` leaves it out and reports how many it left out"). -/
structure Claw where
  inputs : List Outpoint
  leftOutCount : Option Nat
  deriving DecidableEq, Repr

def nodup : List Nat → Bool
  | [] => true
  | o :: os => !os.contains o && nodup os

/-- `OPR-68` against `U`: `T` non-empty, unique and in `U`, an immature coinbase in `T` refused by
name, and `--replace` composed over its recorded outpoints without the scan (`OPR-69`). -/
@[req "OPR-68"]
def composeClaw (s : Vault) (p : Pass) : Selection → Except ClawRefusal Claw
  | .replace recorded => .ok { inputs := recorded, leftOutCount := none }
  | .outpoints T => target s p T false
  | .all => match accept s p with
    | .error e => .error (.inventory e)
    | .ok acc => target s p (acc.inventory.map (·.1)) true
where
  target (s : Vault) (p : Pass) (T : List Outpoint) (all : Bool) : Except ClawRefusal Claw :=
    match accept s p with
    | .error e => .error (.inventory e)
    | .ok acc =>
      if T.isEmpty then .error .emptyTarget
      else if !nodup T then .error .duplicate
      else if T.any (fun o => (acc.immature.map (·.1.1)).contains o) then .error .immatureTarget
      else if !T.all (fun o => (acc.inventory.map (·.1)).contains o) then .error .notInventory
      else .ok { inputs := T, leftOutCount := if all then some acc.immature.length else none }

/-! ## Refresh -/

/-- `OPR-65`'s outcomes as far as this module reads them: a refused inventory, the no-op with its
held-back count, or the eligible coins to batch, with the held-back count. -/
inductive RefreshOutcome
  | refused (e : Refusal)
  | noop (heldBack : Nat)
  | batches (eligible : List Coin) (heldBack : Nat)
  deriving DecidableEq, Repr

/-- The exit status where the outcome alone fixes it: `1` for a refused inventory, `0` for the no-op.
A run that sends batches exits by its watches, which this module does not model. -/
def RefreshOutcome.exit : RefreshOutcome → Option Nat
  | .refused _ => some 1
  | .noop _ => some 0
  | .batches _ _ => none

/-- Whether the outcome writes an authorization, where the outcome alone fixes it: a refused inventory
and the no-op write none. Eligible coins do not by themselves: each batch's composition, fee bounds and
signing decide it, and a later batch is sent only after the earlier batch's watch observed it
(`OPR-65`). This module models none of them. -/
def RefreshOutcome.authorizes : RefreshOutcome → Option Bool
  | .batches _ _ => none
  | _ => some false

/-- `OPR-65` over an accepted pass: eligible coins are those of `U` that meet the age rule, which is
the argument `old`; the held-back count is the rest of `U` and every immature coinbase. "An immature
coinbase (`OPR-33`) is never eligible, whatever its age". -/
@[req "OPR-65"]
def refresh (s : Vault) (p : Pass) (old : Outpoint → Bool) : RefreshOutcome :=
  match accept s p with
  | .error e => .refused e
  | .ok acc =>
    let eligible := acc.inventory.filter (old ·.1)
    let held := (acc.inventory.filter (!old ·.1)).length + acc.immature.length
    if eligible.isEmpty then .noop held else .batches eligible held

/-! ## The accepted pass, inverted -/

theorem accept_ok {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc) :
    s.b.confirmed ≠ [] ∧ Feasibility.ascending (s.b.confirmed.map (·.1)) = true ∧
      (∀ c ∈ s.b.confirmed, valid s.b.tip.height p c = true) ∧
      (∀ c ∈ s.b.confirmed, Sweep.spentInMempool s.b c.1 = false) ∧
      acc = { tip := s.b.tip.height,
              inventory := s.b.confirmed.filter (fun c => !leftOut s.b.tip.height p c),
              immature := (s.b.confirmed.filter (leftOut s.b.tip.height p)).map
                fun c => (c, heightOf p c.1) } := by
  unfold accept at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  cases h
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro he; simp [he] at h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

/-- Whether a coin is left out reads only its outpoint's record. -/
theorem leftOut_congr {tip : Nat} {p : Pass} {c d : Coin} (h : c.1 = d.1) :
    leftOut tip p c = leftOut tip p d := by
  unfold leftOut; rw [h]

/-- What `leftOut` reads: a record whose creating transaction is a coinbase, short of maturity. -/
@[req "WTC-28"]
theorem leftOut_iff (tip : Nat) (p : Pass) (c : Coin) :
    leftOut tip p c = true ↔
      ∃ r, recordOf p c.1 = some r ∧ kind r.tx.inputs = some .coinbase ∧ mature tip r.height = false := by
  unfold leftOut immatureAt
  cases recordOf p c.1 with
  | none => simp
  | some r => simp

theorem mem_inventory {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc) (c : Coin) :
    c ∈ acc.inventory ↔ c ∈ s.b.confirmed ∧ leftOut s.b.tip.height p c = false := by
  obtain ⟨-, -, -, -, rfl⟩ := accept_ok h
  simp

theorem mem_immature {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    (x : Coin × Nat) :
    x ∈ acc.immature ↔
      x.1 ∈ s.b.confirmed ∧ leftOut s.b.tip.height p x.1 = true ∧ x.2 = heightOf p x.1.1 := by
  obtain ⟨-, -, -, -, rfl⟩ := accept_ok h
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    have := List.mem_filter.1 hc
    exact ⟨this.1, this.2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact List.mem_map.2 ⟨x.1, List.mem_filter.2 ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩

/-- Every immature coinbase left out passed its reads and evidence, is a coinbase by its creating
transaction, and is short of maturity at the pass's tip: an invalid or inconsistent coin is never
filtered out as immature, since `accept` refuses it first. -/
@[req "OPR-33"]
theorem immature_validated {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    {x : Coin × Nat} (hx : x ∈ acc.immature) :
    x.1 ∈ s.b.confirmed ∧ valid acc.tip p x.1 = true ∧
      ∃ r, recordOf p x.1.1 = some r ∧ kind r.tx.inputs = some .coinbase ∧ x.2 = r.height ∧
        mature acc.tip r.height = false := by
  obtain ⟨-, -, hval, -, hacc⟩ := accept_ok h
  obtain ⟨h1, h2, h3⟩ := (mem_immature h x).1 hx
  obtain ⟨r, hr, hk, hm⟩ := (leftOut_iff _ _ _).1 h2
  subst hacc
  exact ⟨h1, hval _ h1, r, hr, hk, by simp [h3, heightOf, hr], hm⟩

/-- An ordinary coin keeps the existing treatment: it is in `U` whatever its height. -/
@[req "OPR-33"]
theorem ordinary_kept {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    {c : Coin} (hc : c ∈ s.b.confirmed) {r : Record} (hr : recordOf p c.1 = some r)
    (hk : kind r.tx.inputs = some .ordinary) : c ∈ acc.inventory := by
  refine (mem_inventory h c).2 ⟨hc, ?_⟩
  simp [leftOut, hr, immatureAt, hk]

/-- No coin is lost: every scanned coin is in `U` or among the immature coinbases left out. -/
@[req "OPR-33"]
theorem partition {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    {c : Coin} (hc : c ∈ s.b.confirmed) :
    c ∈ acc.inventory ∨ (c, heightOf p c.1) ∈ acc.immature := by
  cases hl : leftOut s.b.tip.height p c
  · exact .inl ((mem_inventory h c).2 ⟨hc, hl⟩)
  · exact .inr ((mem_immature h _).2 ⟨hc, hl, rfl⟩)

/-- No outpoint is both in `U` and left out. -/
theorem disjoint {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    {o : Outpoint} (hu : o ∈ acc.inventory.map (·.1)) : o ∉ acc.immature.map (·.1.1) := by
  intro hi
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu
  obtain ⟨x, hx, hxo⟩ := List.mem_map.1 hi
  have h1 := ((mem_inventory h c).1 hc).2
  have h2 := ((mem_immature h x).1 hx).2.1
  rw [leftOut_congr hxo] at h2
  rw [h1] at h2
  cases h2

theorem sum_filter_split (f : Coin → Bool) :
    ∀ l : List Coin, sumValues (l.filter (fun c => !f c)) + sumValues (l.filter f) = sumValues l
  | [] => rfl
  | c :: cs => by
    have ih := sum_filter_split f cs
    cases hf : f c <;> simp [List.filter, hf, sumValues] at ih ⊢ <;> omega

/-- Property 4: `I` is the sum of the validated immature coins this pass left out, and with `U` it
makes up the whole scan. -/
@[req "OPR-38"]
theorem value_split {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc) :
    acc.value = sumValues (s.b.confirmed.filter (leftOut s.b.tip.height p)) ∧
      sumValues acc.inventory + acc.value = sumValues s.b.confirmed := by
  obtain ⟨-, -, -, -, rfl⟩ := accept_ok h
  have hv : ((((s.b.confirmed.filter (leftOut s.b.tip.height p)).map
      fun c => (c, heightOf p c.1)).map (·.1.2)).sum) =
      sumValues (s.b.confirmed.filter (leftOut s.b.tip.height p)) := by
    simp [sumValues, List.map_map, Function.comp_def]
  refine ⟨hv, ?_⟩
  simp only [Accepted.value]
  rw [hv]
  exact sum_filter_split _ _

/-! ## The clearing height -/

theorem le_maxHeight : ∀ {l : List Nat} {h : Nat}, h ∈ l → h ≤ maxHeight l
  | [], _, hm => by simp at hm
  | a :: as, h, hm => by
    simp only [List.mem_cons] at hm
    simp only [maxHeight]
    rcases hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxHeight hm) (Nat.le_max_right _ _)

theorem maxHeight_mem : ∀ {l : List Nat}, l ≠ [] → maxHeight l ∈ l
  | [], h => absurd rfl h
  | [a], _ => by simp [maxHeight]
  | a :: b :: bs, _ => by
    have ih := maxHeight_mem (l := b :: bs) (by simp)
    simp only [maxHeight] at ih ⊢
    rcases Nat.le_total a (max b (maxHeight bs)) with hle | hle
    · rw [Nat.max_eq_right hle]; exact List.mem_cons_of_mem _ ih
    · rw [Nat.max_eq_left hle]; exact List.mem_cons_self

/-- Properties 6 and 7: at the reported height every coin counted in `I` has 100 confirmations under
this pass's chain history, and, when at least one coin is counted, one block earlier one of them does
not, so the height is the last coin's maturity: the greatest confirmation height plus `clearOffset`. The report is two numbers and
names no outpoint (`SpendRefusal.immature`). -/
@[req "OPR-38"]
theorem clear_is_last_maturity (acc : Accepted) :
    (∀ x ∈ acc.immature, mature acc.clear x.2 = true) ∧
      (acc.immature ≠ [] → ∃ x ∈ acc.immature, mature (acc.clear - 1) x.2 = false) := by
  constructor
  · intro x hx
    have hle : x.2 ≤ maxHeight (acc.immature.map (·.2)) := le_maxHeight (List.mem_map_of_mem hx)
    rw [mature_iff]; unfold Accepted.clear; omega
  · intro hne
    have hm := maxHeight_mem (l := acc.immature.map (·.2)) (by simpa using hne)
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
    refine ⟨x, hx, ?_⟩
    have : ¬ (x.2 + clearOffset ≤ acc.clear - 1) := by
      unfold Accepted.clear; rw [← hxe]; simp only [clearOffset, maturity]; omega
    cases hmt : mature (acc.clear - 1) x.2
    · rfl
    · exact absurd ((mature_iff _ _).1 hmt) this

/-- On an accepted pass that leaves at least one coin out, the reported height is above the pass's
tip: every counted coin is still immature there. -/
@[req "OPR-38"]
theorem tip_below_clear {s : Vault} {p : Pass} {acc : Accepted} (h : accept s p = .ok acc)
    (hne : acc.immature ≠ []) : acc.tip < acc.clear := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨-, -, r, -, -, hxr, hm⟩ := immature_validated h hx
  have h1 : ¬ (r.height + clearOffset ≤ acc.tip) := fun hle => by
    rw [(mature_iff _ _).2 hle] at hm; cases hm
  have h2 : x.2 ≤ maxHeight (acc.immature.map (·.2)) := le_maxHeight (List.mem_map_of_mem hx)
  unfold Accepted.clear; omega

/-! ## Spend, inverted -/

/-- `Feasibility.composeEvery` succeeds only with `everyRequest`, after `CHN-21`'s check passed. -/
theorem composeEvery_ok {lim : Limits} {txid : Nat} {s : Vault} {q : Request}
    (h : composeEvery lim txid s = .ok q) :
    q = everyRequest lim txid s ∧
      Coverage.covers (sumValues s.b.confirmed - s.floor * vsizeOf lim (s.b.confirmed.map (·.1)).length)
        (sumValues s.b.confirmed) s.cfg.pct = true := by
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
  rename_i hcov
  cases h
  exact ⟨rfl, by simpa using hcov⟩

theorem spend_ok {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request}
    (h : composeSpend lim txid s p = .ok q) :
    ∃ acc, accept s p = .ok acc ∧ acc.inventory ≠ [] ∧
      composeEvery lim txid (view s acc.inventory) = .ok q ∧
      extraCovers (sumValues acc.inventory - q.fee) (sumValues acc.inventory) acc.value s.cfg.pct = true := by
  unfold composeSpend at h
  split at h
  · cases h
  rename_i acc hacc
  split at h
  · cases h
  rename_i hne
  split at h
  · cases h
  rename_i q' hq
  split at h
  · rename_i hx
    cases h
    exact ⟨acc, hacc, by simpa using hne, hq, hx⟩
  · cases h

/-- Property 2 for Spend: the request's inputs, which the primary and its mandatory Escape both spend
(`OPR-33`), are exactly `U`'s outpoints, and no immature coinbase left out is among them. -/
@[req "OPR-33"]
theorem spend_inputs {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request} {acc : Accepted}
    (hacc : accept s p = .ok acc) (h : composeSpend lim txid s p = .ok q) :
    q.inputs = acc.inventory.map (·.1) ∧ ∀ x ∈ acc.immature, x.1.1 ∉ q.inputs := by
  obtain ⟨acc', hacc', -, hq, -⟩ := spend_ok h
  rw [hacc] at hacc'
  cases hacc'
  have hin : q.inputs = acc.inventory.map (·.1) := by
    rw [(composeEvery_ok hq).1]; rfl
  refine ⟨hin, fun x hx hxq => ?_⟩
  rw [hin] at hxq
  exact disjoint hacc hxq (List.mem_map_of_mem (f := (·.1.1)) hx)

/-- Property 5: a composed spend passed the additional check. -/
@[req "OPR-38"]
theorem spend_passed_extra {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request}
    {acc : Accepted} (hacc : accept s p = .ok acc) (h : composeSpend lim txid s p = .ok q) :
    extraCovers (sumValues acc.inventory - q.fee) (sumValues acc.inventory) acc.value s.cfg.pct = true := by
  obtain ⟨acc', hacc', -, -, hx⟩ := spend_ok h
  rw [hacc] at hacc'
  cases hacc'
  exact hx

/-- Properties 5 and 6: where the request `U` composes to fails the additional check, the whole
command refuses with `I` and the clearing height; no request exists to sign. -/
@[req "OPR-38"]
theorem spend_refuses_extra {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {acc : Accepted}
    {q : Request} (hacc : accept s p = .ok acc) (hne : acc.inventory ≠ [])
    (hq : composeEvery lim txid (view s acc.inventory) = .ok q)
    (hx : extraCovers (sumValues acc.inventory - q.fee) (sumValues acc.inventory) acc.value s.cfg.pct = false) :
    composeSpend lim txid s p = .error (.immature acc.value acc.clear) := by
  have hne' : acc.inventory.isEmpty = false := by
    cases hi : acc.inventory with
    | nil => exact absurd hi hne
    | cons _ _ => rfl
  simp [composeSpend, hacc, hne', hq, hx]

/-- Property 8: when leaving the immature coinbases out empties `U`, the spend refuses with the
additional check's report, never an empty spend. -/
@[req "OPR-33"]
theorem spend_empty_inventory {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {acc : Accepted}
    (hacc : accept s p = .ok acc) (he : acc.inventory = []) :
    composeSpend lim txid s p = .error (.immature acc.value acc.clear) := by
  simp [composeSpend, hacc, he]

/-- With nothing left out, the composer's view is the instant itself. -/
theorem view_self {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    (hI : acc.immature = []) : acc.inventory = s.b.confirmed := by
  obtain ⟨-, -, -, -, rfl⟩ := accept_ok hacc
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hI
  simp only
  exact List.filter_eq_self.2 fun c hc => by simp [hI c hc]

/-- **The reduction.** On a pass that leaves nothing out — every history whose coins are ordinary
(`ordinary_only`) or mature — the spend is `Feasibility.composeEvery` over the same instant, its
request and its refusals both unchanged. -/
@[req "OPR-33"]
theorem spend_reduces {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {acc : Accepted}
    (hacc : accept s p = .ok acc) (hI : acc.immature = []) :
    composeSpend lim txid s p =
      match composeEvery lim txid s with
      | .ok q => .ok q
      | .error e => .error (.compose e) := by
  have hU := view_self hacc hI
  have hv : view s acc.inventory = s := by rw [hU]; rfl
  have hne : acc.inventory.isEmpty = false := by
    obtain ⟨hn, -⟩ := accept_ok hacc
    rw [hU]; cases hc : s.b.confirmed with
    | nil => exact absurd hc hn
    | cons _ _ => rfl
  have hval : acc.value = 0 := by simp [Accepted.value, hI]
  unfold composeSpend
  rw [hacc]
  simp only [hne, hv, hval]
  cases hc : composeEvery lim txid s with
  | error e => rfl
  | ok q =>
    obtain ⟨rfl, hcov⟩ := composeEvery_ok hc
    simp only
    rw [hU, extra_zero]
    simpa [everyRequest] using hcov

/-- A history of ordinary outputs only leaves nothing out. -/
@[req "OPR-33"]
theorem ordinary_only {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    (hord : ∀ c ∈ s.b.confirmed, ∀ r, recordOf p c.1 = some r → kind r.tx.inputs = some .ordinary) :
    acc.immature = [] := by
  cases hi : acc.immature with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ acc.immature := by rw [hi]; exact List.mem_cons_self
    obtain ⟨h1, -, r, hr, hk, -⟩ := immature_validated hacc hx
    rw [hord _ h1 r hr] at hk
    cases hk

/-! ## The node's denominator -/

/-- Property 9, with the bridge's conditions named. At the same instant the composer read —
the node's read is the backend's confirmed list, immature coinbases included, with no authorized
unconfirmed value (`hadd`), values agreeing with the book (`hv`), under `DUR-22`'s current guards, and
with the request measured alone (`Feasibility.Vault.pass`) — the node's denominator for the composed
request is `total_in + I`. The composer's exclusion does not reduce it. -/
@[req "DUR-22"]
theorem node_denominator {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request}
    {acc : Accepted} (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hv : ∀ c ∈ s.b.confirmed, s.cfg.book.value c.1 = c.2)
    (hadd : Sweep.additions s.A s.b = [])
    (hacc : accept s p = .ok acc) (h : composeSpend lim txid s p = .ok q) :
    s.coins q.inputs = acc.inventory ∧ s.denominator q = sumValues acc.inventory + acc.value := by
  obtain ⟨-, hasc, -, hsp, -⟩ := accept_ok hacc
  have hin := (spend_inputs hacc h).1
  have hread : s.read = s.b.confirmed := by
    simp only [Feasibility.Vault.read, Feasibility.Vault.snap, Sweep.snapshot, hadd, List.append_nil]
    exact List.filter_eq_self.2 fun c hc => by simp [hsp c hc]
  have hsub : acc.inventory.Sublist s.b.confirmed := by
    obtain ⟨-, -, -, -, rfl⟩ := accept_ok hacc
    exact List.filter_sublist
  have hcoins : s.coins q.inputs = acc.inventory := by
    rw [hin]
    simp only [Feasibility.Vault.coins, List.map_map]
    conv => rhs; rw [← List.map_id acc.inventory]
    apply List.map_congr_left
    intro c hc
    simp [hv c (hsub.subset hc)]
  have hn : (s.read.map (·.1)).Nodup := by
    rw [hread]
    exact ((Feasibility.ascending_iff _).1 hasc).imp Nat.ne_of_lt
  have hden := Feasibility.Vault.denominator_request s q hd hx (by rw [hcoins, hread]; exact hsub) hn
  refine ⟨hcoins, ?_⟩
  rw [hden, Feasibility.Vault.total, hread, (value_split hacc).2]

/-- **The bridge.** Under the same conditions, the node's `DUR-24` on the composed request is
exactly the additional check: success here is the node's coverage at that read. At a later or
different read it is not, and `Exhibits.Coinbase.later_read_refuses` is the case. -/
@[req "DUR-22"]
theorem node_covers_iff_extra {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request}
    {acc : Accepted} (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hv : ∀ c ∈ s.b.confirmed, s.cfg.book.value c.1 = c.2)
    (hadd : Sweep.additions s.A s.b = [])
    (hacc : accept s p = .ok acc) (h : composeSpend lim txid s p = .ok q) :
    s.coverOk q =
      extraCovers (sumValues acc.inventory - q.fee) (sumValues acc.inventory) acc.value s.cfg.pct := by
  obtain ⟨hcoins, hden⟩ := node_denominator hd hx hv hadd hacc h
  simp only [Feasibility.Vault.coverOk, Feasibility.Vault.escape, Feasibility.Vault.inSum, hcoins, hden, extraCovers]

/-- So a composed spend covers at the node, at the read it was composed at. -/
@[req "DUR-24"]
theorem composed_covers_at_node {lim : Limits} {txid : Nat} {s : Vault} {p : Pass} {q : Request}
    {acc : Accepted} (hd : s.cfg.denominator = .restoreAll) (hx : s.cfg.external = .countedWhenSpent)
    (hv : ∀ c ∈ s.b.confirmed, s.cfg.book.value c.1 = c.2)
    (hadd : Sweep.additions s.A s.b = [])
    (hacc : accept s p = .ok acc) (h : composeSpend lim txid s p = .ok q) : s.coverOk q = true := by
  rw [node_covers_iff_extra hd hx hv hadd hacc h]
  exact spend_passed_extra hacc h

/-! ## Claw-back, inverted -/

theorem nodup_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → nodup l = true
  | [], _ => rfl
  | o :: os, h => by
    obtain ⟨hh, ht⟩ := List.pairwise_cons.1 h
    have hno : o ∉ os := fun hm => Nat.lt_irrefl o (hh o hm)
    simp [nodup, hno, nodup_of_pairwise ht]

/-- Property 3: a known-outpoint claw-back whose set names an immature coinbase refuses, at
whichever of `OPR-68`'s checks it first fails. -/
@[req "OPR-68"]
theorem claw_names_immature {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    {T : List Outpoint} {x : Coin × Nat} (hx : x ∈ acc.immature) (hT : x.1.1 ∈ T) (c : Claw) :
    composeClaw s p (.outpoints T) ≠ .ok c := by
  have hany : T.any (fun o => (acc.immature.map (·.1.1)).contains o) = true :=
    List.any_eq_true.2 ⟨x.1.1, hT, by simpa using List.mem_map_of_mem (f := (·.1.1)) hx⟩
  simp only [composeClaw, composeClaw.target, hacc]
  by_cases h1 : T.isEmpty = true
  · rw [if_pos h1]; simp
  rw [if_neg h1]
  by_cases h2 : (!nodup T) = true
  · rw [if_pos h2]; simp
  rw [if_neg h2, if_pos hany]
  simp

/-- Property 3, the other sets: over an accepted pass a known-outpoint claw-back composes exactly when
`OPR-68`'s contract over `U` holds — `T` non-empty, unique, and in `U` — and then its inputs are `T`. An
immature coinbase outside `T` does not enter the condition. -/
@[req "OPR-68"]
theorem claw_ok_iff {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    (T : List Outpoint) :
    composeClaw s p (.outpoints T) = .ok { inputs := T, leftOutCount := none } ↔
      T ≠ [] ∧ nodup T = true ∧ ∀ o ∈ T, o ∈ acc.inventory.map (·.1) := by
  simp only [composeClaw, composeClaw.target, hacc]
  constructor
  · intro h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    split at h
    · cases h
    rename_i h4
    have h4' : ∀ x ∈ T, ∃ y, (x, y) ∈ acc.inventory := by simpa using h4
    exact ⟨fun he => by simp [he] at h1, by simpa using h2, fun o ho => by simpa using h4' o ho⟩
  · rintro ⟨h1, h2, h3⟩
    have hT : T.isEmpty = false := by cases T with
      | nil => exact absurd rfl h1
      | cons _ _ => rfl
    have hnone : T.any (fun o => (acc.immature.map (·.1.1)).contains o) = false := by
      rw [List.any_eq_false]
      intro o ho hc
      exact disjoint hacc (h3 o ho) (by simpa using hc)
    have hall : T.all (fun o => (acc.inventory.map (·.1)).contains o) = true :=
      List.all_eq_true.2 fun o ho => by simpa using h3 o ho
    rw [if_neg (by rw [hT]; simp), if_neg (by rw [h2]; simp), if_neg (by rw [hnone]; simp),
      if_neg (by rw [hall]; simp)]
    rfl

/-- Properties 8 and 12: `--all` names `U`, reports how many immature coinbases it left out, and with
`U` empty has no target to compose. -/
@[req "OPR-68"]
theorem claw_all {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc) :
    composeClaw s p .all =
      if acc.inventory = [] then .error .emptyTarget
      else .ok { inputs := acc.inventory.map (·.1), leftOutCount := some acc.immature.length } := by
  obtain ⟨-, hasc, -, -, hU⟩ := accept_ok hacc
  have hnd : nodup (acc.inventory.map (·.1)) = true := by
    apply nodup_of_pairwise
    rw [hU]
    exact (((Feasibility.ascending_iff _).1 hasc).sublist (List.filter_sublist.map _))
  have hnone : (acc.inventory.map (·.1)).any (fun o => (acc.immature.map (·.1.1)).contains o) = false := by
    rw [List.any_eq_false]
    intro o ho hc
    exact disjoint hacc ho (by simpa using hc)
  have hall : (acc.inventory.map (·.1)).all (fun o => (acc.inventory.map (·.1)).contains o) = true :=
    List.all_eq_true.2 fun o ho => by simpa using ho
  simp only [composeClaw, composeClaw.target, hacc]
  by_cases he : acc.inventory = []
  · simp [he]
  · have hT : (acc.inventory.map (·.1)).isEmpty = false := by
      cases hi : acc.inventory with
      | nil => exact absurd hi he
      | cons _ _ => rfl
    rw [if_neg (by rw [hT]; simp), if_neg (by rw [hnd]; simp), if_neg (by rw [hnone]; simp),
      if_neg (by rw [hall]; simp), if_neg he]
    simp

/-- Property 12, the replacement contract: `--replace` composes over its recorded outpoints and reads
neither the instant nor the scan (`OPR-69`). -/
@[req "OPR-68"]
theorem claw_replace_reads_no_scan (s s' : Vault) (p p' : Pass) (recorded : List Outpoint) :
    composeClaw s p (.replace recorded) = composeClaw s' p' (.replace recorded) := rfl

/-! ## Refresh, inverted -/

/-- Property 2 for refresh, for every age rule: it never selects an immature coinbase. -/
@[req "OPR-65"]
theorem refresh_never_selects {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    (old : Outpoint → Bool) {E : List Coin} {held : Nat} (h : refresh s p old = .batches E held) :
    ∀ c ∈ E, c ∈ acc.inventory ∧ leftOut acc.tip p c = false := by
  obtain ⟨-, -, -, -, hacc'⟩ := accept_ok hacc
  simp only [refresh, hacc] at h
  split at h
  · cases h
  cases h
  intro c hc
  have hcU := (List.mem_filter.1 hc).1
  refine ⟨hcU, ?_⟩
  have := ((mem_inventory hacc c).1 hcU).2
  rw [hacc']; exact this

/-- Property 13: refresh counts every immature coinbase with the coins held back; a valid scan whose
`U` is empty — one holding only immature coinbases — is the successful no-op, exit `0`, with no
authorization. -/
@[req "OPR-65"]
theorem refresh_held_back {s : Vault} {p : Pass} {acc : Accepted} (hacc : accept s p = .ok acc)
    (old : Outpoint → Bool) :
    (refresh s p old = .noop ((acc.inventory.filter (!old ·.1)).length + acc.immature.length) ∨
      refresh s p old = .batches (acc.inventory.filter (old ·.1))
        ((acc.inventory.filter (!old ·.1)).length + acc.immature.length)) ∧
    (acc.inventory = [] →
      refresh s p old = .noop acc.immature.length ∧ (refresh s p old).exit = some 0 ∧
        (refresh s p old).authorizes = some false) := by
  constructor
  · simp only [refresh, hacc]
    split
    · exact .inl rfl
    · exact .inr rfl
  · intro he
    simp [refresh, hacc, he, RefreshOutcome.exit, RefreshOutcome.authorizes]

/-! ## Reorganization -/

/-- Property 10: a pass reads only the instant's confirmed list, tip height and mempool, and its own
records. Nothing from an earlier pass is carried, so a reorganization's new observation — new heights,
new records — recomputes confirmation, maturity, `U`, `I` and the clearing height. -/
@[req "OPR-33"]
theorem accept_reads_instant {s s' : Vault} (p : Pass) (hc : s.b.confirmed = s'.b.confirmed)
    (ht : s.b.tip.height = s'.b.tip.height) (hm : s.b.mempool = s'.b.mempool) :
    accept s p = accept s' p := by
  have hsp : ∀ o, Sweep.spentInMempool s.b o = Sweep.spentInMempool s'.b o := fun o => by
    simp [Sweep.spentInMempool, hm]
  unfold accept
  rw [hc, ht]
  simp only [hsp]

end BtcPolicy.Coinbase
