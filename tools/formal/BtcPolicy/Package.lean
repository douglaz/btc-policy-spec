import BtcPolicy.VaultUnspent
/-! Package ancestry and replacement: `WTC-23`'s
package shape, `WTC-24`'s ancestry validation and `WTC-25`'s replacement, the rules that drive the
`Kernel.packageAccepted` boundary. The snapshot is `VaultUnspent.Snapshot`, taken as it is: its
`read` is the prevout read, and the coin and the outpoint are `Coverage.lean`'s. What the rules
need about a prevout or a resident that the snapshot does not carry comes from a model parameter
keyed by the id, as `Alerts.Spend` is keyed by the scan's spend id and `VaultUnspent.Ledger` by
height and hash: for an outpoint, the txid of its creating transaction; for a resident txid, its
ordered inputs. The vault-authorized set is the third parameter, a list of txids, the set whose
writer is the kernel's. `SPN-33`: "On acceptance the node MUST add the spend's, the Escape's and
every rung's txid to its **vault-authorized set**, which the watchtower recognises (`WTC-18`) and
which qualifies unconfirmed parents at fire time (`DUR-22`)."

`WTC-24`: "Before assembling, a node MUST validate the candidate's ancestry: for a candidate,
every prevout MUST exist (unknown or spent is an error), and an unconfirmed parent MUST be
resident in the mempool AND in the vault-authorized set — an unconfirmed external deposit is
excluded because its parent can be replaced out from under the spend; for a candidate that
replaces a mempool-resident vault-authorized transaction (`WTC-25`) — a higher rung over a
resident rung, a refresh over a resident refresh, or a claw-back over a resident claw-back — a
parent absent from the mempool is confirmed, and the resident's own inputs are read as unspent
for the replacement."

**The two halves of the bump path.** `SPN-46`: "A refresh that is signed but never confirms
leaves no trace on the chain, so a replacement of it over the same inputs at a higher fee is
admissible on every node for as long as the coins stay old enough, `WTC-25` walks its ancestry
over the resident as a replacement, and `CHN-18`'s `0xfffffffd` lets the mempool accept it — that
is the bump path, end to end, and refresh needs no ladder for it." The INGRESS half, whether the
replacement's coins are old enough read from the chain, is `RefreshAge.lean`'s: `bumpDay`,
`bumpChain`, `bumpLog`, `bumpVerdict` and `perNodeLog_refuses_replacement`, with
`Exhibits.wtc25_replacement_admitted_with_current` over `RefreshAge.current`. This module is the
FIRE-TIME half: whether the replacement's prevouts, which the mempool-inclusive read shows spent
by the resident, are admitted by the ancestry walk. No age, interval, log or chain view is
defined here.

One guard parameter (`ADR-0023` decision 6), `ReplacementAncestry`: `overResident` is `WTC-24`
and `WTC-25` as they stand, `plainRead` is the row `F54` records. The theorems here hold under
either value or are stated under `.overResident` or `.plainRead` in full; `Exhibits.lean` holds
every theorem over `current`, so a flip goes red there and nowhere else. Beside the parameter
sits the twin under the withdrawn value.

**The bridge to the kernel.** `Kernel.packageAccepted` stands for the whole of `SPN-39`'s
"assemble the package (`WTC-24`); test it for mempool acceptance" as one transition whose result
is `packageOk`. The kernel's chain view is `{mtp, seen}`: no prevout set, no confirmed-versus-
resident distinction, no ancestor graph, so it carries none of the facts this rule reads, and
the rule is stated here over the `WTC-10` snapshot where those facts live. `validate`'s admitted
verdict is what the assembly step reads before the kernel's flag is set; the kernel omits the
predicate as it omits the ladder, by the modelling order its own docstring records. In the
sweep's order, `DUR-21`: "the selected rung's ancestry is validated (`WTC-24`); and only then the
latch is advanced".

**Not modelled.** `SPN-33`'s writer of the vault-authorized set, the kernel's (`Alerts.snapshot`
is where the same set is taken under the recognition guard); `WTC-26`'s one tolerated rejection
and `DUR-32`'s treatment of every other, the next step after the package leaves here; `WTC-27`'s
broadcast; `CHN-18`'s canonical sort and `CHN-35`'s `nSequence`, cited where they bear;
`DUR-21`'s ordering of the sweep's steps; `DUR-22`'s denominator (`Coverage.Pass.residentRungs`
is the denominator's); and the one-second fire tick and every cost claim in `WTC-24`'s rationale,
since machine timing is not claimed by the formal layer (`Silence.lean`). -/

namespace BtcPolicy.Package
open BtcPolicy.Coverage (Coin Outpoint)
open BtcPolicy.VaultUnspent (Snapshot)

/-! ## The candidate and the two reads (`WTC-24`) -/

/-- The candidate as the package sees it: its txid and its inputs as an ORDERED list of outpoints,
`Coverage.Outpoint` because that is what `Snapshot.read` carries; the `(txid, vout)` pair is the
wire's, and the outpoint's creating txid is `Creator`'s. -/
structure Candidate where
  txid : Nat
  inputs : List Outpoint
  deriving DecidableEq, Repr

/-- The txid of the transaction that created an outpoint: a model parameter keyed by the
outpoint, which the snapshot does not carry. -/
abbrev Creator := Outpoint → Nat

/-- The mempool membership read, ONE argument: the resident txids at the snapshot's sequence, each
with its ordered inputs, so the walk can climb through unconfirmed ancestors. A parent is
unconfirmed iff its txid is in this read; `WTC-24`: "A parent absent from the snapshot still
means confirmed". -/
abbrev MempoolRead := List (Nat × List Outpoint)

/-- The prevout read is the snapshot's `read`, untouched: an outpoint in it exists and is unspent
at the snapshot's tip and sequence; an outpoint not in it is `WTC-24`'s "unknown or spent is an
error", one refusal, since the snapshot does not distinguish the two. -/
@[req "WTC-24"]
def shown (snap : Snapshot) (o : Outpoint) : Bool := snap.read.any (·.1 == o)

/-- `WTC-24`: "more than 24 distinct ancestors is an error, one below Bitcoin Core's default
ancestor limit". Not an emitted value, as `Alerts.capacity` is not. The refresh's input count is the
same figure, `SPN-44`: "A refresh MUST have at most **24** inputs". `SPN-44`: "The constant matches
`WTC-24`'s ancestor limit; a vault with more coins refreshes in batches." -/
@[req "WTC-24"]
def ancestorLimit : Nat := 24

/-! ## The guard parameter (`WTC-24`, `WTC-25`, `F54`) -/

/-- How a replacement's ancestry is read. `overResident` is the rule as it stands: `WTC-24`: "the
resident's own inputs are read as unspent for the replacement", the ancestry `WTC-25` says "MUST
be walked over the resident transaction with inputs treated as spent, because a prevout read
including the mempool hides what the resident already spends" — the read hides them, the walk
over the resident admits them. `plainRead` is the row `F54` records on 2026-09-12, the prevout
read applied as it stands. The row reads "`WTC-24` read the resident's inputs as spent". -/
inductive ReplacementAncestry
  | overResident | plainRead
  deriving DecidableEq, Repr

/-- `WTC-24` as it stands: "the resident's own inputs are read as unspent for the
replacement". -/
@[req "WTC-24"]
def current : ReplacementAncestry := .overResident

/-- The refusals. `unknownOrSpent` is `WTC-24`'s "unknown or spent is an error"; `notResident` a
transaction the candidate depends on as unconfirmed that the membership read lacks, which for a
walked parent cannot arise (`ancestor_resident`) and is emitted for the named resident only;
`notAuthorized` an unconfirmed parent outside the vault-authorized set; `tooManyAncestors` the
limit; `residentNotAuthorized` and `outpointsDiffer` are `WTC-25`'s. -/
inductive Reason
  | unknownOrSpent (o : Outpoint)
  | notResident (txid : Nat)
  | notAuthorized (txid : Nat)
  | tooManyAncestors (count : Nat)
  | residentNotAuthorized (txid : Nat)
  | outpointsDiffer
  deriving DecidableEq, Repr

/-- The verdict: admitted with the deduplicated set of unconfirmed ancestors, or refused. -/
inductive Verdict
  | admitted (ancestors : List Nat)
  | refused (reason : Reason)
  deriving DecidableEq, Repr

/-- Admitted, as a Bool. -/
@[req "WTC-24"]
def Verdict.isAdmitted : Verdict → Bool
  | .admitted _ => true
  | .refused _ => false

/-! ## The ordered-outpoints rule (`WTC-25`) -/

/-- `WTC-25`: "MUST spend exactly the same ordered outpoints as the resident transaction" — the
candidate's input list equals the resident's, as lists. The negative exhibits (`reordered_refused`,
`subset_refused`) never refuse a legitimate replacement: `CHN-18`'s "inputs in canonical outpoint
order (sorted by txid then vout, no duplicates)" makes every composed transaction's inputs
sorted, so two transactions over the same coins have the same list. The sort is not modelled.
The same test at the claw-back's ingress, `SPN-50`: "An outpoint a resident claw-back already
spends reads absent from the mempool-inclusive prevout read; the node MUST apply `WTC-25`'s test
— the resident is a vault-authorized claw-back over exactly these ordered outpoints — or refuse
`UNKNOWN_INPUT`". -/
@[req "WTC-25"]
def sameOrderedOutpoints (candidate resident : List Outpoint) : Bool :=
  decide (candidate = resident)

/-- The resident's inputs read as unspent for the replacement, or the refusal: `[]` when no
resident is named. With a resident named, under either value the resident must be in the
membership read and in the authorized set — `WTC-25`: "The resident MUST be in this node's
vault-authorized set (`WTC-18`); a resident the node never accepted is not something it
replaces." Under `.overResident` the candidate must then spend the resident's ordered outpoints,
and the resident's inputs are read as unspent for it. Under `.plainRead` the resident's inputs
are not read: the prevout read is applied as it stands, which is the row `F54` records. What
lets the mempool take the replacement is the resident's signal, not this read. `CHN-35`: "Every
input's `nSequence` MUST be `0xfffffffd`, refused the same way otherwise, so that a higher-fee
claw-back over the same coins can replace it in the mempool (`WTC-25`)". The refresh's twin,
`SPN-44`: "Every input's `nSequence` MUST be `0xfffffffd` (`CHN-18`), refused `PSBT_INCONSISTENT`
/ `transaction_class` otherwise, so that every refresh signals BIP125 and a later higher-fee
refresh of the same coins can replace it in the mempool". -/
@[req "WTC-25"]
def residentRead (g : ReplacementAncestry) (mem : MempoolRead) (authorized : List Nat)
    (c : Candidate) : Option Nat → Except Reason (List Outpoint)
  | none => .ok []
  | some r =>
    match mem.lookup r with
    | none => .error (.notResident r)
    | some ins =>
      if r ∈ authorized then
        match g with
        | .plainRead => .ok []
        | .overResident =>
          if sameOrderedOutpoints c.inputs ins then .ok ins else .error .outpointsDiffer
      else .error (.residentNotAuthorized r)

/-! ## The ancestry walk (`WTC-24`) -/

/-- Insert a txid unless present: the walk's set is deduplicated as it is built. `WTC-24`:
"Diamond ancestry is deduplicated". -/
@[req "WTC-24"]
def insertNew (t : Nat) (acc : List Nat) : List Nat := if t ∈ acc then acc else t :: acc

/-- Insert each of a list. -/
@[req "WTC-24"]
def insertAll (ts acc : List Nat) : List Nat := ts.foldl (fun a t => insertNew t a) acc

/-- The unconfirmed parents of a list of inputs: each input's creating txid when it is in the
membership read. A creator absent from the read is a confirmed parent, and the walk stops there. -/
@[req "WTC-24"]
def unconfirmedParents (creator : Creator) (mem : MempoolRead) (ins : List Outpoint) : List Nat :=
  (ins.map creator).filter fun t => (mem.lookup t).isSome

/-- One expansion: the unconfirmed parents of every collected ancestor's inputs, inserted. -/
@[req "WTC-24"]
def expand (creator : Creator) (mem : MempoolRead) (acc : List Nat) : List Nat :=
  insertAll (acc.flatMap fun t =>
    match mem.lookup t with
    | some ins => unconfirmedParents creator mem ins
    | none => []) acc

/-- The walk: the unconfirmed ancestors of a list of inputs, deduplicated. Every parent is
resolved against the one membership read the walk takes as an argument, and no per-parent query
exists in the model: the signature is the statement of `WTC-24`'s "Every parent MUST be resolved
against ONE mempool snapshot — a batched membership read". Termination is fuel: the expansion is
applied as many times as the membership read is long, since the base holds distance 1, an
ancestor at distance `d` is collected after `d − 1` expansions and a path through distinct
residents is no longer than the read. The fuel is the walk's termination, not a semantic bound;
the bound the rule sets is `ancestorLimit`, applied to the collected set. -/
@[req "WTC-24"]
def ancestors (creator : Creator) (mem : MempoolRead) (ins : List Outpoint) : List Nat :=
  Nat.repeat (expand creator mem) mem.length (insertAll (unconfirmedParents creator mem ins) [])

/-- The walk's verdict over a collected set: every ancestor authorized — `WTC-24`: "an unconfirmed
external deposit is excluded because its parent can be replaced out from under the spend" — and
the distinct count within the limit. -/
@[req "WTC-24"]
def ancestryVerdict (authorized : List Nat) (anc : List Nat) : Verdict :=
  match anc.find? fun t => !authorized.contains t with
  | some t => .refused (.notAuthorized t)
  | none =>
    if anc.length ≤ ancestorLimit then .admitted anc else .refused (.tooManyAncestors anc.length)

/-- The first input the prevout read does not show and the resident does not admit, if any. -/
@[req "WTC-24"]
def missingPrevout (snap : Snapshot) (admitted ins : List Outpoint) : Option Outpoint :=
  ins.find? fun o => !(shown snap o || admitted.contains o)

/-- `WTC-24`'s validation, whole: the resident resolved under the guard value, every prevout shown
by the read or admitted as the resident's, then the walk from the candidate's inputs — which,
for a replacement, are the resident's, so the walk climbs from the resident's parents. The
snapshot, the membership read and the authorized set are each one argument. -/
@[req "WTC-24"]
def validate (g : ReplacementAncestry) (creator : Creator) (snap : Snapshot) (mem : MempoolRead)
    (authorized : List Nat) (c : Candidate) (replaces : Option Nat) : Verdict :=
  match residentRead g mem authorized c replaces with
  | .error r => .refused r
  | .ok admitted =>
    match missingPrevout snap admitted c.inputs with
    | some o => .refused (.unknownOrSpent o)
    | none => ancestryVerdict authorized (ancestors creator mem c.inputs)

/-! ## The package shape (`WTC-23`) -/

/-- What enters acceptance testing, from a verdict: `WTC-23`: "A package for acceptance testing
MUST be the candidate transaction alone: its unconfirmed ancestors are already in this node's
mempool and Bitcoin Core's package policy rejects a package that re-lists present ancestry, while
a singleton acceptance test still evaluates the candidate against its full in-mempool ancestor
set." Nothing for a refusal. The test itself, `WTC-26`'s "Package acceptance MUST require every
entry allowed, tolerating exactly one rejection reason — `txn-already-in-mempool`", and `DUR-32`'s
treatment of every other rejection are the next step. -/
@[req "WTC-23"]
def submission (c : Candidate) : Verdict → Option (List Nat)
  | .admitted _ => some [c.txid]
  | .refused _ => none

/-- Universal: an admitted verdict submits the candidate alone, and no ancestor the walk collected
other than the candidate's own txid is in it. A transaction is not its own ancestor; the model
does not derive it, since `Creator` is unconstrained, so the conjunct excludes that txid by name
rather than by premise. -/
@[req "WTC-23"]
theorem submission_is_candidate_alone (c : Candidate) (anc : List Nat) :
    submission c (.admitted anc) = some [c.txid] ∧
      ∀ t ∈ anc, t ≠ c.txid → ∀ txs, submission c (.admitted anc) = some txs → t ∉ txs := by
  refine ⟨rfl, fun t _ hne txs hs => ?_⟩
  simp only [submission, Option.some.injEq] at hs
  subst hs
  intro hm
  exact hne (List.mem_singleton.mp hm)

/-! ## What an admitted verdict established -/

/-- Membership through an insertion: what is in the result was inserted or was there. -/
@[req "WTC-24"]
theorem mem_insertAll (ts acc : List Nat) (t : Nat) (h : t ∈ insertAll ts acc) :
    t ∈ ts ∨ t ∈ acc := by
  induction ts generalizing acc with
  | nil => exact Or.inr h
  | cons x xs ih =>
    simp only [insertAll, List.foldl_cons] at h
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem x h)
    · simp only [insertNew] at h
      split at h
      · exact Or.inr h
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (List.mem_cons_self)
        · exact Or.inr h

/-- Insertion preserves distinctness. -/
@[req "WTC-24"]
theorem nodup_insertAll (ts acc : List Nat) (h : acc.Nodup) : (insertAll ts acc).Nodup := by
  induction ts generalizing acc with
  | nil => exact h
  | cons x xs ih =>
    simp only [insertAll, List.foldl_cons]
    apply ih
    simp only [insertNew]
    split
    · exact h
    · exact List.nodup_cons.mpr ⟨by assumption, h⟩

/-- Every walked parent is in the membership read: an unconfirmed parent not resident cannot
arise, since a parent absent from the read is confirmed and the walk stops there. -/
@[req "WTC-24"]
theorem ancestor_resident (creator : Creator) (mem : MempoolRead) (ins : List Outpoint) :
    ∀ t ∈ ancestors creator mem ins, (mem.lookup t).isSome = true := by
  have step : ∀ acc, (∀ t ∈ acc, (mem.lookup t).isSome = true) →
      ∀ t ∈ expand creator mem acc, (mem.lookup t).isSome = true := by
    intro acc hacc t ht
    rcases mem_insertAll _ _ t ht with h | h
    · simp only [List.mem_flatMap] at h
      obtain ⟨a, -, ha⟩ := h
      split at ha
      · exact (List.mem_filter.mp ha).2
      · simp at ha
    · exact hacc t h
  have base : ∀ t ∈ insertAll (unconfirmedParents creator mem ins) [],
      (mem.lookup t).isSome = true := by
    intro t ht
    rcases mem_insertAll _ _ t ht with h | h
    · exact (List.mem_filter.mp h).2
    · simp at h
  unfold ancestors
  generalize mem.length = n
  induction n with
  | zero => exact base
  | succ n ih => exact step _ ih

/-- `WTC-24`: "Diamond ancestry is deduplicated" — universal: the collected set has no
duplicates. -/
@[req "WTC-24"]
theorem ancestors_nodup (creator : Creator) (mem : MempoolRead) (ins : List Outpoint) :
    (ancestors creator mem ins).Nodup := by
  unfold ancestors
  generalize mem.length = n
  induction n with
  | zero => exact nodup_insertAll _ _ List.nodup_nil
  | succ n ih => exact nodup_insertAll _ _ ih

/-- What every admitted verdict established, under either guard value and whatever resident:
the resident resolved to a list of admitted inputs, every input shown by the read or among them,
the ancestors exactly the walk's, every one of them authorized, and their count within the limit.
The refusal theorems below are its corollaries. -/
@[req "WTC-24"]
theorem admitted_only_when (g : ReplacementAncestry) (creator : Creator) (snap : Snapshot)
    (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (replaces : Option Nat)
    (anc : List Nat) (h : validate g creator snap mem authorized c replaces = .admitted anc) :
    (∃ ins, residentRead g mem authorized c replaces = .ok ins ∧
        ∀ o ∈ c.inputs, shown snap o = true ∨ o ∈ ins) ∧
      anc = ancestors creator mem c.inputs ∧ (∀ t ∈ anc, t ∈ authorized) ∧
      anc.length ≤ ancestorLimit := by
  unfold validate at h
  split at h
  · cases h
  · rename_i ins hins
    split at h
    · cases h
    · rename_i hmiss
      unfold ancestryVerdict at h
      split at h
      · cases h
      · rename_i hauth
        split at h
        · rename_i hle
          simp only [Verdict.admitted.injEq] at h
          subst h
          refine ⟨⟨ins, hins, fun o ho => ?_⟩, rfl, fun t ht => ?_, hle⟩
          · have := List.find?_eq_none.mp hmiss o ho
            cases hs : shown snap o
            · simp [hs] at this
              exact Or.inr this
            · exact Or.inl rfl
          · have := List.find?_eq_none.mp hauth t ht
            simpa using this
        · cases h

/-! ## `WTC-24`'s refusals, universal -/

/-- An input the prevout read does not show, with no resident named, is refused under either
value. `WTC-24`: "every prevout MUST exist (unknown or spent is an error)". -/
@[req "WTC-24"]
theorem unshown_refused (g : ReplacementAncestry) (creator : Creator) (snap : Snapshot)
    (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (o : Outpoint) (ho : o ∈ c.inputs)
    (hs : shown snap o = false) :
    (validate g creator snap mem authorized c none).isAdmitted = false := by
  match hv : validate g creator snap mem authorized c none with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨⟨ins, hins, hall⟩, -⟩ := admitted_only_when g creator snap mem authorized c none anc hv
    simp only [residentRead, Except.ok.injEq] at hins
    subst hins
    rcases hall o ho with h | h
    · rw [hs] at h; cases h
    · simp at h

/-- An unconfirmed parent not in the vault-authorized set is refused, under either value and
whatever resident. `WTC-24`: "an unconfirmed parent MUST be resident in the mempool AND in the
vault-authorized set". With `ancestor_resident` this is the bead's refusal of a candidate spending
an unconfirmed non-resident parent: a walked parent is resident by construction, and refused
here when unauthorized. -/
@[req "WTC-24"]
theorem unauthorized_ancestor_refused (g : ReplacementAncestry) (creator : Creator)
    (snap : Snapshot) (mem : MempoolRead) (authorized : List Nat) (c : Candidate)
    (replaces : Option Nat) (t : Nat) (ht : t ∈ ancestors creator mem c.inputs)
    (ha : t ∉ authorized) :
    (validate g creator snap mem authorized c replaces).isAdmitted = false := by
  match hv : validate g creator snap mem authorized c replaces with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨-, rfl, hall, -⟩ :=
      admitted_only_when g creator snap mem authorized c replaces anc hv
    exact absurd (hall t ht) ha

/-- More than `ancestorLimit` distinct ancestors is refused, under either value and whatever
resident. `WTC-24`: "more than 24 distinct ancestors is an error". -/
@[req "WTC-24"]
theorem over_limit_refused (g : ReplacementAncestry) (creator : Creator) (snap : Snapshot)
    (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (replaces : Option Nat)
    (h : ancestorLimit < (ancestors creator mem c.inputs).length) :
    (validate g creator snap mem authorized c replaces).isAdmitted = false := by
  match hv : validate g creator snap mem authorized c replaces with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨-, rfl, -, hle⟩ := admitted_only_when g creator snap mem authorized c replaces anc hv
    omega

/-! ## `WTC-25`'s refusals, universal, and the replacement admitted -/

/-- A resident not in the vault-authorized set refuses under either value. `WTC-25`: "a resident
the node never accepted is not something it replaces". -/
@[req "WTC-25"]
theorem resident_unauthorized_refused (g : ReplacementAncestry) (creator : Creator)
    (snap : Snapshot) (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (r : Nat)
    (ha : r ∉ authorized) :
    (validate g creator snap mem authorized c (some r)).isAdmitted = false := by
  match hv : validate g creator snap mem authorized c (some r) with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨⟨ins, hins, -⟩, -⟩ := admitted_only_when g creator snap mem authorized c (some r) anc hv
    simp only [residentRead] at hins
    split at hins
    · cases hins
    · simp [ha] at hins

/-- A resident not in the membership read refuses under either value: the candidate replaces
nothing resident. -/
@[req "WTC-25"]
theorem resident_absent_refused (g : ReplacementAncestry) (creator : Creator) (snap : Snapshot)
    (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (r : Nat)
    (hm : mem.lookup r = none) :
    (validate g creator snap mem authorized c (some r)).isAdmitted = false := by
  match hv : validate g creator snap mem authorized c (some r) with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨⟨ins, hins, -⟩, -⟩ := admitted_only_when g creator snap mem authorized c (some r) anc hv
    simp [residentRead, hm] at hins

/-- Under `.overResident` in full, inputs that differ from the resident's ordered inputs refuse.
`WTC-25`: "MUST spend exactly the same ordered outpoints as the resident transaction". -/
@[req "WTC-25"]
theorem different_outpoints_refused (creator : Creator) (snap : Snapshot) (mem : MempoolRead)
    (authorized : List Nat) (c : Candidate) (r : Nat) (ins : List Outpoint)
    (hm : mem.lookup r = some ins) (hne : c.inputs ≠ ins) :
    (validate .overResident creator snap mem authorized c (some r)).isAdmitted = false := by
  match hv : validate .overResident creator snap mem authorized c (some r) with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨⟨ins', hins, -⟩, -⟩ :=
      admitted_only_when .overResident creator snap mem authorized c (some r) anc hv
    simp only [residentRead, hm] at hins
    split at hins
    · simp [sameOrderedOutpoints, hne] at hins
    · cases hins

/-- Under `.overResident` in full, over every snapshot — so in particular one whose read shows
none of the inputs, which the mempool-inclusive read hides because the resident spends them: a
replacement over a resident `r` in the membership read and in the authorized set, with exactly
`r`'s ordered inputs, whose every unconfirmed ancestor through `r`'s parents is authorized and
within the limit, is admitted with those ancestors. `WTC-24`: "the resident's own inputs are read
as unspent for the replacement"; `WTC-25`: "Without this clause a refresh could never be
fee-bumped: its first attempt, resident, would make its own inputs read as spent on every node."
Every walked ancestor is resident (`ancestor_resident`), so "resident and authorized" is the one
premise. -/
@[req "WTC-25"]
theorem replacement_admitted (creator : Creator) (snap : Snapshot) (mem : MempoolRead)
    (authorized : List Nat) (c : Candidate) (r : Nat) (ins : List Outpoint)
    (hm : mem.lookup r = some ins) (hr : r ∈ authorized) (hc : c.inputs = ins)
    (hanc : ∀ t ∈ ancestors creator mem c.inputs, t ∈ authorized)
    (hlim : (ancestors creator mem c.inputs).length ≤ ancestorLimit) :
    validate .overResident creator snap mem authorized c (some r) =
      .admitted (ancestors creator mem c.inputs) := by
  subst hc
  have hres : residentRead .overResident mem authorized c (some r) = .ok c.inputs := by
    simp [residentRead, hm, hr, sameOrderedOutpoints]
  have hmiss : missingPrevout snap c.inputs c.inputs = none := by
    apply List.find?_eq_none.mpr
    intro o ho
    simp [ho]
  have hauth : (ancestors creator mem c.inputs).find? (fun t => !authorized.contains t) = none := by
    apply List.find?_eq_none.mpr
    intro t ht
    simp [hanc t ht]
  simp only [validate, hres, hmiss, ancestryVerdict, hauth, hlim, ↓reduceIte]

/-- Under `.plainRead` in full: an input the prevout read does not show is refused whatever the
resident — the row `F54` records, with the resident's inputs read as spent by the
mempool-inclusive read and nothing admitting them. -/
@[req "WTC-25"]
theorem plainRead_refuses_unshown (creator : Creator) (snap : Snapshot) (mem : MempoolRead)
    (authorized : List Nat) (c : Candidate) (replaces : Option Nat) (o : Outpoint)
    (ho : o ∈ c.inputs) (hs : shown snap o = false) :
    (validate .plainRead creator snap mem authorized c replaces).isAdmitted = false := by
  match hv : validate .plainRead creator snap mem authorized c replaces with
  | .refused _ => rfl
  | .admitted anc =>
    obtain ⟨⟨ins, hins, hall⟩, -⟩ :=
      admitted_only_when .plainRead creator snap mem authorized c replaces anc hv
    have hnil : ins = [] := by
      simp only [residentRead] at hins
      split at hins
      · simp only [Except.ok.injEq] at hins; exact hins.symm
      · split at hins
        · cases hins
        · split at hins
          · simp only [Except.ok.injEq] at hins; exact hins.symm
          · cases hins
    subst hnil
    rcases hall o ho with h | h
    · rw [hs] at h; cases h
    · simp at h

/-! ## The ordered-outpoints exhibits (`WTC-25`) -/

/-- `[X, Y]` over `[X, Y]`: the same ordered outpoints. -/
@[req "WTC-25"]
theorem same_outpoints_admitted : sameOrderedOutpoints [1, 2] [1, 2] = true := by decide

/-- `[Y, X]` over `[X, Y]`: the same coins in the other order are refused; `CHN-18`'s canonical
order is why no composed replacement ever takes this branch. -/
@[req "WTC-25"]
theorem reordered_refused : sameOrderedOutpoints [2, 1] [1, 2] = false := by decide

/-- `[X]` over `[X, Y]`: a strict subset is refused. -/
@[req "WTC-25"]
theorem subset_refused : sameOrderedOutpoints [1] [1, 2] = false := by decide

/-! ## The twin under the withdrawn value (`F54`)

A resident `R`, txid 10, authorized and in the membership read, spending two confirmed vault coins
`X = 1` and `Y = 2`, whose creator 0 is not resident; a replacement `R'`, txid 11, over `[X, Y]`;
a snapshot whose read holds neither `X` nor `Y`, since the mempool-inclusive prevout
re-validation dropped them — `R` spends them. Under `.plainRead` `R'` is refused; under `current`
it is admitted (`Exhibits.PackageAncestry.twin_admitted_with_current`). `WTC-25`: "its first
attempt, resident, would make its own inputs read as spent on every node" — made executable. -/

/-- The resident `R`. -/
@[req "WTC-25"] def twinResident : Nat := 10
/-- The coins `R` spends, confirmed: `X` and `Y`. -/
@[req "WTC-25"] def twinInputs : List Outpoint := [1, 2]
/-- The membership read: `R` alone, over `[X, Y]`. -/
@[req "WTC-25"] def twinMembership : MempoolRead := [(twinResident, twinInputs)]
/-- The authorized set: `R`. -/
@[req "WTC-25"] def twinAuthorized : List Nat := [twinResident]
/-- Every outpoint's creator is transaction 0, confirmed and not resident. -/
@[req "WTC-25"] def twinCreator : Creator := fun _ => 0
/-- The snapshot: the read holds neither `X` nor `Y`. -/
@[req "WTC-25"] def twinSnapshot : Snapshot := { tip := ⟨5, 105⟩, sequence := 7, read := [] }
/-- The replacement `R'` over `[X, Y]`. -/
@[req "WTC-25"] def twinReplacement : Candidate := { txid := 11, inputs := twinInputs }

/-- Under `.plainRead` the replacement is refused "unknown or spent" on `X`: the read does not
show it and nothing reads the resident's inputs as unspent. -/
@[req "WTC-25"]
theorem twin_refused_with_plainRead :
    validate .plainRead twinCreator twinSnapshot twinMembership twinAuthorized twinReplacement
      (some twinResident) = .refused (.unknownOrSpent 1) := by
  decide

/-! ## The diamond (`WTC-24`)

Two unconfirmed parents `P1 = 21` and `P2 = 22` each spend one output of one unconfirmed
grandparent `G = 20`, which spends a confirmed coin; the candidate spends one output of each
parent. All three are authorized and resident. The walk counts three, not four. -/

/-- Outpoints 31 and 32 are `P1`'s and `P2`'s outputs, 41 and 42 are `G`'s, 50 is confirmed. -/
@[req "WTC-24"]
def diamondCreator : Creator := fun o =>
  if o == 31 then 21 else if o == 32 then 22 else if o == 41 || o == 42 then 20 else 0
/-- The membership read: `G` over the confirmed coin, `P1` and `P2` each over one of `G`'s. -/
@[req "WTC-24"] def diamondMembership : MempoolRead := [(20, [50]), (21, [41]), (22, [42])]
/-- All three authorized. -/
@[req "WTC-24"] def diamondAuthorized : List Nat := [20, 21, 22]
/-- The read shows the two parents' outputs, mempool additions from the authorized set. -/
@[req "WTC-24"]
def diamondSnapshot : Snapshot := { tip := ⟨5, 105⟩, sequence := 7, read := [(31, 1), (32, 1)] }
/-- The candidate over the two parents' outputs. -/
@[req "WTC-24"] def diamondCandidate : Candidate := { txid := 23, inputs := [31, 32] }

/-- The diamond, decided: three distinct ancestors, each of `G`, `P1` and `P2` collected once, and
admitted under either value with no resident named. -/
@[req "WTC-24"]
theorem diamond_counts_three :
    (ancestors diamondCreator diamondMembership diamondCandidate.inputs).length = 3 ∧
      (∀ t ∈ [20, 21, 22], t ∈ ancestors diamondCreator diamondMembership diamondCandidate.inputs) ∧
      (validate .overResident diamondCreator diamondSnapshot diamondMembership diamondAuthorized
        diamondCandidate none).isAdmitted = true ∧
      (validate .plainRead diamondCreator diamondSnapshot diamondMembership diamondAuthorized
        diamondCandidate none).isAdmitted = true := by
  decide

end BtcPolicy.Package
