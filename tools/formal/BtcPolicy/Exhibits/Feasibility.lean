import BtcPolicy.Evaluate
import BtcPolicy.Cursor
import BtcPolicy.Coverage
import BtcPolicy.Deadline
import BtcPolicy.Classification
import BtcPolicy.Membership
import BtcPolicy.RefreshAge
import BtcPolicy.Kernel
import BtcPolicy.Federation
import BtcPolicy.Ingress
import BtcPolicy.Lifetime
import BtcPolicy.Sweep
import BtcPolicy.Settlement
import BtcPolicy.Budget
import BtcPolicy.Ledger
import BtcPolicy.Silence
import BtcPolicy.FedSilence
import BtcPolicy.Admission
import BtcPolicy.Progress
import BtcPolicy.Delivery
import BtcPolicy.Chain
import BtcPolicy.Watchtower
import BtcPolicy.VaultUnspent
import BtcPolicy.Alerts
import BtcPolicy.Package
import BtcPolicy.Trace
import BtcPolicy.TxAccounting
import BtcPolicy.Feasibility
import BtcPolicy.Recovery
import BtcPolicy.EscapeCustody
import BtcPolicy.ClawbackIngress
import BtcPolicy.ClawHandler
import BtcPolicy.PreRelease
import BtcPolicy.Coinbase
import BtcPolicy.Ladder
import BtcPolicy.Assembly
import BtcPolicy.RungRelease
import BtcPolicy.LadderRelease
import BtcPolicy.RungIngress
import BtcPolicy.RungAssembly
import BtcPolicy.VariantReceipt
import BtcPolicy.ClassAssembly
import BtcPolicy.LadderShape
import BtcPolicy.AcceptedSet
import BtcPolicy.Lifecycle
import BtcPolicy.Retained
import BtcPolicy.ReceiptExpiry
import BtcPolicy.ReleaseQuota
import BtcPolicy.Possession
import BtcPolicy.ExpirySilence
import BtcPolicy.VariantSilence
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.Feasibility
open BtcPolicy.Feasibility
open BtcPolicy.Coverage (Coin Outpoint)

/-! ### Fast-exit feasibility

Research task `bps-uaer.17`, over `F1`, `F2` and `F48`. Every state below is a `Sweep.Backend` instant
with hand-chosen values; `Coverage.current`, `Coverage.currentExternal` and `Package.current` are the
guards. `Limits` here is 2-of-3 with one `P2WSH` output, the primary and the Escape on the wire. Its
wire figures are assumptions of these exhibits, and `escape_feerate_floor` is 1 unless a state says
otherwise. -/






/-- A parent near the consensus limit, nearly all witness (`F1`'s "consensus-valid very large
parent"). -/
def huge : Parent := ⟨1000, 3980000⟩
/-- A parent over twice the body cap, inside the domain. -/
def over2 : Parent := ⟨1000, 2100000⟩

def refusal : Except Refusal Request → Option Refusal
  | .error e => some e
  | .ok _ => none

theorem ok_of_toOption {x : Except Refusal Request} {q : Request} (h : x.toOption = some q) :
    x = .ok q := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok a =>
    simp only [Except.toOption, Option.some.injEq] at h
    rw [h]


/-! #### A feasible state -/

def smallCoins : List Coin := [(1, 60000), (2, 30000), (3, 10000)]
def smallVault : Vault :=
  mk smallCoins (fun o => if o == 1 then 60000 else if o == 2 then 30000 else 10000)
    fun _ => some plain

/-- **A feasible state with its constructed request.** The composer spends every coin and what it
builds validates, reached both by the check and by `compose_bounded`'s premises. -/
@[req "OPR-33"]
theorem feasible_constructed :
    (composeEvery lim 9 smallVault).toOption = some (everyRequest lim 9 smallVault) ∧
      (everyRequest lim 9 smallVault).inputs = [1, 2, 3] ∧
      smallVault.bounded lim .ignore (everyRequest lim 9 smallVault) = true ∧
      smallVault.bounded lim .verify (everyRequest lim 9 smallVault) = true ∧
      smallVault.bounded lim .refuse (everyRequest lim 9 smallVault) = false := by
  decide +kernel

/-- `compose_bounded`'s premises hold at that state, so the theorem has an inhabitant. -/
@[req "OPR-33"]
theorem compose_bounded_inhabited :
    smallVault.bounded lim .ignore (everyRequest lim 9 smallVault) = true :=
  compose_bounded .ignore (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    (ok_of_toOption (x := composeEvery lim 9 smallVault) (q := everyRequest lim 9 smallVault)
      (by decide +kernel))

/-- `feasible_iff_best` at that state with its count bound discharged: 620 inputs is `OPR-35`'s
figure at this shape. One coin reaches the share, two fewer than the composer spends. -/
@[req "DUR-24"]
theorem closed_form_small :
    (∃ q, q.carried = false ∧ smallVault.bounded lim .ignore q = true) :=
  (feasible_iff_best smallVault lim .ignore false (fun _ => true) 620 rfl rfl (by decide)
    (by decide) (by decide) (by decide)
    (countOnly_of_slack smallVault lim .ignore 620 250 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
      (by decide +kernel) (by decide))).2 ⟨1, by decide, by decide +kernel⟩

/-- The count bound itself: at this shape 620 inputs fit `OPR-35`'s vsize bound and 621 do not, and
at 8-of-15 the same bound stops at 268. -/
@[req "OPR-35"]
theorem vsize_capacity :
    vsizeOf lim 620 ≤ vsizeCap ∧ vsizeCap < vsizeOf lim 621 ∧
      vsizeOf { lim with t := 8, n := 15 } 268 ≤ vsizeCap ∧
      vsizeCap < vsizeOf { lim with t := 8, n := 15 } 269 := by
  decide +kernel

/-- A full ladder on the wire lowers the count under these sizes: with five PSBTs at 400 bytes the
body cap binds before the vsize bound does. -/
@[req "API-4"]
theorem ladder_lowers_capacity :
    let full : Limits := { lim with psbts := 5 }
    (smallVault.wire full (List.range 524) false ≤ bodyCap) = false ∧
      (smallVault.wire lim (List.range 620) false ≤ bodyCap) = true := by
  decide +kernel

/-! #### `F1`: consolidation and fragments -/

/-- One large coin and 621 dust coins an outsider sent. -/
def dustCoins : List Coin := (0, 1000000000) :: (List.range 621).map fun i => (i + 1, 546)
def dustVault : Vault := mk dustCoins (fun o => if o == 0 then 1000000000 else 546) fun _ => some plain

/-- **The composer's refusal is not infeasibility.** Dust alone stops `OPR-33`'s composer, which has
"no coin selection and no omission"; one input covers the vault, and the dust stays in its
denominator. -/
@[req "OPR-33"]
theorem dust_stops_composer_only :
    refusal (composeEvery lim 9 dustVault) = some .vsizeOver ∧
      dustVault.bounded lim .ignore (requestOver dustVault lim 9 [0]) = true ∧
      dustVault.denominator (requestOver dustVault lim 9 [0]) = dustVault.total ∧
      dustVault.total = 1000000000 + 621 * 546 := by
  decide +kernel

/-- `n` coins of 100 000. -/
def even (n : Nat) : List Coin := (List.range n).map fun i => (i, 100000)
def evenVault (n : Nat) : Vault := mk (even n) (fun _ => 100000) fun _ => some plain

theorem evenVault_read (n : Nat) : (evenVault n).read = even n := by
  simp [Vault.read, Vault.snap, Sweep.snapshot, Sweep.additions, evenVault, mk, instant,
    Sweep.spentInMempool]

/-- **`F1`, fragmentation: no bounded request exists.** Every coin equal, and more of them than `620`
inputs can reach at `MAN-9`'s floor: `fragmented_infeasible` over every request, not a search. The
state is admissible: canonical, values agreeing, every parent small. -/
@[req "DUR-24"]
theorem fragments_infeasible (rule : ParentRule) (q : Request) :
    (evenVault 1216).bounded lim rule q = false := by
  have hv : ∀ c ∈ (evenVault 1216).read, (evenVault 1216).cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [evenVault_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hle : ∀ c ∈ (evenVault 1216).read, c.2 ≤ 100000 := by
    intro c hc
    rw [evenVault_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    exact Nat.le_refl _
  exact Vault.fragmented_infeasible rfl rfl (by decide +kernel) hv hle
    (fun q h => Vault.inputs_le_of_vsize (N := 620) (by decide +kernel) h) (by decide +kernel) q

/-- Below that count the same vault has a request, by `feasible_iff_best` at 620 inputs with the fee
at the floor paid: 620 of 1 213 coins cover. The two figures bracket the threshold at this floor. -/
@[req "DUR-24"]
theorem fragments_feasible_below :
    ∃ q, q.carried = false ∧ (evenVault 1213).bounded lim .ignore q = true := by
  have hrd := evenVault_read 1213
  have hs : ascending ((evenVault 1213).read.map (·.1)) = true := by rw [hrd]; decide +kernel
  have hv : ∀ c ∈ (evenVault 1213).read, (evenVault 1213).cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [hrd] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hsum : Coverage.sumValues (even 620) = 62000000 := by decide +kernel
  have hsub : (even 620).Sublist (even 1213) := by
    have : even 620 = (even 1213).take 620 := by decide +kernel
    rw [this]
    exact List.take_sublist _ _
  have hbest : 62000000 ≤ best 620 ((evenVault 1213).read.filter fun _ => true) := by
    have hft : (even 1213).filter (fun _ => true) = even 1213 := List.filter_eq_self.2 fun _ _ => rfl
    rw [hrd, hft]
    exact hsum ▸ best_ge _ _ 620 hsub (by decide +kernel)
  refine (feasible_iff_best (evenVault 1213) lim .ignore false (fun _ => true) 620 rfl rfl hs hv
    (by rw [Vault.total, hrd]; decide +kernel) (by decide)
    (countOnly_of_slack _ lim .ignore 620 250 (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => Nat.le_of_eq rfl)
      (by decide +kernel) (fun _ _ => rfl))).2 ⟨620, by decide, ?_⟩
  have hf : (evenVault 1213).floor * vsizeOf lim 620 = vsizeOf lim 620 := Nat.one_mul _
  have hvs : vsizeOf lim 620 ≤ 99900 := by decide +kernel
  have ht : (evenVault 1213).total * (evenVault 1213).cfg.pct = 6186300000 := by
    rw [Vault.total, hrd]
    decide +kernel
  rw [ht, hf]
  omega

/-! #### `F1`: a large parent -/

/-- Sixteen outputs of one parent near the consensus limit, equal in value. -/
def toxicCoins : List Coin := (List.range 16).map fun i => (i, 100000)
def toxicVault : Vault :=
  mk toxicCoins (fun _ => 100000) (fun _ => some huge) (creator := fun _ => 7)

theorem toxic_read : toxicVault.read = toxicCoins := by decide

/-- The parents are inside the assumed domain, and the large one's non-witness bytes hold its sixteen
`P2WSH` outputs at 43 bytes each. -/
@[req "OPR-35"]
theorem huge_in_domain : huge.inDomain = true ∧ over2.inDomain = true ∧ 16 * 43 ≤ huge.base := by decide

/-- **`F1`, large parent: no bounded request exists.** Nine inputs from this parent project past
`OPR-35`'s 64 MiB, eight carry half the value, and `MAN-9`'s floor needs more than half. -/
@[req "OPR-35"]
theorem toxic_infeasible (rule : ParentRule) (q : Request) :
    toxicVault.bounded lim rule q = false := by
  have hv : ∀ c ∈ toxicVault.read, toxicVault.cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [toxic_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hle : ∀ c ∈ toxicVault.read, c.2 ≤ 100000 := by
    intro c hc
    rw [toxic_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    exact Nat.le_refl _
  have hm : ∀ c ∈ toxicVault.read, 3981000 ≤ toxicVault.parentBytes c.1 := fun _ _ =>
    Nat.le_of_eq (show 3981000 = _ from rfl)
  exact Vault.fragmented_infeasible rfl rfl (by decide) hv hle
    (fun q h => Vault.inputs_le_of_retained (N := 8) (m := 3981000) hm (by decide +kernel) h)
    (by decide +kernel) q

/-- That refutation is the composer's and the signer's bound, not the node's. A node reading no
parent takes a request of nine of these coins; `OPR-35` refuses to retain them, and the composer
stops at the same bound. -/
@[req "OPR-35"]
theorem toxic_node_would_take :
    toxicVault.nodeOk lim .ignore (requestOver toxicVault lim 9 (List.range 9)) = true ∧
      toxicVault.boundOk lim (List.range 9) = false ∧
      toxicVault.boundOk lim (List.range 8) = true ∧
      refusal (composeEvery lim 9 toxicVault) = some .retainedOver := by
  decide +kernel

/-- One such parent paying the vault once breaks nothing with the wire stripped: inside the domain
eight inputs always fit (`Vault.eight_inputs_always_retained`), so `F1`'s large parent needs
multiplicity or a wire that carries it. -/
@[req "OPR-35"]
theorem one_large_parent_composes :
    let v := mk [(0, 100000)] (fun _ => 100000) (fun _ => some huge)
    (composeEvery lim 9 v).toOption = some (everyRequest lim 9 v) := by
  decide +kernel

/-! #### `F2`: vault-authorized unconfirmed value -/

/-- A prior vault spend, 500, is resident over coin 1 and pays 90 000 back to the vault as coin 5;
coin 0 holds the rest. -/
def priorCreator : Package.Creator := fun o => if o == 5 then 500 else funding o
def priorVault : Vault :=
  { cfg := cfgOf (fun o => if o == 0 then 10000 else if o == 1 then 95000 else 90000) priorCreator,
    A := [500], b := instant [(0, 10000), (1, 95000)] [(500, [1])] [(500, (5, 90000))],
    parentOf := fun _ => some plain, floor := 1 }

/-- **`F2`, the gap: a request exists that the composer cannot build.** The node takes a request
over the unconfirmed change, `WTC-24` admitting its one authorized ancestor. `OPR-34` refuses the
whole inventory for coin 1 ("A coin mempool-spent by a prior vault spend is the common case"). -/
@[req "OPR-39"]
theorem prior_spend_composer_refuses :
    priorVault.read = [(0, 10000), (5, 90000)] ∧
      priorVault.bounded lim .ignore (requestOver priorVault lim 9 [0, 5]) = true ∧
      refusal (composeEvery lim 9 priorVault) = some (.mempoolSpent 1) := by
  decide +kernel

/-- And composing over the remainder would not help, the reason `OPR-34` gives: "Composing over the
remainder yields an under-covered Escape." No request over confirmed coins alone covers this state. -/
@[req "OPR-34"]
theorem confirmed_only_undercovers (q : Request) (h : ∀ o ∈ q.inputs, o = 0) :
    priorVault.nodeOk lim .ignore q = false := by
  refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 == 0) rfl rfl (by decide) (by decide)
    (by decide +kernel) ?_
  intro c hc
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
  simp [h o ho]

/-- A chain of `k` residents, each spending the last one's change; only the tail's is unspent. -/
def chainMempool (k : Nat) : Package.MempoolRead :=
  (List.range k).map fun i => (i + 1, [if i == 0 then 1000 else i])
def chainPending (k : Nat) : List (Nat × Coin) :=
  (List.range k).map fun i => (i + 1, (i + 1, 90000))
def chainCreator (k : Nat) : Package.Creator := fun o => if 1 ≤ o && o ≤ k then o else funding o
def chainVault (k : Nat) : Vault :=
  { cfg := cfgOf (fun o => if o == 0 then 10000 else if o == 1000 then 90000 else 90000) (chainCreator k),
    A := (List.range k).map (· + 1),
    b := instant [(0, 10000), (1000, 90000)] (chainMempool k) (chainPending k),
    parentOf := fun _ => some plain, floor := 1 }

/-- **`F2`, the deep chain: no bounded request exists.** The value sits on the tail of 25 residents,
all vault-authorized. The tail itself has 24 ancestors, which `WTC-24` calls "one below Bitcoin
Core's default ancestor limit", so a default mempool can hold it; a candidate spending it has 25.
No selection goes around it (`deep_coin_excluded`), coin 0 alone does not cover, and nothing leaves
the denominator. Here the node's own rule refuses, under every `F48` reading. -/
@[req "WTC-24"]
theorem deep_chain_infeasible (rule : ParentRule) (q : Request) :
    (chainVault 25).nodeOk lim rule q = false := by
  have hrd : (chainVault 25).read = [(0, 10000), (25, 90000)] := by decide +kernel
  by_cases hin : 25 ∈ q.inputs
  · have : (chainVault 25).ancestryOk q.inputs = false :=
      deep_coin_excluded hin (by decide +kernel)
    simp [Vault.nodeOk, this]
  · refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 != 25) rfl rfl
      (by decide +kernel) (by rw [hrd]; decide +kernel) (by decide +kernel) ?_
    intro c hc
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
    have : o ≠ 25 := fun he => hin (he ▸ ho)
    simpa using this

/-- One link shorter the same state has a request over the tail: 24 ancestors pass. -/
@[req "WTC-24"]
theorem shallow_chain_feasible :
    (chainVault 24).read = [(0, 10000), (24, 90000)] ∧
      (chainVault 24).bounded lim .ignore (requestOver (chainVault 24) lim 9 [0, 24]) = true := by
  decide +kernel

/-! #### `F48`: inputs without full previous transactions -/

/-- Coin 0 holds most of the value and its parent is more than a body cap's worth. -/
def largeVault : Vault :=
  mk [(0, 90000), (1, 10000)] (fun o => if o == 0 then 90000 else 10000)
    fun t => if t == funding 0 then some over2 else some plain

/-- **`F48` moves the verdict.** At one state, under `ignore` and `verify` a stripped request is
bounded. Under `refuse` a request must carry its parents, the parent then exceeds `API-4`'s body cap,
and the other coin does not cover: no request. `F48` says the rule "matters for `F1`'s size bounds";
this is that, and it answers nothing. -/
@[req "API-4"]
theorem f48_moves_the_verdict (q : Request) :
    largeVault.bounded lim .ignore (requestOver largeVault lim 9 [0, 1]) = true ∧
      largeVault.bounded lim .verify (requestOver largeVault lim 9 [0, 1]) = true ∧
      largeVault.nodeOk lim .refuse q = false := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  cases hc : q.carried with
  | false => simp [Vault.nodeOk, Vault.wireOk, hc]
  | true =>
    by_cases hin : 0 ∈ q.inputs
    · have : largeVault.wireOk lim .refuse q.inputs true = false :=
        Vault.carried_parent_over_body hin (by decide +kernel)
      simp [Vault.nodeOk, hc, this]
    · refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 != 0) rfl rfl (by decide)
        (by decide) (by decide +kernel) ?_
      intro c hc'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc'
      have : o ≠ 0 := fun he => hin (he ▸ ho)
      simpa using this

/-- Coin 0's full previous transaction cannot be obtained. -/
def missingVault : Vault :=
  mk [(0, 90000), (1, 10000)] (fun o => if o == 0 then 90000 else 10000)
    fun t => if t == funding 0 then none else some plain

/-- **`F48`, no full previous transaction: no bounded request exists.** `CHN-22` makes the coin
unsignable and the composer refuses. The other coin does not cover, and the coin stays in the
denominator. A node that reads no parent would take a request over it, had one been signed: signing
needs the parent the wire strips, which is where the finding and `CHN-22` meet. -/
@[req "CHN-22"]
theorem missing_parent_infeasible (rule : ParentRule) (q : Request) :
    missingVault.bounded lim rule q = false ∧
      missingVault.nodeOk lim .ignore (requestOver missingVault lim 9 [0, 1]) = true ∧
      refusal (composeEvery lim 9 missingVault) = some (.noParent 0) := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  refine Vault.unreachable_infeasible (usable := fun c => c.1 != 0) rfl rfl (by decide) (by decide)
    (fun q hq c hc => ?_) (by decide +kernel) q
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
  have hall : (q.inputs.all fun o => (missingVault.parent o).isSome) = true := by
    simp only [Vault.bounded, Vault.boundOk, Bool.and_eq_true] at hq
    exact hq.2.1.2
  have hsome := List.all_eq_true.1 hall o ho
  have : o ≠ 0 := by
    rintro rfl
    exact absurd hsome (by decide)
  simpa using this

/-- Every state the refutations and comparisons above name is admissible. -/
@[req "MAN-9"]
theorem states_admissible :
    smallVault.admissible = true ∧ dustVault.admissible = true ∧ (evenVault 1216).admissible = true ∧
      (evenVault 1213).admissible = true ∧ toxicVault.admissible = true ∧ priorVault.admissible = true ∧
      (chainVault 25).admissible = true ∧ (chainVault 24).admissible = true ∧
      largeVault.admissible = true ∧ missingVault.admissible = true := by
  decide +kernel

/-! #### The denominator is not the repair -/

def halves : Vault := mk [(0, 50000), (1, 50000)] (fun _ => 50000) fun _ => some plain

/-- **Omitting a coin from the denominator is what `MAN-9`'s floor forbids.** Each coin alone covers
a denominator that omits the other, so two input-disjoint Escapes both pass. Against `DUR-22`'s value
neither does. An omitted coin stays counted, and that is why infeasibility above is not repaired by
narrowing what is protected. -/
@[req "DUR-22"]
theorem omitting_admits_two :
    let d := fun o => (halves.escape (requestOver halves lim 9 [o])).delivered
    Coverage.covers (d 0) 50000 Coverage.floorPct = true ∧
      Coverage.covers (d 1) 50000 Coverage.floorPct = true ∧ d 0 + d 1 ≤ 100000 ∧
      halves.denominator (requestOver halves lim 9 [0]) = 100000 ∧
      halves.denominator (requestOver halves lim 9 [1]) = 100000 ∧
      halves.coverOk (requestOver halves lim 9 [0]) = false ∧
      halves.coverOk (requestOver halves lim 9 [1]) = false := by
  decide +kernel

/-! #### Bounded-selection ideas, compared -/

/-- Dust before the large coin: prefix selection misses it, largest-first finds it. -/
def lateCoin : Vault :=
  mk [(0, 546), (1, 546), (2, 546), (999, 1000000000)]
    (fun o => if o == 999 then 1000000000 else 546) fun _ => some plain

/-- The largest coin has no parent: largest-first picks it and stops, and a request exists. -/
def largeNoParent : Vault :=
  mk [(0, 50000), (1, 30000), (2, 30000)] (fun o => if o == 0 then 50000 else 30000)
    fun t => if t == funding 0 then none else some plain

/-- **No idea here dominates, and none repairs an infeasible state.** Spending every coin fails where
prefix selection works (`dustVault`); prefix fails where largest-first works (`lateCoin`); largest-first
fails where a third selection works (`largeNoParent`), which `F1`'s "distinguish an unsupported toxic
fragment from insufficient funds" also asks. On `fragments_infeasible` and `toxic_infeasible` every
selection fails, being a request. Nothing here selects a mechanism. -/
@[req "OPR-33"]
theorem selection_ideas_compared :
    refusal (composeEvery lim 9 dustVault) = some .vsizeOver ∧
      dustVault.bounded lim .ignore (byPrefix dustVault lim 9 2) = true ∧
      lateCoin.bounded lim .ignore (byPrefix lateCoin lim 9 2) = false ∧
      lateCoin.bounded lim .ignore (byLargest lateCoin lim 9 2) = true ∧
      largeNoParent.bounded lim .ignore (byLargest largeNoParent lim 9 2) = false ∧
      largeNoParent.bounded lim .ignore (requestOver largeNoParent lim 9 [1, 2]) = true := by
  decide +kernel

/-! #### On the composed sweep -/

section Run
open BtcPolicy.Sweep BtcPolicy.Sweep.Cases
open BtcPolicy.Federation.Cases (honest)

/-- The sweep fixture's book with coin 9 given its value, and its guards as they stand. -/
def runBook : Book :=
  { Cases.book with value := fun o => if o == 9 then 1000 else Cases.book.value o }
def runCfg : Cfg :=
  { Cases.cfg Coverage.current Coverage.currentExternal Package.current with book := runBook }

/-- **The request the composed sweep assembles validates.** `Exhibits.Sweep.successful_sweep`'s Escape
over `Sweep.Cases.vault`, read as a request: same inputs, its fee the difference it pays, no feerate
floor since the fixture's values are too small to carry one. -/
@[req "DUR-24"]
theorem swept_request_validates :
    let v : Vault := { cfg := Exhibits.Sweep.cfgNow, A := [], b := vault, parentOf := fun _ => some plain,
                       floor := 0 }
    let q : Request := { txid := Kernel.RegistrationCases.txE.id, inputs := Kernel.RegistrationCases.txE.inputs, fee := 10 }
    v.bounded lim .ignore q = true ∧ (v.escape q).delivered = Cases.book.delivered Kernel.RegistrationCases.txE.id := by
  decide +kernel

/-- **Armed, fast exit unavailable, and nothing submitted.** At an instant where one Escape cannot
reach its share (`vaultLarge`, its third coin in no input), both nodes arm, the hot spend is frozen
and the partials are delivered. That registered Escape's assembly is refused and the send submits
nothing. Another request over all three coins would pass at this read: this run is one Escape's
failure, not a state with no request. `F1`: "Funds remain under vault and Recovery authority; what is lost is the
fast exit." -/
@[req "DUR-24"]
theorem armed_no_fast_exit :
    let ss := delivered ++ [.observe 1 vaultLarge]
    let p := record Kernel.current [] (start vaultLarge) ss
    let n := (p.2.fed.worlds 1).node
    legal runCfg Kernel.current honest [] (start vaultLarge) ss = true ∧
      n.armed = true ∧ ((p.2.fed.worlds 2).node).armed = true ∧
      n.cands.any (fun c => c.id == Kernel.RegistrationCases.c1.id && c.frozen) = true ∧
      covered runCfg (authorizedAt p.2 p.1 1) n vaultLarge Kernel.RegistrationCases.e1 = false ∧
      admits runCfg honest p.2 p.1 (assemble 1 Kernel.RegistrationCases.e1.id) = false ∧
      submits Kernel.current p.2 (sendAt 1 Kernel.RegistrationCases.e1.id) = [] := by
  decide

/-- The same verdict from the theorem, at that node's own selected set: the delivery is within what
the Escape's own inputs hold, and the read holds a thousand more. -/
@[req "DUR-24"]
theorem armed_verdict_from_bound :
    let ss := delivered ++ [.observe 1 vaultLarge]
    let p := record Kernel.current [] (start vaultLarge) ss
    covered runCfg (authorizedAt p.2 p.1 1) (p.2.fed.worlds 1).node vaultLarge
      Kernel.RegistrationCases.e1 = false :=
  covered_false_of_value_bound _ _ _ _ _ 100 rfl rfl (by decide) (by decide) (by decide) (by decide)

end Run

end BtcPolicy.Exhibits.Feasibility

namespace BtcPolicy.Exhibits.Recovery
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Recovery
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Sweep.Cases (vault honest4 start delivered armed)
open BtcPolicy.Settlement (confirmedAt)

/-! ### Recovery authority and the five classes

Research task `bps-uaer.18`. Every run below is a `Recovery.Execution` over `Kernel.current`, the
guard values as they stand and `Sweep.Cases`' federation: four honest nodes, keys 1 to 4, threshold 2,
outpoints 0 and 1 created by transaction 7. The lock is the default vault's. The instants are
hand-chosen; the runs are not. Custody is written in, never derived: that is the whole of what these
exhibits say about keys. -/

def lock : Nat := Timelock.defaultNSequence
def secs : Nat := 15552000

/-- Outpoint 50 is the refresh's output, outpoint 51 the next refresh's; 3 is the sweep fixture's
external deposit, and the rest come from funding transaction 7. -/
def creator : Package.Creator := fun o =>
  if o == 50 then 600 else if o == 51 then 601 else if o == 3 then 300 else 7

def rcfg : Cfg :=
  { sweep := { Sweep.Cases.cfg Coverage.current Coverage.currentExternal Package.current with creator := creator },
    t := 2, recKeys := [11, 12, 13], sealedLock := lock }

theorem lock_secs : lockSecs lock = secs := by decide

/-- Funding transaction 7 confirmed at height 3, whose parent's MTP is 1000. Height 9's MTP is a thousand
seconds on: both coins are young. -/
def young : Backend :=
  { vault with tip := ⟨9, 109⟩, heights := [(7, 3)], mtps := [(2, 1000), (3, 1100), (9, 2000)] }
/-- The same chain later, with the tip's MTP one second short of the lock. -/
def almost : Backend := { young with sequence := 2, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs - 1)], tip := ⟨9, 209⟩ }
/-- The tip's MTP exactly at the lock. -/
def ripe : Backend := { young with sequence := 3, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs)], tip := ⟨9, 309⟩ }
/-- `ripe` with a large third coin no Escape spends. -/
def ripeLarge : Backend := { ripe with confirmed := [(0, 40), (1, 60), (9, 1000)] }

/-- The Operator's Recovery spend of outpoint 0. -/
def rtx : Tx := { id := 900, inputs := [0], outflow := 0 }
def rspend : Spend := { tx := rtx, sequences := [lock], witness := Alerts.recoveryWitness }

/-- It confirms in block 10, whose parent is `ripe`'s tip. -/
def minedR : Backend :=
  { ripe with
    tip := ⟨10, 410⟩, sequence := 4, confirmed := [(1, 60)], mined := [(900, [0])],
    heights := [(900, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 600)] }
/-- A chain that shows it confirmed in a block whose parent's lock has not passed. -/
def earlyR : Backend :=
  { young with
    tip := ⟨10, 510⟩, sequence := 4, confirmed := [(1, 60)], mined := [(900, [0])],
    heights := [(900, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 2000), (10, 2600)] }
/-- A reorganization to a chain with no spend, on which funding transaction 7 confirmed at height 8. -/
def reorgYoung : Backend :=
  { ripe with
    tip := ⟨9, 609⟩, sequence := 5, heights := [(7, 8)],
    mtps := [(7, 1000 + secs - 5), (8, 1000 + secs - 2), (9, 1000 + secs)] }
/-- A reorganization that keeps the funding block and drops every spend. -/
def reorgBack : Backend := { ripe with tip := ⟨10, 710⟩, sequence := 5, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 700)] }
/-- A reorganization on which an external transaction spent outpoint 0. -/
def reorgSpent : Backend :=
  { ripe with
    tip := ⟨10, 810⟩, sequence := 5, confirmed := [(1, 60)], mined := [(777, [0])],
    heights := [(777, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 800)] }

def full : Holder := { keys := [11, 12, 13], descriptor := true, network := true }
def nobody : Holder := { keys := [], descriptor := false, network := false }

/-- The start: a fresh federation at instant `b`; the Operator holds all, the attacker nothing. -/
def st0 (b : Backend) : St := { sw := start b, op := full, att := nobody }

theorem st0_fresh (b : Backend) : Fresh honest4 (st0 b) := by
  have h : Federation.Fresh honest4 Federation.Cases.fed0 := by
    unfold Federation.Fresh
    decide
  exact ⟨⟨h, rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl⟩

abbrev base (ss : List Sweep.Step) : List BtcPolicy.Recovery.Step := ss.map .base

def runOf (b : Backend) (xs : List BtcPolicy.Recovery.Step) : Trace × St := record Kernel.current [] (st0 b) xs
def isLegal (b : Backend) (xs : List BtcPolicy.Recovery.Step) : Bool := legal rcfg Kernel.current honest4 [] (st0 b) xs
def failsOf (b : Backend) (xs : List BtcPolicy.Recovery.Step) (sc : Scenario) : List Failure :=
  failures rcfg (runOf b xs).2 (runOf b xs).1 honest4 sc
def canPublish (b : Backend) (xs : List BtcPolicy.Recovery.Step) (who : Party) (sp : Spend) : Bool :=
  admits rcfg Kernel.current honest4 (runOf b xs).2 (runOf b xs).1 (.publish who sp)

theorem execution_of (b : Backend) (xs : List BtcPolicy.Recovery.Step) (h : isLegal b xs = true) :
    Execution rcfg Kernel.current honest4 (runOf b xs).1 (runOf b xs).2 :=
  execution_of_legal (.init _ (st0_fresh b)) h

/-- The Normal-path question throughout: the hot spend over outpoint 0, user-signed. -/
def sc0 : Scenario :=
  { coin := 0, target := tx1, userSigs := [{ msg := sighash tx1 0, input := 0 }], hot := true }

/-- Nodes 1 and 2 armed, the Escape released and possessed at node 1, which reads this instant; nodes 3
and 4 took nothing, so a hot spend still has two open signers. -/
def swept (b : Backend) : List BtcPolicy.Recovery.Step := base (delivered ++ [.observe 1 b])

/-! #### One scenario per class, standing alone -/

/-- **Recovery not yet mature.** The Normal path has its signers, node 1 can assemble the Escape, the
Operator holds everything and nothing is out: all that fails is this coin's age. -/
@[req "CHN-4"]
theorem only_not_mature : isLegal young (swept young) = true ∧
    failsOf young (swept young) sc0 = [.notMature] := by
  decide

/-- **Missing custody capability.** The same run on the mature chain, the Operator two keys short. -/
@[req "OPS-33"]
theorem only_missing_custody :
    isLegal ripe (swept ripe ++ [.lose 11, .lose 12]) = true ∧
      failsOf ripe (swept ripe ++ [.lose 11, .lose 12]) sc0 = [.missingCustody] := by
  decide

/-- **Waiting for inclusion.** The same run with the Recovery spend published and not confirmed. -/
@[req "SEC-54"]
theorem only_awaiting :
    isLegal ripe (swept ripe ++ [.publish .operator rspend]) = true ∧
      failsOf ripe (swept ripe ++ [.publish .operator rspend]) sc0 = [.awaitingInclusion] := by
  decide

/-- **Unavailable fast exit.** The vault holds a coin the Escape leaves out, so it covers too little of
the read (`Exhibits.Sweep.armed_without_eligible_escape`). -/
@[req "DUR-24"]
theorem only_fast_unavailable :
    isLegal ripeLarge (swept ripeLarge) = true ∧
      failsOf ripeLarge (swept ripeLarge) sc0 = [.fastUnavailable] := by
  decide

/-- **Blocked Normal authority.** Nodes 1 and 2 are armed and nodes 3 and 4 dead: no signer remains for
the hot spend, while the Escape and Recovery both stand. -/
@[req "DUR-11"]
theorem only_normal_blocked :
    isLegal ripe (swept ripe ++ [.die 3, .die 4]) = true ∧
      failsOf ripe (swept ripe ++ [.die 3, .die 4]) sc0 = [.normalBlocked] := by
  decide

/-- The same class from a lost user key instead: nodes 3 and 4 are open and would be the quorum, and no
user signature exists. `SEC-54`: "Loss of `U` prevents fresh user signatures". -/
@[req "SEC-54"]
theorem normal_blocked_by_user_key :
    failsOf ripe (swept ripe) { sc0 with userSigs := [] } = [.normalBlocked] ∧
      normalOpen rcfg (runOf ripe (swept ripe)).2 honest4 sc0 = true := by
  decide

/-- **Not interchangeable.** Each class has a reachable scenario standing in it alone, so each pair of
classes is told apart by a reachable scenario. -/
@[req "SEC-54"]
theorem classes_stand_alone (f : Failure) :
    ∃ T st, Execution rcfg Kernel.current honest4 T st ∧ failures rcfg st T honest4 sc0 = [f] := by
  cases f with
  | normalBlocked => exact ⟨_, _, execution_of _ _ only_normal_blocked.1, only_normal_blocked.2⟩
  | fastUnavailable => exact ⟨_, _, execution_of _ _ only_fast_unavailable.1, only_fast_unavailable.2⟩
  | notMature => exact ⟨_, _, execution_of _ _ only_not_mature.1, only_not_mature.2⟩
  | missingCustody => exact ⟨_, _, execution_of _ _ only_missing_custody.1, only_missing_custody.2⟩
  | awaitingInclusion => exact ⟨_, _, execution_of _ _ only_awaiting.1, only_awaiting.2⟩

/-! #### Eligible, possible, included -/

/-- **A mature coin with custody held.** The Operator publishes at the lock, equality passing; it waits;
the chain confirms it in the next block; the coin stands in no class. `Recovery.included_origin` applies to
this run. -/
@[req "OPS-26"]
theorem mature_with_custody_included :
    let xs := [BtcPolicy.Recovery.Step.publish .operator rspend, .base (.chain minedR)]
    isLegal ripe xs = true ∧ eligible rcfg ripe rspend = true ∧
      confirmedAt (runOf ripe xs).2.sw.truth rtx = true ∧
      failsOf ripe [.publish .operator rspend] sc0 = [.fastUnavailable, .awaitingInclusion] ∧
      failsOf ripe xs sc0 = [] := by
  decide

/-- The theorem's premises on that run: it has an inhabitant. -/
@[req "OPS-26"]
theorem included_origin_inhabited :
    let xs := [BtcPolicy.Recovery.Step.publish .operator rspend, .base (.chain minedR)]
    includedOk rcfg (runOf ripe xs).2.sw.truth rspend = true ∧
      ∃ st₀, (st₀, BtcPolicy.Recovery.Step.publish .operator rspend) ∈ (runOf ripe xs).1 ∧
        eligible rcfg st₀.sw.truth rspend = true ∧ capable rcfg (st₀.holder .operator) = true := by
  intro xs
  exact included_origin (p := (.operator, rspend)) (execution_of ripe xs (by decide)) (by decide) (by decide)

/-- **Not yet mature, with everything else held.** One second short, the chain refuses every party; at
the lock it takes the Operator's. The same spend with the sequence that disables relative locks, or the
Normal branch's witness, is refused at the lock. -/
@[req "CHN-10"]
theorem before_maturity_refused :
    canPublish young [] .operator rspend = false ∧ canPublish almost [] .operator rspend = false ∧
      canPublish ripe [] .operator rspend = true ∧
      canPublish ripe [] .operator { rspend with sequences := [0xffffffff] } = false ∧
      canPublish ripe [] .operator { rspend with witness := Alerts.normalWitness } = false := by
  decide

/-- **Custody short, with the coin mature.** One key lost leaves two and Recovery stands. Two lost, or the
descriptor backup lost with all three keys held, and it does not. Two copies of one key count once. -/
@[req "OPS-23"]
theorem missing_custody_refused :
    canPublish ripe [.lose 11] .operator rspend = true ∧
      canPublish ripe [.lose 11, .lose 12] .operator rspend = false ∧
      canPublish ripe [.loseBackup] .operator rspend = false ∧
      capable rcfg { full with keys := [11, 11] } = false ∧
      capable rcfg { full with keys := [11, 99] } = false ∧
      capable rcfg { full with network := false } = false := by
  decide

/-- **`SEC-54` row 14's maturity half.** An attacker with two copied keys and the public backup can spend
no coin before its lock has passed, and can spend it, against an Operator holding everything, at the lock; the
chain then shows the attacker's spend. That this is theft, and who holds which key, is outside. -/
@[req "SEC-54"]
theorem two_keys_gate_on_maturity :
    let ks : List BtcPolicy.Recovery.Step := [.copy 11, .copy 12, .learnBackup]
    canPublish young ks .attacker rspend = false ∧ canPublish ripe ks .attacker rspend = true ∧
      canPublish ripe [.copy 11, .learnBackup] .attacker rspend = false ∧
      isLegal ripe (ks ++ [.publish .attacker rspend, .base (.chain minedR)]) = true ∧
      confirmedAt (runOf ripe (ks ++ [.publish .attacker rspend, .base (.chain minedR)])).2.sw.truth rtx = true := by
  decide

/-- A chain cannot show a published spend where its lock did not allow it: the move to that instant is
not admitted, and the move to the instant where it did allow is. -/
@[req "CHN-10"]
theorem early_inclusion_refused :
    admits rcfg Kernel.current honest4 (runOf ripe [.publish .operator rspend]).2
        (runOf ripe [.publish .operator rspend]).1 (.base (.chain earlyR)) = false ∧
      admits rcfg Kernel.current honest4 (runOf ripe [.publish .operator rspend]).2
        (runOf ripe [.publish .operator rspend]).1 (.base (.chain minedR)) = true := by
  decide

/-- A chain over slots: the coin mature at slots 0 and 1, the spend confirmed from slot 2 on, its input
spent there. -/
def chainAt (u : Nat) : Backend := if u < 2 then ripe else minedR

theorem chainAt_serves : Serves rcfg chainAt (fun u => u % 2 == 1) rspend := by
  intro u _ he
  have hu : u + 1 ≥ 2 := by
    by_cases h : u < 2
    · have : u % 2 = 1 := by simpa using ‹(fun u => u % 2 == 1) u = true›
      omega
    · omega
  simp only [chainAt, if_neg (Nat.not_lt.2 hu)]
  decide

theorem chainAt_enabled (u : Nat) :
    (eligible rcfg (chainAt u) rspend || confirmedAt (chainAt u) rspend.tx) = true := by
  unfold chainAt
  split <;> decide

/-- `Recovery.included_within` and `Recovery.included_eventually` have an inhabitant, on a chain where the
spend's input is spent once it confirms: service every other slot, so `bounded 1`, and confirmation by slot 2. -/
@[req "OPS-26"]
theorem inclusion_inhabited :
    (∃ u, 0 ≤ u ∧ u ≤ 0 + 1 + 1 ∧ confirmedAt (chainAt u) rspend.tx = true) ∧
      ∃ u, 0 ≤ u ∧ confirmedAt (chainAt u) rspend.tx = true := by
  have hb : (Progress.Profile.bounded 1).Holds (fun u => u % 2 == 1) := by
    intro t
    by_cases h : t % 2 = 1
    · exact ⟨t, Nat.le_refl _, by omega, by simp [h]⟩
    · exact ⟨t + 1, by omega, by omega, by simp; omega⟩
  exact ⟨included_within hb chainAt_serves fun u _ _ => chainAt_enabled u,
    included_eventually (Progress.bounded_eventual hb) chainAt_serves fun u _ => chainAt_enabled u⟩

/-! #### A coin's history is the chain's -/

/-- **Lockdown does not restart maturity.** On the young chain nodes 1 and 2 arm, and the deadline driver
latches both past `T`: the coin's age is what it was and the Operator's spend is refused. The chain alone
moves it to the lock, where the spend stands, exactly as on the run with no duress and no latch at all. -/
@[req "CHN-4"]
theorem lockdown_does_not_restart :
    let lat : List BtcPolicy.Recovery.Step :=
      swept young ++ [.latch 1 (envAt 1000 1000), .latch 2 (envAt 1000 1000)]
    let lat' := lat ++ [.base (.chain ripe)]
    isLegal young lat' = true ∧
      (runOf young lat).2.latched = [2, 1] ∧
      (lockAge (clock (runOf young lat).2.sw.truth) 7 = lockAge (clock young) 7) ∧
      canPublish young lat .operator rspend = false ∧
      canPublish young lat' .operator rspend = true ∧
      canPublish ripe [] .operator rspend = true ∧
      lockAge (clock (runOf young lat').2.sw.truth) 7 = lockAge (clock (runOf ripe []).2.sw.truth) 7 := by
  decide

/-- A latched node registers nothing new, and an unarmed node's driver has nothing to latch. -/
@[req "DUR-7"]
theorem latched_takes_no_accept :
    let lat : List BtcPolicy.Recovery.Step := swept young ++ [.latch 1 (envAt 1000 1000)]
    admits rcfg Kernel.current honest4 (runOf young lat).2 (runOf young lat).1
        (.base (Sweep.Cases.duressAt 1 30 RegistrationCases.c3 RegistrationCases.e3)) = false ∧
      admits rcfg Kernel.current honest4 (runOf young lat).2 (runOf young lat).1
        (.latch 3 (envAt 1000 1000)) = false := by
  decide

/-- The refresh: outpoint 0 into outpoint 50. -/
def rf : Tx := { id := 600, inputs := [0], outflow := 0 }
def afterRefresh : Backend := confirmRefresh ripe rf [(50, 39)] 10 910 (1000 + secs + 600)
/-- The successor's chain a month on, and at its own lock. -/
def month : Backend :=
  { afterRefresh with
    tip := ⟨11, 911⟩, sequence := afterRefresh.sequence + 1,
    mtps := (11, 1000 + secs + 600 + 2592000) :: afterRefresh.mtps }
def succRipe : Backend :=
  { afterRefresh with
    tip := ⟨12, 912⟩, sequence := afterRefresh.sequence + 2,
    mtps := (12, 1000 + secs + secs) :: afterRefresh.mtps }
/-- A Recovery spend of the successor. -/
def rspend50 : Spend := { rspend with tx := { rtx with id := 901, inputs := [50] } }

/-- **A confirmed refresh's outputs start their own count.** The parent is mature; the refresh spends it,
so nothing can reach the parent any more. The successor reads its own block's parent: young at once and a
month on, mature only at its own lock. `SPN-46`'s own age, which reads the confirming block, admits the
parent's refresh at thirty days, and admits the successor's a month on, before its lock: so a holder who
keeps refreshing keeps a coin young, the part of `SEC-54` row 14 that says "only refresh keeps a coin
young". -/
@[req "CHN-4"]
theorem refresh_starts_own_count :
    matured rcfg ripe 0 = true ∧ matured rcfg afterRefresh 0 = false ∧
      matured rcfg afterRefresh 50 = false ∧ matured rcfg month 50 = false ∧
      matured rcfg succRipe 50 = true ∧
      RefreshAge.admit .chainMtp 2592000 (clock ripe) [] 0 7 = true ∧
      RefreshAge.admit .chainMtp 2592000 (clock month) [] 0 600 = true ∧
      isLegal ripe [.base (.chain afterRefresh), .base (.chain month)] = true ∧
      canPublish ripe [.base (.chain afterRefresh), .base (.chain month)] .operator rspend50 = false ∧
      canPublish ripe [.base (.chain afterRefresh), .base (.chain succRipe)] .operator rspend50 = true := by
  decide

/-- `Recovery.successor_own_history` on that refresh: it has an inhabitant. -/
@[req "CHN-4"]
theorem successor_own_history_inhabited :
    lockAge (clock afterRefresh) 600 = some 600 ∧ ¬ lockSecs rcfg.sealedLock ≤ 600 ∧
      matured rcfg afterRefresh 50 = false :=
  ⟨(successor_own_history rcfg ripe rf [(50, 39)] 10 910 (1000 + secs + 600) (by decide) (o := 50)
      (by decide) (by decide)).1.trans (by decide), by decide, by decide⟩

/-- **A reorganization can make a mature coin young.** The funding transaction re-confirms at height 8,
and the spend the chain allowed a moment ago is refused, with the same keys. -/
@[req "CHN-4"]
theorem reorg_makes_coin_young :
    isLegal ripe [.base (.chain reorgYoung)] = true ∧ matured rcfg ripe 0 = true ∧
      matured rcfg reorgYoung 0 = false ∧
      canPublish ripe [] .operator rspend = true ∧
      canPublish ripe [.base (.chain reorgYoung)] .operator rspend = false ∧
      failsOf ripe (base [.chain reorgYoung]) { sc0 with userSigs := sc0.userSigs } =
        [.fastUnavailable, .notMature] := by
  decide

/-- **A reorganization can undo an inclusion.** The spend confirmed; a reorganization drops it: the coin is
unspent again, and the spend is waiting again, with no step of any party's. -/
@[req "SEC-54"]
theorem reorg_undoes_inclusion :
    let xs : List BtcPolicy.Recovery.Step :=
      [.publish .operator rspend, .base (.chain minedR)]
    let ys := xs ++ [.base (.chain reorgBack)]
    isLegal ripe ys = true ∧ failsOf ripe xs sc0 = [] ∧
      confirmedAt reorgBack rtx = false ∧ matured rcfg reorgBack 0 = true ∧
      (failsOf ripe ys sc0).contains .awaitingInclusion = true := by
  decide

/-- **A reorganization can spend the coin.** On the other chain an external transaction spent it, and a
Recovery spend of it is refused. The coin has moved and stands in no class. -/
@[req "CHN-4"]
theorem reorg_spends_coin :
    isLegal ripe [.base (.chain reorgSpent)] = true ∧
      canPublish ripe [.base (.chain reorgSpent)] .operator rspend = false ∧
      failsOf ripe (base [.chain reorgSpent]) sc0 = [] := by
  decide

/-! #### Death, loss and what stays -/

/-- **`SEC-54` rows L3, L7 and L8 at one mature coin.** Every node is dead: the Normal path and the fast exit
are gone and Recovery stands. Then the Operator also loses two keys, or the descriptor backup, and nothing
remains: three classes at once, each for its own reason. -/
@[req "SEC-54"]
theorem dead_federation :
    let allDead : List BtcPolicy.Recovery.Step := [.die 1, .die 2, .die 3, .die 4]
    isLegal ripe allDead = true ∧ failsOf ripe allDead sc0 = [.normalBlocked, .fastUnavailable] ∧
      canPublish ripe allDead .operator rspend = true ∧
      failsOf ripe (allDead ++ [.lose 11, .lose 12]) sc0 =
        [.normalBlocked, .fastUnavailable, .missingCustody] ∧
      canPublish ripe (allDead ++ [.lose 11, .lose 12]) .operator rspend = false ∧
      failsOf ripe (allDead ++ [.loseBackup]) sc0 = [.normalBlocked, .fastUnavailable, .missingCustody] ∧
      canPublish ripe (allDead ++ [.loseBackup]) .operator rspend = false := by
  decide

/-- **Death stops a later copy, not an earlier one.** A dead node's key cannot be extracted; one copied
before it died stays copied, and its copy can still sign. -/
@[req "DUR-18"]
theorem copy_before_death_stays :
    let xs : List BtcPolicy.Recovery.Step := [.die 1]
    let ys : List BtcPolicy.Recovery.Step := [.base (.fed (.extract 1)), .die 1]
    admits rcfg Kernel.current honest4 (runOf ripe xs).2 (runOf ripe xs).1 (.base (.fed (.extract 1))) = false ∧
      isLegal ripe ys = true ∧ (runOf ripe ys).2.sw.fed.extracted.contains 1 = true ∧
      admits rcfg Kernel.current honest4 (runOf ripe ys).2 (runOf ripe ys).1
        (.base (.fed (.forge (Sweep.Cases.part RegistrationCases.c1 1 0)))) = true := by
  decide

/-- **What left a node stays out.** The Escape is sent, the sender dies: the submission still stands, and
another node's Escape need not. An external transaction confirming over the Escape's second input conflicts
it, on this instant's chain, while outpoint 0 is unspent. -/
def conflictX : Backend :=
  { ripe with
    tip := ⟨10, 1010⟩, sequence := 6, confirmed := [(0, 40)], mined := [(777, [1])],
    heights := [(777, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 800)] }

@[req "SEC-54"]
theorem submission_outlives_sender :
    let sentS := swept ripe ++ base [Sweep.Cases.assemble 1 RegistrationCases.e1.id, Sweep.Cases.sendAt 1 RegistrationCases.e1.id]
    isLegal ripe (sentS ++ [.die 1, .die 2, .base (.chain conflictX)]) = true ∧
      failsOf ripe sentS sc0 = [.awaitingInclusion] ∧
      failsOf ripe (sentS ++ [.die 1, .die 2]) sc0 = [.awaitingInclusion] ∧
      failsOf ripe (sentS ++ [.die 1, .die 2, .base (.chain conflictX)]) sc0 = [.fastUnavailable] := by
  decide

/-- **A dead node's history stays.** Node 1 releases and dies. It takes no later step, and its partial stays
in the inventory; it is counted as a record although the node can sign nothing more. -/
@[req "DUR-18"]
theorem death_keeps_record :
    let xs := base armed ++ [.die 1]
    isLegal ripe xs = true ∧
      admits rcfg Kernel.current honest4 (runOf ripe xs).2 (runOf ripe xs).1
        (.base (.fed (.process 1 envFire .firePass))) = false ∧
      (runOf ripe xs).2.sw.fed.parts.contains (Sweep.Cases.part RegistrationCases.e1 1 0) = true ∧
      openSigner (runOf ripe xs).2 honest4 RegistrationCases.e1.tx false 1 = false := by
  decide

end BtcPolicy.Exhibits.Recovery
