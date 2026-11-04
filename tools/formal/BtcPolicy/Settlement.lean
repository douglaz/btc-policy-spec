import BtcPolicy.Sweep
import BtcPolicy.Ledger
/-! Chain observation in the composed sweep: mempool sightings, eviction, confirmation and
reorganization over the one backend world of `BtcPolicy.Sweep`, with the kernel's chain view read
from it. Nodes still move by `Kernel.step` and nothing else, and the backend still moves by
`Sweep.Step.chain` to any instant at all.

**The tie.** `Sweep.Execution` hands each kernel step a chain view (`Kernel.ChainView.seen`, which
`Kernel.settle` reads) that nothing constrains. `Settlement.Execution` is the same execution with one
more guard, `Settlement.readOk`: every transaction in the view a node's step is handed is shown by
that node's latest observation, resident in its mempool or confirmed there (`Settlement.shows`). An
observation is an instant the truth has actually been (`Settlement.observed_was_truth`), so a node
acts on no settlement the chain never showed (`Settlement.settlement_shown`). The guard is one way:
a node may be handed less than its observation shows, so a settlement can go unprocessed, and under
`Kernel.Defeat.mempoolResidency`, which reads the view, an omitted transaction counts as absent.
`Settlement.to_sweep` forgets the guard, so every result of
`BtcPolicy.Sweep` holds here.

**Reorganization and eviction.** A reorg and an eviction are `Sweep.Step.chain` moves to an instant
that no longer shows a transaction an earlier one did. No step reads such a move except through a
later observation, and no kernel event undoes a settlement. Whatever the chain did between,
`Settlement.exposure_persists` keeps every partial in the federation's inventory, every extracted
key and every exposure row of every node at an earlier state, on every sweep execution, and
`Settlement.defeat_persists` keeps a defeat under the premises its docstring states.

**Mempool and confirmation.** `SPN-33`'s settlement reads presence alone, "seen in the mempool or
confirmed" (`Settlement.settle_reads_seen_only`). Under the ledger's current settlement and
release values no settlement refunds a reservation, mempool-only or confirmed
(`Settlement.settlement_refunds_nothing`). Where the
two do differ is in what `Sweep` reads at an assembly: a confirmed output is in `WTC-10`'s snapshot,
and a resident deposit's output is an unconfirmed external one. The exhibits in
`BtcPolicy.Exhibits.Settlement` run each case.

**Not modelled.** Nothing makes a transaction confirm, stay confirmed or reach a mempool: there is no
chain-progress or inclusion premise because no theorem here concludes a confirmation. The kernel's
`Kernel.ChainView.mtp` stays untied. An instant's confirmed transactions, its confirmed outputs and
its resident ones are independent fields, so an instant need not be a consistent chain state. The
ledger is not part of the composed state: `Settlement.settlement_refunds_nothing` runs
`Ledger.sysStep` on the settling node's world with any ledger. A candidate whose id has left the
registry is outside `Settlement.defeat_persists`: the kernel can register that id again at a later
acceptance. -/

namespace BtcPolicy.Settlement
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Federation
open BtcPolicy.Sweep (Backend State Cfg)

/-! ## What an instant shows -/

/-- The instant holds this transaction, its id and ordered inputs, resident in its mempool. -/
def resident (b : Backend) (tx : Tx) : Bool := b.mempool.contains (tx.id, tx.inputs)

/-- The instant holds it confirmed. -/
def confirmedAt (b : Backend) (tx : Tx) : Bool := b.mined.contains (tx.id, tx.inputs)

/-- `SPN-33`'s "seen in the mempool or confirmed", at one instant. -/
@[req "SPN-33"]
def shows (b : Backend) (tx : Tx) : Bool := resident b tx || confirmedAt b tx

/-- The chain view a kernel step at node `i` may be handed in state `st`: every transaction in it is
shown by the node's latest observation. No observation, an empty view. -/
def viewOk (st : State) (i : Nat) (env : Env) : Bool :=
  env.chain.seen.all fun tx => match st.obs i with
    | some b => shows b tx
    | none => false

/-- The guard on a federation step that runs a kernel step: its chain view is read off the acting
node's latest observation. -/
def readOk (st : State) : Sweep.Step → Bool
  | .fed s => match actor s with
    | some (i, env, _) => viewOk st i env
    | none => true
  | _ => true

/-- A sweep step `Sweep.admits` admits and whose chain view the acting node observed. -/
def admits (cfg : Cfg) (honest : List Nat) (st : State) (T : Sweep.Trace) (s : Sweep.Step) : Bool :=
  Sweep.admits cfg honest st T s && readOk st s

/-- A reachable composed execution whose kernel steps read the chain through observation. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Sweep.Trace → State → Prop
  | init (st : State) (h : Sweep.Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Sweep.Step) (ha : admits cfg honest st T s = true) :
      Execution cfg r honest T st → Execution cfg r honest ((st, s) :: T) (Sweep.apply r st s)

/-- Forgetting the tie leaves a sweep execution. -/
theorem to_sweep {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : State}
    (hx : Execution cfg r honest T st) : Sweep.Execution cfg r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | next s ha _ ih =>
    simp only [admits, Bool.and_eq_true] at ha
    exact .next s ha.1 ih

/-! ## Observation -/

/-- Every observation a node holds is an instant the truth has been, now or earlier: observation
delay, never an invented world. -/
theorem observed_was_truth {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : State} (hx : Sweep.Execution cfg r honest T st) {i : Nat} {b : Backend}
    (hb : st.obs i = some b) : b = st.truth ∨ b ∈ st.past := by
  induction hx with
  | init st h => rw [h.2.2 i] at hb; cases hb
  | next s ha _ ih =>
    cases s with
    | fed s =>
      simp only [Sweep.apply] at hb ⊢
      cases hs : Sweep.assembly s with
      | none => rw [hs] at hb; exact ih hb
      | some p =>
        obtain ⟨j, _⟩ := p
        rw [hs] at hb
        by_cases hij : i = j
        · simp [hij] at hb
        · simp only [hij, ↓reduceIte] at hb
          exact ih hb
    | chain b' =>
      simp only [Sweep.apply] at hb ⊢
      rcases ih hb with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · exact .inr (List.mem_cons_of_mem _ h)
    | observe j b' =>
      simp only [Sweep.apply] at hb ⊢
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, Option.some.injEq] at hb
        subst hb
        simp only [Sweep.admits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
          List.contains_iff_mem] at ha
        exact ha.2
      · simp only [hij, ↓reduceIte] at hb
        exact ih hb

/-- `SPN-33`'s settlement reads presence alone: two chain views that agree on whether they show the
transaction leave the same node, whether one showed it resident and the other confirmed. -/
@[req "SPN-33"]
theorem settle_reads_seen_only (env₁ env₂ : Env) (n : Node) (tx : Tx)
    (h : env₁.chain.seen.contains tx = env₂.chain.seen.contains tx) :
    settle env₁ n tx = settle env₂ n tx := by
  simp only [settle, h]

theorem seen_of_settle_changes {env : Env} {n : Node} {tx : Tx} (h : settle env n tx ≠ n) :
    env.chain.seen.contains tx = true := by
  cases hs : env.chain.seen.contains tx with
  | true => rfl
  | false =>
    have : settle env n tx = n := by simp only [settle, hs, Bool.not_false, ↓reduceIte]
    exact absurd this h

/-- A settlement a node acts on was shown to it: if its settle step changes its node, its latest
observation, an instant the truth has been, showed the transaction resident or confirmed. -/
@[req "SPN-33"]
theorem settlement_shown {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {tx : Tx}
    (ha : admits cfg honest st T (.fed (.process i env (.settle tx))) = true)
    (hch : settle env (st.fed.worlds i).node tx ≠ (st.fed.worlds i).node) :
    ∃ b, st.obs i = some b ∧ shows b tx = true ∧ (b = st.truth ∨ b ∈ st.past) := by
  have hseen := List.contains_iff_mem.1 (seen_of_settle_changes hch)
  simp only [admits, Bool.and_eq_true, readOk, actor, viewOk, List.all_eq_true] at ha
  have hv := ha.2 tx hseen
  cases hb : st.obs i with
  | none => rw [hb] at hv; cases hv
  | some b =>
    rw [hb] at hv
    exact ⟨b, rfl, hv, observed_was_truth (to_sweep hx) hb⟩

/-- At every admitted settle step, under the ledger's current settlement and release values: the
ledger's composed step on
the settling node's world moves that world exactly as the sweep does, and keeps every row of any
ledger with its commitment, amount, reservation time and expiry, whether the instant showed the
transaction resident or confirmed. `SPN-33`: "Mempool-only settlement MUST NOT refund a
reservation", and "a conflicting confirmation refunds nothing at the confirmation". A settlement that
changes the node was shown to it (`Settlement.settlement_shown`). -/
@[req "SPN-33"]
theorem settlement_refunds_nothing {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : State} (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {tx : Tx}
    (ha : admits cfg honest st T (.fed (.process i env (.settle tx))) = true)
    (g : Ledger.Guards) (hs : g.settlement = .retainOnMempool)
    (hrel : g.release = .acceptedAdmission) (lcfg : Ledger.Config) (l : Ledger.Ledger) :
    (Ledger.sysStep g lcfg r env ⟨st.fed.worlds i, l⟩ (.settle tx)).1.world =
        (step r env (st.fed.worlds i) (.settle tx)).1 ∧
      (∀ row ∈ l, ∃ row' ∈ (Ledger.sysStep g lcfg r env ⟨st.fed.worlds i, l⟩
          (.settle tx)).1.led,
        row'.cid = row.cid ∧ row'.amount = row.amount ∧ row'.reservedAt = row.reservedAt ∧
          row'.expiry = row.expiry) ∧
      (settle env (st.fed.worlds i).node tx ≠ (st.fed.worlds i).node →
        ∃ b, st.obs i = some b ∧ shows b tx = true ∧ (b = st.truth ∨ b ∈ st.past)) := by
  refine ⟨by simp [Ledger.sysStep, Ledger.refusedByBudget], fun row hrow => ?_,
    settlement_shown hx ha⟩
  exact Ledger.retained_outside_prune_and_admission g hs hrel lcfg r env _ _
    (by simp) (by simp [Ledger.admitted]) row hrow

/-! ## What a chain move cannot undo -/

/-- One sweep step keeps the federation's partial inventory, its extracted keys and every node's
exposure rows. -/
theorem step_keeps_exposure (r : Rules) (st : State) (s : Sweep.Step) :
    (∀ x ∈ st.fed.parts, x ∈ (Sweep.apply r st s).fed.parts) ∧
      (∀ j ∈ st.fed.extracted, j ∈ (Sweep.apply r st s).fed.extracted) ∧
      ∀ i, ∀ x ∈ (st.fed.worlds i).exposure, x ∈ ((Sweep.apply r st s).fed.worlds i).exposure := by
  cases s with
  | fed s =>
    refine ⟨fun x hx => parts_grows r _ s hx, fun j hj => extracted_grows r _ s hj,
      fun i x hx => ?_⟩
    simp only [Sweep.apply]
    cases hact : actor s with
    | none => rw [apply_no_actor r _ s hact i]; exact hx
    | some a =>
      obtain ⟨j, env, e⟩ := a
      rw [apply_of_actor r _ s hact i]
      split
      · rename_i hij
        subst hij
        exact exposure_monotone r env _ e x hx
      · exact hx
  | chain b => exact ⟨fun x hx => hx, fun j hj => hj, fun i x hx => hx⟩
  | observe j b => exact ⟨fun x hx => hx, fun j hj => hj, fun i x hx => hx⟩

/-- Historical exposure survives every chain move, a reorg or an eviction included: what any earlier
state of a sweep execution held in the partial inventory, the extracted set or any node's exposure
rows, the final state holds. -/
@[req "POL-18"]
theorem exposure_persists {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : State} (hx : Sweep.Execution cfg r honest T st) {st₀ : State} {s : Sweep.Step}
    (hm : (st₀, s) ∈ T) :
    (∀ x ∈ st₀.fed.parts, x ∈ st.fed.parts) ∧ (∀ j ∈ st₀.fed.extracted, j ∈ st.fed.extracted) ∧
      ∀ i, ∀ x ∈ (st₀.fed.worlds i).exposure, x ∈ (st.fed.worlds i).exposure := by
  induction hx with
  | init st h => cases hm
  | @next T st' s' _ _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact step_keeps_exposure r _ _
    · obtain ⟨h1, h2, h3⟩ := ih hm
      obtain ⟨k1, k2, k3⟩ := step_keeps_exposure r st' s'
      exact ⟨fun x hx => k1 x (h1 x hx), fun j hj => k2 j (h2 j hj),
        fun i x hx => k3 i x (h3 i x hx)⟩

/-- One sweep step from a reachable state keeps a resident terminal id terminal at an honest node:
`Kernel.terminal_sticky` at the acting node, and no change anywhere else. -/
theorem step_keeps_terminal {cfg : Cfg} {r : Rules} (hr : r.registration = .preserve)
    {honest : List Nat} {T : Sweep.Trace} {st : State} (hx : Sweep.Execution cfg r honest T st)
    {i : Nat} (hi : i ∈ honest) (s : Sweep.Step) {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands)
    (ht : c.terminal = true) :
    ∀ c' ∈ ((Sweep.apply r st s).fed.worlds i).node.cands, c'.id = c.id → c'.terminal = true := by
  have hw : Reachable r (st.fed.worlds i) :=
    (project_execution (Sweep.fed_execution hx) hi).reachable
  have same (c' : Cand) (hc' : c' ∈ (st.fed.worlds i).node.cands) (hid : c'.id = c.id) :
      c'.terminal = true := by
    rw [eq_of_mem_ids_nodup (ids_nodup hr hw) hc' hc hid]; exact ht
  intro c' hc' hid
  cases s with
  | fed s =>
    simp only [Sweep.apply] at hc'
    cases hact : actor s with
    | none => rw [apply_no_actor r _ s hact i] at hc'; exact same c' hc' hid
    | some a =>
      obtain ⟨j, env, e⟩ := a
      rw [apply_of_actor r _ s hact i] at hc'
      split at hc'
      · rename_i hij
        subst hij
        exact terminal_sticky r hr env _ hw e c hc ht c' hc' hid
      · exact same c' hc' hid
  | chain b => exact same c' hc' hid
  | observe j b => exact same c' hc' hid

/-- A defeat survives every chain move, a reorg or an eviction of the defeating transaction
included. Under `SPN-33`'s terminal flag and repaired registration: a candidate terminal at honest
node `i` in an earlier state `st₀` of a sweep execution is terminal, and never due in any
environment, at the final state, provided its id stayed resident at node `i` in every state between.
`SPN-33`: "a hot spend a claw-back has defeated is not finalized once its Hold has matured even if the
claw-back is later evicted". -/
@[req "SPN-33"]
theorem defeat_persists {cfg : Cfg} {r : Rules} (hr : r.registration = .preserve)
    (hd : r.defeat = .terminalFlag) {honest : List Nat} {T : Sweep.Trace} {st : State}
    (hx : Sweep.Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest)
    {T₁ T₂ : Sweep.Trace} {st₀ : State} {s : Sweep.Step} (hT : T = T₂ ++ (st₀, s) :: T₁) {c : Cand}
    (hres : ∀ p ∈ T₂, ∃ c' ∈ (p.1.fed.worlds i).node.cands, c'.id = c.id)
    (hc : c ∈ (st₀.fed.worlds i).node.cands) (ht : c.terminal = true) :
    ∀ c' ∈ (st.fed.worlds i).node.cands, c'.id = c.id →
      c'.terminal = true ∧ ∀ env, due r env (st.fed.worlds i).node c' = false := by
  suffices h : ∀ c' ∈ (st.fed.worlds i).node.cands, c'.id = c.id → c'.terminal = true from
    fun c' hc' hid => ⟨h c' hc' hid, fun env => terminal_never_due r hd env _ c' (h c' hc' hid)⟩
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st' s' _ hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hT
      exact step_keeps_terminal hr hx' hi _ hc ht
    | cons p T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      have hprev := ih hT fun q hq => hres q (List.mem_cons_of_mem _ hq)
      obtain ⟨d, hd', hdid⟩ := hres (st', s') List.mem_cons_self
      exact fun c' hc' hid =>
        step_keeps_terminal hr hx' hi s' hd' (hprev d hd' hdid) c' hc' (hid.trans hdid.symm)

/-! ## Running a schedule -/

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Sweep.Trace → State → List Sweep.Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg honest st T s && legal cfg r honest ((st, s) :: T) (Sweep.apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace}
    {st : State} (hx : Execution cfg r honest T st) {ss : List Sweep.Step}
    (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (Sweep.record r T st ss).1 (Sweep.record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

/-! ## Fixtures -/

namespace Cases
open BtcPolicy.Kernel.RegistrationCases
open BtcPolicy.Sweep.Cases (vault)

/-- Nodes 1 and 2 accept `(c1, e1)` with no duress, node 2 relays, and node 1 takes the receipt: its
hot spend over outpoint 0 has its quorum and fires at wall 100. -/
def ready : List Sweep.Step :=
  [.fed (Federation.Cases.acceptAt 1), .fed (Federation.Cases.acceptAt 2), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩)]

def settleAt (i : Nat) (env : Env) (tx : Tx) : Sweep.Step := .fed (.process i env (.settle tx))
def fireAt (i : Nat) (env : Env) : Sweep.Step := .fed (.process i env .firePass)

/-- The claw-back over outpoint 0 resident; then gone, the vault as before. -/
def clawResident : Backend := { vault with sequence := 2, mempool := [(claw.id, claw.inputs)] }
def evicted : Backend := { vault with sequence := 3 }

/-- The claw-back confirmed at height 6; then a reorganization to another block at height 6 that
holds nothing, outpoint 0 unspent again. -/
def clawMined : Backend :=
  { vault with tip := ⟨6, 106⟩, sequence := 2, confirmed := [(1, 60)], mined := [(claw.id, claw.inputs)] }
def reorged : Backend := { vault with tip := ⟨6, 206⟩, sequence := 3 }

/-- The hot spend's own transaction confirmed at height 6, and the same reorganization. -/
def spendMined : Backend :=
  { vault with tip := ⟨6, 106⟩, sequence := 2, confirmed := [(1, 60)], mined := [(tx1.id, tx1.inputs)] }
def envSpend : Env := envAt 130 70 [tx1]
def envAfter : Env := envAt 140 80

/-- An external transaction, 777, spending outpoint 0, confirmed at height 6. -/
def spendExternal : Tx := { id := 777, inputs := [0], outflow := 0 }
def externalMined : Backend :=
  { vault with
    tip := ⟨6, 106⟩, sequence := 2, confirmed := [(1, 60)],
    mined := [(spendExternal.id, spendExternal.inputs)] }
def envExternal : Env := envAt 120 60 [spendExternal]

/-- An external deposit, transaction 300 creating outpoint 3 worth 100, resident; then confirmed. -/
def depositResident : Backend :=
  { vault with sequence := 2, mempool := [(300, [99])], pending := [(300, (3, 100))] }
def depositMined : Backend :=
  { vault with
    tip := ⟨6, 106⟩, sequence := 3, confirmed := [(0, 40), (1, 60), (3, 100)],
    mined := [(300, [99])] }

/-- The claw-back becomes resident, node 1 reads it and settles it, and a fire pass reads the same
view; then the claw-back is evicted and node 1 reads the vault without it. -/
def mempoolThenEvicted : List Sweep.Step :=
  ready ++ [.chain clawResident, .observe 1 clawResident, settleAt 1 envClaw claw, fireAt 1 envClaw,
    .chain evicted, .observe 1 evicted]

/-- The claw-back confirms, node 1 reads it and settles it; a reorganization drops it, and node 1
reads the new tip. -/
def minedThenReorged : List Sweep.Step :=
  ready ++ [.chain clawMined, .observe 1 clawMined, settleAt 1 envClaw claw, .chain reorged,
    .observe 1 reorged]

/-- Node 1 releases its hot spend; the spend confirms and node 1 settles it; a reorganization drops
it, and node 1 reads the new tip. -/
def releasedThenReorged : List Sweep.Step :=
  ready ++ [fireAt 1 envFire, .chain spendMined, .observe 1 spendMined, settleAt 1 envSpend tx1,
    .chain reorged, .observe 1 reorged]

/-- After the duress release and delivery of `Sweep.Cases.delivered`, the external spend confirms and
node 1 reads it. -/
def externalConfirmed : List Sweep.Step :=
  Sweep.Cases.delivered ++ [.chain externalMined, .observe 1 externalMined]

/-- After the same delivery, node 1 reads the deposit resident; it confirms and node 1 reads again. -/
def depositSeen : List Sweep.Step :=
  Sweep.Cases.delivered ++ [.chain depositResident, .observe 1 depositResident]
def depositConfirmed : List Sweep.Step := depositSeen ++ [.chain depositMined, .observe 1 depositMined]

end Cases

end BtcPolicy.Settlement
