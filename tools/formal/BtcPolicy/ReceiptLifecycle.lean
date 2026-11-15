import BtcPolicy.Lifecycle
import BtcPolicy.Retained
import BtcPolicy.ReceiptExpiry
import BtcPolicy.VariantSilence
/-! The expiry-aware receipt on the lifecycle run (`NCH-24`, `NCH-25`, `SPN-41`, `POL-18`, `DUR-28`, `DUR-29`,
`DUR-31`), as `docs/research/receipt-lifecycle-contract.md` fixes it. A layer beside the existing definitions: no
definition or theorem statement changes, and no kernel event is added.

**The receipt step.** `ReceiptLifecycle.xvapply` is a step of `VariantSilence.VFed` (a ledgered federation, the honest
envelopes sent so far and each node's kept records): `VariantSilence.vapply` with `ReceiptExpiry.xapply` in place of
`FedSilence.lapply`, and with two changes to the store (`ReceiptLifecycle.xstore`). At a delivery the receiver's lookup
evicts on (`ReceiptExpiry.evictsAt`), nothing arrives; at a step after which its acting node holds more records under
an id than before (`ReceiptLifecycle.bornAt`, the count `Lifecycle.births` compares), the node's kept records under
that id are dropped. Off an evicting delivery and off a birth under an id already resident at the acting node, and
with every kept record resident (`ReceiptLifecycle.Resident`, which every run keeps:
`ReceiptLifecycle.resident_inv`), the step is `VariantSilence.vapply` (`ReceiptLifecycle.xvapply_eq`).

**The layer.** Its state (`ReceiptLifecycle.State`) is a `Lifecycle.State` with each node's Hot ledger, the envelopes
and the kept records; the receipt's federation is the lifecycle state's. Its steps are `RungAssembly.Step`, each with
a label. At a federation step the federation, the ledgers, the envelopes and the store are the receipt step's, and
every other field is `Lifecycle.apply`'s on the step with each acceptance mapped through `FedSilence.kernelStep`
(`ReceiptLifecycle.mapStep`); off an evicting delivery the whole lifecycle state is `Lifecycle.apply`'s on the mapped
step (`ReceiptLifecycle.apply_ls`). Admission (`ReceiptLifecycle.admits`) is `Lifecycle.admits` on the mapped step with
one substitution: the assembly guard reads the layer's possession (`ReceiptLifecycle.heldAt`, `VariantSilence.vheld`'s
form), so `ClassAssembly.finalAt`, `ClassAssembly.candOk`, `ClassAssembly.guard` and `ClassAssembly.assembleOk` are
restated beside, each with that possession. A delivery's label is admissible as `VariantSilence.vlabelOk` has it.

**What is proved.** On the subdomain where no delivery evicts and no step births under an id resident at its acting
node (`ReceiptLifecycle.Quiet`), forgetting the ledgers, envelopes and store leaves a `Lifecycle.Execution`, and the
kept records are `VariantReceipt.kept` of the labelled history (`ReceiptLifecycle.to_lifecycle`). The federation and
ledger part of every run is `ReceiptExpiry.xrun` over its federation steps, each admitted (`ReceiptLifecycle.to_xrun`),
and at a delivery the receiver's node and ledger are `ReceiptExpiry.sysRecv`'s (`ReceiptLifecycle.deliver_sys`). The
history is kept (`ReceiptLifecycle.history_kept`), relays included (`ReceiptLifecycle.relays_kept`). Every rung send
is on a permit earned at an earlier admitted assembly with no step since that ended it, a birth under the id at the node included
(`ReceiptLifecycle.permit_origin`, `ReceiptLifecycle.submitted_origin`, `ReceiptLifecycle.keeps_unborn`); a delivery,
evicting or not, ends no permit (`ReceiptLifecycle.deliver_keeps_permits`); under `Registration.preserve` an eviction
leaves no record under the id, and no send under it is admitted until a birth (`ReceiptLifecycle.no_send_until_birth`),
which ends the old permits (`ReceiptLifecycle.born_ends_permits`). A kept record came from a live lookup whose store
test passed, with no birth since (`ReceiptLifecycle.kept_origin`). A rung's assembly is the finalization over the
layer's possession (`ReceiptLifecycle.assemble_sound`, `ReceiptLifecycle.guard_sound`), and the retained lifetime holds
on the layer (`ReceiptLifecycle.lifetime_mono`). The delivery's observation carries the answer
(`ReceiptLifecycle.dobs_answer`) and, on a live lookup only, the store's decisions (`ReceiptLifecycle.dobs_live`).

**Premises.** The Hot ledger's results (`ReceiptExpiry.refund_only_permitted`, `ReceiptExpiry.exposed_kept`) are used
with their own premises (`Ledger.Release.acceptedAdmission`, and `Ledger.Refund.onCollection` for the first). Wallet
equality, signer equals sender, the sighash type and signature verification are inside the admission boundary of
`Federation.admits` and not modelled. No projection to `RungAssembly.Execution` that keeps rung steps is claimed, nor
one to `ClassAssembly.Execution` off the agreement subdomain. No SILENCE theorem is stated here. -/

namespace BtcPolicy.ReceiptLifecycle
open BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence
open BtcPolicy.ReceiptExpiry (xapply evictsAt evicts lookup answer sysRecv Lookup Answer)
open BtcPolicy.VariantSilence (VFed)
open BtcPolicy.Sweep (Backend)
open BtcPolicy.RungAssembly (Cfg Step escapeAt rungAt)

/-! ## The receipt step on the labelled ledgered state -/

/-- How many records node `j` of federation `f` holds under id `cid`: `Lifecycle.countAt`'s count. -/
def fcount (f : Federation.Fed) (j cid : Nat) : Nat := (f.worlds j).node.cands.countP (·.id == cid)

theorem countAt_fcount (sw : Sweep.State) (j cid : Nat) : Lifecycle.countAt sw j cid = fcount sw.fed j cid := rfl

/-- Whether the receipt step births a record under `cid` at node `j`: after it, node `j` holds more records under
that id than before. -/
def bornAt (g : Guards) (lcfg : Config) (r : Rules) (F : LFed) (s : Federation.Step) (j cid : Nat) : Bool :=
  decide (fcount F.fed j cid < fcount (xapply g lcfg r F s).fed j cid)

/-- Node `j`'s kept records after the receipt step: at the acting node, the store's arrival added unless already
kept, where nothing arrives at an evicting delivery, then filtered by the records resident after the step, and with
every record under an id the step births at the node dropped; elsewhere as they were. -/
@[req "NCH-25"]
def xstore (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (V : VFed) (s : Federation.Step)
    (h : Option Nat) (j : Nat) : List (Nat × Authority.Sig) :=
  match Federation.actor (kernelStep g lcfg V.lf s) with
  | some (i, env, e) =>
    if j = i then
      (VariantReceipt.addNew (V.store i)
        (if evictsAt V.lf s then [] else VariantReceipt.arrival keys (V.lf.fed.worlds i, env, e, h))).filter
        fun p => ((xapply g lcfg r V.lf s).fed.worlds i).node.cands.any (·.id == p.1) &&
          !bornAt g lcfg r V.lf s i p.1
    else V.store j
  | none => V.store j

/-- **The receipt step.** `VariantSilence.vapply` with `ReceiptExpiry.xapply` in place of `FedSilence.lapply` and
`ReceiptLifecycle.xstore` in place of `VariantSilence.vstore`. -/
@[req "NCH-24"]
def xvapply (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (V : VFed) (s : Federation.Step)
    (h : Option Nat) : VFed :=
  { lf := xapply g lcfg r V.lf s, envs := VariantSilence.newEnvs r g lcfg V.lf s ++ V.envs,
    store := xstore keys g lcfg r V s h }

/-- Whether the step births a record under an id already resident at its acting node. -/
def rebirthAt (g : Guards) (lcfg : Config) (r : Rules) (F : LFed) (s : Federation.Step) : Bool :=
  match Federation.actor (kernelStep g lcfg F s) with
  | some (i, _, _) => (F.fed.worlds i).node.cands.any fun c => bornAt g lcfg r F s i c.id
  | none => false

/-- Every kept record is under an id resident at its node. -/
def Resident (V : VFed) : Prop := ∀ i, ∀ p ∈ V.store i, (V.lf.fed.worlds i).node.cands.any (·.id == p.1) = true

theorem mem_addNew {K new : List (Nat × Authority.Sig)} {p : Nat × Authority.Sig}
    (h : p ∈ VariantReceipt.addNew K new) : p ∈ K ∨ p ∈ new := by
  unfold VariantReceipt.addNew at h
  rcases List.mem_append.1 h with h | h
  · exact .inl h
  · exact .inr (List.mem_filter.1 h).1

/-- What arrives is a record under a resident id that passed the store test. -/
theorem mem_arrival {keys : List Nat} {w : World} {env : Env} {e : Event} {h : Option Nat}
    {p : Nat × Authority.Sig} (hp : p ∈ VariantReceipt.arrival keys (w, env, e, h)) :
    ∃ m k s cid, e = .receivePartial m k s cid ∧ VariantReceipt.storable keys w.node m k s cid h = true ∧
      p = (cid, { msg := m, input := k, signer := s }) := by
  cases e with
  | receivePartial m k s cid =>
    simp only [VariantReceipt.arrival] at hp
    split at hp
    · next hs =>
      rw [List.mem_singleton] at hp
      exact ⟨m, k, s, cid, rfl, hs, hp⟩
    · cases hp
  | _ => simp [VariantReceipt.arrival] at hp

theorem arrival_resident {keys : List Nat} {w : World} {env : Env} {e : Event} {h : Option Nat}
    {p : Nat × Authority.Sig} (hp : p ∈ VariantReceipt.arrival keys (w, env, e, h)) :
    w.node.cands.any (·.id == p.1) = true := by
  obtain ⟨m, k, s, cid, -, hs, rfl⟩ := mem_arrival hp
  obtain ⟨-, c, hc, hid, -⟩ := VariantReceipt.storable_iff.1 hs
  exact List.any_eq_true.2 ⟨c, hc, by simp [hid]⟩

theorem xapply_other (g : Guards) (lcfg : Config) (r : Rules) (F : LFed) (s : Federation.Step) {i j : Nat}
    {env : Env} {e : Event} (hact : Federation.actor (kernelStep g lcfg F s) = some (i, env, e)) (hji : j ≠ i) :
    (xapply g lcfg r F s).fed.worlds j = F.fed.worlds j := by
  cases s with
  | deliverPartial i' env' x =>
    simp only [kernelStep, Federation.actor, Option.some.injEq, Prod.mk.injEq] at hact
    obtain ⟨rfl, -, -⟩ := hact
    simp [xapply, hji]
  | process i' env' e' =>
    show (lapply g lcfg r F _).fed.worlds j = _
    rw [lapply_fed, Federation.apply_of_actor r _ _ hact j, if_neg hji]
  | deliver i' env' m =>
    show (lapply g lcfg r F _).fed.worlds j = _
    rw [lapply_fed, Federation.apply_of_actor r _ _ hact j, if_neg hji]
  | _ => simp [kernelStep, Federation.actor] at hact

theorem xapply_none (g : Guards) (lcfg : Config) (r : Rules) (F : LFed) (s : Federation.Step)
    (hact : Federation.actor (kernelStep g lcfg F s) = none) (j : Nat) :
    (xapply g lcfg r F s).fed.worlds j = F.fed.worlds j := by
  cases s with
  | deliverPartial i' env' x => simp [kernelStep, Federation.actor] at hact
  | process i' env' e' => simp [kernelStep, Federation.actor] at hact
  | deliver i' env' m => simp [kernelStep, Federation.actor] at hact
  | _ =>
    show (lapply g lcfg r F _).fed.worlds j = _
    rw [lapply_fed, Federation.apply_no_actor r _ _ hact j]

/-- The receipt step keeps every kept record resident. -/
theorem resident_step {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {V : VFed} (hr : Resident V)
    (s : Federation.Step) (h : Option Nat) : Resident (xvapply keys g lcfg r V s h) := by
  intro j p hp
  change p ∈ xstore keys g lcfg r V s h j at hp
  change ((xapply g lcfg r V.lf s).fed.worlds j).node.cands.any (·.id == p.1) = true
  unfold xstore at hp
  split at hp
  · next i env e hact =>
    split at hp
    · next hji =>
      subst hji
      have := (List.mem_filter.1 hp).2
      simp only [Bool.and_eq_true] at this
      exact this.1
    · next hji =>
      rw [xapply_other g lcfg r V.lf s hact hji]
      exact hr j p hp
  · next hact =>
    rw [xapply_none g lcfg r V.lf s hact]
    exact hr j p hp

/-- **Off an eviction and a rebirth the step is the variant-bound one.** With every kept record resident, a step that
is not an evicting delivery and births under no id resident at its acting node is `VariantSilence.vapply`. -/
@[req "NCH-25"]
theorem xvapply_eq {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {V : VFed} {s : Federation.Step}
    (h : Option Nat) (he : evictsAt V.lf s = false) (hb : rebirthAt g lcfg r V.lf s = false) (hr : Resident V) :
    xvapply keys g lcfg r V s h = VariantSilence.vapply keys g lcfg r V s h := by
  have hx := ReceiptExpiry.xapply_unevicted g lcfg r V.lf s he
  unfold xvapply VariantSilence.vapply
  rw [hx]
  congr 1
  funext j
  unfold xstore VariantSilence.vstore
  cases hact : Federation.actor (kernelStep g lcfg V.lf s) with
  | none => rfl
  | some a =>
    obtain ⟨i, env, e⟩ := a
    dsimp only
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_pos rfl, he, if_neg Bool.false_ne_true]
      apply List.filter_congr
      intro p hp
      rw [hx]
      have hres : (V.lf.fed.worlds j).node.cands.any (·.id == p.1) = true := by
        rcases mem_addNew hp with hp | hp
        · exact hr j p hp
        · exact arrival_resident hp
      have hbo : bornAt g lcfg r V.lf s j p.1 = false := by
        unfold rebirthAt at hb
        rw [hact] at hb
        obtain ⟨c, hc, hid⟩ := List.any_eq_true.1 hres
        have hid' : c.id = p.1 := by simpa using hid
        rw [← hid']
        rw [List.any_eq_false] at hb
        cases hcb : bornAt g lcfg r V.lf s j c.id
        · rfl
        · exact absurd hcb (hb c hc)
      simp [hbo]
    · rw [if_neg hji, if_neg hji]

/-! ## The layer -/

/-- A `Lifecycle.State` with each node's Hot ledger, the honest envelopes sent so far, newest first, and each node's
kept records. -/
structure State where
  ls : Lifecycle.State
  leds : Nat → Ledger
  envs : List (Exp × Option Nat) := []
  store : Nat → List (Nat × Authority.Sig) := fun _ => []

/-- The ledgered federation of a state. -/
def State.lf (st : State) : LFed := { fed := st.ls.cs.sw.fed, leds := st.leds }

/-- The receipt's state of a state. -/
def State.vf (st : State) : VFed := { lf := st.lf, envs := st.envs, store := st.store }

/-- A history, newest first, each step with the state it was taken in and its label. -/
abbrev Trace := List (State × Step × Option Nat)

/-- The step the lifecycle run takes for a step of the layer: each acceptance mapped through `FedSilence.kernelStep`,
the Hot budget's staged refusal. -/
def mapStep (g : Guards) (lcfg : Config) (st : State) : Step → Step
  | .base (.fed s) => .base (.fed (kernelStep g lcfg st.lf s))
  | s => s

/-- The history as the lifecycle run's: the lifecycle states and the mapped steps. -/
def forget (g : Guards) (lcfg : Config) (T : Trace) : Lifecycle.Trace :=
  T.map fun a => (a.1.ls, mapStep g lcfg a.1 a.2.1, a.2.2)

/-- The history as `ClassAssembly`'s. -/
def cls (g : Guards) (lcfg : Config) (T : Trace) : ClassAssembly.LTrace := Lifecycle.toL (forget g lcfg T)

/-- A lifecycle state with its federation replaced. -/
def withFed (l : Lifecycle.State) (f : Federation.Fed) : Lifecycle.State :=
  { l with cs := { l.cs with sw := { l.cs.sw with fed := f } } }

/-- One step. A federation step takes the receipt step for the federation, the ledgers, the envelopes and the store,
and `Lifecycle.apply` on the mapped step for every other field; every other step is `Lifecycle.apply`'s. -/
@[req "NCH-24"]
def apply (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) : Step → Option Nat → State
  | .base (.fed s), h =>
    { ls := withFed (Lifecycle.apply r st.ls (.base (.fed (kernelStep g lcfg st.lf s)))) (xapply g lcfg r st.lf s).fed,
      leds := (xapply g lcfg r st.lf s).leds, envs := VariantSilence.newEnvs r g lcfg st.lf s ++ st.envs,
      store := xstore keys g lcfg r st.vf s h }
  | s, _ => { st with ls := Lifecycle.apply r st.ls s }

/-- Node `i`'s possession: its own signatures and its kept records (`VariantSilence.vheld`). -/
@[req "DUR-28"]
def heldAt (st : State) (i : Nat) : List Authority.Sig := VariantSilence.vheld st.vf i

/-- `ClassAssembly.finalAt` over the layer's possession. -/
@[req "DUR-28"]
def finalAt (cfg : Cfg) (st : State) (i : Nat) (c : Cand) : Option Nat :=
  Ladder.finalize cfg.lc.pre.sweep.keys (st.ls.cs.sw.fed.worlds i).node.t c.ladder (heldAt st i) c.track.latch

/-- `ClassAssembly.candOk` over the layer's possession. -/
@[req "SPN-39"]
def candOk (cfg : Cfg) (st : State) (L : ClassAssembly.LTrace) (i : Nat) (c : Cand) : Bool :=
  match st.ls.cs.sw.obs i with
  | none => false
  | some b =>
    if c.isEscape then
      finalAt cfg st i c == some 0 &&
        Assembly.rungCheck cfg.asm (ClassAssembly.readAt st.ls.cs L i c) b c (heldAt st i) 0
    else
      Assembly.checkAt cfg.asm (Sweep.authorizedAt st.ls.cs.sw (ClassAssembly.sweepT L) i)
        (Assembly.clawTxsAt st.ls.cs.sw (ClassAssembly.sweepT L) i) (st.ls.cs.sw.fed.worlds i).node (heldAt st i) b c

/-- `ClassAssembly.guard` over the layer's possession. -/
@[req "SPN-39"]
def guard (cfg : Cfg) (st : State) (L : ClassAssembly.LTrace) : Sweep.Step → Bool
  | .fed (.process i _ (.packageAccepted cid)) =>
    (st.ls.cs.sw.fed.worlds i).node.cands.all fun c => !(c.id == cid) || candOk cfg st L i c
  | _ => true

/-- `ClassAssembly.assembleOk` over the layer's possession. -/
@[req "DUR-29"]
def assembleOk (cfg : Cfg) (st : State) (L : ClassAssembly.LTrace) (i cid m : Nat) : Bool :=
  match escapeAt (st.ls.cs.sw.fed.worlds i).node cid, st.ls.cs.sw.obs i with
  | some c, some b => finalAt cfg st i c == some m &&
      Assembly.rungCheck cfg.asm (ClassAssembly.readAt st.ls.cs L i c) b c (heldAt st i) m
  | _, _ => false

/-- `Lifecycle.admits` on the mapped step, with the assembly guard and a rung's assembly over the layer's
possession. -/
def admits (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) (st : State) (T : Trace)
    (s : Step) : Bool :=
  match mapStep g lcfg st s with
  | .base b => LadderRelease.admits cfg.lc honest st.ls.cs.sw (ClassAssembly.sweepT (cls g lcfg T)) b &&
      guard cfg st (cls g lcfg T) b && Settlement.readOk st.ls.cs.sw b && Lifecycle.kernelSendOk st.ls.cs b
  | .assemble i cid m => honest.contains i && assembleOk cfg st (cls g lcfg T) i cid m && !st.ls.used.contains i
  | .send i env cid m => honest.contains i && RungAssembly.sendOk r env st.ls.cs i cid m && Lifecycle.sendOk st.ls i cid m

/-- A delivery's label is admissible as `VariantSilence.vlabelOk` has it; no other step's label is read. -/
@[req "NCH-24"]
def labelOk (st : State) : Step → Option Nat → Bool
  | .base (.fed s), h => VariantSilence.vlabelOk st.vf s h
  | _, _ => true

/-- A fresh start: `Lifecycle`'s, nothing sent and nothing kept. The ledgers are an input. -/
def Fresh (honest : List Nat) (st : State) : Prop :=
  Lifecycle.Fresh honest st.ls ∧ st.envs = [] ∧ ∀ i, st.store i = []

/-- A reachable execution of the layer. -/
inductive Execution (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Fresh honest st) : Execution cfg g lcfg r honest [] st
  | next {T st} (s : Step) (h : Option Nat) (ha : admits cfg g lcfg r honest st T s = true)
      (hl : labelOk st s h = true) : Execution cfg g lcfg r honest T st →
      Execution cfg g lcfg r honest ((st, s, h) :: T) (apply cfg.lc.pre.sweep.keys g lcfg r st s h)

/-! ## The step against the lifecycle's -/

/-- Whether a step is a delivery the receiver's lookup evicts on. -/
def evictsStep (st : State) : Step → Bool
  | .base (.fed s) => evictsAt st.lf s
  | _ => false

theorem apply_vf (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Federation.Step)
    (h : Option Nat) : (apply keys g lcfg r st (.base (.fed s)) h).vf = xvapply keys g lcfg r st.vf s h := rfl

/-- **Off an evicting delivery the lifecycle state is the lifecycle's step.** -/
@[req "NCH-24"]
theorem apply_ls (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step) (h : Option Nat)
    (he : evictsStep st s = false) : (apply keys g lcfg r st s h).ls = Lifecycle.apply r st.ls (mapStep g lcfg st s) := by
  cases s with
  | base b =>
    cases b with
    | fed s =>
      simp only [evictsStep] at he
      show withFed _ (xapply g lcfg r st.lf s).fed = _
      rw [ReceiptExpiry.xapply_unevicted g lcfg r st.lf s he, lapply_fed]
      rfl
    | chain b => rfl
    | observe i b => rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

theorem apply_perm (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) : (apply keys g lcfg r st s h).ls.perm = Lifecycle.permAfter r st.ls (mapStep g lcfg st s) := by
  cases s with
  | base b => cases b <;> rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

theorem apply_subs (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) : (apply keys g lcfg r st s h).ls.subs = Lifecycle.subsAfter r st.ls (mapStep g lcfg st s) := by
  cases s with
  | base b => cases b <;> rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

/-- A step that is not a federation step moves no federation, ledger, envelope or kept record. -/
theorem apply_vf_other (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) (hs : ∀ s', s ≠ .base (.fed s')) : (apply keys g lcfg r st s h).vf = st.vf := by
  have hfed : (apply keys g lcfg r st s h).ls.cs.sw.fed = st.ls.cs.sw.fed := by
    cases s with
    | base b =>
      cases b with
      | fed s' => exact absurd rfl (hs s')
      | chain b => rfl
      | observe i b => rfl
    | assemble i cid m =>
      show (RungAssembly.apply r st.ls.cs (.assemble i cid m)).sw.fed = _
      rw [RungAssembly.apply_sw r st.ls.cs (by simp)]
    | send i env cid m =>
      show (RungAssembly.apply r st.ls.cs (.send i env cid m)).sw.fed = _
      rw [RungAssembly.apply_sw r st.ls.cs (by simp)]
  have hrest : (apply keys g lcfg r st s h).leds = st.leds ∧ (apply keys g lcfg r st s h).envs = st.envs ∧
      (apply keys g lcfg r st s h).store = st.store := by
    cases s with
    | base b =>
      cases b with
      | fed s' => exact absurd rfl (hs s')
      | chain b => exact ⟨rfl, rfl, rfl⟩
      | observe i b => exact ⟨rfl, rfl, rfl⟩
    | assemble i cid m => exact ⟨rfl, rfl, rfl⟩
    | send i env cid m => exact ⟨rfl, rfl, rfl⟩
  simp only [State.vf, State.lf, hfed, hrest.1, hrest.2.1, hrest.2.2]

theorem fed_nonfed {s : Step} (hs : ∀ s', s ≠ .base (.fed s')) (keys : List Nat) (g : Guards) (lcfg : Config)
    (r : Rules) (st : State) (h : Option Nat) :
    (apply keys g lcfg r st s h).ls.cs.sw.fed = st.ls.cs.sw.fed :=
  congrArg (fun V : VFed => V.lf.fed) (apply_vf_other keys g lcfg r st s h hs)

/-- Every run keeps each kept record resident at its node. -/
theorem resident_inv {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) : Resident st.vf := by
  induction hx with
  | init st h => intro i p hp; change p ∈ st.store i at hp; rw [h.2.2 i] at hp; cases hp
  | @next T st s lab ha hl hx ih =>
    cases s with
    | base b =>
      cases b with
      | fed s => rw [apply_vf]; exact resident_step ih s lab
      | chain b => rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact ih
      | observe j b => rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact ih
    | assemble i cid m => rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact ih
    | send i env cid m => rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact ih

/-! ## Agreement with the lifecycle run -/

/-- The step is not an evicting delivery, and births under no id resident at its acting node. -/
def Quiet (g : Guards) (lcfg : Config) (r : Rules) (st : State) : Step → Bool
  | .base (.fed s) => !evictsAt st.lf s && !rebirthAt g lcfg r st.lf s
  | _ => true

/-- The layer's kept records and envelopes are `VariantReceipt.kept`'s and `VariantReceipt.envelopes`' over the
labelled federation steps of the forgotten history. -/
def Agrees (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (T : Trace) (st : State) : Prop :=
  VariantSilence.Agrees cfg.lc.pre.sweep.keys r (ClassAssembly.fedL (cls g lcfg T)) st.vf

theorem fedL_fed (g : Guards) (lcfg : Config) (st : State) (s : Federation.Step) (lab : Option Nat) (T : Trace) :
    ClassAssembly.fedL (cls g lcfg ((st, .base (.fed s), lab) :: T)) =
      (st.ls.cs.sw.fed, kernelStep g lcfg st.lf s, lab) :: ClassAssembly.fedL (cls g lcfg T) := rfl

theorem fedL_other {g : Guards} {lcfg : Config} {st : State} {s : Step} {lab : Option Nat} {T : Trace}
    (hs : ∀ s', s ≠ .base (.fed s')) :
    ClassAssembly.fedL (cls g lcfg ((st, s, lab) :: T)) = ClassAssembly.fedL (cls g lcfg T) := by
  cases s with
  | base b =>
    cases b with
    | fed s' => exact absurd rfl (hs s')
    | chain b => rfl
    | observe j b => rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

theorem mapStep_base (g : Guards) (lcfg : Config) (st : State) (b : Sweep.Step) :
    ∃ b', mapStep g lcfg st (.base b) = .base b' := by
  cases b <;> exact ⟨_, rfl⟩

theorem heldAt_eq {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {T : Trace} {st : State}
    (hag : Agrees cfg g lcfg r T st) (i : Nat) : heldAt st i = ClassAssembly.heldAt cfg st.ls.cs (cls g lcfg T) i :=
  VariantSilence.vheld_held hag i

theorem candOk_eq {cfg : Cfg} {st : State} {L : ClassAssembly.LTrace}
    (hH : ∀ i, heldAt st i = ClassAssembly.heldAt cfg st.ls.cs L i) (i : Nat) (c : Cand) :
    candOk cfg st L i c = ClassAssembly.candOk cfg st.ls.cs L i c := by
  unfold candOk ClassAssembly.candOk finalAt ClassAssembly.finalAt
  rw [hH]
  rfl

theorem guard_eq {cfg : Cfg} {st : State} {L : ClassAssembly.LTrace}
    (hH : ∀ i, heldAt st i = ClassAssembly.heldAt cfg st.ls.cs L i) (b : Sweep.Step) :
    guard cfg st L b = ClassAssembly.guard cfg st.ls.cs L b := by
  unfold guard
  split
  · next i env cid => simp only [ClassAssembly.guard, candOk_eq hH]
  · next hne =>
    unfold ClassAssembly.guard
    split
    · next i env cid => exact absurd rfl (hne i env cid)
    · rfl

theorem assembleOk_eq {cfg : Cfg} {st : State} {L : ClassAssembly.LTrace}
    (hH : ∀ i, heldAt st i = ClassAssembly.heldAt cfg st.ls.cs L i) (i cid m : Nat) :
    assembleOk cfg st L i cid m = ClassAssembly.assembleOk cfg st.ls.cs L i cid m := by
  unfold assembleOk ClassAssembly.assembleOk finalAt ClassAssembly.finalAt
  rw [hH]
  rfl

theorem admits_lifecycle {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} {s : Step} (hag : Agrees cfg g lcfg r T st) (ha : admits cfg g lcfg r honest st T s = true) :
    Lifecycle.admits cfg r honest st.ls (forget g lcfg T) (mapStep g lcfg st s) = true := by
  have hH := heldAt_eq hag
  unfold admits at ha
  generalize mapStep g lcfg st s = s' at ha ⊢
  cases s' with
  | base b =>
    dsimp only at ha
    simp only [Lifecycle.admits, ClassAssembly.admits]
    rw [show Lifecycle.toL (forget g lcfg T) = cls g lcfg T from rfl, ← guard_eq hH b]
    exact ha
  | assemble i cid m =>
    dsimp only at ha
    simp only [Lifecycle.admits, ClassAssembly.admits]
    rw [show Lifecycle.toL (forget g lcfg T) = cls g lcfg T from rfl, ← assembleOk_eq hH i cid m]
    exact ha
  | send i env cid m =>
    dsimp only at ha
    simp only [Lifecycle.admits, ClassAssembly.admits]
    exact ha

theorem label_lifecycle {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {T : Trace} {st : State} {s : Step}
    {h : Option Nat} (hag : Agrees cfg g lcfg r T st) (hl : labelOk st s h = true) :
    ClassAssembly.labelOk r st.ls.cs (cls g lcfg T) (mapStep g lcfg st s) h = true := by
  cases s with
  | base b =>
    cases b with
    | fed s =>
      cases s with
      | deliverPartial i env x =>
        simp only [labelOk, VariantSilence.vlabelOk, mapStep, kernelStep, ClassAssembly.labelOk,
          VariantReceipt.labelOk, ← hag.1] at hl ⊢
        exact hl
      | process i env e => rfl
      | _ => rfl
    | chain b => rfl
    | observe i b => rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

/-- **Agreement with the lifecycle run** (`NCH-24`, `NCH-25`, `DUR-29`). On a history where no delivery evicts and
no step births under an id resident at its acting node, forgetting the ledgers, the envelopes and the store, with each
acceptance mapped through `FedSilence.kernelStep`, leaves a `Lifecycle.Execution`, and the layer's kept records and
envelopes are `VariantReceipt.kept`'s and `VariantReceipt.envelopes`' over the labelled history. Every result over
`Lifecycle.Execution`, and through `Lifecycle.to_classed`, `Lifecycle.to_ladder` and `Lifecycle.to_settlement` the
earlier layers' results, applies there. -/
@[req "DUR-29"]
theorem to_lifecycle {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) (hq : ∀ a ∈ T, Quiet g lcfg r a.1 a.2.1 = true) :
    Lifecycle.Execution cfg r honest (forget g lcfg T) st.ls ∧ Agrees cfg g lcfg r T st := by
  induction hx with
  | init st h => exact ⟨.init _ h.1, h.2.1, fun i => h.2.2 i⟩
  | @next T st s lab ha hl hx ih =>
    obtain ⟨hlx, hag⟩ := ih (fun a ha' => hq a (List.mem_cons_of_mem _ ha'))
    have hqs : Quiet g lcfg r st s = true := hq _ (List.mem_cons_self ..)
    have he : evictsStep st s = false := by
      cases s with
      | base b =>
        cases b with
        | fed s =>
          simp only [Quiet, Bool.and_eq_true, Bool.not_eq_true'] at hqs
          exact hqs.1
        | chain b => rfl
        | observe i b => rfl
      | assemble i cid m => rfl
      | send i env cid m => rfl
    refine ⟨?_, ?_⟩
    · rw [apply_ls _ _ _ _ st s lab he]
      exact .next _ lab (admits_lifecycle hag ha) (label_lifecycle hag hl) hlx
    · cases s with
      | base b =>
        cases b with
        | fed s =>
          simp only [Quiet, Bool.and_eq_true, Bool.not_eq_true'] at hqs
          have hag' : VariantSilence.Agrees cfg.lc.pre.sweep.keys r (ClassAssembly.fedL (cls g lcfg T)) st.vf := hag
          unfold Agrees
          rw [fedL_fed, apply_vf, xvapply_eq (V := st.vf) lab hqs.1 hqs.2 (resident_inv hx)]
          exact VariantSilence.agrees_step hag' s lab
        | chain b =>
          unfold Agrees
          rw [fedL_other (s := .base (.chain b)) (by simp),
            apply_vf_other _ _ _ _ _ (.base (.chain b)) _ (by simp)]; exact hag
        | observe j b =>
          unfold Agrees
          rw [fedL_other (s := .base (.observe j b)) (by simp),
            apply_vf_other _ _ _ _ _ (.base (.observe j b)) _ (by simp)]; exact hag
      | assemble i cid m =>
        unfold Agrees
        rw [fedL_other (s := .assemble i cid m) (by simp),
          apply_vf_other _ _ _ _ _ (.assemble i cid m) _ (by simp)]; exact hag
      | send i env cid m =>
        unfold Agrees
        rw [fedL_other (s := .send i env cid m) (by simp),
          apply_vf_other _ _ _ _ _ (.send i env cid m) _ (by simp)]; exact hag

/-! ## Agreement with the receipt -/

/-- **At a delivery the receiver is the receipt's** (`NCH-24`, `POL-18`). The receiver's world and Hot ledger after
an admitted delivery are `ReceiptExpiry.sysRecv`'s at its state before the step and the delivery's own sample, so its
node is `ReceiptExpiry.receive`'s after `ReceiptExpiry.lookup`, and the answer is `ReceiptExpiry.answer`'s there. -/
@[req "NCH-24"]
theorem deliver_sys (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (i : Nat) (env : Env)
    (x : Exp) (h : Option Nat) :
    (apply keys g lcfg r st (.base (.fed (.deliverPartial i env x))) h).lf.sys i =
        sysRecv g lcfg env (st.lf.sys i) x.msg x.input x.signer x.cid ∧
      ((apply keys g lcfg r st (.base (.fed (.deliverPartial i env x))) h).ls.cs.sw.fed.worlds i).node =
        ReceiptExpiry.receive env (st.ls.cs.sw.fed.worlds i).node x.msg x.input x.signer x.cid := by
  refine ⟨?_, ?_⟩
  · simp [apply, State.lf, LFed.sys, xapply, withFed]
  · simp [apply, withFed, xapply, sysRecv, ReceiptExpiry.wstep, LFed.sys, State.lf]

/-- The federation steps of a history, oldest first. -/
def fedSteps : Trace → List Federation.Step
  | [] => []
  | (_, .base (.fed s), _) :: T => fedSteps T ++ [s]
  | _ :: T => fedSteps T

theorem xrun_snoc (g : Guards) (lcfg : Config) (r : Rules) :
    ∀ (l : List Federation.Step) (F : LFed) (s : Federation.Step),
      ReceiptExpiry.xrun g lcfg r F (l ++ [s]) = xapply g lcfg r (ReceiptExpiry.xrun g lcfg r F l) s
  | [], _, _ => rfl
  | y :: l, F, s => by
    simp only [List.cons_append, ReceiptExpiry.xrun]
    exact xrun_snoc g lcfg r l _ s

theorem xlegal_snoc (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) :
    ∀ (l : List Federation.Step) (F : LFed) (s : Federation.Step),
      ReceiptExpiry.xlegal g lcfg r honest F (l ++ [s]) =
        (ReceiptExpiry.xlegal g lcfg r honest F l &&
          Federation.admits honest (ReceiptExpiry.xrun g lcfg r F l).fed s)
  | [], F, s => by simp [ReceiptExpiry.xlegal, ReceiptExpiry.xrun]
  | y :: l, F, s => by
    simp only [List.cons_append, ReceiptExpiry.xlegal, ReceiptExpiry.xrun, Bool.and_assoc]
    rw [xlegal_snoc g lcfg r honest l _ s]

theorem admits_fed {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    {s : Federation.Step} (ha : admits cfg g lcfg r honest st T (.base (.fed s)) = true) :
    Federation.admits honest st.ls.cs.sw.fed s = true := by
  simp only [admits, mapStep, LadderRelease.admits, Sweep.admits, Bool.and_eq_true] at ha
  have h := ha.1.1.1.1.1
  rwa [show st.ls.cs.sw.fed = st.lf.fed from rfl, admits_kernelStep] at h

/-- **The federation and ledger part is the receipt's run** (`NCH-24`). From a fresh start, the ledgered federation
of every run is `ReceiptExpiry.xrun` over its federation steps, and every one of them is admitted where it is taken
(`ReceiptExpiry.xlegal`), so the receipt's results apply at each step. -/
@[req "NCH-24"]
theorem to_xrun {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg g lcfg r honest T st) :
    ∃ st₀, Fresh honest st₀ ∧ ReceiptExpiry.xrun g lcfg r st₀.lf (fedSteps T) = st.lf ∧
      ReceiptExpiry.xlegal g lcfg r honest st₀.lf (fedSteps T) = true := by
  induction hx with
  | init st h => exact ⟨st, h, rfl, rfl⟩
  | @next T st s lab ha hl hx ih =>
    obtain ⟨st₀, h0, hrun, hleg⟩ := ih
    refine ⟨st₀, h0, ?_⟩
    cases s with
    | base b =>
      cases b with
      | fed s =>
        show ReceiptExpiry.xrun g lcfg r st₀.lf (fedSteps T ++ [s]) = _ ∧
          ReceiptExpiry.xlegal g lcfg r honest st₀.lf (fedSteps T ++ [s]) = true
        rw [xrun_snoc, xlegal_snoc, hrun, hleg, Bool.true_and]
        exact ⟨rfl, admits_fed ha⟩
      | chain b =>
        refine ⟨?_, hleg⟩
        show _ = (apply _ g lcfg r st (.base (.chain b)) lab).vf.lf
        rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact hrun
      | observe j b =>
        refine ⟨?_, hleg⟩
        show _ = (apply _ g lcfg r st (.base (.observe j b)) lab).vf.lf
        rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact hrun
    | assemble i cid m =>
      refine ⟨?_, hleg⟩
      show _ = (apply _ g lcfg r st (.assemble i cid m) lab).vf.lf
      rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact hrun
    | send i env cid m =>
      refine ⟨?_, hleg⟩
      show _ = (apply _ g lcfg r st (.send i env cid m) lab).vf.lf
      rw [apply_vf_other _ _ _ _ _ _ _ (by simp)]; exact hrun

/-! ## History -/

/-- One step keeps the partial inventory, the extracted keys, every node's exposure rows and the submission
history: at a delivery, evicting or not, as `ReceiptExpiry.xapply_inventories` and `ReceiptExpiry.xapply_exposure`
have it; at every other step as `Lifecycle.step_kept` has it. -/
theorem step_kept (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) :
    (∀ x ∈ st.ls.cs.sw.fed.parts, x ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.parts) ∧
      (∀ j ∈ st.ls.cs.sw.fed.extracted, j ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.extracted) ∧
      (∀ i, ∀ x ∈ (st.ls.cs.sw.fed.worlds i).exposure,
        x ∈ ((apply keys g lcfg r st s h).ls.cs.sw.fed.worlds i).exposure) ∧
      ∀ x ∈ st.ls.subs, x ∈ (apply keys g lcfg r st s h).ls.subs := by
  have viaLs (he : evictsStep st s = false) :
      (∀ x ∈ st.ls.cs.sw.fed.parts, x ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.parts) ∧
        (∀ j ∈ st.ls.cs.sw.fed.extracted, j ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.extracted) ∧
        (∀ i, ∀ x ∈ (st.ls.cs.sw.fed.worlds i).exposure,
          x ∈ ((apply keys g lcfg r st s h).ls.cs.sw.fed.worlds i).exposure) ∧
        ∀ x ∈ st.ls.subs, x ∈ (apply keys g lcfg r st s h).ls.subs := by
    rw [apply_ls keys g lcfg r st s h he]
    exact Lifecycle.step_kept r st.ls (mapStep g lcfg st s)
  cases s with
  | base b =>
    cases b with
    | fed s =>
      cases s with
      | deliverPartial i env x =>
        refine ⟨fun y hy => ?_, fun j hj => ?_, fun j y hy => ?_, fun y hy =>
          (Lifecycle.step_kept r st.ls (.base (.fed (.deliverPartial i env x)))).2.2.2 y hy⟩
        · show y ∈ (xapply g lcfg r st.lf (.deliverPartial i env x)).fed.parts
          rw [(ReceiptExpiry.xapply_inventories g lcfg r st.lf i env x).1]; exact hy
        · show j ∈ (xapply g lcfg r st.lf (.deliverPartial i env x)).fed.extracted
          rw [(ReceiptExpiry.xapply_inventories g lcfg r st.lf i env x).2.2]; exact hj
        · show y ∈ ((xapply g lcfg r st.lf (.deliverPartial i env x)).fed.worlds j).exposure
          by_cases hji : j = i
          · subst hji
            rw [ReceiptExpiry.xapply_exposure]
            exact List.mem_append_left _ hy
          · rw [xapply_other g lcfg r st.lf _ rfl hji]; exact hy
      | _ => exact viaLs rfl
    | chain b => exact viaLs rfl
    | observe j b => exact viaLs rfl
  | assemble i cid m => exact viaLs rfl
  | send i env cid m => exact viaLs rfl

/-- **History is kept** (`POL-18`, `SEC-54`). What any earlier state of a run held in the partial inventory, the
extracted set, any node's exposure rows or the submission history, the final state holds: across every eviction,
refusal and birth. Only local retention, the registry and the kept records, can shrink. -/
@[req "POL-18"]
theorem history_kept {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {st₀ : State} {s : Step} {lab : Option Nat}
    (hm : (st₀, s, lab) ∈ T) :
    (∀ x ∈ st₀.ls.cs.sw.fed.parts, x ∈ st.ls.cs.sw.fed.parts) ∧
      (∀ j ∈ st₀.ls.cs.sw.fed.extracted, j ∈ st.ls.cs.sw.fed.extracted) ∧
      (∀ i, ∀ x ∈ (st₀.ls.cs.sw.fed.worlds i).exposure, x ∈ (st.ls.cs.sw.fed.worlds i).exposure) ∧
      ∀ x ∈ st₀.ls.subs, x ∈ st.ls.subs := by
  induction hx with
  | init st h => cases hm
  | @next T st' s' h' _ _ _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact step_kept _ g lcfg r _ _ _
    · obtain ⟨h1, h2, h3, h4⟩ := ih hm
      obtain ⟨k1, k2, k3, k4⟩ := step_kept cfg.lc.pre.sweep.keys g lcfg r st' s' h'
      exact ⟨fun x hx => k1 x (h1 x hx), fun j hj => k2 j (h2 j hj), fun i x hx => k3 i x (h3 i x hx),
        fun x hx => k4 x (h4 x hx)⟩

/-- One lifecycle step keeps the relay inventory: a federation step as `Federation.net_grows` has it, a chain move
and an observation leave the federation alone, and a rung step moves no federation state. -/
theorem lstep_relays_kept (r : Rules) (st : Lifecycle.State) (s : Step) {n : Federation.Relay}
    (hn : n ∈ st.cs.sw.fed.net) : n ∈ (Lifecycle.apply r st s).cs.sw.fed.net := by
  cases s with
  | base b =>
    cases b with
    | fed s => exact Federation.net_grows r _ s hn
    | chain b => exact hn
    | observe j b => exact hn
  | assemble i cid m =>
    rw [show (Lifecycle.apply r st (.assemble i cid m)).cs.sw = st.cs.sw from
      RungAssembly.apply_sw (s := .assemble i cid m) r st.cs (by simp)]
    exact hn
  | send i env cid m =>
    rw [show (Lifecycle.apply r st (.send i env cid m)).cs.sw = st.cs.sw from
      RungAssembly.apply_sw (s := .send i env cid m) r st.cs (by simp)]
    exact hn

/-- One step keeps the relay inventory: at a delivery, evicting or not, as `ReceiptExpiry.xapply_inventories` has
it; at every other step as `ReceiptLifecycle.lstep_relays_kept` has it. -/
theorem step_relays_kept (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) {n : Federation.Relay} (hn : n ∈ st.ls.cs.sw.fed.net) :
    n ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.net := by
  have viaLs (he : evictsStep st s = false) : n ∈ (apply keys g lcfg r st s h).ls.cs.sw.fed.net := by
    rw [apply_ls keys g lcfg r st s h he]
    exact lstep_relays_kept r st.ls (mapStep g lcfg st s) hn
  cases s with
  | base b =>
    cases b with
    | fed s =>
      cases s with
      | deliverPartial i env x =>
        show n ∈ (xapply g lcfg r st.lf (.deliverPartial i env x)).fed.net
        rw [(ReceiptExpiry.xapply_inventories g lcfg r st.lf i env x).2.1]; exact hn
      | _ => exact viaLs rfl
    | chain b => exact viaLs rfl
    | observe j b => exact viaLs rfl
  | assemble i cid m => exact viaLs rfl
  | send i env cid m => exact viaLs rfl

/-- **Relays are kept** (`POL-18`, `SEC-54`), beside `ReceiptLifecycle.history_kept`: every relay in the inventory at
an earlier state of a run is in the inventory at the final state, across every eviction, refusal and birth. -/
@[req "POL-18"]
theorem relays_kept {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {st₀ : State} {s : Step} {lab : Option Nat}
    (hm : (st₀, s, lab) ∈ T) : ∀ n ∈ st₀.ls.cs.sw.fed.net, n ∈ st.ls.cs.sw.fed.net := by
  induction hx with
  | init st h => cases hm
  | @next T st' s' h' _ _ _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact fun n hn => step_relays_kept _ g lcfg r _ _ _ hn
    · exact fun n hn => step_relays_kept cfg.lc.pre.sweep.keys g lcfg r st' s' h' (ih hm n hn)

/-! ## Births and permits -/

/-- Whether a step of the layer births a record under `cid` at node `j`: after it, node `j` holds more records under
that id than before. -/
def born (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step) (h : Option Nat)
    (j cid : Nat) : Bool :=
  decide (fcount st.ls.cs.sw.fed j cid < fcount (apply keys g lcfg r st s h).ls.cs.sw.fed j cid)

theorem count_receivePartial (n : Node) (m : Sighash) (i s cid k : Nat) :
    (receivePartial n m i s cid).cands.countP (·.id == k) = n.cands.countP (·.id == k) := by
  rw [ReceiptExpiry.receivePartial_stored]
  simp only [List.countP_map]
  congr 1
  funext c
  simp [Function.comp, (ReceiptExpiry.stored_fields m i s cid c).1]

theorem count_receive_le (env : Env) (n : Node) (m : Sighash) (i s cid k : Nat) :
    (ReceiptExpiry.receive env n m i s cid).cands.countP (·.id == k) ≤ n.cands.countP (·.id == k) := by
  unfold ReceiptExpiry.receive
  split
  · exact List.filter_sublist.countP_le
  · rw [count_receivePartial]; exact Nat.le_refl _

/-- A delivery, evicting or not, births nothing anywhere. -/
theorem deliver_count_le (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (i : Nat) (env : Env)
    (x : Exp) (h : Option Nat) (j k : Nat) :
    fcount (apply keys g lcfg r st (.base (.fed (.deliverPartial i env x))) h).ls.cs.sw.fed j k ≤
      fcount st.ls.cs.sw.fed j k := by
  show fcount (xapply g lcfg r st.lf (.deliverPartial i env x)).fed j k ≤ _
  unfold fcount
  by_cases hji : j = i
  · subst hji
    simp only [xapply, if_true]
    exact count_receive_le _ _ _ _ _ _ _
  · rw [xapply_other g lcfg r st.lf _ rfl hji]; exact Nat.le_refl _

theorem births_deliver (r : Rules) (sw : Sweep.State) (i : Nat) (env : Env) (x : Exp) (j cid : Nat) :
    Lifecycle.births r sw (.fed (.deliverPartial i env x)) j cid = false := by
  unfold Lifecycle.births Lifecycle.countAt
  simp only [decide_eq_false_iff_not, Nat.not_lt]
  show ((Federation.apply r sw.fed (.deliverPartial i env x)).worlds j).node.cands.countP _ ≤ _
  rw [Federation.apply_of_actor r _ _ rfl j]
  split
  · next hj =>
    subst hj
    show (receivePartial _ _ _ _ _).cands.countP _ ≤ _
    rw [count_receivePartial]; exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **An evicting receipt ends no permit** (`DUR-29`, `DUR-31`). A delivery, evicting or not, keeps every permit: it
is no pass, prune, birth, settlement or send. -/
@[req "DUR-31"]
theorem deliver_keeps_permits (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (i : Nat)
    (env : Env) (x : Exp) (h : Option Nat) :
    (apply keys g lcfg r st (.base (.fed (.deliverPartial i env x))) h).ls.perm = st.ls.perm := by
  rw [apply_perm]
  show st.ls.perm.filter _ = st.ls.perm
  apply List.filter_eq_self.2
  intro p _
  simp [Lifecycle.keeps, Lifecycle.endsAt, Lifecycle.settlesAt, kernelStep, births_deliver]

/-- **A step that keeps a permit births nothing under its id** (`DUR-31`). Where `Lifecycle.keeps` keeps a permit of
node `j` under `cid` at a step of the layer, the step births no record under `cid` at node `j`. -/
@[req "DUR-31"]
theorem keeps_unborn (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) {j cid : Nat} (hk : Lifecycle.keeps r j cid st.ls (mapStep g lcfg st s) = true) :
    born keys g lcfg r st s h j cid = false := by
  unfold born
  simp only [decide_eq_false_iff_not, Nat.not_lt]
  cases s with
  | base b =>
    cases b with
    | fed s =>
      cases s with
      | deliverPartial i env x => exact deliver_count_le keys g lcfg r st i env x h j cid
      | _ =>
        rw [apply_ls keys g lcfg r st _ h rfl]
        simp only [mapStep, Lifecycle.keeps, Bool.and_eq_true, Bool.not_eq_true'] at hk
        have hb := hk.1.2
        simp only [Lifecycle.births, decide_eq_false_iff_not, Nat.not_lt] at hb
        exact hb
    | chain b => rw [fed_nonfed (by simp)]; exact Nat.le_refl _
    | observe i b => rw [fed_nonfed (by simp)]; exact Nat.le_refl _
  | assemble i cid' m => rw [fed_nonfed (by simp)]; exact Nat.le_refl _
  | send i env cid' m => rw [fed_nonfed (by simp)]; exact Nat.le_refl _

/-- **A birth ends the old permits** (`DUR-31`). After a step of the layer that births a record under `cid` at node
`j`, node `j` holds no permit under `cid`. -/
@[req "DUR-31"]
theorem born_ends_permits (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : State) (s : Step)
    (h : Option Nat) {j cid : Nat} (hb : born keys g lcfg r st s h j cid = true) :
    ∀ p ∈ (apply keys g lcfg r st s h).ls.perm, ¬(p.node = j ∧ p.cid = cid) := by
  intro p hp ⟨h1, h2⟩
  rw [apply_perm] at hp
  have hk : Lifecycle.keeps r p.node p.cid st.ls (mapStep g lcfg st s) = true := by
    cases s with
    | base b =>
      obtain ⟨b', hb'⟩ := mapStep_base g lcfg st b
      rw [hb'] at hp ⊢
      exact (List.mem_filter.1 hp).2
    | assemble i cid' m =>
      exfalso
      unfold born at hb
      rw [fed_nonfed (s := .assemble i cid' m) (by simp)] at hb
      simp at hb
    | send i env cid' m =>
      exfalso
      unfold born at hb
      rw [fed_nonfed (s := .send i env cid' m) (by simp)] at hb
      simp at hb
  rw [h1, h2] at hk
  rw [keeps_unborn keys g lcfg r st s h hk] at hb
  cases hb

/-- Permit `p` was recorded earlier in `T`, `T₁` the history before that step: an admitted rung assembly of its rung
at its node under its id, `ReceiptLifecycle.assembleOk` over the layer's possession at that state, at a node whose
current observation no rung assembly had read, that observation the permit's, and the rung's txid the permit's; and
no step since, in `T₂`, ended the node's permits or consumed them, a birth under the id at the node included
(`Lifecycle.keeps` on each mapped step). -/
def Permitted (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (T : Trace) (p : Lifecycle.Permit) : Prop :=
  ∃ T₁ T₂ st h, T = T₂ ++ (st, .assemble p.node p.cid p.rung, h) :: T₁ ∧
    assembleOk cfg st (cls g lcfg T₁) p.node p.cid p.rung = true ∧ p.node ∉ st.ls.used ∧
    st.ls.cs.sw.obs p.node = some p.obs ∧
    (∃ gr, rungAt (st.ls.cs.sw.fed.worlds p.node).node p.cid p.rung = some gr ∧ gr.tx.id = p.txid) ∧
    ∀ q ∈ T₂, Lifecycle.keeps r p.node p.cid q.1.ls (mapStep g lcfg q.1 q.2.1) = true

theorem Permitted.cons {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {T : Trace} {p : Lifecycle.Permit}
    (y : State × Step × Option Nat) (h : Permitted cfg g lcfg r T p)
    (hk : Lifecycle.keeps r p.node p.cid y.1.ls (mapStep g lcfg y.1 y.2.1) = true) :
    Permitted cfg g lcfg r (y :: T) p := by
  obtain ⟨T₁, T₂, st, h', rfl, h1, h2, h3, h4, hT₂⟩ := h
  refine ⟨T₁, y :: T₂, st, h', rfl, h1, h2, h3, h4, fun q hq => ?_⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hk
  · exact hT₂ q hq

/-- **Every permit was earned** (`DUR-29`), restating `Lifecycle.permit_origin` on the layer. Each live permit is an
honest node's, recorded at an earlier admitted rung assembly over the layer's possession, with no step since that
ended the node's permits or consumed them (`ReceiptLifecycle.Permitted`). -/
@[req "DUR-29"]
theorem permit_origin {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {p : Lifecycle.Permit} (hp : p ∈ st.ls.perm) :
    p.node ∈ honest ∧ Permitted cfg g lcfg r T p := by
  induction hx with
  | init st h => rw [h.1.2.1] at hp; cases hp
  | @next T st s lab ha hl hx ih =>
    rw [apply_perm] at hp
    cases s with
    | base b =>
      obtain ⟨b', hb'⟩ := mapStep_base g lcfg st b
      rw [hb'] at hp
      obtain ⟨hp, hk⟩ := List.mem_filter.1 hp
      obtain ⟨hi, hP⟩ := ih hp
      refine ⟨hi, hP.cons _ ?_⟩
      show Lifecycle.keeps r p.node p.cid st.ls (mapStep g lcfg st (.base b)) = true
      rw [hb']
      exact hk
    | send j env cid m =>
      simp only [mapStep, Lifecycle.permAfter] at hp
      obtain ⟨hp, hk⟩ := List.mem_filter.1 hp
      obtain ⟨hi, hP⟩ := ih hp
      exact ⟨hi, hP.cons _ hk⟩
    | assemble j cid m =>
      simp only [mapStep, Lifecycle.permAfter] at hp
      cases hg : rungAt (st.ls.cs.sw.fed.worlds j).node cid m with
      | none =>
        simp only [hg] at hp
        obtain ⟨hi, hP⟩ := ih hp
        exact ⟨hi, hP.cons _ rfl⟩
      | some gr =>
        cases hb : st.ls.cs.sw.obs j with
        | none =>
          simp only [hg, hb] at hp
          obtain ⟨hi, hP⟩ := ih hp
          exact ⟨hi, hP.cons _ rfl⟩
        | some b =>
          simp only [hg, hb] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · simp only [admits, mapStep, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at ha
            obtain ⟨⟨hi, hok⟩, hu⟩ := ha
            exact ⟨hi, T, [], st, lab, rfl, hok, by simpa using hu, hb, ⟨gr, hg, rfl⟩, by simp⟩
          · obtain ⟨hi, hP⟩ := ih hp
            exact ⟨hi, hP.cons _ rfl⟩

theorem sentAt_not_escape {r : Rules} {cs : RungAssembly.State} {b : Sweep.Step}
    (hk : Lifecycle.kernelSendOk cs b = true) {q : Nat × Bool × Tx} (hq : q ∈ Lifecycle.sentAt r cs.sw b) :
    q.2.1 = false := by
  obtain ⟨j, env, cid, p, rfl, hp, rfl⟩ := Lifecycle.mem_sentAt hq
  obtain ⟨c, hc, rfl, -⟩ := Lifecycle.sentBy_send hp
  have hcm := List.mem_of_find?_eq_some hc
  have hid : c.id = cid := by simpa using List.find?_some hc
  simp only [Lifecycle.kernelSendOk, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    not_and] at hk
  cases he : c.isEscape
  · rfl
  · exact absurd he (hk c hcm hid)

/-- **No send across a lifetime** (`DUR-29`, `DUR-31`), restating `Lifecycle.submitted_origin` on the layer. Each
Escape entry of the submission history, node `i` and transaction `tx`, was added at a rung's send by honest node `i`,
at a step where `tx` is rung `m` of its Escape-role resident under the id, which the send's own state and instant
re-authorize; the send used a live permit `p` of node `i` for that rung and txid whose observation passed `DUR-31`'s
classification, recorded at an earlier admitted assembly of that rung and txid by node `i` with no step between that
ended node `i`'s permits, birthed a record under the id at node `i`, settled a rung of that Escape there, or consumed
them (`ReceiptLifecycle.Permitted`). No kernel send adds one. -/
@[req "DUR-29"]
theorem submitted_origin {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat} {tx : Tx} (h : (i, true, tx) ∈ st.ls.subs) :
    i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid m lab, T = T₂ ++ (st₀, .send i env cid m, lab) :: T₁ ∧
      ∃ c gr p, escapeAt (st₀.ls.cs.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some gr ∧ gr.tx = tx ∧
        due r env (st₀.ls.cs.sw.fed.worlds i).node c = true ∧
        releaseAuthorized r (st₀.ls.cs.sw.fed.worlds i).node c = true ∧
        p ∈ st₀.ls.perm ∧ p.node = i ∧ p.cid = cid ∧ p.rung = m ∧ p.txid = gr.tx.id ∧
        Lifecycle.quiet p.obs c m = true ∧ Permitted cfg g lcfg r T₁ p := by
  induction hx with
  | init st h0 => rw [h0.1.2.2.2] at h; cases h
  | @next T st s lab ha hl hx ih =>
    have lift (h : (i, true, tx) ∈ st.ls.subs) : i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid m lab',
        (st, s, lab) :: T = T₂ ++ (st₀, .send i env cid m, lab') :: T₁ ∧
        ∃ c gr p, escapeAt (st₀.ls.cs.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some gr ∧ gr.tx = tx ∧
          due r env (st₀.ls.cs.sw.fed.worlds i).node c = true ∧
          releaseAuthorized r (st₀.ls.cs.sw.fed.worlds i).node c = true ∧
          p ∈ st₀.ls.perm ∧ p.node = i ∧ p.cid = cid ∧ p.rung = m ∧ p.txid = gr.tx.id ∧
          Lifecycle.quiet p.obs c m = true ∧ Permitted cfg g lcfg r T₁ p := by
      obtain ⟨hi, T₁, T₂, st₀, env, cid, m, lab', rfl, rest⟩ := ih h
      exact ⟨hi, T₁, (st, s, lab) :: T₂, st₀, env, cid, m, lab', rfl, rest⟩
    rw [apply_subs] at h
    cases s with
    | assemble j cid m => exact lift h
    | base b =>
      have hk : Lifecycle.kernelSendOk st.ls.cs (match mapStep g lcfg st (.base b) with
          | .base b' => b' | _ => b) = true := by
        cases b with
        | fed s =>
          simp only [admits, mapStep, Bool.and_eq_true] at ha
          exact ha.2
        | chain b' =>
          simp only [admits, mapStep, Bool.and_eq_true] at ha
          exact ha.2
        | observe j b' =>
          simp only [admits, mapStep, Bool.and_eq_true] at ha
          exact ha.2
      have hm : ∃ b', mapStep g lcfg st (.base b) = .base b' ∧ Lifecycle.kernelSendOk st.ls.cs b' = true := by
        cases b with
        | fed s => exact ⟨_, rfl, hk⟩
        | chain b' => exact ⟨_, rfl, hk⟩
        | observe j b' => exact ⟨_, rfl, hk⟩
      obtain ⟨b', hb', hk'⟩ := hm
      rw [hb'] at h
      simp only [Lifecycle.subsAfter, List.mem_append] at h
      rcases h with h | h
      · have := sentAt_not_escape hk' h
        cases this
      · exact lift h
    | send j env cid m =>
      simp only [mapStep, Lifecycle.subsAfter] at h
      cases hg : rungAt (st.ls.cs.sw.fed.worlds j).node cid m with
      | none => simp only [hg] at h; exact lift h
      | some gr =>
        simp only [hg] at h
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq, true_and] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [admits, mapStep, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨⟨hi, hok⟩, hperm⟩ := ha
          obtain ⟨c, g', hc, hg', -, hdue, hauth⟩ := RungAssembly.sendOk_iff.1 hok
          rw [RungAssembly.rungAt_of hc, hg'] at hg
          simp only [Option.some.injEq] at hg
          subst hg
          simp only [Lifecycle.sendOk, hc, hg', Lifecycle.permitOk, List.any_eq_true, Bool.and_eq_true,
            beq_iff_eq] at hperm
          obtain ⟨p, hp, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩ := hperm
          exact ⟨hi, T, [], st, env, cid, m, lab, rfl, c, g', p, hc, hg', rfl, hdue, hauth, hp, h1, h2, h3, h4, h5,
            (permit_origin hx hp).2⟩
        · exact lift h

/-! ## Under `Registration.preserve`: one record per id, and no send until a birth -/

theorem nodup_receive {env : Env} {n : Node} {m : Sighash} {i s cid : Nat} (hn : (n.cands.map Cand.id).Nodup) :
    ((ReceiptExpiry.receive env n m i s cid).cands.map Cand.id).Nodup := by
  unfold ReceiptExpiry.receive
  split
  · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hn
  · rw [ReceiptExpiry.receivePartial_stored]
    simp only [List.map_map]
    have : (Cand.id ∘ ReceiptExpiry.stored m i s cid) = Cand.id := by
      funext c; exact (ReceiptExpiry.stored_fields m i s cid c).1
    rw [this]; exact hn

/-- **One record per id on the layer** (`SPN-32`). Under `Registration.preserve`, at every state of a run each
honest node holds at most one record per id: the kernel's steps keep it (`Kernel.ids_nodup_step`), and an eviction
only removes records. -/
@[req "SPN-32"]
theorem ids_nodup {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} (hr : r.registration = .preserve)
    {honest : List Nat} {T : Trace} {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat}
    (hi : i ∈ honest) : ((st.ls.cs.sw.fed.worlds i).node.cands.map Cand.id).Nodup := by
  induction hx with
  | init st h => rw [(h.1.1.1.1.2.2 i hi).2.2.2.1]; exact List.nodup_nil
  | @next T st s lab ha hl hx ih =>
    cases s with
    | base b =>
      cases b with
      | fed s =>
        show (((xapply g lcfg r st.lf s).fed.worlds i).node.cands.map Cand.id).Nodup
        cases s with
        | deliverPartial j env x =>
          by_cases hij : i = j
          · subst hij
            simp only [xapply, if_true]
            exact nodup_receive ih
          · rw [xapply_other g lcfg r st.lf _ rfl hij]; exact ih
        | _ =>
          show (((lapply g lcfg r st.lf _).fed.worlds i).node.cands.map Cand.id).Nodup
          rw [lapply_fed]
          cases hact : Federation.actor (kernelStep g lcfg st.lf _) with
          | none => rw [Federation.apply_no_actor r _ _ hact i]; exact ih
          | some a =>
            obtain ⟨j, env, e⟩ := a
            rw [Federation.apply_of_actor r _ _ hact i]
            split
            · next hij => subst hij; exact ids_nodup_step hr env _ e ih
            · exact ih
      | chain b => rw [fed_nonfed (by simp)]; exact ih
      | observe j b => rw [fed_nonfed (by simp)]; exact ih
    | assemble j cid m => rw [fed_nonfed (by simp)]; exact ih
    | send j env cid m => rw [fed_nonfed (by simp)]; exact ih

theorem eq_of_nodup_id : ∀ {l : List Cand}, (l.map Cand.id).Nodup → ∀ {a b : Cand}, a ∈ l → b ∈ l →
    a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hn, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hx : ∀ {y : Cand}, y ∈ l → y.id ≠ x.id := fun hy he => hn.1 (List.mem_map.2 ⟨_, hy, he⟩)
    rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
    · rw [h1, h2]
    · exact absurd (by rw [← hab, h1]) (hx h2)
    · exact absurd (by rw [hab, h2]) (hx h1)
    · exact eq_of_nodup_id hn.2 h1 h2 hab

/-- With one record per id, an eviction leaves no record under the id. -/
@[req "NCH-24"]
theorem evict_clears {env : Env} {n : Node} {cid : Nat} (hn : (n.cands.map Cand.id).Nodup)
    (he : evicts env n cid = true) : (ReceiptExpiry.evict env n cid).cands.countP (·.id == cid) = 0 := by
  obtain ⟨c₀, hf, hk1, hk2⟩ := ReceiptExpiry.evicts_strict he
  have hc₀ := List.mem_of_find?_eq_some hf
  have hid₀ : c₀.id = cid := by simpa using List.find?_some hf
  rw [List.countP_eq_zero]
  intro c hc hcid
  have hcid' : c.id = cid := by simpa using hcid
  obtain ⟨hcm, hor⟩ := ReceiptExpiry.mem_evict.1 hc
  rcases hor with hne | hkeep
  · exact hne hcid'
  · have hcc : c = c₀ := eq_of_nodup_id hn hcm hc₀ (by rw [hcid', hid₀])
    subst hcc
    simp [ReceiptExpiry.keepsAt, hk1, hk2] at hkeep

/-- Where node `i` holds no record under `cid`, no send under it is admitted. -/
@[req "DUR-31"]
theorem absent_refuses_send {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {st : State}
    {T : Trace} {i cid : Nat} (h0 : fcount st.ls.cs.sw.fed i cid = 0) (env : Env) (m : Nat) :
    admits cfg g lcfg r honest st T (.send i env cid m) = false := by
  have hn : escapeAt (st.ls.cs.sw.fed.worlds i).node cid = none := by
    unfold escapeAt
    rw [List.find?_eq_none]
    intro c hc hce
    unfold fcount at h0
    rw [List.countP_eq_zero] at h0
    simp only [Bool.and_eq_true] at hce
    exact h0 c hc hce.1
  simp [admits, mapStep, Lifecycle.sendOk, hn]

/-- An invariant of the states along a stretch of a run: holding after its first step and kept by every later step,
it holds at the end. -/
theorem along {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} (P : State → Prop) :
    ∀ {T : Trace} {st : State}, Execution cfg g lcfg r honest T st →
      ∀ {T₁ T₂ : Trace} {st₀ : State} {s₀ : Step} {h₀ : Option Nat}, T = T₂ ++ (st₀, s₀, h₀) :: T₁ →
        P (apply cfg.lc.pre.sweep.keys g lcfg r st₀ s₀ h₀) →
        (∀ q ∈ T₂, P q.1 → P (apply cfg.lc.pre.sweep.keys g lcfg r q.1 q.2.1 q.2.2)) → P st := by
  intro T st hx
  induction hx with
  | init st h => intro T₁ T₂ st₀ s₀ h₀ hT; cases T₂ <;> cases hT
  | @next T st s lab ha hl hx ih =>
    intro T₁ T₂ st₀ s₀ h₀ hT hP hstep
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact hP
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      exact hstep _ (List.mem_cons_self ..) (ih hT hP fun q hq => hstep q (List.mem_cons_of_mem _ hq))

/-- A step of a run was admitted at its own state, after a reachable history. -/
theorem prefix_exec {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} :
    ∀ {T : Trace} {st : State}, Execution cfg g lcfg r honest T st →
      ∀ {T₂ T₁ : Trace} {st₀ : State} {s : Step} {h : Option Nat}, T = T₂ ++ (st₀, s, h) :: T₁ →
        Execution cfg g lcfg r honest T₁ st₀ ∧ admits cfg g lcfg r honest st₀ T₁ s = true := by
  intro T st hx
  induction hx with
  | init st h => intro T₂ T₁ st₀ s h' hT; cases T₂ <;> cases hT
  | next s' h' ha hl hx ih =>
    intro T₂ T₁ st₀ s h hT
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx, ha⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      exact ih hT.2

/-- **No send under an evicted id until a birth** (`DUR-29`, `DUR-31`, `NCH-24`). Under `Registration.preserve`,
after a delivery at honest node `i` whose lookup evicts on `x.cid`, and over every later step that births no record
under that id at node `i`, node `i` holds no record under it and no send under it is admitted; a birth ends the old
permits (`ReceiptLifecycle.born_ends_permits`). -/
@[req "DUR-31"]
theorem no_send_until_birth {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} (hr : r.registration = .preserve)
    {honest : List Nat} {T : Trace} {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest)
    {T₁ T₂ : Trace} {st₀ : State} {env : Env} {x : Exp} {h₀ : Option Nat}
    (hT : T = T₂ ++ (st₀, .base (.fed (.deliverPartial i env x)), h₀) :: T₁)
    (he : evictsAt st₀.lf (.deliverPartial i env x) = true)
    (hb : ∀ q ∈ T₂, born cfg.lc.pre.sweep.keys g lcfg r q.1 q.2.1 q.2.2 i x.cid = false) :
    fcount st.ls.cs.sw.fed i x.cid = 0 ∧ ∀ env' m, admits cfg g lcfg r honest st T (.send i env' x.cid m) = false := by
  have h0 : fcount st.ls.cs.sw.fed i x.cid = 0 := by
    refine along (fun st' => fcount st'.ls.cs.sw.fed i x.cid = 0) hx hT ?_ ?_
    · have hn := ids_nodup hr (prefix_exec hx hT).1 hi
      show fcount (xapply g lcfg r st₀.lf (.deliverPartial i env x)).fed i x.cid = 0
      unfold fcount
      simp only [xapply, if_true]
      show (ReceiptExpiry.receive env (st₀.ls.cs.sw.fed.worlds i).node x.msg x.input x.signer x.cid).cands.countP _ = 0
      have he' : evicts env (st₀.ls.cs.sw.fed.worlds i).node x.cid = true := he
      unfold ReceiptExpiry.receive
      rw [if_pos he']
      exact evict_clears hn he'
    · intro q hq hq0
      have := hb q hq
      simp only [born, decide_eq_false_iff_not, Nat.not_lt] at this
      exact Nat.le_zero.1 (hq0 ▸ this)
  exact ⟨h0, fun env' m => absent_refuses_send h0 env' m⟩

/-- **A re-registration after an eviction needs an earlier sample** (`NCH-24`, `SPN-32`). The record an eviction
removes had its expiry passed at the delivery's effective time; a request signing that expiry, taken at an effective
time no earlier, is not registered: `Kernel.accept` leaves the registry as it was. A claw-back is outside this
statement. -/
@[req "NCH-24"]
theorem reregister_refused {env : Env} {n : Node} {cid : Nat} (he : evicts env n cid = true) :
    ∃ c ∈ n.cands, c.id = cid ∧ ∀ (r : Rules) (env' : Env), env.eff.notAfter env'.eff = true →
      ∀ (n' : Node) (acid : Nat) (d : Bool) (sp es : Cand), (accept r env' n' acid d c.expiry sp es).cands = n'.cands := by
  obtain ⟨c, hf, hk, -⟩ := ReceiptExpiry.evicts_strict he
  refine ⟨c, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ?_⟩
  intro r env' hle n' acid d sp es
  have hk' : env'.eff.atOrBefore c.expiry = false := Clocks.Effective.not_atOrBefore_weaken hk hle
  unfold accept
  split
  · simp
  · have : Clocks.Mono.deadline env'.mono c.expiry env'.eff = none := by
      simp only [Clocks.Effective.atOrBefore, decide_eq_false_iff_not] at hk'
      simp only [Clocks.Mono.deadline]
      rw [if_neg hk']
    simp only [this]

/-! ## Retention apart from authority -/

theorem live_of {env : Env} {n : Node} {cid : Nat} (he : evicts env n cid = false)
    (hr : n.cands.any (·.id == cid) = true) : lookup env n cid = .live := by
  unfold evicts at he
  unfold lookup at he ⊢
  cases hf : n.cands.find? (·.id == cid) with
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨c, hc, hid⟩ := List.any_eq_true.1 hr
    exact absurd hid (hf c hc)
  | some c =>
    rw [hf] at he
    simp only at he ⊢
    split
    · rfl
    · next hk => simp [hk] at he

theorem actor_receive {honest : List Nat} {g : Guards} {lcfg : Config} {F : LFed} {s : Federation.Step}
    (ha : Federation.admits honest F.fed s = true) {j : Nat} {env : Env} {m : Sighash} {k sg cid : Nat}
    (hact : Federation.actor (kernelStep g lcfg F s) = some (j, env, .receivePartial m k sg cid)) :
    ∃ x : Exp, s = .deliverPartial j env x ∧ x.msg = m ∧ x.input = k ∧ x.signer = sg ∧ x.cid = cid := by
  cases s with
  | deliverPartial i env' x =>
    simp only [kernelStep, Federation.actor, Option.some.injEq, Prod.mk.injEq, Event.receivePartial.injEq] at hact
    obtain ⟨rfl, rfl, h1, h2, h3, h4⟩ := hact
    exact ⟨x, rfl, h1, h2, h3, h4⟩
  | process i env' e =>
    simp only [kernelStep, Federation.actor, Option.some.injEq, Prod.mk.injEq] at hact
    obtain ⟨rfl, rfl, he⟩ := hact
    cases e with
    | accept cid' d E sp es =>
      simp only [kernelEvent] at he
      split at he <;> cases he
    | receivePartial m' k' s' c' =>
      simp [Federation.admits, Federation.ownEvent] at ha
    | _ => simp [kernelEvent] at he
  | deliver i env' msg => simp [kernelStep, Federation.actor] at hact
  | _ => simp [kernelStep, Federation.actor] at hact

/-- **A kept record came through a live receipt** (`NCH-24`, `NCH-25`, `DUR-28`). Each record node `i` keeps was
stored at an earlier admitted delivery to node `i`, whose lookup at its own sample was live and whose store test
passed, with no step since that birthed a record under its id at node `i`. Retention is local: an eviction or a birth
can remove it, while every exposure row and inventory partial stays (`ReceiptLifecycle.history_kept`). -/
@[req "NCH-25"]
theorem kept_origin {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat} {p : Nat × Authority.Sig}
    (hp : p ∈ st.store i) :
    ∃ T₁ T₂ st₀ env x h, T = T₂ ++ (st₀, .base (.fed (.deliverPartial i env x)), h) :: T₁ ∧
      lookup env (st₀.ls.cs.sw.fed.worlds i).node x.cid = .live ∧
      VariantReceipt.storable cfg.lc.pre.sweep.keys (st₀.ls.cs.sw.fed.worlds i).node x.msg x.input x.signer x.cid h =
        true ∧
      p = (x.cid, { msg := x.msg, input := x.input, signer := x.signer }) ∧
      ∀ q ∈ T₂, born cfg.lc.pre.sweep.keys g lcfg r q.1 q.2.1 q.2.2 i p.1 = false := by
  induction hx with
  | init st h => rw [h.2.2 i] at hp; cases hp
  | @next T st s lab ha hl hx ih =>
    have lift (hp : p ∈ st.store i) (hb : born cfg.lc.pre.sweep.keys g lcfg r st s lab i p.1 = false) :
        ∃ T₁ T₂ st₀ env x h, (st, s, lab) :: T = T₂ ++ (st₀, .base (.fed (.deliverPartial i env x)), h) :: T₁ ∧
          lookup env (st₀.ls.cs.sw.fed.worlds i).node x.cid = .live ∧
          VariantReceipt.storable cfg.lc.pre.sweep.keys (st₀.ls.cs.sw.fed.worlds i).node x.msg x.input x.signer
            x.cid h = true ∧
          p = (x.cid, { msg := x.msg, input := x.input, signer := x.signer }) ∧
          ∀ q ∈ T₂, born cfg.lc.pre.sweep.keys g lcfg r q.1 q.2.1 q.2.2 i p.1 = false := by
      obtain ⟨T₁, T₂, st₀, env, x, h, rfl, h1, h2, h3, h4⟩ := ih hp
      refine ⟨T₁, (st, s, lab) :: T₂, st₀, env, x, h, rfl, h1, h2, h3, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hb
      · exact h4 q hq
    have unmoved (hw : (apply cfg.lc.pre.sweep.keys g lcfg r st s lab).ls.cs.sw.fed.worlds i =
        st.ls.cs.sw.fed.worlds i) (k : Nat) : born cfg.lc.pre.sweep.keys g lcfg r st s lab i k = false := by
      simp [born, fcount, hw]
    cases s with
    | base b =>
      cases b with
      | fed s =>
        change p ∈ xstore cfg.lc.pre.sweep.keys g lcfg r st.vf s lab i at hp
        unfold xstore at hp
        split at hp
        · next j env e hact =>
          split at hp
          · next hij =>
            subst hij
            obtain ⟨hp, hf⟩ := List.mem_filter.1 hp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
            have hb : born cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed s)) lab i p.1 = false := hf.2
            rcases mem_addNew hp with hp | hp
            · exact lift hp hb
            · split at hp
              · cases hp
              · next hev =>
                obtain ⟨m, k, sg, cid, rfl, hs, rfl⟩ := mem_arrival hp
                have hadm := admits_fed ha
                rw [show st.ls.cs.sw.fed = st.vf.lf.fed from rfl] at hadm
                obtain ⟨x, rfl, rfl, rfl, rfl, rfl⟩ := actor_receive hadm hact
                have hres : (st.ls.cs.sw.fed.worlds i).node.cands.any (·.id == x.cid) = true := by
                  obtain ⟨-, c, hc, hid, -⟩ := VariantReceipt.storable_iff.1 hs
                  exact List.any_eq_true.2 ⟨c, hc, by simp [hid]⟩
                have hev' : evicts env (st.ls.cs.sw.fed.worlds i).node x.cid = false := by
                  simpa [evictsAt, State.vf, State.lf] using hev
                exact ⟨T, [], st, env, x, lab, rfl, live_of hev' hres, hs, rfl, by simp⟩
          · next hij =>
            refine lift hp (unmoved ?_ p.1)
            exact xapply_other g lcfg r st.lf s hact hij
        · next hact =>
          refine lift hp (unmoved ?_ p.1)
          exact xapply_none g lcfg r st.lf s hact i
      | chain b =>
        rw [show (apply _ g lcfg r st (.base (.chain b)) lab).store = st.store from rfl] at hp
        exact lift hp (unmoved (by rw [fed_nonfed (by simp)]) p.1)
      | observe j b =>
        rw [show (apply _ g lcfg r st (.base (.observe j b)) lab).store = st.store from rfl] at hp
        exact lift hp (unmoved (by rw [fed_nonfed (by simp)]) p.1)
    | assemble j cid m =>
      rw [show (apply _ g lcfg r st (.assemble j cid m) lab).store = st.store from rfl] at hp
      exact lift hp (unmoved (by rw [fed_nonfed (by simp)]) p.1)
    | send j env cid m =>
      rw [show (apply _ g lcfg r st (.send j env cid m) lab).store = st.store from rfl] at hp
      exact lift hp (unmoved (by rw [fed_nonfed (by simp)]) p.1)

/-! ## Assembly and release -/

/-- **What a rung's assembly established** (`DUR-28`, `DUR-29`), restating `ClassAssembly.assemble_sound` over the
layer's possession: an observation and an Escape-role resident under the id, the assembled rung at index `m` at or
below its latch with its own quorum and no rung above it at or below the latch with one, and that rung's coverage,
exact fee, ancestry as a replacement of a resident lower rung, and package verdict (`ClassAssembly.rung_sound`). -/
@[req "DUR-29"]
theorem assemble_sound {cfg : Cfg} {st : State} {L : ClassAssembly.LTrace} {i cid m : Nat}
    (h : assembleOk cfg st L i cid m = true) :
    ∃ c b gr, escapeAt (st.ls.cs.sw.fed.worlds i).node cid = some c ∧ st.ls.cs.sw.obs i = some b ∧
      c.ladder[m]? = some gr ∧ m ≤ c.track.latch ∧
      Authority.quorum cfg.lc.pre.sweep.keys (st.ls.cs.sw.fed.worlds i).node.t gr.tx
        ((heldAt st i).filter fun s => s.msg.1 == gr.tx.id) = true ∧
      (∀ k, m < k → k ≤ c.track.latch →
        Ladder.quorumAt cfg.lc.pre.sweep.keys (st.ls.cs.sw.fed.worlds i).node.t c.ladder (heldAt st i) k = false) ∧
      Ladder.coveredTx cfg.lc.pre.sweep (Ladder.passAt cfg.lc.pre.sweep (ClassAssembly.readAt st.ls.cs L i c) b)
        gr.tx = true ∧
      PreRelease.feeOk cfg.lc.pre (Assembly.exactVsize cfg.asm gr.tx) gr.tx = true ∧
      (∃ anc, Package.validate cfg.lc.pre.sweep.ancestry cfg.lc.pre.sweep.creator
        (Sweep.snapshot (ClassAssembly.readAt st.ls.cs L i c).A b) b.mempool (ClassAssembly.readAt st.ls.cs L i c).A
        (Sweep.candidateOf gr.tx)
        (Ladder.replacesOf (c.ladder.map (·.tx)) (PreRelease.membership b (c.ladder.map (·.tx))) m) =
          .admitted anc) ∧
      Assembly.packageOk cfg.asm b gr.tx = true := by
  unfold assembleOk at h
  cases hc : escapeAt (st.ls.cs.sw.fed.worlds i).node cid with
  | none => simp [hc] at h
  | some c =>
    cases hb : st.ls.cs.sw.obs i with
    | none => simp [hc, hb] at h
    | some b =>
      simp only [hc, hb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨gr, hg, hle, hq, habove, hcov, hfee, hanc, hpk⟩ :=
        ClassAssembly.rung_sound (ClassAssembly.txs_readAt st.ls.cs L i c) h.1 h.2
      exact ⟨c, b, gr, rfl, rfl, hg, hle, hq, habove, hcov, hfee, hanc, hpk⟩

/-- **What an inherited assembly established** (`SPN-39`), restating `ClassAssembly.guard_sound` over the layer's
possession. At an admitted assembly of commitment `cid` at node `i`, each resident `c` under `cid` finds an
observation and passed its check there: an Escape-role resident as the finalization of rung 0 with rung 0's
`Assembly.rungCheck`, every other resident its class's `Assembly.checkAt`. -/
@[req "SPN-39"]
theorem guard_sound {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {st : State}
    {T : Trace} {i : Nat} {env : Env} {cid : Nat}
    (ha : admits cfg g lcfg r honest st T (.base (.fed (.process i env (.packageAccepted cid)))) = true)
    {c : Cand} (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (hid : c.id = cid) :
    ∃ b, st.ls.cs.sw.obs i = some b ∧
      (c.isEscape = true → finalAt cfg st i c = some 0 ∧
        Assembly.rungCheck cfg.asm (ClassAssembly.readAt st.ls.cs (cls g lcfg T) i c) b c (heldAt st i) 0 = true) ∧
      (c.isEscape = false → Assembly.checkAt cfg.asm (Sweep.authorizedAt st.ls.cs.sw (ClassAssembly.sweepT (cls g lcfg T)) i)
        (Assembly.clawTxsAt st.ls.cs.sw (ClassAssembly.sweepT (cls g lcfg T)) i) (st.ls.cs.sw.fed.worlds i).node
        (heldAt st i) b c = true) := by
  simp only [admits, mapStep, kernelStep, kernelEvent, guard, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne] at ha
  have hk : candOk cfg st (cls g lcfg T) i c = true := by
    rcases ha.1.1.2 c hc with h | h
    · exact absurd hid h
    · exact h
  unfold candOk at hk
  cases hb : st.ls.cs.sw.obs i with
  | none => rw [hb] at hk; cases hk
  | some b =>
    rw [hb] at hk
    refine ⟨b, rfl, fun he => ?_, fun he => ?_⟩
    · simp only [he, if_true, Bool.and_eq_true, beq_iff_eq] at hk
      exact hk
    · simp only [he] at hk
      exact hk

/-- **One step of the layer, at node `i`** (`DUR-27`), restating `Retained.sweep_step`. Each record after an
admitted step is one before it with the same registration-owned fields, a floor no lower and, while the earlier
latch is on the ladder, a latch no lower and on the ladder; or a record born at the step, with a fresh release
state. An evicting delivery only removes records. -/
theorem sweep_step {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {st : State}
    {T : Trace} {s : Step} {h : Option Nat} (ha : admits cfg g lcfg r honest st T s = true) (i : Nat) {c : Cand}
    (hc : c ∈ ((apply cfg.lc.pre.sweep.keys g lcfg r st s h).ls.cs.sw.fed.worlds i).node.cands) :
    (∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
        d.track.floor ≤ c.track.floor ∧
        (d.track.latch < d.ladder.length → d.track.latch ≤ c.track.latch ∧ c.track.latch < c.ladder.length)) ∨
      (c.track = {} ∧ born cfg.lc.pre.sweep.keys g lcfg r st s h i c.id = true) := by
  have same (d : Cand) (hd : d ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (h1 : Retained.reg d = Retained.reg c)
      (h2 : d.track = c.track) :
      ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
        d.track.floor ≤ c.track.floor ∧
        (d.track.latch < d.ladder.length → d.track.latch ≤ c.track.latch ∧ c.track.latch < c.ladder.length) :=
    ⟨d, hd, h1, by rw [h2]; exact Nat.le_refl _,
      fun hl => ⟨by rw [h2]; exact Nat.le_refl _, by rw [← h2, ← (Retained.reg_eq h1).2.2.1]; exact hl⟩⟩
  cases s with
  | assemble j cid m => rw [fed_nonfed (by simp)] at hc; exact .inl (same c hc rfl rfl)
  | send j env cid m => rw [fed_nonfed (by simp)] at hc; exact .inl (same c hc rfl rfl)
  | base b =>
    cases hev : evictsStep st (.base b) with
    | false =>
      have hls := apply_ls cfg.lc.pre.sweep.keys g lcfg r st (.base b) h hev
      have hb : ∃ b', mapStep g lcfg st (.base b) = .base b' ∧
          LadderRelease.admits cfg.lc honest st.ls.cs.sw (ClassAssembly.sweepT (cls g lcfg T)) b' = true := by
        cases b <;>
        · refine ⟨_, rfl, ?_⟩
          simp only [admits, mapStep, Bool.and_eq_true] at ha
          exact ha.1.1.1
      obtain ⟨b', hb', hlad⟩ := hb
      rw [hb'] at hls
      have hsw : (apply cfg.lc.pre.sweep.keys g lcfg r st (.base b) h).ls.cs.sw = Sweep.apply r st.ls.cs.sw b' := by
        rw [hls]; rfl
      rw [hsw] at hc
      rcases Retained.sweep_step hlad i hc with hl | ⟨h1, h2⟩
      · exact .inl hl
      · refine .inr ⟨h1, ?_⟩
        simp only [born, hsw, decide_eq_true_eq]
        exact h2
    | true =>
      cases b with
      | fed s =>
        cases s with
        | deliverPartial j env x =>
          have hc' : c ∈ ((xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds i).node.cands := hc
          by_cases hij : i = j
          · subst hij
            have he' : evicts env (st.ls.cs.sw.fed.worlds i).node x.cid = true := hev
            have hn : ((xapply g lcfg r st.lf (.deliverPartial i env x)).fed.worlds i).node =
                ReceiptExpiry.evict env (st.ls.cs.sw.fed.worlds i).node x.cid := by
              simp [xapply, sysRecv, ReceiptExpiry.wstep, ReceiptExpiry.receive, LFed.sys, State.lf, he']
            rw [hn] at hc'
            exact .inl (same c (ReceiptExpiry.mem_evict.1 hc').1 rfl rfl)
          · rw [xapply_other g lcfg r st.lf _ rfl hij] at hc'
            exact .inl (same c hc' rfl rfl)
        | _ => simp [evictsStep, evictsAt] at hev
      | chain b => simp [evictsStep] at hev
      | observe j b => simp [evictsStep] at hev

/-- **The latch stays on the retained ladder** (`DUR-27`), restating `Retained.latch_on_ladder` on the layer: at
every state of a run, each resident of an honest node has its latch below its own ladder's length. -/
@[req "DUR-27"]
theorem latch_on_ladder {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.ls.cs.sw.fed.worlds i).node.cands, c.track.latch < c.ladder.length := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.1.1.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | next s lab ha hl hx ih =>
    intro c hc
    rcases sweep_step ha i hc with ⟨d, hd, -, -, hl⟩ | ⟨h1, -⟩
    · exact (hl (ih d hd)).2
    · rw [h1]; exact Retained.ladder_pos c

/-- **One step of a lifetime on the layer** (`DUR-27`), restating `Retained.life_step`. At an admitted step that
births no record under `k` at an honest node, each record under `k` after it is one before it with the same
registration-owned fields, its floor and its latch no lower. -/
@[req "DUR-27"]
theorem life_step {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {s : Step} {h : Option Nat}
    (ha : admits cfg g lcfg r honest st T s = true) {k : Nat}
    (hb : born cfg.lc.pre.sweep.keys g lcfg r st s h i k = false) :
    ∀ c ∈ ((apply cfg.lc.pre.sweep.keys g lcfg r st s h).ls.cs.sw.fed.worlds i).node.cands, c.id = k →
      ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
        d.track.floor ≤ c.track.floor ∧ d.track.latch ≤ c.track.latch := by
  intro c hc hk
  rcases sweep_step ha i hc with ⟨d, hd, h1, h2, h3⟩ | ⟨-, h2⟩
  · exact ⟨d, hd, h1, h2, (h3 (latch_on_ladder hx hi d hd)).1⟩
  · subst hk; rw [hb] at h2; cases h2

/-- **The retained lifetime on the layer** (`DUR-27`, `SPN-38`), restating `Retained.lifetime_mono`. Over a stretch
of a run in which no step births a record under `k` at honest node `i`, every record under `k` at its end descends
from one at its start with the same registration-owned fields, whose release floor and rung latch it does not lower.
An eviction removes records and births none, so it does not end a lifetime by itself; a re-registration after it is
a birth. -/
@[req "DUR-27"]
theorem lifetime_mono {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : Trace} {st₀ : State} {s₀ : Step} {h₀ : Option Nat} (hT : T = T₂ ++ (st₀, s₀, h₀) :: T₁)
    (hb : ∀ y ∈ T₂ ++ [(st₀, s₀, h₀)], born cfg.lc.pre.sweep.keys g lcfg r y.1 y.2.1 y.2.2 i k = false) :
    ∀ c ∈ (st.ls.cs.sw.fed.worlds i).node.cands, c.id = k →
      ∃ d ∈ (st₀.ls.cs.sw.fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
        d.track.floor ≤ c.track.floor ∧ d.track.latch ≤ c.track.latch := by
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st s lab ha hl hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact life_step hx' hi ha (hb (st, s, lab) (by simp))
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      intro c hc hk
      obtain ⟨d, hd, h1, h2, h3⟩ := life_step hx' hi ha (hb _ (List.mem_cons_self ..)) c hc hk
      obtain ⟨e, he, g1, g2, g3⟩ :=
        ih hT (fun z hz => hb z (List.mem_cons_of_mem _ hz)) d hd (by rw [(Retained.reg_eq h1).1]; exact hk)
      exact ⟨e, he, g1.trans h1, Nat.le_trans g2 h2, Nat.le_trans g3 h3⟩

/-! ## The delivery's observation -/

/-- What a delivery shows: the receiver, the signer, the label, the answer, and the store's decisions only when the
lookup is live. -/
structure DObs where
  receiver : Nat
  signer : Nat
  label : Option Nat
  answer : Answer
  checks : Option VariantSilence.Checks
  deriving DecidableEq, Repr

/-- A step's delivery observation, taken on the state before it; none for a step that is not a delivery. -/
@[req "NCH-24"]
def dobs (keys : List Nat) (V : VFed) : Federation.Step → Option Nat → Option DObs
  | .deliverPartial i env x, h =>
    some { receiver := i, signer := x.signer, label := h, answer := answer env (V.lf.fed.worlds i).node x.cid,
           checks := if lookup env (V.lf.fed.worlds i).node x.cid = .live then
             some (VariantSilence.checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h)
             else none }
  | _, _ => none

/-- **The answer is the receipt's** (`NCH-24`): the receiver, the signer and the answer the observation carries are
those `ReceiptExpiry.xfobs` carries. -/
@[req "NCH-24"]
theorem dobs_answer (mk : Silence.Marker) (g : Guards) (lcfg : Config) (r : Rules) (peers keys : List Nat) (V : VFed)
    (s : Federation.Step) (h : Option Nat) :
    (dobs keys V s h).map (fun o => (o.receiver, o.signer, o.answer)) =
      (ReceiptExpiry.xfobs mk g lcfg r peers V.lf s).answer := by
  cases s <;> rfl

/-- **On a live lookup the decisions are the variant-bound store's** (`NCH-25`): the receiver, the signer, the label
and the decisions are `VariantSilence.storeObs`'s; on any other lookup the observation carries no decision. -/
@[req "NCH-25"]
theorem dobs_live (keys : List Nat) (V : VFed) (i : Nat) (env : Env) (x : Exp) (h : Option Nat) :
    (lookup env (V.lf.fed.worlds i).node x.cid = .live →
      (dobs keys V (.deliverPartial i env x) h).map (fun o => (o.receiver, o.signer, o.label, o.checks)) =
        (VariantSilence.storeObs keys V (.deliverPartial i env x) h).map
          (fun o => (o.receiver, o.signer, o.label, some o.checks))) ∧
      (lookup env (V.lf.fed.worlds i).node x.cid ≠ .live →
        (dobs keys V (.deliverPartial i env x) h).map (·.checks) = some none) := by
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · simp [dobs, VariantSilence.storeObs, hl]
  · simp [dobs, hl]

/-! ## Running a schedule -/

/-- A delivery's label after a state: that of the newest envelope of the partial sent so far, if any. -/
def labelFor (st : State) : Step → Option Nat
  | .base (.fed (.deliverPartial _ _ x)) => (st.envs.find? fun z => z.1 == x).bind (·.2)
  | _ => none

/-- A scheduled step's label: the one the schedule gives, or else `ReceiptLifecycle.labelFor`'s. -/
def labelOf (st : State) : Step × Option (Option Nat) → Option Nat
  | (s, none) => labelFor st s
  | (_, some h) => h

/-- A schedule run from a state, each step labelled by `ReceiptLifecycle.labelOf`. -/
def record (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) :
    Trace → State → List (Step × Option (Option Nat)) → Trace × State
  | T, st, [] => (T, st)
  | T, st, a :: ss =>
    record keys g lcfg r ((st, a.1, labelOf st a) :: T) (apply keys g lcfg r st a.1 (labelOf st a)) ss

/-- Every step of a schedule admitted where it is taken, with an admissible label. -/
def legal (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) :
    Trace → State → List (Step × Option (Option Nat)) → Bool
  | _, _, [] => true
  | T, st, a :: ss => admits cfg g lcfg r honest st T a.1 && labelOk st a.1 (labelOf st a) &&
      legal cfg g lcfg r honest ((st, a.1, labelOf st a) :: T)
        (apply cfg.lc.pre.sweep.keys g lcfg r st a.1 (labelOf st a)) ss

theorem execution_of_legal {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg g lcfg r honest T st) {ss : List (Step × Option (Option Nat))}
    (hl : legal cfg g lcfg r honest T st ss = true) :
    Execution cfg g lcfg r honest (record cfg.lc.pre.sweep.keys g lcfg r T st ss).1
      (record cfg.lc.pre.sweep.keys g lcfg r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons a ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next a.1 _ hl.1.1 hl.1.2 hx) hl.2

/-- A federation step the Hot budget does not refuse: `FedSilence.kernelStep` leaves it as it is. -/
def stands (g : Guards) (lcfg : Config) (st : State) : Step → Bool
  | .base (.fed s) => kernelStep g lcfg st.lf s == s
  | _ => true

theorem mapStep_stands {g : Guards} {lcfg : Config} {st : State} {s : Step} (h : stands g lcfg st s = true) :
    mapStep g lcfg st s = s := by
  cases s with
  | base b =>
    cases b with
    | fed s =>
      simp only [stands, beq_iff_eq] at h
      simp only [mapStep, h]
    | chain b => rfl
    | observe j b => rfl
  | assemble i cid m => rfl
  | send i env cid m => rfl

/-- Every step of a history quiet and standing: the history the lifecycle run takes is the layer's own steps. -/
def quietRun (g : Guards) (lcfg : Config) (r : Rules) (T : Trace) : Bool :=
  T.all fun a => Quiet g lcfg r a.1 a.2.1 && stands g lcfg a.1 a.2.1

theorem quietRun_quiet {g : Guards} {lcfg : Config} {r : Rules} {T : Trace} (h : quietRun g lcfg r T = true) :
    ∀ a ∈ T, Quiet g lcfg r a.1 a.2.1 = true := by
  intro a ha
  simp only [quietRun, List.all_eq_true, Bool.and_eq_true] at h
  exact (h a ha).1

theorem forget_stands {g : Guards} {lcfg : Config} {r : Rules} {T : Trace} (h : quietRun g lcfg r T = true) :
    forget g lcfg T = T.map fun a => (a.1.ls, a.2.1, a.2.2) := by
  unfold forget
  apply List.map_congr_left
  intro a ha
  simp only [quietRun, List.all_eq_true, Bool.and_eq_true] at h
  rw [mapStep_stands (h a ha).2]

end BtcPolicy.ReceiptLifecycle
