import BtcPolicy.ExpirySilence
import BtcPolicy.ReceiptLifecycle
/-! SILENCE over the receipt step of the lifecycle layer (`DUR-1`, `NCH-24`, `NCH-25`, `SPN-41`, `POL-18`), as
`docs/research/receipt-lifecycle-contract.md` fixes it in *The observer and SILENCE*. A layer beside the existing
definitions: no definition or theorem statement changes, and no kernel event is added.

**The operation.** `ReceiptLifecycle.xvapply`, the receipt step on the labelled ledgered state
`VariantSilence.VFed`: `VariantSilence.vapply` with `ReceiptExpiry.xapply` in place of `FedSilence.lapply`, so a
delivered partial is looked up at its own sample, evicts an expired candidate (answering `UNKNOWN_CANDIDATE` and
taking `POL-18`'s refund) or runs `Kernel.receivePartial`; nothing arrives in the store at an evicting delivery, and
the records under an id the step births at its acting node are dropped (`ReceiptLifecycle.xstore`).

**The observer.** `LifecycleSilence.XVObs`: `FedSilence.FObs`, the part `ReceiptExpiry.xfobs` computes (the acting
node's observation on the state the receipt leaves), with the delivery observation `ReceiptLifecycle.dobs`: at a
delivered partial the receiver, the signer, the label, the answer, and the store's decisions
(`VariantSilence.Checks`) only when the lookup is live, as the contract fixes it. `VariantSilence.checks` reports
found for any resident record, an expired one included; the answer, not `found`, tells a live lookup.

**The event alphabet.** The steps of `FedSilence.PStep`, each with one label (`VariantSilence.LStep`): a kernel input
at a node (a request or staged refusal carrying the PIN it presented, or a PIN-less kernel event), and every
federation step taken as it is in both runs (a process step, a relay's or a partial's delivery, an unstaged relay,
an emitted or injected relay, an extraction, a forgery).

**The walk.** `LifecycleSilence.xvwalk` is `FedSilence.walk` with `xvapply` and `xvobs`; its stop is `walk`'s word for
word: the first step that is not admitted, or whose acting node, in either run, is outside its own horizon
(`Silence.preHorizon`) at that step's own sample or receives a request shape `Silence.wfEvent` refuses. Its
`FedSilence.FObs` part with the answers is `ExpirySilence.xwalk` (`LifecycleSilence.xvwalk_xwalk`), and with no
evicting delivery its `FObs` part is `walk` (`LifecycleSilence.xvwalk_walk`).

**What is derived.** The two runs take one labelled schedule; that is the environmental premise, as in
`VariantSilence`. From the coupled states before a step (`VariantSilence.VCoupled`: `FedSilence.FCoupled`, one
envelope list, the same kept records at every honest node) and `FedSilence.FInv`, the proofs derive the lookup, the
eviction and the answer (`ExpirySilence.lookup_pub`, `ExpirySilence.evicts_pub`, `ExpirySilence.answer_pub`, through
`ExpirySilence.keepsAt_factor`), the refund (`ExpirySilence.sysRecv_coupled`), the store's decisions
(`VariantSilence.checks_pub`), the birth drop, which reads only record counts under an id
(`LifecycleSilence.count_pub`, `LifecycleSilence.bornAt_pub`), the records kept (`LifecycleSilence.xstore_pub`) and
the delivery observation (`LifecycleSilence.dobs_pub`). `LifecycleSilence.xvpstep_pub` puts them together for one
step; no equality of the states after a step is assumed.

**Results.** `LifecycleSilence.xvfed_silence`, `xvfed_silence_fresh`, `xvfed_silence_adaptive` and
`xvfed_silence_adaptive_fresh` are `VariantSilence.vfed_silence` and its siblings over `xvwalk`, with their premises.
`LifecycleSilence.xvfed_coupled` lifts the records and the Held projection over every reached pair. On a schedule
with no evicting delivery and no birth under a resident id, from states whose kept records are resident, the walk
is `VariantSilence.vwalk` joined with `ExpirySilence.xwalk`'s answers (`LifecycleSilence.xvwalk_vwalk`), and `vwalk` is
read back from it (`LifecycleSilence.xvwalk_split`), so no field `vwalk` compares is dropped there. The earlier results
keep their domains and are restated by none of these.

**Outside.** As for `FedSilence`: serialized bytes, the answer's wire encoding and its timing are not modelled, so
equal observations are equal shapes and decisions, not equal bytes, and response timing stays `F22`'s open finding.
The rung, assembly, send and chain steps of the lifecycle run, the pre-release and assembly public inputs, and the
claw-back log's lifecycle are not in this walk. -/

namespace BtcPolicy.LifecycleSilence

open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.ReceiptExpiry (xapply xfobs XObs evictsAt evicts lookup answer Answer Lookup unevicted)
open BtcPolicy.VariantSilence (VFed VCoupled VUEq LStep VObs StoreObs vobs vapply vwalk newEnvs node_pub)
open BtcPolicy.ReceiptLifecycle (fcount bornAt xstore xvapply rebirthAt Resident DObs dobs)
open BtcPolicy.VariantReceipt (arrival)

variable {r : Rules}

/-! ## The birth drop through the projection -/

/-- **A node's record count under an id is public.** -/
@[req "NCH-25"]
theorem count_pub {na nb : Node} (hn : pubNode r na = pubNode r nb) (cid : Nat) :
    na.cands.countP (·.id == cid) = nb.cands.countP (·.id == cid) := by
  have key : ∀ n : Node, n.cands.countP (·.id == cid) = (pubNode r n).cands.countP (·.id == cid) := by
    intro n
    simp only [pubNode, List.countP_map, Function.comp_def, pubCand_id]
  rw [key na, key nb, hn]

/-- **The two runs birth alike.** From one public projection of the acting node before the step and one after it,
the step births a record under an id in both runs or in neither: `ReceiptLifecycle.bornAt` reads only the node's
record counts under the id. -/
@[req "NCH-25"]
theorem bornAt_pub {g : Guards} {cfg : Config} {FA FB : LFed} {sA sB : Federation.Step} {i : Nat}
    (h0 : pubNode r (FA.fed.worlds i).node = pubNode r (FB.fed.worlds i).node)
    (h1 : pubNode r ((xapply g cfg r FA sA).fed.worlds i).node = pubNode r ((xapply g cfg r FB sB).fed.worlds i).node)
    (cid : Nat) : bornAt g cfg r FA sA i cid = bornAt g cfg r FB sB i cid := by
  unfold bornAt fcount
  rw [count_pub h0 cid, count_pub h1 cid]

/-! ## The store and the delivery observation -/

/-- The records at every honest node after one receipt step, from the arrival in both runs: nothing at an evicting
delivery, and the birth drop read through the projection. -/
theorem xstore_pub {keys : List Nat} {g : Guards} {cfg : Config} {honest : List Nat} {A B : VFed}
    (hc : VCoupled r honest A B) {sA sB : Federation.Step} (h : Option Nat)
    (h1 : FCoupled r honest (xapply g cfg r A.lf sA) (xapply g cfg r B.lf sB))
    (hact : (Federation.actor (kernelStep g cfg A.lf sA) = none ∧
        Federation.actor (kernelStep g cfg B.lf sB) = none) ∨
      ∃ i env eA eB, i ∈ honest ∧ Federation.actor (kernelStep g cfg A.lf sA) = some (i, env, eA) ∧
        Federation.actor (kernelStep g cfg B.lf sB) = some (i, env, eB) ∧
        (if evictsAt A.lf sA then [] else arrival keys (A.lf.fed.worlds i, env, eA, h)) =
          (if evictsAt B.lf sB then [] else arrival keys (B.lf.fed.worlds i, env, eB, h))) :
    ∀ j ∈ honest, xstore keys g cfg r A sA h j = xstore keys g cfg r B sB h j := by
  intro j hj
  unfold xstore
  rcases hact with ⟨ha, hb⟩ | ⟨i, env, eA, eB, hi, ha, hb, harr⟩
  · rw [ha, hb]; exact hc.store j hj
  · rw [ha, hb]
    dsimp only
    split
    · rw [hc.store i hi, harr]
      congr 1
      funext p
      rw [VariantSilence.resident_pub (node_pub h1 hi) p.1, bornAt_pub (node_pub hc.fed hi) (node_pub h1 hi) p.1]
    · exact hc.store j hj

/-- **A delivery is observed alike.** At an honest receiver inside its horizon in both runs, the delivery
observation is the same: the answer (`ExpirySilence.answer_pub`), whether the lookup is live
(`ExpirySilence.lookup_pub`) and, on a live lookup, the store's decisions (`VariantSilence.checks_pub`). -/
@[req "NCH-24"]
theorem dobs_pub (hdr : r.driverTime = .ratchet) (keys : List Nat) {honest : List Nat} {A B : VFed}
    (hc : VCoupled r honest A B) (hia : FInv r honest A.lf) (hib : FInv r honest B.lf) {i : Nat} (hi : i ∈ honest)
    (env : Env) (x : Exp) (h : Option Nat)
    (hpa : preHorizon r env (A.lf.fed.worlds i).node = true) (hpb : preHorizon r env (B.lf.fed.worlds i).node = true) :
    dobs keys A (.deliverPartial i env x) h = dobs keys B (.deliverPartial i env x) h := by
  have hn := node_pub hc.fed hi
  have hl := ExpirySilence.lookup_pub hdr hn (hia i hi) (hib i hi) hpa hpb x.cid
  have ha := ExpirySilence.answer_pub hdr hn (hia i hi) (hib i hi) hpa hpb x.cid
  have hk := VariantSilence.checks_pub keys (B.store i) hn x.msg x.input x.signer x.cid h
  simp only [dobs, hl, ha, hc.store i hi, hk]

/-! ## One step -/

/-- One step's observation: `FedSilence.FObs` as the receipt step leaves it, and the delivery observation. -/
structure XVObs where
  base : FObs
  delivery : Option DObs
  deriving DecidableEq, Repr

/-- One labelled step's observation, taken on the state before it. -/
def xvobs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) (V : VFed)
    (s : Federation.Step) (h : Option Nat) : XVObs :=
  { base := (xfobs mk g cfg r peers V.lf s).base, delivery := dobs keys V s h }

/-- **One labelled schedule step, in both runs.** From two coupled layer states, each carrying the invariant, a step
admitted in the first run with its acting node inside its horizon in both leaves two coupled layer states, keeps the
invariant, and is observed alike, the answer and the store's decisions on a live lookup included. At a delivery the
lookup, the eviction, the answer, the refund, the store's decisions, the birth drop and the records kept are
derived, not assumed. -/
@[req "DUR-1"]
theorem xvpstep_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers keys : List Nat}
    {A B : VFed} (hc : VCoupled r honest A B) (hia : FInv r honest A.lf) (hib : FInv r honest B.lf)
    (p : PStep) (h : Option Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (ha : Federation.admits honest A.lf.fed (p.step tbls₀) = true)
    (hpa : inside r A.lf (p.step tbls₀) = true) (hpb : inside r B.lf (p.step tbls₁) = true) :
    VCoupled r honest (xvapply keys g cfg r A (p.step tbls₀) h) (xvapply keys g cfg r B (p.step tbls₁) h) ∧
    FInv r honest (xvapply keys g cfg r A (p.step tbls₀) h).lf ∧
    FInv r honest (xvapply keys g cfg r B (p.step tbls₁) h).lf ∧
    xvobs mk g cfg r peers keys A (p.step tbls₀) h = xvobs mk g cfg r peers keys B (p.step tbls₁) h := by
  obtain ⟨h1, h2, h3, h4⟩ := ExpirySilence.xpstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr
    hc.fed hia hib p tbls₀ tbls₁ ha hpa hpb
  have main : newEnvs r g cfg A.lf (p.step tbls₀) = newEnvs r g cfg B.lf (p.step tbls₁) ∧
      (∀ j ∈ honest, xstore keys g cfg r A (p.step tbls₀) h j = xstore keys g cfg r B (p.step tbls₁) h j) ∧
      dobs keys A (p.step tbls₀) h = dobs keys B (p.step tbls₁) h := by
    cases p with
    | input i env x =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb h1 ⊢
      have hi := actor_honest ha rfl
      have h1' : FCoupled r honest (lapply g cfg r A.lf (.process i env (x.event (tbls₀ i))))
          (lapply g cfg r B.lf (.process i env (x.event (tbls₁ i)))) := h1
      obtain ⟨he, -⟩ := VariantSilence.process_layer (keys := keys) ht hd hr hcl hdr hc hia hib hi env x
        (tbls₀ i) (tbls₁ i) h hpa.1 hpb.1 hpa.2 h1'
      refine ⟨he, xstore_pub hc h h1 (.inr ⟨i, env, _, _, hi, rfl, rfl, ?_⟩), rfl⟩
      simp only [evictsAt, Bool.false_eq_true, ↓reduceIte]
      have hled : A.lf.leds i = B.lf.leds i := (hc.fed.node i hi).led
      rw [hled]
      exact VariantSilence.arrival_input keys g cfg env (B.lf.leds i) (node_pub hc.fed hi) h x (tbls₀ i) (tbls₁ i)
    | net s =>
      cases s with
      | process i env e =>
        simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb h1 ⊢
        have hi := actor_honest ha rfl
        have h1' : FCoupled r honest (lapply g cfg r A.lf (.process i env e)) (lapply g cfg r B.lf (.process i env e)) :=
          h1
        obtain ⟨he, -⟩ := VariantSilence.process_layer (keys := keys) ht hd hr hcl hdr hc hia hib hi env
          (.pinless e) (fun _ => false) (fun _ => false) h hpa.1 hpb.1 hpa.2 h1'
        refine ⟨he, xstore_pub hc h h1 (.inr ⟨i, env, _, _, hi, rfl, rfl, ?_⟩), rfl⟩
        simp only [evictsAt, Bool.false_eq_true, ↓reduceIte]
        have hled : A.lf.leds i = B.lf.leds i := (hc.fed.node i hi).led
        rw [hled]
        exact VariantSilence.arrival_input keys g cfg env (B.lf.leds i) (node_pub hc.fed hi) h (.pinless e)
          (fun _ => false) (fun _ => false)
      | deliver i env m =>
        simp only [PStep.step] at ha h1 ⊢
        exact ⟨rfl, xstore_pub hc h h1 (.inr ⟨i, env, _, _, actor_honest ha rfl, rfl, rfl, rfl⟩), rfl⟩
      | deliverPartial i env x =>
        simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb h1 ⊢
        have hi := actor_honest ha rfl
        have hn := node_pub hc.fed hi
        have hev := ExpirySilence.evicts_pub hdr hn (hia i hi) (hib i hi) hpa.1 hpb.1 x.cid
        refine ⟨rfl, xstore_pub hc h h1 (.inr ⟨i, env, _, _, hi, rfl, rfl, ?_⟩),
          dobs_pub hdr keys hc hia hib hi env x h hpa.1 hpb.1⟩
        rw [VariantSilence.arrival_pub keys hn env _ h]
        simp only [evictsAt, hev]
        rfl
      | unstaged i cid => exact ⟨rfl, xstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | emit i cid => exact ⟨rfl, xstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | inject m => exact ⟨rfl, xstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | extract j => exact ⟨rfl, xstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | forge x => exact ⟨rfl, xstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
  obtain ⟨he, hs, hdo⟩ := main
  refine ⟨⟨h1, ?_, hs⟩, h2, h3, ?_⟩
  · show newEnvs r g cfg A.lf (p.step tbls₀) ++ A.envs = newEnvs r g cfg B.lf (p.step tbls₁) ++ B.envs
    rw [he, hc.envs]
  · simp only [xvobs, h4, hdo]

/-! ## The walk and the relation -/

/-- `FedSilence.walk` over the receipt step: the same stop, with `ReceiptLifecycle.xvapply` and `xvobs`. -/
def xvwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : VFed → VFed → List LStep → List (XVObs × XVObs)
  | _, _, [] => []
  | A, B, (p, h) :: rest =>
    if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁) then
      (xvobs mk g cfg r peers keys A (p.step tbls₀) h, xvobs mk g cfg r peers keys B (p.step tbls₁) h) ::
        xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ (xvapply keys g cfg r A (p.step tbls₀) h)
          (xvapply keys g cfg r B (p.step tbls₁) h) rest
    else []

/-- The state pairs `xvwalk` reaches, one after each step it takes. -/
def xvreach (g : Guards) (cfg : Config) (r : Rules) (honest keys : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) :
    VFed → VFed → List LStep → List (VFed × VFed)
  | _, _, [] => []
  | A, B, (p, h) :: rest =>
    if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁) then
      (xvapply keys g cfg r A (p.step tbls₀) h, xvapply keys g cfg r B (p.step tbls₁) h) ::
        xvreach g cfg r honest keys tbls₀ tbls₁ (xvapply keys g cfg r A (p.step tbls₀) h)
          (xvapply keys g cfg r B (p.step tbls₁) h) rest
    else []

/-- A labelled schedule run through the receipt step. -/
def xvrun (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) :
    VFed → List (Federation.Step × Option Nat) → VFed
  | V, [] => V
  | V, (s, h) :: ss => xvrun keys g cfg r (xvapply keys g cfg r V s h) ss

/-- **SILENCE over the lifecycle layer's receipt step, under one fixed exogenous schedule.** `DUR-1`: "Every
observable a node emits MUST be identical between a normal-PIN and a duress-PIN request".

`VariantSilence.vfed_silence` over `ReceiptLifecycle.xvapply`: one labelled schedule, two enrolment families, two
coupled layer states, and the two runs emit equal `LifecycleSilence.XVObs`, the answer to each delivered partial and
the store's decisions on a live lookup included, at every step of `LifecycleSilence.xvwalk`, whose stop is
`FedSilence.walk`'s. An evicting delivery and a birth are inside the walk wherever the acting node is inside its
horizon in both runs. The premises are `vfed_silence`'s; nothing is assumed of the lookups, the store's decisions or
the records after any step. -/
@[req "DUR-1"]
theorem xvfed_silence {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), VCoupled r honest A B → FInv r honest A.lf →
      FInv r honest B.lf → ∀ y ∈ xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched, y.1 = y.2 := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hc hia hib y hy
    simp only [xvwalk] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', hobs⟩ :=
        xvpstep_pub (peers := peers) (keys := keys) hg ht hd hr hcl hdr hc hia hib p h tbls₀ tbls₁ ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hobs
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-- **The records and the Held projection, by induction over the reachable coupled states.** Every state pair the
walk reaches is coupled: one envelope list, the same records at every honest node after every eviction and birth, and
so the same Held projection (`VariantSilence.vheld_pub`). Each pair's coupling is derived from the pair before it. -/
@[req "DUR-28"]
theorem xvfed_coupled (g : Guards) (cfg : Config) (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    (honest keys : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), VCoupled r honest A B → FInv r honest A.lf →
      FInv r honest B.lf → ∀ y ∈ xvreach g cfg r honest keys tbls₀ tbls₁ A B sched,
        VCoupled r honest y.1 y.2 ∧ ∀ i ∈ honest, VariantSilence.vheld y.1 i = VariantSilence.vheld y.2 i := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hc hia hib y hy
    simp only [xvreach] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', -⟩ :=
        xvpstep_pub (mk := .committed) (peers := []) (keys := keys) rfl ht hd hr hcl hdr hc hia hib p h tbls₀ tbls₁
          ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hc', fun i hi => VariantSilence.vheld_pub hc' hi⟩
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-! ## The initial boundary -/

/-- The lookup reads no `unarmedT`, so neither does the eviction decision. -/
theorem evictsAt_u {A A' : LFed} (h : UEq A A') (s : Federation.Step) : evictsAt A s = evictsAt A' s := by
  cases s with
  | deliverPartial i env x =>
    obtain ⟨u, hu⟩ := VariantSilence.node_u h i
    simp only [evictsAt, hu]
    rfl
  | _ => rfl

theorem bornAt_u {g : Guards} {cfg : Config} {A A' : LFed} (h : UEq A A') (s : Federation.Step) (j cid : Nat) :
    bornAt g cfg r A s j cid = bornAt g cfg r A' s j cid := by
  unfold bornAt fcount
  rw [VariantSilence.cands_u h j, VariantSilence.cands_u (ExpirySilence.xapply_u (g := g) (cfg := cfg) (r := r) h s) j]

theorem xvapply_u {keys : List Nat} {g : Guards} {cfg : Config} {r : Rules} {A A' : VFed} (h : VUEq A A')
    (s : Federation.Step) (lab : Option Nat) :
    VUEq (xvapply keys g cfg r A s lab) (xvapply keys g cfg r A' s lab) := by
  have hv := VariantSilence.vapply_u (keys := keys) (g := g) (cfg := cfg) (r := r) h s lab
  obtain ⟨hu, -, hs⟩ := h
  have hl := ExpirySilence.xapply_u (g := g) (cfg := cfg) (r := r) hu s
  have hk : kernelStep g cfg A.lf s = kernelStep g cfg A'.lf s := by
    cases s with
    | process i env e => simp only [kernelStep, VariantSilence.leds_u hu i]
    | _ => rfl
  refine ⟨hl, hv.2.1, ?_⟩
  funext j
  show xstore keys g cfg r A s lab j = xstore keys g cfg r A' s lab j
  unfold xstore
  rw [hk]
  split
  · rename_i i env e _
    split
    · rw [hs, evictsAt_u hu s]
      have hw : A.lf.fed.worlds i = (withUnarmedT (A'.lf.sys i) (hu.2.2.2 i).choose).world :=
        congrArg Sys.world (hu.2.2.2 i).choose_spec
      have ha : arrival keys (A.lf.fed.worlds i, env, e, lab) = arrival keys (A'.lf.fed.worlds i, env, e, lab) := by
        rw [hw]; cases e <;> rfl
      rw [ha]
      congr 1
      funext p
      rw [VariantSilence.cands_u hl i, bornAt_u hu s i p.1]
    · rw [hs]
  · rw [hs]

theorem xvobs_u {mk : Marker} {g : Guards} {cfg : Config} {r : Rules} {peers keys : List Nat} {A A' : VFed}
    (h : VUEq A A') (s : Federation.Step) (lab : Option Nat) :
    xvobs mk g cfg r peers keys A s lab = xvobs mk g cfg r peers keys A' s lab := by
  obtain ⟨hu, -, hs⟩ := h
  have hb := ExpirySilence.xfobs_u (mk := mk) (g := g) (cfg := cfg) (r := r) (peers := peers) hu s
  have hd : dobs keys A s lab = dobs keys A' s lab := by
    cases s with
    | deliverPartial i env x =>
      obtain ⟨u, hw⟩ := VariantSilence.node_u hu i
      simp only [dobs, hs, hw]
      rfl
    | _ => rfl
  simp only [xvobs, hb, hd]

theorem xvwalk_u (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B A' B' : VFed), VUEq A A' → VUEq B B' →
      xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched =
        xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A' B' sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B A' B' ha hb
    obtain ⟨_, adA, inA, _⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) ha.1 (p.step tbls₀)
    obtain ⟨_, _, inB, _⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) hb.1 (p.step tbls₁)
    simp only [xvwalk, adA, inA, inB, xvobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) ha,
      xvobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) hb,
      ih _ _ _ _ (xvapply_u (g := g) (cfg := cfg) ha _ _) (xvapply_u (g := g) (cfg := cfg) hb _ _)]

/-- **`xvfed_silence` at every initial state the federation admits with its sweep flags clear**, with nothing sent
and nothing kept, as `VariantSilence.vfed_silence_fresh` states it. -/
@[req "DUR-1"]
theorem xvfed_silence_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) :
    ∀ (sched : List LStep),
      ∀ y ∈ xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ (VFed.init F) (VFed.init F) sched, y.1 = y.2 := by
  intro sched y hy
  rw [xvwalk_u mk g cfg r honest peers keys tbls₀ tbls₁ sched _ _ _ _ (VariantSilence.initU_u F)
    (VariantSilence.initU_u F)] at hy
  have hinv := VariantSilence.initU_inv (r := r) F hf hs
  exact xvfed_silence hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁ sched _ _
    (VariantSilence.vcoupled_refl r honest _) hinv hinv y hy

/-! ## An adaptive observer over the `XVObs` history -/

/-- `FedSilence.Observer` reading the observations this walk emits, answers and store decisions included: its next
labelled step is a function of its own run's `XVObs` history alone. -/
structure XVObserver where
  next : List XVObs → Option LStep

/-- `FedSilence.awalk` over the receipt step: each run's observer reads its own run's history. -/
def xvawalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : XVObserver) :
    Nat → VFed → VFed → List XVObs → List XVObs → List (XVObs × XVObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match σ.next hA, σ.next hB with
    | some (p, h), some (q, h') =>
      if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
          inside r B.lf (q.step tbls₁) then
        (xvobs mk g cfg r peers keys A (p.step tbls₀) h, xvobs mk g cfg r peers keys B (q.step tbls₁) h') ::
          xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (xvapply keys g cfg r A (p.step tbls₀) h)
            (xvapply keys g cfg r B (q.step tbls₁) h') (hA ++ [xvobs mk g cfg r peers keys A (p.step tbls₀) h])
            (hB ++ [xvobs mk g cfg r peers keys B (q.step tbls₁) h'])
      else []
    | _, _ => []

/-- The labelled schedule an `XVObserver` selects in one run, at most `n` steps. -/
def xvplay (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) (tbls : Nat → Enrolment)
    (σ : XVObserver) : Nat → VFed → List XVObs → List LStep
  | 0, _, _ => []
  | n + 1, F, h =>
    match σ.next h with
    | none => []
    | some (p, l) => (p, l) :: xvplay mk g cfg r peers keys tbls σ n (xvapply keys g cfg r F (p.step tbls) l)
        (h ++ [xvobs mk g cfg r peers keys F (p.step tbls) l])

/-- **Equal histories, the same step**, as `FedSilence.awalk_walk` states it. No rule premise is taken. -/
theorem xvawalk_xvwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : XVObserver) :
    ∀ (n : Nat) (A B : VFed) (h : List XVObs),
      (∀ y ∈ xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (xvplay mk g cfg r peers keys tbls₀ σ n A h),
        y.1 = y.2) →
      xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h =
        xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (xvplay mk g cfg r peers keys tbls₀ σ n A h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B h heq
    cases hσ : σ.next h with
    | none => simp only [xvawalk, xvplay, hσ, xvwalk]
    | some ph =>
      obtain ⟨p, l⟩ := ph
      simp only [xvplay, hσ] at heq ⊢
      simp only [xvawalk, hσ]
      simp only [xvwalk] at heq ⊢
      split
      · rename_i hguard
        simp only [hguard, if_true, List.mem_cons, forall_eq_or_imp] at heq
        obtain ⟨hhead, htail⟩ := heq
        rw [← hhead, ih _ _ _ htail]
      · rfl

/-- **SILENCE over the lifecycle layer's receipt step against an adaptive observer**, as
`FedSilence.fed_silence_adaptive` states it: the observer reads its own run's `XVObs` history, answers and store
decisions included, and nothing else. -/
@[req "DUR-1"]
theorem xvfed_silence_adaptive {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : XVObserver) :
    ∀ (n : Nat) (A B : VFed) (h : List XVObs), VCoupled r honest A B → FInv r honest A.lf → FInv r honest B.lf →
      xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h =
          xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (xvplay mk g cfg r peers keys tbls₀ σ n A h) ∧
        ∀ y ∈ xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h, y.1 = y.2 := by
  intro n A B h hc hia hib
  have hw := xvfed_silence (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁
    (xvplay mk g cfg r peers keys tbls₀ σ n A h) A B hc hia hib
  have he := xvawalk_xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h hw
  exact ⟨he, he ▸ hw⟩

/-- **`xvfed_silence_adaptive` at every initial state the federation admits with its sweep flags clear**, with an
observer that has seen nothing, nothing sent and nothing kept. -/
@[req "DUR-1"]
theorem xvfed_silence_adaptive_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) (σ : XVObserver) :
    ∀ n : Nat,
      xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] [] =
          xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ (VFed.init F) (VFed.init F)
            (xvplay mk g cfg r peers keys tbls₀ σ n (VFed.init F) []) ∧
        ∀ y ∈ xvawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] [], y.1 = y.2 := by
  intro n
  have hw := xvfed_silence_fresh (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁ F hf hs
    (xvplay mk g cfg r peers keys tbls₀ σ n (VFed.init F) [])
  have he := xvawalk_xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] hw
  exact ⟨he, he ▸ hw⟩

/-! ## The earlier domains -/

/-- The observation with the store's decisions dropped: `ReceiptExpiry.XObs`. -/
def XVObs.toX (o : XVObs) : XObs :=
  { base := o.base, answer := o.delivery.map fun d => (d.receiver, d.signer, d.answer) }

theorem xvobs_toX (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) (V : VFed)
    (s : Federation.Step) (h : Option Nat) :
    (xvobs mk g cfg r peers keys V s h).toX = xfobs mk g cfg r peers V.lf s :=
  ExpirySilence.xobs_ext rfl (ReceiptLifecycle.dobs_answer mk g cfg r peers keys V s h)

/-- **The answer part is the expiry-aware walk.** `ExpirySilence.xwalk` over the schedule without its labels is
`xvwalk` with the store's decisions dropped: the same stop, and the same `ReceiptExpiry.XObs` at every step. No rule
premise is taken. -/
@[req "NCH-24"]
theorem xvwalk_xwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed),
      (xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched).map (fun y => (y.1.toX, y.2.toX)) =
        ExpirySilence.xwalk mk g cfg r honest peers tbls₀ tbls₁ A.lf B.lf (sched.map Prod.fst) := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B
    simp only [xvwalk, ExpirySilence.xwalk, List.map_cons]
    split
    · simp only [List.map_cons, xvobs_toX, ih]
      rfl
    · rfl

/-- **Off evictions, the earlier walk is this walk's `FObs` part.** On a schedule where no delivery evicts in either
run, `FedSilence.walk` over the schedule without its labels is `xvwalk` with the delivery observations dropped: the
same stop, and the same `FedSilence.FObs` at every step. No rule premise is taken. -/
theorem xvwalk_walk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (sched : List LStep) (A B : VFed)
    (hua : unevicted g cfg r A.lf ((sched.map Prod.fst).map (·.step tbls₀)) = true)
    (hub : unevicted g cfg r B.lf ((sched.map Prod.fst).map (·.step tbls₁)) = true) :
    (xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched).map (fun y => (y.1.base, y.2.base)) =
      walk mk g cfg r honest peers tbls₀ tbls₁ A.lf B.lf (sched.map Prod.fst) := by
  rw [← ExpirySilence.xwalk_walk mk g cfg r honest peers tbls₀ tbls₁ _ _ _ hua hub,
    ← xvwalk_xwalk mk g cfg r honest peers keys tbls₀ tbls₁ sched A B, List.map_map]
  rfl

/-- No step of a labelled schedule is an evicting delivery or births under an id resident at its acting node, where
the receipt step's run takes it: `ReceiptLifecycle.xvapply_eq`'s premise at every step. -/
def quiet (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) :
    VFed → List (Federation.Step × Option Nat) → Bool
  | _, [] => true
  | V, (s, h) :: ss => !evictsAt V.lf s && !rebirthAt g cfg r V.lf s && quiet keys g cfg r (xvapply keys g cfg r V s h) ss

/-- `VariantSilence.VObs` with `ReceiptExpiry.XObs`'s answer: the delivery observation they give together, the store's
decisions shown when the answer is found. -/
def joinObs (v : VObs) (x : XObs) : XVObs :=
  { base := v.base,
    delivery := match v.store, x.answer with
      | some o, some (_, _, a) =>
        some { receiver := o.receiver, signer := o.signer, label := o.label, answer := a,
               checks := if a = .found then some o.checks else none }
      | _, _ => none }

theorem answer_found_iff (env : Env) (n : Node) (cid : Nat) : answer env n cid = .found ↔ lookup env n cid = .live := by
  unfold answer
  cases lookup env n cid <;> simp

/-- Off an evicting delivery, one step's observation is the variant-aware one with the answer joined. -/
theorem xvobs_join (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) {V : VFed}
    {s : Federation.Step} (h : Option Nat) (he : evictsAt V.lf s = false) :
    xvobs mk g cfg r peers keys V s h = joinObs (vobs mk g cfg r peers keys V s h) (xfobs mk g cfg r peers V.lf s) := by
  have hb := ReceiptExpiry.xfobs_unevicted mk g cfg r peers V.lf s he
  simp only [xvobs, joinObs, vobs, hb]
  congr 1
  cases s with
  | deliverPartial i env x =>
    simp only [dobs, VariantSilence.storeObs, xfobs, Option.some.injEq]
    congr 1
    by_cases hl : lookup env (V.lf.fed.worlds i).node x.cid = .live
    · rw [if_pos hl, if_pos ((answer_found_iff _ _ _).2 hl)]
    · rw [if_neg hl, if_neg (fun ha => hl ((answer_found_iff _ _ _).1 ha))]
  | _ => rfl

/-- The store's decisions at a lookup that finds no candidate under the id, from a store that keeps no record under
it: nothing found, and only the signer range read. -/
def missChecks (keys : List Nat) (s : Nat) : VariantSilence.Checks :=
  { found := false, rung := false, input := false, hash := false, signer := keys.contains s, stored := false,
    fresh := true }

/-- `VariantSilence.VObs` read back from an `XVObs`: the decisions shown, or those of a lookup that finds no candidate
where none are shown. -/
def splitObs (keys : List Nat) (o : XVObs) : VObs :=
  { base := o.base,
    store := o.delivery.map fun d =>
      { receiver := d.receiver, signer := d.signer, label := d.label, checks := d.checks.getD (missChecks keys d.signer) } }

theorem any_id_and {l : List Cand} {cid : Nat} (h : l.any (·.id == cid) = false) (q : Cand → Bool) :
    l.any (fun c => c.id == cid && q c) = false := by
  rw [List.any_eq_false] at h ⊢
  intro c hc hq
  simp only [Bool.and_eq_true] at hq
  exact h c hc hq.1

theorem lookup_unknown {env : Env} {n : Node} {cid : Nat} (h : lookup env n cid = .unknown) :
    n.cands.any (·.id == cid) = false := by
  unfold lookup at h
  cases hf : n.cands.find? (·.id == cid) with
  | none =>
    rw [List.any_eq_false]
    intro c hc hcid
    exact List.find?_eq_none.1 hf c hc hcid
  | some c =>
    rw [hf] at h
    dsimp only at h
    split at h <;> cases h

/-- With no candidate under the id at the receiver and no record kept under it, the store's decisions are
`missChecks`'s. -/
theorem checks_miss (keys : List Nat) (S : List (Nat × Authority.Sig)) {n : Node} (m : Sighash) (k s : Nat)
    {cid : Nat} (h : Option Nat) (hn : n.cands.any (·.id == cid) = false) (hS : ∀ p ∈ S, p.1 ≠ cid) :
    VariantSilence.checks keys S n m k s cid h = missChecks keys s := by
  have hf : S.contains (cid, { msg := m, input := k, signer := s }) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    exact hS _ (List.contains_iff_mem.1 hc) rfl
  have hst : VariantReceipt.storable keys n m k s cid h = false := by
    unfold VariantReceipt.storable
    rw [any_id_and hn, Bool.and_false]
  simp only [VariantSilence.checks, missChecks, hn, any_id_and hn, hst, hf, Bool.not_false]

/-- **Off an evicting delivery, the variant-aware observation is read back from this one.** At a state whose kept
records are resident, a step that is not an evicting delivery is observed by `VariantSilence.vobs` as `splitObs` reads
it from `xvobs`: where no decision is shown the lookup found no candidate, and the decisions are `missChecks`'s. -/
theorem xvobs_split (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) {V : VFed}
    {s : Federation.Step} (h : Option Nat) (he : evictsAt V.lf s = false) (hr : Resident V) :
    splitObs keys (xvobs mk g cfg r peers keys V s h) = vobs mk g cfg r peers keys V s h := by
  have hb := ReceiptExpiry.xfobs_unevicted mk g cfg r peers V.lf s he
  cases s with
  | deliverPartial i env x =>
    have hc : (if lookup env (V.lf.fed.worlds i).node x.cid = .live then
          some (VariantSilence.checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h)
          else none).getD (missChecks keys x.signer) =
        VariantSilence.checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h := by
      by_cases hl : lookup env (V.lf.fed.worlds i).node x.cid = .live
      · rw [if_pos hl]
        rfl
      · rw [if_neg hl]
        have hu : lookup env (V.lf.fed.worlds i).node x.cid = .unknown := by
          cases hk : lookup env (V.lf.fed.worlds i).node x.cid with
          | unknown => rfl
          | live => exact absurd hk hl
          | expired => simp [evictsAt, evicts, hk] at he
        have hn := lookup_unknown hu
        refine (checks_miss keys (V.store i) x.msg x.input x.signer h hn fun p hp hpc => ?_).symm
        have hres := hr i p hp
        rw [hpc, hn] at hres
        cases hres
    simp only [splitObs, xvobs, vobs, hb, dobs, VariantSilence.storeObs, Option.map_some, hc]
  | _ => simp only [splitObs, xvobs, vobs, hb, dobs, VariantSilence.storeObs, Option.map_none]

/-- **On the earlier domain, nothing the variant-aware walk compares is dropped.** From two states whose kept records
are resident, on a schedule with no evicting delivery and no birth under a resident id in either run,
`VariantSilence.vwalk` is `xvwalk` read back through `splitObs`, step by step: equal `XVObs` there give equal
`VariantSilence.VObs`. No rule premise is taken. -/
@[req "NCH-24"]
theorem xvwalk_split (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), Resident A → Resident B →
      quiet keys g cfg r A (sched.map fun ph => (ph.1.step tbls₀, ph.2)) = true →
      quiet keys g cfg r B (sched.map fun ph => (ph.1.step tbls₁, ph.2)) = true →
      vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched =
        (xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched).map
          fun y => (splitObs keys y.1, splitObs keys y.2) := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hra hrb hqa hqb
    simp only [List.map_cons, quiet, Bool.and_eq_true, Bool.not_eq_true'] at hqa hqb
    obtain ⟨⟨hea, hba⟩, hqa⟩ := hqa
    obtain ⟨⟨heb, hbb⟩, hqb⟩ := hqb
    have hxa := ReceiptLifecycle.xvapply_eq (keys := keys) h hea hba hra
    have hxb := ReceiptLifecycle.xvapply_eq (keys := keys) h heb hbb hrb
    have ih' := ih _ _ (ReceiptLifecycle.resident_step hra _ h) (ReceiptLifecycle.resident_step hrb _ h) hqa hqb
    simp only [xvwalk, vwalk]
    by_cases hc : (Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁)) = true
    · rw [if_pos hc, if_pos hc, List.map_cons, ← hxa, ← hxb, ih', xvobs_split mk g cfg r peers keys h hea hra,
        xvobs_split mk g cfg r peers keys h heb hrb]
    · rw [if_neg hc, if_neg hc]
      rfl

/-- **On the earlier domain, this walk is the variant-aware walk with the answers joined.** From two states whose
kept records are resident, on a schedule with no evicting delivery and no birth under a resident id in either run,
`xvwalk` is `VariantSilence.vwalk`'s observations joined, step by step, with `ExpirySilence.xwalk`'s answers. So
`VariantSilence.vfed_silence` and `ExpirySilence.xfed_silence` keep their domains, and on this one their walks are
this walk's. No rule premise is taken. -/
@[req "NCH-24"]
theorem xvwalk_vwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), Resident A → Resident B →
      quiet keys g cfg r A (sched.map fun ph => (ph.1.step tbls₀, ph.2)) = true →
      quiet keys g cfg r B (sched.map fun ph => (ph.1.step tbls₁, ph.2)) = true →
      xvwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched =
        List.zipWith (fun v x => (joinObs v.1 x.1, joinObs v.2 x.2))
          (vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched)
          (ExpirySilence.xwalk mk g cfg r honest peers tbls₀ tbls₁ A.lf B.lf (sched.map Prod.fst)) := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hra hrb hqa hqb
    simp only [List.map_cons, quiet, Bool.and_eq_true, Bool.not_eq_true'] at hqa hqb
    obtain ⟨⟨hea, hba⟩, hqa⟩ := hqa
    obtain ⟨⟨heb, hbb⟩, hqb⟩ := hqb
    have hxa := ReceiptLifecycle.xvapply_eq (keys := keys) h hea hba hra
    have hxb := ReceiptLifecycle.xvapply_eq (keys := keys) h heb hbb hrb
    have hla := ReceiptExpiry.xapply_unevicted g cfg r A.lf _ hea
    have hlb := ReceiptExpiry.xapply_unevicted g cfg r B.lf _ heb
    have ih' := ih _ _ (ReceiptLifecycle.resident_step hra _ h) (ReceiptLifecycle.resident_step hrb _ h) hqa hqb
    simp only [xvwalk, vwalk, ExpirySilence.xwalk, List.map_cons]
    by_cases hc : (Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁)) = true
    · rw [if_pos hc, if_pos hc, if_pos hc, List.zipWith_cons_cons, ih', xvobs_join mk g cfg r peers keys h hea,
        xvobs_join mk g cfg r peers keys h heb, hxa, hxb, hla, hlb]
      rfl
    · rw [if_neg hc, if_neg hc, if_neg hc]
      rfl

end BtcPolicy.LifecycleSilence
