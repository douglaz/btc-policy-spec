import BtcPolicy.FedSilence
import BtcPolicy.VariantReceipt
/-! SILENCE over the variant-aware receipt of a partial (`DUR-1`, `NCH-23`, `NCH-24`, `NCH-25`). A layer beside the
existing definitions: no definition or theorem statement changes, and no kernel event is added.

**The domain.** The labelled receipt domain as it stands: the ledgered federation run of `FedSilence`, whose delivered
partial is `Kernel.receivePartial` (`FedSilence.lapply`), with each step carrying a label (`VariantReceipt.LTrace`). It
keeps that domain's exclusion of receipt-time eviction: no lookup here reads the candidate's expiry, and the
expiry-aware receipt (`ReceiptExpiry`, `ExpirySilence`) is not combined with this one.

**The operation.** `VariantReceipt.storable`'s store decision on one delivered, labelled partial, and the records it
keeps (`VariantReceipt.kept`). A state of this layer, `VariantSilence.VFed`, is a ledgered federation with the honest
envelopes sent so far (`VariantReceipt.envelopes`) and each node's kept records; `VariantSilence.vapply` steps them
together, and `VariantSilence.agrees_step` shows they are the labelled trace's envelopes and `VariantReceipt.kept`
records, so `VariantSilence.vheld` is `VariantReceipt.held` (`VariantSilence.vheld_held`). A labelled run whose
steps are admitted, with admissible labels, is a `VariantReceipt.Execution` (`VariantSilence.vrun_execution`).

**What the store reads.** Of the candidate under the partial's commitment id: its id, its ladder (`Kernel.Cand.ladder`:
the base's transaction and hash and the rungs above it, each a transaction and a user-signature hash) and its role
(`Kernel.Cand.isEscape`, read off its id and pair). Of the partial: its message, input, signer and commitment id, and
its label. Of the node: the receiver's configured keys, a parameter, and the records it already keeps. The record
kept is filtered by the candidates resident after the step. Every candidate field read is in the public projection
(`Silence.pubCand` erases the freeze bit and a selected Escape's window, neither read here).

**The observer.** `VariantSilence.VObs` is `FedSilence.FObs` with the store's decisions on a delivered partial
(`VariantSilence.Checks`): the lookup (`found`, a resident candidate under the id), the rung found by its message at
the input, the input in range, the Escape-role hash match, the signer in range, and whether the record is new. The
lookup is kept apart from the acceptance: `found` with a failed hash is a refusal, not a store. The decisions are
not a wire reply: the model has no `NCH-17` reply on a partial, and no signature check (`BAD_PARTIAL_SIG`). They are
the internal decisions the receipt makes, compared whole so that a leak through any of them is a difference.

**What is derived.** The two runs take one schedule of steps, each with one label: a delivery's label is a schedule
input, as the delivered row is. From the coupled states before each step the proofs derive the store's decisions
(`VariantSilence.checks_pub`), the records kept and their first-record order (`VariantSilence.store_deliver`), the
honest envelopes and so the labels an honest sender's variant gives (`VariantSilence.variantOf_pub`), the label
admissibility (`VariantSilence.vlabelOk_pub`) and the Held projection (`VariantSilence.vheld_pub`). No equality of
histories, Held sets or envelopes after a step is assumed: each comes from the coupling before it
(`VariantSilence.vpstep_pub`, `VariantSilence.vfed_coupled`).

**The horizon is unchanged.** `VariantSilence.vwalk`'s stop is `FedSilence.walk`'s, word for word, and its
`FedSilence.FObs` part is `walk` (`VariantSilence.vwalk_walk`).

**Outside.** A label under an extracted signer is any label (`VariantReceipt.labelOk`): no honest origin follows for
it. A candidate that is not Escape-role is not compared on its hash, and its base hash's default value is never read
as signing material. Receipt-time expiry, the lifecycle run and its permits, serialized bytes and timing (`F22`) stay
outside, as for `FedSilence`. -/

namespace BtcPolicy.VariantSilence

open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.VariantReceipt (rungOf variantOf storable arrival addNew kept emitted envelopes labelOk lproject
  forget LTrace)

variable {r : Rules}

/-! ## The store's reads through the projection -/

theorem pubCand_baseSig (sel : List Nat) (c : Cand) : (pubCand r sel c).baseSig = c.baseSig := by
  unfold pubCand; split <;> rfl

theorem pubCand_ladder (sel : List Nat) (c : Cand) : (pubCand r sel c).ladder = c.ladder := by
  simp only [Cand.ladder, pubCand_tx, pubCand_baseSig, pubCand_above]

theorem rungOf_pub (sel : List Nat) (c : Cand) (m : Sighash) (k : Nat) :
    rungOf (pubCand r sel c) m k = rungOf c m k := by
  simp only [rungOf, pubCand_ladder]

/-- **The retained variant is public.** The user-signature hash of a node's retained variant for a partial is read
off the node's public projection. -/
@[req "SPN-36"]
theorem variantOf_factor (n : Node) (m : Sighash) (k cid : Nat) :
    variantOf n m k cid = (((pubNode r n).cands.find? fun c => c.id == cid && (rungOf c m k).isSome).bind
      fun c => (rungOf c m k).map (·.userSig)) := by
  let P : Cand → Bool := fun c => c.id == cid && (rungOf c m k).isSome
  have hf := find?_comm (pubCand r (selIds n)) P n.cands P (fun c _ => by simp [P, pubCand_id, rungOf_pub])
  show (n.cands.find? P).bind _ = ((n.cands.map (pubCand r (selIds n))).find? P).bind _
  rw [← hf]
  cases n.cands.find? P with
  | none => rfl
  | some c => simp [rungOf_pub]

theorem variantOf_pub {na nb : Node} (hn : pubNode r na = pubNode r nb) (m : Sighash) (k cid : Nat) :
    variantOf na m k cid = variantOf nb m k cid := by
  rw [variantOf_factor (r := r) na, variantOf_factor (r := r) nb, hn]

theorem resident_pub {na nb : Node} (hn : pubNode r na = pubNode r nb) (q : Nat) :
    na.cands.any (·.id == q) = nb.cands.any (·.id == q) :=
  cands_any_pub' hn _ (fun sel c => by simp [pubCand_id])

theorem ownSigs_pub {na nb : Node} (hn : pubNode r na = pubNode r nb) :
    RungIngress.ownSigs na = RungIngress.ownSigs nb := by
  have key : ∀ n : Node, RungIngress.ownSigs n = ((pubNode r n).cands.flatMap fun c => c.ladder.flatMap fun g =>
      (List.range g.tx.inputs.length).map fun k =>
        ({ msg := sighash g.tx k, input := k, signer := (pubNode r n).id } : Authority.Sig)) := by
    intro n
    simp only [RungIngress.ownSigs, pubNode, List.flatMap_map, pubCand_ladder]
  rw [key na, key nb, hn]

/-! ## The store's decisions -/

/-- A rung of the candidate has the partial's message at its input. -/
def rungAt (c : Cand) (m : Sighash) (k : Nat) : Bool := (rungOf c m k).isSome

/-- That rung has the input in range. -/
def inputAt (c : Cand) (m : Sighash) (k : Nat) : Bool :=
  match rungOf c m k with
  | none => false
  | some g => decide (k < g.tx.inputs.length)

/-- That rung has the input in range and, on an Escape-role candidate, its hash is the label: the candidate
conjunct of `VariantReceipt.storable`. -/
def hashAt (c : Cand) (m : Sighash) (k : Nat) (h : Option Nat) : Bool :=
  match rungOf c m k with
  | none => false
  | some g => decide (k < g.tx.inputs.length) && (!c.isEscape || h == some g.userSig)

/-- The store's decisions on one labelled partial, in `NCH-24`'s order as far as this store models it. `found` is
the lookup: a resident candidate under the commitment id. `rung`, `input` and `hash` are "the rung is found by
txid", the input in range and "the user-signature hash matches" on a candidate under the id, each including the
ones before it; `signer` is the signer among the receiver's keys; `fresh` says the record is not already kept
(`NCH-25`). The lookup's success is `found` alone and is not the store's acceptance. -/
structure Checks where
  found : Bool
  rung : Bool
  input : Bool
  hash : Bool
  signer : Bool
  stored : Bool
  fresh : Bool
  deriving DecidableEq, Repr

/-- The store takes it and keeps a record it did not have. -/
def Checks.adds (c : Checks) : Bool := c.stored && c.fresh

/-- The decisions at node `n`, with the records `S` it keeps, on a partial by message `m`, input `k`, signer `s`,
commitment `cid`, with label `h`. -/
@[req "NCH-24"]
def checks (keys : List Nat) (S : List (Nat × Authority.Sig)) (n : Node) (m : Sighash) (k s cid : Nat)
    (h : Option Nat) : Checks :=
  { found := n.cands.any (·.id == cid)
    rung := n.cands.any fun c => c.id == cid && rungAt c m k
    input := n.cands.any fun c => c.id == cid && inputAt c m k
    hash := n.cands.any fun c => c.id == cid && hashAt c m k h
    signer := keys.contains s
    stored := storable keys n m k s cid h
    fresh := !S.contains (cid, { msg := m, input := k, signer := s }) }

/-- The store's decision, `VariantReceipt.storable`, is the signer range and the hash decision together. -/
@[req "NCH-24"]
theorem checks_stored (keys : List Nat) (S : List (Nat × Authority.Sig)) (n : Node) (m : Sighash)
    (k s cid : Nat) (h : Option Nat) :
    (checks keys S n m k s cid h).stored = ((checks keys S n m k s cid h).signer &&
      (checks keys S n m k s cid h).hash) := by
  rfl

/-- **The store's decision is public.** Two nodes with one public projection make the same store decision on one
labelled partial. -/
@[req "NCH-24"]
theorem storable_pub (keys : List Nat) {na nb : Node} (hn : pubNode r na = pubNode r nb) (m : Sighash)
    (k s cid : Nat) (h : Option Nat) : storable keys na m k s cid h = storable keys nb m k s cid h := by
  have e : ∀ n : Node, storable keys n m k s cid h =
      (keys.contains s && n.cands.any fun c => c.id == cid && hashAt c m k h) := fun _ => rfl
  rw [e na, e nb, cands_any_pub' hn _ (fun sel c => by simp [pubCand_id, hashAt, rungOf_pub, pubCand_isEscape])]

/-- **The two runs decide alike.** Two nodes with one public projection and the same kept records make the same
decisions on one labelled partial: the lookup, the rung, the input and signer ranges, the Escape-role hash, the
store's decision and the duplicate test. -/
@[req "NCH-24"]
theorem checks_pub (keys : List Nat) (S : List (Nat × Authority.Sig)) {na nb : Node}
    (hn : pubNode r na = pubNode r nb) (m : Sighash) (k s cid : Nat) (h : Option Nat) :
    checks keys S na m k s cid h = checks keys S nb m k s cid h := by
  have h0 := storable_pub keys hn m k s cid h
  have h1 := resident_pub hn cid
  have h2 : (na.cands.any fun c => c.id == cid && rungAt c m k) = nb.cands.any fun c => c.id == cid && rungAt c m k :=
    cands_any_pub' hn _ (fun sel c => by simp [pubCand_id, rungAt, rungOf_pub])
  have h3 : (na.cands.any fun c => c.id == cid && inputAt c m k) =
      nb.cands.any fun c => c.id == cid && inputAt c m k :=
    cands_any_pub' hn _ (fun sel c => by simp [pubCand_id, inputAt, rungOf_pub])
  have h4 : (na.cands.any fun c => c.id == cid && hashAt c m k h) =
      nb.cands.any fun c => c.id == cid && hashAt c m k h :=
    cands_any_pub' hn _ (fun sel c => by simp [pubCand_id, hashAt, rungOf_pub, pubCand_isEscape])
  simp only [checks, h0, h1, h2, h3, h4]

theorem arrival_pub (keys : List Nat) {wa wb : World} (hn : pubNode r wa.node = pubNode r wb.node) (env : Env)
    (e : Event) (h : Option Nat) : arrival keys (wa, env, e, h) = arrival keys (wb, env, e, h) := by
  cases e with
  | receivePartial m k s cid =>
    simp only [arrival]
    rw [storable_pub keys hn]
  | _ => rfl

/-- An input's arrival, under either enrolment table: a request or a staged refusal stores nothing. -/
theorem arrival_input (keys : List Nat) (g : Guards) (cfg : Config) (env : Env) (l : Ledger) {wa wb : World}
    (hn : pubNode r wa.node = pubNode r wb.node) (h : Option Nat) (x : Silence.Input) (t₀ t₁ : Enrolment) :
    arrival keys (wa, env, kernelEvent g cfg env l (x.event t₀), h) =
      arrival keys (wb, env, kernelEvent g cfg env l (x.event t₁), h) := by
  cases x with
  | request cid pin E sp es =>
    simp only [Silence.Input.event, kernelEvent]
    split <;> split <;> rfl
  | refusal cid pin E pair code => rfl
  | pinless e => exact arrival_pub keys hn env _ h

/-! ## The layer's state and step -/

/-- A ledgered federation with the honest envelopes sent so far, newest first, and each node's kept records. -/
structure VFed where
  lf : LFed
  envs : List (Exp × Option Nat)
  store : Nat → List (Nat × Authority.Sig)

/-- A start with nothing sent and nothing kept. -/
def VFed.init (F : LFed) : VFed := { lf := F, envs := [], store := fun _ => [] }

/-- The envelopes a step sends: the partials of a process step's fan-out, each with the hash of the sender's
retained variant (`VariantReceipt.emitted`), at the kernel event `Ledger.sysStep` takes. -/
def newEnvs (r : Rules) (g : Guards) (cfg : Config) (F : LFed) (s : Federation.Step) : List (Exp × Option Nat) :=
  match kernelStep g cfg F s with
  | .process i env e => emitted r (F.fed.worlds i) env e
  | _ => []

/-- Node `j`'s kept records after a step: at the acting node, the store's arrival added unless already kept, then
filtered by the candidates resident after the step, as `VariantReceipt.kept` has it; elsewhere as they were. -/
def vstore (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) (V : VFed) (s : Federation.Step)
    (h : Option Nat) (j : Nat) : List (Nat × Authority.Sig) :=
  match Federation.actor (kernelStep g cfg V.lf s) with
  | some (i, env, e) =>
    if j = i then
      (addNew (V.store i) (arrival keys (V.lf.fed.worlds i, env, e, h))).filter
        fun p => ((lapply g cfg r V.lf s).fed.worlds i).node.cands.any (·.id == p.1)
    else V.store j
  | none => V.store j

/-- One labelled step. -/
def vapply (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) (V : VFed) (s : Federation.Step)
    (h : Option Nat) : VFed :=
  { lf := lapply g cfg r V.lf s, envs := newEnvs r g cfg V.lf s ++ V.envs, store := vstore keys g cfg r V s h }

/-- Node `i`'s possession: its own signatures and its kept records, `VariantReceipt.held`'s form. -/
def vheld (V : VFed) (i : Nat) : List Authority.Sig :=
  RungIngress.ownSigs (V.lf.fed.worlds i).node ++ (V.store i).map Prod.snd

/-- The store's arrival added to the records `S`: the partial's record appended exactly when the decisions say the
store takes it and `S` does not already keep it. -/
theorem addNew_arrival (keys : List Nat) (S : List (Nat × Authority.Sig)) (w : World) (env : Env) (m : Sighash)
    (k s cid : Nat) (h : Option Nat) :
    addNew S (arrival keys (w, env, .receivePartial m k s cid, h)) =
      if (checks keys S w.node m k s cid h).adds then S ++ [(cid, { msg := m, input := k, signer := s })] else S := by
  have hadd : (checks keys S w.node m k s cid h).adds =
      (storable keys w.node m k s cid h && !S.contains (cid, { msg := m, input := k, signer := s })) := by
    rfl
  rw [hadd]
  simp only [addNew, arrival]
  cases storable keys w.node m k s cid h <;>
    cases hk : S.contains (cid, { msg := m, input := k, signer := s }) <;> simp <;> simpa using hk

/-- **One delivered partial, first record kept** (`NCH-25`). At the receiver, the records after the delivery are
the records before it, with the partial's record appended exactly when the store takes it and does not already keep
it, filtered by residency. A record already kept is never replaced, and a refusal adds nothing. -/
@[req "NCH-25"]
theorem store_deliver (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) (V : VFed) (i : Nat) (env : Env)
    (x : Exp) (h : Option Nat) :
    (vapply keys g cfg r V (.deliverPartial i env x) h).store i =
      (if (checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h).adds then
        V.store i ++ [(x.cid, { msg := x.msg, input := x.input, signer := x.signer })] else V.store i).filter
        fun p => (V.lf.fed.worlds i).node.cands.any (·.id == p.1) := by
  have hw : ((lapply g cfg r V.lf (.deliverPartial i env x)).fed.worlds i).node =
      Kernel.receivePartial (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid := by
    rw [lapply_fed, Federation.apply_of_actor r _ _ rfl i, if_pos rfl]
    rfl
  simp only [vapply, vstore, kernelStep, Federation.actor, hw, VariantReceipt.resident_receive, addNew_arrival,
    ↓reduceIte]

/-- A delivery leaves the partial inventory as it was: a refused partial stays exposed. -/
@[req "POL-18"]
theorem deliver_parts (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) (V : VFed) (i : Nat) (env : Env)
    (x : Exp) (h : Option Nat) :
    (vapply keys g cfg r V (.deliverPartial i env x) h).lf.fed.parts = V.lf.fed.parts := rfl

/-! ## The labelled trace -/

/-- The labelled composed trace a labelled ledgered run leaves, newest first. -/
def vtrace (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) :
    LTrace → VFed → List (Federation.Step × Option Nat) → LTrace
  | T, _, [] => T
  | T, V, (s, h) :: ss =>
    vtrace keys g cfg r ((V.lf.fed, kernelStep g cfg V.lf s, h) :: T) (vapply keys g cfg r V s h) ss

/-- A labelled schedule run through the layer's step. -/
def vrun (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) :
    VFed → List (Federation.Step × Option Nat) → VFed
  | V, [] => V
  | V, (s, h) :: ss => vrun keys g cfg r (vapply keys g cfg r V s h) ss

/-- The layer's envelopes and records are the labelled trace's. -/
def Agrees (keys : List Nat) (r : Rules) (T : LTrace) (V : VFed) : Prop :=
  V.envs = envelopes r (forget T) ∧ ∀ i, V.store i = kept keys (lproject i T) (V.lf.fed.worlds i).node

theorem agrees_init (keys : List Nat) (r : Rules) (F : LFed) : Agrees keys r [] (VFed.init F) :=
  ⟨rfl, fun _ => rfl⟩

/-- **The layer is the labelled store.** One step keeps the layer's envelopes equal to the labelled trace's
`VariantReceipt.envelopes`, and each node's records equal to its `VariantReceipt.kept`. -/
@[req "NCH-24"]
theorem agrees_step {keys : List Nat} {g : Guards} {cfg : Config} {T : LTrace} {V : VFed}
    (ha : Agrees keys r T V) (s : Federation.Step) (h : Option Nat) :
    Agrees keys r ((V.lf.fed, kernelStep g cfg V.lf s, h) :: T) (vapply keys g cfg r V s h) := by
  obtain ⟨he, hk⟩ := ha
  refine ⟨?_, fun j => ?_⟩
  · show newEnvs r g cfg V.lf s ++ V.envs = envelopes r ((V.lf.fed, kernelStep g cfg V.lf s) :: forget T)
    rw [he]
    unfold newEnvs
    cases kernelStep g cfg V.lf s <;> rfl
  · show vstore keys g cfg r V s h j =
      kept keys (lproject j ((V.lf.fed, kernelStep g cfg V.lf s, h) :: T)) ((lapply g cfg r V.lf s).fed.worlds j).node
    unfold vstore
    cases hact : Federation.actor (kernelStep g cfg V.lf s) with
    | none =>
      simp only [lproject, hact]
      rw [lapply_fed, Federation.apply_no_actor r _ _ hact j]
      exact hk j
    | some a =>
      obtain ⟨i, env, e⟩ := a
      by_cases hji : j = i
      · subst hji
        simp only [lproject, hact, if_true, VariantReceipt.kept]
        rw [hk j]
      · have hij : ¬ i = j := fun h => hji h.symm
        simp only [lproject, hact, hji, hij, if_false]
        rw [lapply_fed, Federation.apply_of_actor r _ _ hact j, if_neg hji]
        exact hk j

theorem vheld_held {keys : List Nat} {T : LTrace} {V : VFed} (ha : Agrees keys r T V) (i : Nat) :
    vheld V i = VariantReceipt.held keys i T V.lf.fed := by
  simp only [vheld, VariantReceipt.held, ha.2 i]

/-- A step's label is admissible: a delivery's is an envelope sent so far, or its signer is extracted. -/
def vlabelOk (V : VFed) : Federation.Step → Option Nat → Bool
  | .deliverPartial _ _ x, h => V.envs.contains (x, h) || V.lf.fed.extracted.contains x.signer
  | _, _ => true

/-- Every step admitted where it is taken, with an admissible label. -/
def vlegal (keys : List Nat) (g : Guards) (cfg : Config) (r : Rules) (honest : List Nat) :
    VFed → List (Federation.Step × Option Nat) → Bool
  | _, [] => true
  | V, (s, h) :: ss =>
    Federation.admits honest V.lf.fed s && vlabelOk V s h && vlegal keys g cfg r honest (vapply keys g cfg r V s h) ss

/-- **A labelled ledgered run is a labelled execution.** From a `VariantReceipt.Execution` the layer agrees with, a
schedule whose steps are admitted with admissible labels leaves a `VariantReceipt.Execution`, and the layer still
agrees with it: its records are `VariantReceipt.kept` and its possession `VariantReceipt.held`. -/
@[req "NCH-24"]
theorem vrun_execution {keys : List Nat} {g : Guards} {cfg : Config} {honest : List Nat} {T : LTrace} {V : VFed}
    (hx : VariantReceipt.Execution r honest T V.lf.fed) (ha : Agrees keys r T V) :
    ∀ ss, vlegal keys g cfg r honest V ss = true →
      VariantReceipt.Execution r honest (vtrace keys g cfg r T V ss) (vrun keys g cfg r V ss).lf.fed ∧
        Agrees keys r (vtrace keys g cfg r T V ss) (vrun keys g cfg r V ss) := by
  intro ss
  induction ss generalizing T V with
  | nil => intro _; exact ⟨hx, ha⟩
  | cons sh ss ih =>
    obtain ⟨s, h⟩ := sh
    intro hl
    simp only [vlegal, Bool.and_eq_true] at hl
    obtain ⟨⟨had, hlab⟩, hrest⟩ := hl
    have hadk : Federation.admits honest V.lf.fed (kernelStep g cfg V.lf s) = true := by
      rw [admits_kernelStep]; exact had
    have hlk : labelOk r (forget T) V.lf.fed (kernelStep g cfg V.lf s) h = true := by
      cases s with
      | deliverPartial i env x =>
        simp only [kernelStep, labelOk, vlabelOk, ← ha.1] at hlab ⊢
        exact hlab
      | _ => rfl
    have hx' := VariantReceipt.Execution.next (kernelStep g cfg V.lf s) h hadk hlk hx
    rw [← lapply_fed] at hx'
    simp only [vtrace, vrun]
    exact ih hx' (agrees_step ha s h) hrest

/-! ## The coupling -/

/-- Two layer states: the federations coupled by `FedSilence.FCoupled`, one envelope list, and the same records at
every honest node. -/
structure VCoupled (r : Rules) (honest : List Nat) (A B : VFed) : Prop where
  fed : FCoupled r honest A.lf B.lf
  envs : A.envs = B.envs
  store : ∀ i ∈ honest, A.store i = B.store i

theorem vcoupled_refl (r : Rules) (honest : List Nat) (A : VFed) : VCoupled r honest A A :=
  ⟨fcoupled_refl r honest A.lf, rfl, fun _ _ => rfl⟩

theorem node_pub {honest : List Nat} {A B : LFed} (hc : FCoupled r honest A B) {i : Nat} (hi : i ∈ honest) :
    pubNode r (A.fed.worlds i).node = pubNode r (B.fed.worlds i).node :=
  (hc.node i hi).node

/-- **The Held projection is the same in both runs**, at every honest node. -/
@[req "DUR-28"]
theorem vheld_pub {honest : List Nat} {A B : VFed} (hc : VCoupled r honest A B) {i : Nat} (hi : i ∈ honest) :
    vheld A i = vheld B i := by
  simp only [vheld]
  rw [ownSigs_pub (node_pub hc.fed hi), hc.store i hi]

/-- **A label admissible in one run is admissible in the other.** The envelopes and the extracted set are the same,
so an honest envelope's label, from the sender's retained variant, is the same label in both runs. -/
@[req "NCH-23"]
theorem vlabelOk_pub {honest : List Nat} {A B : VFed} (hc : VCoupled r honest A B) (s : Federation.Step)
    (h : Option Nat) : vlabelOk A s h = vlabelOk B s h := by
  cases s with
  | deliverPartial i env x => simp only [vlabelOk, hc.envs, hc.fed.extracted]
  | _ => rfl

theorem emitted_kernel (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env) (e : Event) :
    emitted r (F.fed.worlds i) env (kernelEvent g cfg env (F.leds i) e) =
      (Federation.fanout (F.fed.worlds i) (sysStep g cfg r env (F.sys i) e).2).map
        fun x => (x, variantOf (F.fed.worlds i).node x.msg x.input x.cid) := by
  have h := (sysStep_kernel g cfg r env (F.sys i) e).2
  simp only [LFed.sys] at h
  simp only [emitted, LFed.sys, h]

/-- The store at every honest node after one step, from the arrival in both runs. -/
theorem vstore_pub {keys : List Nat} {g : Guards} {cfg : Config} {honest : List Nat} {A B : VFed}
    (hc : VCoupled r honest A B) {sA sB : Federation.Step} (h : Option Nat)
    (h1 : FCoupled r honest (lapply g cfg r A.lf sA) (lapply g cfg r B.lf sB))
    (hact : (Federation.actor (kernelStep g cfg A.lf sA) = none ∧
        Federation.actor (kernelStep g cfg B.lf sB) = none) ∨
      ∃ i env eA eB, i ∈ honest ∧ Federation.actor (kernelStep g cfg A.lf sA) = some (i, env, eA) ∧
        Federation.actor (kernelStep g cfg B.lf sB) = some (i, env, eB) ∧
        arrival keys (A.lf.fed.worlds i, env, eA, h) = arrival keys (B.lf.fed.worlds i, env, eB, h)) :
    ∀ j ∈ honest, vstore keys g cfg r A sA h j = vstore keys g cfg r B sB h j := by
  intro j hj
  unfold vstore
  rcases hact with ⟨ha, hb⟩ | ⟨i, env, eA, eB, hi, ha, hb, harr⟩
  · rw [ha, hb]; exact hc.store j hj
  · rw [ha, hb]
    dsimp only
    split
    · rw [hc.store i hi, harr]
      congr 1
      funext p
      exact resident_pub (node_pub h1 hi) p.1
    · exact hc.store j hj

/-- The layer's parts of a process step at an honest node, in both runs. -/
theorem process_layer {keys : List Nat} {g : Guards} {cfg : Config} (ht : r.traversal = .always)
    (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {honest : List Nat} {A B : VFed} (hc : VCoupled r honest A B)
    (hia : FInv r honest A.lf) (hib : FInv r honest B.lf) {i : Nat} (hi : i ∈ honest) (env : Env)
    (x : Silence.Input) (tbl₀ tbl₁ : Enrolment) (h : Option Nat)
    (hpa : preHorizon r env (A.lf.fed.worlds i).node = true)
    (hpb : preHorizon r env (B.lf.fed.worlds i).node = true)
    (hwf : wfEvent r (A.lf.fed.worlds i).node (x.event tbl₀) = true)
    (h1 : FCoupled r honest (lapply g cfg r A.lf (.process i env (x.event tbl₀)))
      (lapply g cfg r B.lf (.process i env (x.event tbl₁)))) :
    newEnvs r g cfg A.lf (.process i env (x.event tbl₀)) = newEnvs r g cfg B.lf (.process i env (x.event tbl₁)) ∧
    ∀ j ∈ honest, vstore keys g cfg r A (.process i env (x.event tbl₀)) h j =
      vstore keys g cfg r B (.process i env (x.event tbl₁)) h j := by
  obtain ⟨-, heff, -, -, -⟩ := advance_pub (mk := .committed) (g := g) (cfg := cfg) rfl ht hd hr hcl hdr hc.fed hia
    hib hi env x tbl₀ tbl₁ hpa hpb hwf
  have hn := node_pub hc.fed hi
  have hled : A.lf.leds i = B.lf.leds i := (hc.fed.node i hi).led
  refine ⟨?_, vstore_pub hc h h1 (.inr ⟨i, env, _, _, hi, rfl, rfl, ?_⟩)⟩
  · simp only [newEnvs, kernelStep]
    rw [emitted_kernel, emitted_kernel, heff, fanout_pub hn]
    congr 1
    funext y
    rw [variantOf_pub hn]
  · rw [hled]
    exact arrival_input keys g cfg env (B.lf.leds i) hn h x tbl₀ tbl₁

/-- The decisions the observer reads at a delivered partial: receiver, signer, label and the store's decisions. -/
structure StoreObs where
  receiver : Nat
  signer : Nat
  label : Option Nat
  checks : Checks
  deriving DecidableEq, Repr

/-- `FedSilence.FObs` with the store's decisions on a delivered partial. -/
structure VObs where
  base : FObs
  store : Option StoreObs
  deriving DecidableEq, Repr

def storeObs (keys : List Nat) (V : VFed) : Federation.Step → Option Nat → Option StoreObs
  | .deliverPartial i _ x, h =>
    some ⟨i, x.signer, h, checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h⟩
  | _, _ => none

/-- One step's observation. -/
def vobs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) (V : VFed)
    (s : Federation.Step) (h : Option Nat) : VObs :=
  { base := fobs mk g cfg r peers V.lf s, store := storeObs keys V s h }

/-- **One labelled schedule step, in both runs.** From two coupled layer states, each carrying the invariant, a step
admitted in the first run with its acting node inside its horizon in both leaves two coupled layer states, keeps the
invariant, and is observed alike, the store's decisions included. The envelopes, the records kept and the Held
projection after the step are derived, not assumed. -/
@[req "DUR-1"]
theorem vpstep_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers keys : List Nat}
    {A B : VFed} (hc : VCoupled r honest A B) (hia : FInv r honest A.lf) (hib : FInv r honest B.lf)
    (p : PStep) (h : Option Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (ha : Federation.admits honest A.lf.fed (p.step tbls₀) = true)
    (hpa : inside r A.lf (p.step tbls₀) = true) (hpb : inside r B.lf (p.step tbls₁) = true) :
    VCoupled r honest (vapply keys g cfg r A (p.step tbls₀) h) (vapply keys g cfg r B (p.step tbls₁) h) ∧
    FInv r honest (vapply keys g cfg r A (p.step tbls₀) h).lf ∧
    FInv r honest (vapply keys g cfg r B (p.step tbls₁) h).lf ∧
    vobs mk g cfg r peers keys A (p.step tbls₀) h = vobs mk g cfg r peers keys B (p.step tbls₁) h := by
  obtain ⟨h1, h2, h3, h4⟩ := pstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr hc.fed hia hib p
    tbls₀ tbls₁ ha hpa hpb
  have main : newEnvs r g cfg A.lf (p.step tbls₀) = newEnvs r g cfg B.lf (p.step tbls₁) ∧
      (∀ j ∈ honest, vstore keys g cfg r A (p.step tbls₀) h j = vstore keys g cfg r B (p.step tbls₁) h j) ∧
      storeObs keys A (p.step tbls₀) h = storeObs keys B (p.step tbls₁) h := by
    cases p with
    | input i env x =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb h1 ⊢
      obtain ⟨he, hs⟩ := process_layer (keys := keys) ht hd hr hcl hdr hc hia hib (actor_honest ha rfl) env x
        (tbls₀ i) (tbls₁ i) h hpa.1 hpb.1 hpa.2 h1
      exact ⟨he, hs, rfl⟩
    | net s =>
      cases s with
      | process i env e =>
        simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb h1 ⊢
        obtain ⟨he, hs⟩ := process_layer (keys := keys) ht hd hr hcl hdr hc hia hib (actor_honest ha rfl) env
          (.pinless e) (fun _ => false) (fun _ => false) h hpa.1 hpb.1 hpa.2 h1
        exact ⟨he, hs, rfl⟩
      | deliver i env m =>
        simp only [PStep.step] at ha h1 ⊢
        exact ⟨rfl, vstore_pub hc h h1 (.inr ⟨i, env, _, _, actor_honest ha rfl, rfl, rfl, rfl⟩), rfl⟩
      | deliverPartial i env x =>
        simp only [PStep.step] at ha h1 ⊢
        have hi := actor_honest ha rfl
        refine ⟨rfl, vstore_pub hc h h1 (.inr ⟨i, env, _, _, hi, rfl, rfl,
          arrival_pub keys (node_pub hc.fed hi) env _ h⟩), ?_⟩
        simp only [storeObs, hc.store i hi, checks_pub keys (B.store i) (node_pub hc.fed hi)]
      | unstaged i cid => exact ⟨rfl, vstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | emit i cid => exact ⟨rfl, vstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | inject m => exact ⟨rfl, vstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | extract j => exact ⟨rfl, vstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
      | forge x => exact ⟨rfl, vstore_pub hc h h1 (.inl ⟨rfl, rfl⟩), rfl⟩
  obtain ⟨he, hs, hso⟩ := main
  refine ⟨⟨h1, ?_, hs⟩, h2, h3, ?_⟩
  · show newEnvs r g cfg A.lf (p.step tbls₀) ++ A.envs = newEnvs r g cfg B.lf (p.step tbls₁) ++ B.envs
    rw [he, hc.envs]
  · simp only [vobs, h4, hso]

/-! ## The walk and the relation -/

/-- A labelled schedule step: the step and the label a delivery carries, one for both runs. -/
abbrev LStep := PStep × Option Nat

/-- `FedSilence.walk` over the layer: the same stop, with `vapply` and `vobs`. -/
def vwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : VFed → VFed → List LStep → List (VObs × VObs)
  | _, _, [] => []
  | A, B, (p, h) :: rest =>
    if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁) then
      (vobs mk g cfg r peers keys A (p.step tbls₀) h, vobs mk g cfg r peers keys B (p.step tbls₁) h) ::
        vwalk mk g cfg r honest peers keys tbls₀ tbls₁ (vapply keys g cfg r A (p.step tbls₀) h)
          (vapply keys g cfg r B (p.step tbls₁) h) rest
    else []

/-- The state pairs `vwalk` reaches, one after each step it takes. -/
def vreach (g : Guards) (cfg : Config) (r : Rules) (honest keys : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) :
    VFed → VFed → List LStep → List (VFed × VFed)
  | _, _, [] => []
  | A, B, (p, h) :: rest =>
    if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
        inside r B.lf (p.step tbls₁) then
      (vapply keys g cfg r A (p.step tbls₀) h, vapply keys g cfg r B (p.step tbls₁) h) ::
        vreach g cfg r honest keys tbls₀ tbls₁ (vapply keys g cfg r A (p.step tbls₀) h)
          (vapply keys g cfg r B (p.step tbls₁) h) rest
    else []

/-- **SILENCE over the variant-aware receipt, under one fixed exogenous schedule.** `DUR-1`: "Every observable a
node emits MUST be identical between a normal-PIN and a duress-PIN request".

`FedSilence.fed_silence` with every delivered partial's store decisions in the observation: one labelled schedule,
two enrolment families, two coupled layer states, and the two runs emit equal `VariantSilence.VObs` at every step of
`VariantSilence.vwalk`, whose stop is `FedSilence.walk`'s. The premises are `fed_silence`'s with the layer's
coupling; nothing is assumed of the store's decisions or of the records after any step. -/
@[req "DUR-1"]
theorem vfed_silence {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), VCoupled r honest A B → FInv r honest A.lf →
      FInv r honest B.lf → ∀ y ∈ vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched, y.1 = y.2 := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hc hia hib y hy
    simp only [vwalk] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', hobs⟩ :=
        vpstep_pub (peers := peers) (keys := keys) hg ht hd hr hcl hdr hc hia hib p h tbls₀ tbls₁ ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hobs
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-- **The records and the Held projection, by induction over the reachable coupled states.** Every state pair the
walk reaches is coupled: one envelope list, the same records at every honest node, and so the same Held projection
(`VariantSilence.vheld_pub`). Each pair's coupling is derived from the pair before it. -/
@[req "DUR-28"]
theorem vfed_coupled (g : Guards) (cfg : Config) (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet)
    (honest keys : List Nat) (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed), VCoupled r honest A B → FInv r honest A.lf →
      FInv r honest B.lf → ∀ y ∈ vreach g cfg r honest keys tbls₀ tbls₁ A B sched,
        VCoupled r honest y.1 y.2 ∧ ∀ i ∈ honest, vheld y.1 i = vheld y.2 i := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B hc hia hib y hy
    simp only [vreach] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', -⟩ :=
        vpstep_pub (mk := .committed) (peers := []) (keys := keys) rfl ht hd hr hcl hdr hc hia hib p h tbls₀ tbls₁
          ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hc', fun i hi => vheld_pub hc' hi⟩
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-! ## The initial boundary -/

/-- Two layer states equal but for each node's `unarmedT`. -/
def VUEq (A A' : VFed) : Prop := UEq A.lf A'.lf ∧ A.envs = A'.envs ∧ A.store = A'.store

theorem leds_u {A A' : LFed} (h : UEq A A') (i : Nat) : A.leds i = A'.leds i := by
  obtain ⟨u, hu⟩ := h.2.2.2 i
  exact congrArg Sys.led hu

theorem cands_u {A A' : LFed} (h : UEq A A') (i : Nat) :
    (A.fed.worlds i).node.cands = (A'.fed.worlds i).node.cands := by
  obtain ⟨u, hu⟩ := world_u h i
  rw [hu]; rfl

theorem node_u {A A' : LFed} (h : UEq A A') (i : Nat) :
    ∃ u, (A.fed.worlds i).node = { (A'.fed.worlds i).node with unarmedT := u } := by
  obtain ⟨u, hu⟩ := world_u h i
  exact ⟨u, by rw [hu]; rfl⟩

theorem vapply_u {keys : List Nat} {g : Guards} {cfg : Config} {r : Rules} {A A' : VFed} (h : VUEq A A')
    (s : Federation.Step) (lab : Option Nat) :
    VUEq (vapply keys g cfg r A s lab) (vapply keys g cfg r A' s lab) := by
  obtain ⟨hu, he, hs⟩ := h
  have hl := (lapply_u (mk := .committed) (g := g) (cfg := cfg) (r := r) (honest := []) (peers := []) hu s).1
  have hk : kernelStep g cfg A.lf s = kernelStep g cfg A'.lf s := by
    cases s with
    | process i env e => simp only [kernelStep, leds_u hu i]
    | _ => rfl
  refine ⟨hl, ?_, ?_⟩
  · show newEnvs r g cfg A.lf s ++ A.envs = newEnvs r g cfg A'.lf s ++ A'.envs
    rw [he]
    congr 1
    cases s with
    | process i env e =>
      obtain ⟨u, hu'⟩ := hu.2.2.2 i
      obtain ⟨⟨v, -⟩, heff⟩ := sysStep_u g cfg r env hu' e
      simp only [newEnvs, kernelStep]
      rw [emitted_kernel, emitted_kernel, heff]
      obtain ⟨w, hw⟩ := node_u hu i
      have hwd : A.lf.fed.worlds i = (withUnarmedT (A'.lf.sys i) u).world := congrArg Sys.world hu'
      rw [hwd]
      rfl
    | _ => rfl
  · funext j
    show vstore keys g cfg r A s lab j = vstore keys g cfg r A' s lab j
    unfold vstore
    rw [hk]
    split
    · rename_i i env e _
      split
      · rw [hs]
        have hw : A.lf.fed.worlds i = (withUnarmedT (A'.lf.sys i) (hu.2.2.2 i).choose).world :=
          congrArg Sys.world (hu.2.2.2 i).choose_spec
        have ha : arrival keys (A.lf.fed.worlds i, env, e, lab) = arrival keys (A'.lf.fed.worlds i, env, e, lab) := by
          rw [hw]; cases e <;> rfl
        rw [ha]
        congr 1
        funext p
        rw [cands_u hl i]
      · rw [hs]
    · rw [hs]

theorem vobs_u {mk : Marker} {g : Guards} {cfg : Config} {r : Rules} {peers keys : List Nat} {A A' : VFed}
    (h : VUEq A A') (s : Federation.Step) (lab : Option Nat) :
    vobs mk g cfg r peers keys A s lab = vobs mk g cfg r peers keys A' s lab := by
  obtain ⟨hu, -, hs⟩ := h
  have hb := (lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := []) (peers := peers) hu s).2.2.2
  have hso : storeObs keys A s lab = storeObs keys A' s lab := by
    cases s with
    | deliverPartial i env x =>
      obtain ⟨u, hw⟩ := node_u hu i
      simp only [storeObs, hs, hw]
      rfl
    | _ => rfl
  simp only [vobs, hb, hso]

theorem vwalk_u (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B A' B' : VFed), VUEq A A' → VUEq B B' →
      vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched =
        vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A' B' sched := by
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
    simp only [vwalk, adA, inA, inB, vobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) ha,
      vobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) hb,
      ih _ _ _ _ (vapply_u (g := g) (cfg := cfg) ha _ _) (vapply_u (g := g) (cfg := cfg) hb _ _)]

/-- The layer's start over `F` with every node's `T` as its `unarmedT`. -/
def initU (F : LFed) : VFed := VFed.init (withU F (fun i => (F.fed.worlds i).node.T))

theorem initU_u (F : LFed) : VUEq (VFed.init F) (initU F) :=
  ⟨⟨rfl, rfl, rfl, fun i => ⟨(F.fed.worlds i).node.unarmedT, rfl⟩⟩, rfl, rfl⟩

theorem initU_inv {honest : List Nat} (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) : FInv r honest (initU F).lf := by
  intro i hi
  obtain ⟨_, _, ha, hc, _, _⟩ := hf.2.2 i hi
  exact nodeInv_initial ((initU F).lf.fed.worlds i).node _ hc ha (hs i hi) rfl

/-- **`vfed_silence` at every initial state the federation admits with its sweep flags clear**, with nothing sent
and nothing kept, as `FedSilence.fed_silence_fresh` states it. -/
@[req "DUR-1"]
theorem vfed_silence_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) :
    ∀ (sched : List LStep),
      ∀ y ∈ vwalk mk g cfg r honest peers keys tbls₀ tbls₁ (VFed.init F) (VFed.init F) sched, y.1 = y.2 := by
  intro sched y hy
  rw [vwalk_u mk g cfg r honest peers keys tbls₀ tbls₁ sched _ _ _ _ (initU_u F) (initU_u F)] at hy
  have hinv := initU_inv (r := r) F hf hs
  exact vfed_silence hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁ sched _ _ (vcoupled_refl r honest _) hinv
    hinv y hy

/-! ## An adaptive observer over the `VObs` history -/

/-- `FedSilence.Observer` reading the observations this walk emits, the store's decisions included: its next
labelled step is a function of its own run's `VObs` history alone. -/
structure VObserver where
  next : List VObs → Option LStep

/-- `FedSilence.awalk` over the layer: each run's observer reads its own run's history. -/
def vawalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : VObserver) :
    Nat → VFed → VFed → List VObs → List VObs → List (VObs × VObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match σ.next hA, σ.next hB with
    | some (p, h), some (q, h') =>
      if Federation.admits honest A.lf.fed (p.step tbls₀) && inside r A.lf (p.step tbls₀) &&
          inside r B.lf (q.step tbls₁) then
        (vobs mk g cfg r peers keys A (p.step tbls₀) h, vobs mk g cfg r peers keys B (q.step tbls₁) h') ::
          vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (vapply keys g cfg r A (p.step tbls₀) h)
            (vapply keys g cfg r B (q.step tbls₁) h') (hA ++ [vobs mk g cfg r peers keys A (p.step tbls₀) h])
            (hB ++ [vobs mk g cfg r peers keys B (q.step tbls₁) h'])
      else []
    | _, _ => []

/-- The labelled schedule a `VObserver` selects in one run, at most `n` steps. -/
def vplay (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers keys : List Nat) (tbls : Nat → Enrolment)
    (σ : VObserver) : Nat → VFed → List VObs → List LStep
  | 0, _, _ => []
  | n + 1, F, h =>
    match σ.next h with
    | none => []
    | some (p, l) => (p, l) :: vplay mk g cfg r peers keys tbls σ n (vapply keys g cfg r F (p.step tbls) l)
        (h ++ [vobs mk g cfg r peers keys F (p.step tbls) l])

/-- **Equal histories, the same step**, as `FedSilence.awalk_walk` states it. No rule premise is taken. -/
theorem vawalk_vwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : VObserver) :
    ∀ (n : Nat) (A B : VFed) (h : List VObs),
      (∀ y ∈ vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (vplay mk g cfg r peers keys tbls₀ σ n A h),
        y.1 = y.2) →
      vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h =
        vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (vplay mk g cfg r peers keys tbls₀ σ n A h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B h heq
    cases hσ : σ.next h with
    | none => simp only [vawalk, vplay, hσ, vwalk]
    | some ph =>
      obtain ⟨p, l⟩ := ph
      simp only [vplay, hσ] at heq ⊢
      simp only [vawalk, hσ]
      simp only [vwalk] at heq ⊢
      split
      · rename_i hguard
        simp only [hguard, if_true, List.mem_cons, forall_eq_or_imp] at heq
        obtain ⟨hhead, htail⟩ := heq
        rw [← hhead, ih _ _ _ htail]
      · rfl

/-- **SILENCE over the variant-aware receipt against an adaptive observer**, as `FedSilence.fed_silence_adaptive`
states it: the observer reads its own run's `VObs` history, the store's decisions included, and nothing else. -/
@[req "DUR-1"]
theorem vfed_silence_adaptive {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : VObserver) :
    ∀ (n : Nat) (A B : VFed) (h : List VObs), VCoupled r honest A B → FInv r honest A.lf → FInv r honest B.lf →
      vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h =
          vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B (vplay mk g cfg r peers keys tbls₀ σ n A h) ∧
        ∀ y ∈ vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h h, y.1 = y.2 := by
  intro n A B h hc hia hib
  have hw := vfed_silence (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁
    (vplay mk g cfg r peers keys tbls₀ σ n A h) A B hc hia hib
  have he := vawalk_vwalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n A B h hw
  exact ⟨he, he ▸ hw⟩

/-- **`vfed_silence_adaptive` at every initial state the federation admits with its sweep flags clear**, with an
observer that has seen nothing, nothing sent and nothing kept. -/
@[req "DUR-1"]
theorem vfed_silence_adaptive_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) (σ : VObserver) :
    ∀ n : Nat,
      vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] [] =
          vwalk mk g cfg r honest peers keys tbls₀ tbls₁ (VFed.init F) (VFed.init F)
            (vplay mk g cfg r peers keys tbls₀ σ n (VFed.init F) []) ∧
        ∀ y ∈ vawalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] [], y.1 = y.2 := by
  intro n
  have hw := vfed_silence_fresh (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers keys tbls₀ tbls₁ F hf hs
    (vplay mk g cfg r peers keys tbls₀ σ n (VFed.init F) [])
  have he := vawalk_vwalk mk g cfg r honest peers keys tbls₀ tbls₁ σ n (VFed.init F) (VFed.init F) [] hw
  exact ⟨he, he ▸ hw⟩

/-! ## The earlier domain -/

/-- **The earlier walk is this walk's `FObs` part.** `FedSilence.walk` over the schedule without its labels is
`vwalk` with the store's decisions dropped: the same stop, and the same `FedSilence.FObs` at every step. No rule
premise is taken. -/
theorem vwalk_walk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers keys : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List LStep) (A B : VFed),
      (vwalk mk g cfg r honest peers keys tbls₀ tbls₁ A B sched).map (fun y => (y.1.base, y.2.base)) =
        walk mk g cfg r honest peers tbls₀ tbls₁ A.lf B.lf (sched.map Prod.fst) := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons ph rest ih =>
    obtain ⟨p, h⟩ := ph
    intro A B
    simp only [vwalk, walk, List.map_cons]
    split
    · simp only [List.map_cons, vobs, ih]
      rfl
    · rfl

end BtcPolicy.VariantSilence
