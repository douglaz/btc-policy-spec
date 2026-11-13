import BtcPolicy.ReceiptExpiry
/-! SILENCE over the expiry-aware receipt of a partial (`DUR-1`, `NCH-24`, `SPN-41`, `POL-18`). A layer beside the
existing definitions: no definition or theorem statement changes, and no kernel event is added.

**The operation.** `ReceiptExpiry.xapply` takes a delivered partial through `ReceiptExpiry.sysRecv`: the receiving
node looks the candidate up at the step's own sample (`ReceiptExpiry.lookup`), evicts it when the lookup finds it
expired (`ReceiptExpiry.evict`), answers `UNKNOWN_CANDIDATE` unless the lookup is live (`ReceiptExpiry.answer`), and
refunds an unexposed reservation where `POL-18` permits (`Ledger.refundAtPrune`). Every other step is
`FedSilence.lapply`'s. The observer is `ReceiptExpiry.XObs`: `FedSilence.FObs` with the channel answer to a delivered
partial, by receiver, sender and answer. The answer is the response this operation adds, and it is compared whole.
An eviction addresses no message to any peer, so `FedSilence.sent` is empty at a delivery, as before.

**The walk.** `ExpirySilence.xwalk` is `FedSilence.walk` with `xapply` and `xfobs` in place of `lapply` and `fobs`.
Its stop is `walk`'s, word for word: the first step that is not admitted, or whose acting node, in either run, is
outside its own horizon (`Silence.preHorizon`) at that step's own sample or receives a request shape
`Silence.wfEvent` refuses. A delivery is a node step at the receiving node, so a delivery ends the walk exactly where
it ended `walk`; no step is added to or removed from the stop.

**What is derived.** The two runs take one schedule (`FedSilence.PStep`), so the receipt's sample, the delivered
row and its receiver are the same in both: that common schedule is the environmental premise, and it is the
experiment `FedSilence.fed_silence` already fixes. From the coupled states the proofs derive the rest of what the
receipt reads:

- the keep test is a function of the public projection and the sample (`ExpirySilence.keepsAt_factor`): a
  candidate's expiry and pair are public (`Silence.pubCand_expiry`, `Silence.pubCand_pair`), and `SPN-41`'s
  exemption reads an Escape's window, which inside the horizon is read off `Node.unarmedT`
  (`Silence.exemptEscape_factor`), as at the prune pass;
- so the lookup, the eviction decision and the answer are the same in both runs (`ExpirySilence.lookup_pub`,
  `ExpirySilence.evicts_pub`, `ExpirySilence.answer_pub`), and the registry the eviction leaves is coupled
  (`ExpirySilence.evict_pub`);
- the ledger: `POL-18`'s refund reads each row's commitment against the registry the receipt leaves, so one ledger
  between the two runs stays one ledger (`ExpirySilence.sysRecv_coupled`);
- the invariant: an eviction only drops candidates, so `Silence.NodeInv` is kept (`ExpirySilence.inv_evict`,
  `ExpirySilence.inv_receive`).

No equality of the two resulting executions is assumed: each step's coupling is derived from the coupling before
it (`ExpirySilence.xpstep_pub`).

**Results.** `ExpirySilence.xfed_silence`, `xfed_silence_fresh`, `xfed_silence_adaptive` and
`xfed_silence_adaptive_fresh` are `FedSilence.fed_silence`, `fed_silence_fresh`, `fed_silence_adaptive` and
`fed_silence_adaptive_fresh` over `xwalk`, with the same premises and the same horizon. The adaptive observer reads
the `XObs` history (`ExpirySilence.XObserver`). On a schedule where no delivery evicts in either run, the `FObs` part
of `xwalk` is `FedSilence.walk` (`ExpirySilence.xwalk_walk`), so the earlier results keep their domain and are
restated by none of these.

**Outside.** As for `FedSilence`: serialized bytes, the answer's wire encoding and its timing are not modelled, so
equal answers are equal shapes and not equal bytes, and response timing stays `F22`'s open finding. `NCH-24`'s other
checks are as `Kernel.receivePartial` models them. The variant-bound store (`VariantReceipt`), the lifecycle run and
its permits are not in this walk. The threat profile and the `SEC-10` premises are `FedSilence`'s. -/

namespace BtcPolicy.ExpirySilence

open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.ReceiptExpiry

variable {r : Rules}

/-! ## The lookup through the projection -/

/-- `ReceiptExpiry.keepsAt` read off the public projection: the candidate's expiry against the sample, or an Escape
sharing its pair that `Silence.exemptPub` exempts, with a selected Escape's window read off `unarmedT`. -/
def keepsP (r : Rules) (env : Env) (p : PubNode) (c : Cand) : Bool :=
  env.eff.atOrBefore c.expiry ||
    p.cands.any fun e => e.pair == c.pair &&
      exemptPub r env p.sel (env.eff.atOrBefore (p.unarmedT.plus p.combineSlack)) e

/-- `ReceiptExpiry.lookup` read off the public projection. -/
def lookupP (r : Rules) (env : Env) (p : PubNode) (cid : Nat) : Lookup :=
  match p.cands.find? (·.id == cid) with
  | none => .unknown
  | some c => if keepsP r env p c then .live else .expired

/-- **The keep test is public inside the horizon.** On a node carrying `Silence.NodeInv`, inside its horizon at the
receipt's sample, `NCH-24`'s keep test is a function of the node's public projection, the projected candidate and
the sample. -/
@[req "SPN-41"]
theorem keepsAt_factor (hdr : r.driverTime = .ratchet) {env : Env} {n : Node} {L : Effective}
    (hi : NodeInv r n L) (hp : preHorizon r env n = true) (c : Cand) :
    keepsAt env n c = keepsP r env (pubNode r n) (pubCand r (selIds n) c) := by
  simp only [keepsAt, keepsP, pubNode, pubCand_expiry]
  congr 1
  rw [any_comm (pubCand r (selIds n))
    (fun ee => ee.pair == (pubCand r (selIds n) c).pair &&
      exemptPub r env (selIds n) (env.eff.atOrBefore (n.unarmedT.plus n.combineSlack)) ee)
    n.cands _ (fun e he => by simp only [exemptEscape_factor hdr hi hp e he, pubCand_pair])]

/-- **The lookup is public inside the horizon.** -/
@[req "NCH-24"]
theorem lookup_factor (hdr : r.driverTime = .ratchet) {env : Env} {n : Node} {L : Effective}
    (hi : NodeInv r n L) (hp : preHorizon r env n = true) (cid : Nat) :
    lookup env n cid = lookupP r env (pubNode r n) cid := by
  have hf := find?_comm (pubCand r (selIds n)) (fun c : Cand => c.id == cid) n.cands
    (fun c : Cand => c.id == cid) (fun c _ => by simp only [pubCand_id])
  unfold lookup lookupP
  show _ = match (n.cands.map (pubCand r (selIds n))).find? (fun c => c.id == cid) with
    | none => Lookup.unknown
    | some c => if keepsP r env (pubNode r n) c then Lookup.live else Lookup.expired
  rw [← hf]
  cases n.cands.find? (fun c => c.id == cid) with
  | none => rfl
  | some c => simp only [Option.map_some, keepsAt_factor hdr hi hp c]

/-- **The two runs look the candidate up alike.** Two nodes with one public projection, each carrying
`Silence.NodeInv` and each inside its horizon at the receipt's sample, find the same lookup outcome. -/
@[req "NCH-24"]
theorem lookup_pub (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node} {La Lb : Effective}
    (hn : pubNode r na = pubNode r nb) (hia : NodeInv r na La) (hib : NodeInv r nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (cid : Nat) :
    lookup env na cid = lookup env nb cid := by
  rw [lookup_factor hdr hia hpa, lookup_factor hdr hib hpb, hn]

/-- Both evict, or neither. -/
@[req "NCH-24"]
theorem evicts_pub (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node} {La Lb : Effective}
    (hn : pubNode r na = pubNode r nb) (hia : NodeInv r na La) (hib : NodeInv r nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (cid : Nat) :
    evicts env na cid = evicts env nb cid := by
  simp only [evicts, lookup_pub hdr hn hia hib hpa hpb cid]

/-- **The answer is the same in both runs**: `UNKNOWN_CANDIDATE` in both, or found in both. -/
@[req "NCH-24"]
theorem answer_pub (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node} {La Lb : Effective}
    (hn : pubNode r na = pubNode r nb) (hia : NodeInv r na La) (hib : NodeInv r nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (cid : Nat) :
    answer env na cid = answer env nb cid := by
  simp only [answer, lookup_pub hdr hn hia hib hpa hpb cid]

/-- **The registry an eviction leaves is coupled.** The records the two lookups drop are the same records, by
projection. -/
@[req "NCH-24"]
theorem evict_pub (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node} {La Lb : Effective}
    (hn : pubNode r na = pubNode r nb) (hia : NodeInv r na La) (hib : NodeInv r nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (cid : Nat) :
    pubNode r (evict env na cid) = pubNode r (evict env nb cid) := by
  let q : Cand → Bool := fun pc => !(pc.id == cid && !keepsP r env (pubNode r na) pc)
  refine pubNode_ext_cands hn ?_
  rw [filter_comm (pubCand r (selIds na)) q na.cands _
      (fun c _ => by simp only [q, pubCand_id, keepsAt_factor hdr hia hpa c]),
    filter_comm (pubCand r (selIds nb)) q nb.cands _
      (fun c _ => by simp only [q, pubCand_id, keepsAt_factor hdr hib hpb c, hn]),
    pub_cands hn]

/-- The receipt's node, in both runs. -/
theorem receive_pub (hdr : r.driverTime = .ratchet) {env : Env} {na nb : Node} {La Lb : Effective}
    (hn : pubNode r na = pubNode r nb) (hia : NodeInv r na La) (hib : NodeInv r nb Lb)
    (hpa : preHorizon r env na = true) (hpb : preHorizon r env nb = true) (m : Sighash) (i s cid : Nat) :
    pubNode r (receive env na m i s cid) = pubNode r (receive env nb m i s cid) := by
  unfold receive
  rw [evicts_pub hdr hn hia hib hpa hpb cid]
  split
  · exact evict_pub hdr hn hia hib hpa hpb cid
  · exact receivePartial_pub hn m i s cid

/-! ## The ledger -/

theorem refundAtPrune_pub {x y : Node} (h : pubNode r x = pubNode r y) (f : Refund) (env : Env) (l : Ledger) :
    refundAtPrune f env x l = refundAtPrune f env y l := by
  unfold refundAtPrune
  refine congrArg (List.filter · l) (funext fun row => ?_)
  rw [cands_any_pub h (fun c => c.id == row.cid) (fun c => by simp [pubCand_id])
    (fun c => by simp [pubCand_id])]

/-- **The receipt, node and ledger, in both runs.** From two coupled composed states, each carrying
`Silence.NodeInv` and each inside its horizon at the receipt's sample, the receipt leaves two coupled states: the
public projections agree, the exposure histories agree, and the Hot ledger, `POL-18`'s refund included, is one
ledger. -/
@[req "POL-18"]
theorem sysRecv_coupled (hdr : r.driverTime = .ratchet) (g : Guards) (cfg : Config) {env : Env} {a b : Sys}
    (hc : Coupled r a b) (hia : NodeInv r a.world.node a.world.node.ratchet)
    (hib : NodeInv r b.world.node b.world.node.ratchet)
    (hpa : preHorizon r env a.world.node = true) (hpb : preHorizon r env b.world.node = true)
    (m : Sighash) (i s cid : Nat) :
    Coupled r (sysRecv g cfg env a m i s cid) (sysRecv g cfg env b m i s cid) := by
  have hn := receive_pub hdr hc.node hia hib hpa hpb m i s cid
  have he := evicts_pub hdr hc.node hia hib hpa hpb cid
  refine ⟨hn, by simp only [sysRecv, wstep, hc.exposure], ?_⟩
  simp only [sysRecv, wstep, hc.led, he]
  rw [markExposed_pub hn]
  split
  · rw [refundAtPrune_pub hn]
  · rfl

/-! ## The invariant -/

/-- An eviction keeps `Silence.NodeInv`: it only drops candidates. -/
theorem inv_evict {env : Env} {n : Node} {L : Effective} (hi : NodeInv r n L) (cid : Nat) :
    NodeInv r (evict env n cid) L := by
  refine inv_frame hi rfl rfl rfl rfl rfl rfl rfl ?_ ?_
  · exact hi.idsUnique.sublist ((List.filter_sublist).map Cand.id)
  · intro c hc
    exact ⟨c, (List.mem_filter.1 hc).1, rfl, rfl, rfl, rfl, rfl, rfl, id, id, rfl⟩

/-- The store keeps `Silence.NodeInv`: it only adds a signer to one record. -/
theorem inv_receivePartial {n : Node} {L : Effective} (hi : NodeInv r n L) (m : Sighash) (i s cid : Nat) :
    NodeInv r (receivePartial n m i s cid) L := by
  have hid : ∀ c, (stored m i s cid c).id = c.id := fun c => (stored_fields m i s cid c).1
  rw [receivePartial_stored]
  refine inv_frame hi rfl rfl rfl rfl rfl rfl rfl ?_ ?_
  · show ((n.cands.map (stored m i s cid)).map Cand.id).Nodup
    rw [List.map_map]
    have : (Cand.id ∘ stored m i s cid) = Cand.id := funext hid
    rw [this]
    exact hi.idsUnique
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine ⟨c, hc, ?_⟩
    unfold stored
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, id, id, rfl⟩

/-- The receipt keeps `Silence.NodeInv`, evicting or storing. -/
theorem inv_receive {env : Env} {n : Node} {L : Effective} (hi : NodeInv r n L) (m : Sighash) (i s cid : Nat) :
    NodeInv r (receive env n m i s cid) L := by
  unfold receive
  split
  · exact inv_evict hi cid
  · exact inv_receivePartial hi m i s cid

/-- The receipt moves no time ratchet. -/
theorem receive_ratchet (env : Env) (n : Node) (m : Sighash) (i s cid : Nat) :
    (receive env n m i s cid).ratchet = n.ratchet := by
  unfold receive; split <;> rfl

/-! ## One step of the walk -/

/-- A delivered partial's observation at the receiving node: the response is silent, no marker, no effect and no
visit; the pending listing and the Lockdown bit are read off the state the receipt leaves. -/
theorem obsOf_receivePartial (mk : Marker) (cfg : Config) (env : Env) {a a' b b' : Sys}
    (h : pubNode r a'.world.node = pubNode r b'.world.node) (effs : List Effect) (m : Sighash) (i s cid : Nat) :
    obsOf mk cfg r env a a' effs (.receivePartial m i s cid) =
      obsOf mk cfg r env b b' effs (.receivePartial m i s cid) := by
  simp only [obsOf, respond, markerOf, work, pending_pub h, pub_lockedDown h]

theorem xobs_ext {x y : XObs} (hb : x.base = y.base) (ha : x.answer = y.answer) : x = y := by
  cases x; cases y; simp_all

/-- A step that is not a delivered partial is `FedSilence.lapply`'s, observed as `FedSilence.fobs` with no answer. -/
theorem xapply_other (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (s : Federation.Step)
    (hs : ∀ i env x, s ≠ .deliverPartial i env x) :
    xapply g cfg r F s = lapply g cfg r F s := by
  cases s with
  | deliverPartial i env x => exact absurd rfl (hs i env x)
  | _ => rfl

theorem xfobs_other (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat) (F : LFed)
    (s : Federation.Step) (hs : ∀ i env x, s ≠ .deliverPartial i env x) :
    xfobs mk g cfg r peers F s = { base := fobs mk g cfg r peers F s, answer := none } := by
  cases s with
  | deliverPartial i env x => exact absurd rfl (hs i env x)
  | _ => rfl

/-- **One delivered partial, in both runs.** At an honest receiver inside its horizon in both runs, the
expiry-aware receipt leaves two coupled federations, keeps the invariant in each, and is observed alike, the answer
included. Nothing is assumed of the two receipts beyond the coupling before them and the common schedule step. -/
@[req "NCH-24"]
theorem deliver_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config} (hdr : r.driverTime = .ratchet)
    {honest peers : List Nat} {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A)
    (hib : FInv r honest B) {i : Nat} (hi : i ∈ honest) (env : Env) (x : Exp)
    (hpa : preHorizon r env (A.fed.worlds i).node = true) (hpb : preHorizon r env (B.fed.worlds i).node = true) :
    FCoupled r honest (xapply g cfg r A (.deliverPartial i env x)) (xapply g cfg r B (.deliverPartial i env x)) ∧
    FInv r honest (xapply g cfg r A (.deliverPartial i env x)) ∧
    FInv r honest (xapply g cfg r B (.deliverPartial i env x)) ∧
    xfobs mk g cfg r peers A (.deliverPartial i env x) = xfobs mk g cfg r peers B (.deliverPartial i env x) := by
  subst hg
  have hci := hc.node i hi
  have hiai := hia i hi
  have hibi := hib i hi
  have hcoup := sysRecv_coupled hdr g cfg (a := A.sys i) (b := B.sys i) hci hiai hibi hpa hpb
    x.msg x.input x.signer x.cid
  have hsys : ∀ (F : LFed) (j : Nat), (xapply g cfg r F (.deliverPartial i env x)).sys j =
      if j = i then sysRecv g cfg env (F.sys i) x.msg x.input x.signer x.cid else F.sys j := by
    intro F j
    by_cases h : j = i
    · subst h; simp [xapply, LFed.sys] <;> rfl
    · simp [xapply, LFed.sys, h]
  have inv : ∀ F : LFed, FInv r honest F → FInv r honest (xapply g cfg r F (.deliverPartial i env x)) := by
    intro F hF j hj
    by_cases h : j = i
    · subst h
      have := inv_receive (env := env) (hF j hj) x.msg x.input x.signer x.cid
      simpa [xapply, sysRecv, wstep, LFed.sys, receive_ratchet] using this
    · have := hF j hj
      simpa [xapply, h] using this
  refine ⟨⟨by simp only [xapply_inventories, hc.net], by simp only [xapply_inventories, hc.parts],
    by simp only [xapply_inventories, hc.extracted], fun j hj => ?_⟩, inv A hia, inv B hib, ?_⟩
  · rw [hsys, hsys]
    split
    · exact hcoup
    · exact hc.node j hj
  · have hans := answer_pub hdr hci.node hiai hibi hpa hpb x.cid
    have hobs := obsOf_receivePartial .committed cfg env (a := A.sys i) (b := B.sys i) hcoup.node []
      x.msg x.input x.signer x.cid
    refine xobs_ext ?_ ?_
    · simp only [xfobs, xlocal, hobs, xapply_inventories, hc.net, hc.parts, hc.extracted, sent, received]
    · simp only [xfobs, LFed.sys] at hans ⊢
      rw [hans]

/-- **One schedule step, in both runs**, as `FedSilence.pstep_pub` states it, over the expiry-aware receipt and its
observer. -/
theorem xpstep_pub {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) {honest peers : List Nat}
    {A B : LFed} (hc : FCoupled r honest A B) (hia : FInv r honest A) (hib : FInv r honest B)
    (p : PStep) (tbls₀ tbls₁ : Nat → Enrolment)
    (ha : Federation.admits honest A.fed (p.step tbls₀) = true)
    (hpa : inside r A (p.step tbls₀) = true) (hpb : inside r B (p.step tbls₁) = true) :
    FCoupled r honest (xapply g cfg r A (p.step tbls₀)) (xapply g cfg r B (p.step tbls₁)) ∧
    FInv r honest (xapply g cfg r A (p.step tbls₀)) ∧
    FInv r honest (xapply g cfg r B (p.step tbls₁)) ∧
    xfobs mk g cfg r peers A (p.step tbls₀) = xfobs mk g cfg r peers B (p.step tbls₁) := by
  have other : (∀ i env x, p.step tbls₀ ≠ .deliverPartial i env x) →
      (∀ i env x, p.step tbls₁ ≠ .deliverPartial i env x) →
      FCoupled r honest (xapply g cfg r A (p.step tbls₀)) (xapply g cfg r B (p.step tbls₁)) ∧
      FInv r honest (xapply g cfg r A (p.step tbls₀)) ∧
      FInv r honest (xapply g cfg r B (p.step tbls₁)) ∧
      xfobs mk g cfg r peers A (p.step tbls₀) = xfobs mk g cfg r peers B (p.step tbls₁) := by
    intro h₀ h₁
    obtain ⟨h1, h2, h3, h4⟩ := pstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr hc hia hib p
      tbls₀ tbls₁ ha hpa hpb
    rw [xapply_other g cfg r A _ h₀, xapply_other g cfg r B _ h₁, xfobs_other mk g cfg r peers A _ h₀,
      xfobs_other mk g cfg r peers B _ h₁, h4]
    exact ⟨h1, h2, h3, rfl⟩
  cases p with
  | input i env x => exact other (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | net s =>
    cases s with
    | deliverPartial i env x =>
      simp only [PStep.step, inside, Federation.actor, Bool.and_eq_true] at ha hpa hpb ⊢
      exact deliver_pub hg hdr hc hia hib (actor_honest ha rfl) env x hpa.1 hpb.1
    | _ => exact other (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

/-! ## The walk and the relation -/

/-- `FedSilence.walk` over the expiry-aware receipt: the same stop, with `ReceiptExpiry.xapply` and
`ReceiptExpiry.xfobs`. -/
def xwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) : LFed → LFed → List PStep → List (XObs × XObs)
  | _, _, [] => []
  | A, B, p :: rest =>
    if Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
        inside r B (p.step tbls₁) then
      (xfobs mk g cfg r peers A (p.step tbls₀), xfobs mk g cfg r peers B (p.step tbls₁)) ::
        xwalk mk g cfg r honest peers tbls₀ tbls₁ (xapply g cfg r A (p.step tbls₀))
          (xapply g cfg r B (p.step tbls₁)) rest
    else []

/-- **SILENCE over the expiry-aware receipt, under one fixed exogenous schedule.** `DUR-1`: "Every observable a
node emits MUST be identical between a normal-PIN and a duress-PIN request".

`FedSilence.fed_silence` with every delivered partial taken through `NCH-24`'s lookup: one schedule, two enrolment
families, two coupled federation states, and the two runs emit equal `ReceiptExpiry.XObs`, the channel answer
included, at every step of `ExpirySilence.xwalk`, whose stop is `FedSilence.walk`'s. An evicting delivery is inside
the walk wherever its receiving node is inside its horizon in both runs. The premises are `fed_silence`'s; nothing
is assumed of the receipts. -/
@[req "DUR-1"]
theorem xfed_silence {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic) (hr : r.registration = .preserve)
    (hcl : r.closeTime = .ratchet) (hdr : r.driverTime = .ratchet) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed), FCoupled r honest A B → FInv r honest A →
      FInv r honest B → ∀ y ∈ xwalk mk g cfg r honest peers tbls₀ tbls₁ A B sched, y.1 = y.2 := by
  intro sched
  induction sched with
  | nil => intro A B _ _ _ y hy; cases hy
  | cons p rest ih =>
    intro A B hc hia hib y hy
    simp only [xwalk] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨ha, hpa⟩, hpb⟩ := hguard
      obtain ⟨hc', hia', hib', hobs⟩ :=
        xpstep_pub (g := g) (cfg := cfg) (peers := peers) hg ht hd hr hcl hdr hc hia hib p tbls₀ tbls₁ ha hpa hpb
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hobs
      · exact ih _ _ hc' hia' hib' y hy
    · cases hy

/-! ## The initial boundary -/

theorem sysRecv_u (g : Guards) (cfg : Config) (env : Env) {s s' : Sys} {u : Wall} (h : s = withUnarmedT s' u)
    (m : Sighash) (i sg cid : Nat) :
    sysRecv g cfg env s m i sg cid = withUnarmedT (sysRecv g cfg env s' m i sg cid) u := by
  subst h
  have he : evicts env (withUnarmedT s' u).world.node cid = evicts env s'.world.node cid := rfl
  simp only [sysRecv, wstep, receive, he]
  cases evicts env s'.world.node cid <;> rfl

theorem xapply_u {g : Guards} {cfg : Config} {r : Rules} {A A' : LFed} (h : UEq A A') (s : Federation.Step) :
    UEq (xapply g cfg r A s) (xapply g cfg r A' s) := by
  cases s with
  | deliverPartial i env x =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      obtain ⟨u, hu⟩ := h4 j
      exact ⟨u, by simpa [xapply, LFed.sys] using sysRecv_u g cfg env hu x.msg x.input x.signer x.cid⟩
    · simpa [xapply, LFed.sys, hj] using h4 j
  | _ => exact (lapply_u (mk := .committed) (honest := []) (peers := []) h _).1

theorem xfobs_u {mk : Marker} {g : Guards} {cfg : Config} {r : Rules} {peers : List Nat} {A A' : LFed}
    (h : UEq A A') (s : Federation.Step) : xfobs mk g cfg r peers A s = xfobs mk g cfg r peers A' s := by
  cases s with
  | deliverPartial i env x =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨u, hu⟩ := h4 i
    have hs := sysRecv_u g cfg env hu x.msg x.input x.signer x.cid
    have hw : (A.fed.worlds i).node = { (A'.fed.worlds i).node with unarmedT := u } := by
      have := congrArg (fun s : Sys => s.world.node) hu
      simpa [LFed.sys, withUnarmedT] using this
    simp only [xfobs, xlocal, xapply_inventories, h1, h2, h3, sent, received]
    rw [hs, hu, obsOf_unarmedT, hw]
    rfl
  | _ =>
    rw [xfobs_other mk g cfg r peers A _ (fun _ _ _ h => by cases h),
      xfobs_other mk g cfg r peers A' _ (fun _ _ _ h => by cases h),
      (lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := []) (peers := peers) h _).2.2.2]

theorem xwalk_u (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B A' B' : LFed), UEq A A' → UEq B B' →
      xwalk mk g cfg r honest peers tbls₀ tbls₁ A B sched =
        xwalk mk g cfg r honest peers tbls₀ tbls₁ A' B' sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons p rest ih =>
    intro A B A' B' ha hb
    obtain ⟨_, adA, inA, _⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) ha (p.step tbls₀)
    obtain ⟨_, _, inB, _⟩ := lapply_u (mk := mk) (g := g) (cfg := cfg) (r := r) (honest := honest)
      (peers := peers) hb (p.step tbls₁)
    simp only [xwalk, adA, inA, inB, xfobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) ha,
      xfobs_u (mk := mk) (g := g) (cfg := cfg) (peers := peers) hb,
      ih _ _ _ _ (xapply_u (g := g) (cfg := cfg) ha _) (xapply_u (g := g) (cfg := cfg) hb _)]

/-- **`xfed_silence` at every initial state the federation admits with its sweep flags clear**, as
`FedSilence.fed_silence_fresh` states it. -/
@[req "DUR-1"]
theorem xfed_silence_fresh {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) :
    ∀ (sched : List PStep), ∀ y ∈ xwalk mk g cfg r honest peers tbls₀ tbls₁ F F sched, y.1 = y.2 := by
  intro sched y hy
  let F' := withU F (fun i => (F.fed.worlds i).node.T)
  have hu : UEq F F' :=
    ⟨rfl, rfl, rfl, fun i => ⟨(F.fed.worlds i).node.unarmedT, rfl⟩⟩
  rw [xwalk_u mk g cfg r honest peers tbls₀ tbls₁ sched F F F' F' hu hu] at hy
  have hinv : FInv r honest F' := by
    intro i hi
    obtain ⟨_, _, ha, hc, _, _⟩ := hf.2.2 i hi
    exact nodeInv_initial (F'.fed.worlds i).node _ hc ha (hs i hi) rfl
  exact xfed_silence hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ sched F' F' (fcoupled_refl r honest F')
    hinv hinv y hy

/-! ## An adaptive observer over the `XObs` history -/

/-- `FedSilence.Observer` reading the observations this walk emits, answers included: its next schedule step is a
function of its own run's `XObs` history alone. -/
structure XObserver where
  next : List XObs → Option PStep

/-- A scheduler that may also read the state it is about to step. -/
abbrev XScheduler := LFed → List XObs → Option PStep

def XObserver.sched (σ : XObserver) : XScheduler := fun _ h => σ.next h

/-- `FedSilence.awalk` over the expiry-aware receipt. -/
def xawalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (c : XScheduler) :
    Nat → LFed → LFed → List XObs → List XObs → List (XObs × XObs)
  | 0, _, _, _, _ => []
  | n + 1, A, B, hA, hB =>
    match c A hA, c B hB with
    | some p, some q =>
      if Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
          inside r B (q.step tbls₁) then
        (xfobs mk g cfg r peers A (p.step tbls₀), xfobs mk g cfg r peers B (q.step tbls₁)) ::
          xawalk mk g cfg r honest peers tbls₀ tbls₁ c n (xapply g cfg r A (p.step tbls₀))
            (xapply g cfg r B (q.step tbls₁)) (hA ++ [xfobs mk g cfg r peers A (p.step tbls₀)])
            (hB ++ [xfobs mk g cfg r peers B (q.step tbls₁)])
      else []
    | _, _ => []

/-- The schedule an `XObserver` selects in one run, at most `n` steps. -/
def xplay (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat)
    (tbls : Nat → Enrolment) (σ : XObserver) : Nat → LFed → List XObs → List PStep
  | 0, _, _ => []
  | n + 1, F, h =>
    match σ.next h with
    | none => []
    | some p => p :: xplay mk g cfg r peers tbls σ n (xapply g cfg r F (p.step tbls))
        (h ++ [xfobs mk g cfg r peers F (p.step tbls)])

/-- **Equal histories, the same step**, as `FedSilence.awalk_walk` states it. No rule premise is taken. -/
theorem xawalk_xwalk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (σ : XObserver) :
    ∀ (n : Nat) (A B : LFed) (h : List XObs),
      (∀ y ∈ xwalk mk g cfg r honest peers tbls₀ tbls₁ A B (xplay mk g cfg r peers tbls₀ σ n A h), y.1 = y.2) →
      xawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
        xwalk mk g cfg r honest peers tbls₀ tbls₁ A B (xplay mk g cfg r peers tbls₀ σ n A h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro A B h heq
    cases hσ : σ.next h with
    | none => simp only [xawalk, XObserver.sched, xplay, hσ, xwalk]
    | some p =>
      simp only [xplay, hσ] at heq ⊢
      simp only [xawalk, XObserver.sched, hσ]
      simp only [xwalk] at heq ⊢
      split
      · rename_i hguard
        simp only [hguard, if_true, List.mem_cons, forall_eq_or_imp] at heq
        obtain ⟨hhead, htail⟩ := heq
        rw [← hhead, ih _ _ _ htail]
      · rfl

/-- **SILENCE over the expiry-aware receipt against an adaptive observer**, as `FedSilence.fed_silence_adaptive`
states it: the observer reads its own run's `XObs` history, answers included, and nothing else. -/
@[req "DUR-1"]
theorem xfed_silence_adaptive {mk : Marker} (hg : mk = .committed) {g : Guards} {cfg : Config}
    (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (σ : XObserver) :
    ∀ (n : Nat) (A B : LFed) (h : List XObs), FCoupled r honest A B → FInv r honest A →
      FInv r honest B →
      xawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h =
          xwalk mk g cfg r honest peers tbls₀ tbls₁ A B (xplay mk g cfg r peers tbls₀ σ n A h) ∧
        ∀ y ∈ xawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n A B h h, y.1 = y.2 := by
  intro n A B h hc hia hib
  have hw := xfed_silence (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁
    (xplay mk g cfg r peers tbls₀ σ n A h) A B hc hia hib
  have he := xawalk_xwalk mk g cfg r honest peers tbls₀ tbls₁ σ n A B h hw
  exact ⟨he, he ▸ hw⟩

/-- **`xfed_silence_adaptive` at every initial state the federation admits with its sweep flags clear**, with an
observer that has seen nothing. -/
@[req "DUR-1"]
theorem xfed_silence_adaptive_fresh {mk : Marker} (hg : mk = .committed) {g : Guards}
    {cfg : Config} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (honest peers : List Nat) (tbls₀ tbls₁ : Nat → Enrolment)
    (F : LFed) (hf : Federation.Fresh honest F.fed)
    (hs : ∀ i ∈ honest, (F.fed.worlds i).node.sweepActive = false) (σ : XObserver) :
    ∀ n : Nat,
      xawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [] =
          xwalk mk g cfg r honest peers tbls₀ tbls₁ F F (xplay mk g cfg r peers tbls₀ σ n F []) ∧
        ∀ y ∈ xawalk mk g cfg r honest peers tbls₀ tbls₁ σ.sched n F F [] [], y.1 = y.2 := by
  intro n
  have hw := xfed_silence_fresh (g := g) (cfg := cfg) hg ht hd hr hcl hdr honest peers tbls₀ tbls₁ F hf hs
    (xplay mk g cfg r peers tbls₀ σ n F [])
  have he := xawalk_xwalk mk g cfg r honest peers tbls₀ tbls₁ σ n F F [] hw
  exact ⟨he, he ▸ hw⟩

/-! ## The earlier domain -/

/-- **Off evictions, the earlier walk is this walk's `FObs` part.** On a schedule where no delivery evicts in either
run, `FedSilence.walk` is `xwalk` with each answer dropped: the same stop, and the same `FedSilence.FObs` at every
step. No rule premise is taken. -/
theorem xwalk_walk (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (honest peers : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) :
    ∀ (sched : List PStep) (A B : LFed),
      unevicted g cfg r A (sched.map (·.step tbls₀)) = true →
      unevicted g cfg r B (sched.map (·.step tbls₁)) = true →
      (xwalk mk g cfg r honest peers tbls₀ tbls₁ A B sched).map (fun y => (y.1.base, y.2.base)) =
        walk mk g cfg r honest peers tbls₀ tbls₁ A B sched := by
  intro sched
  induction sched with
  | nil => intros; rfl
  | cons p rest ih =>
    intro A B ha hb
    simp only [List.map_cons, unevicted, Bool.and_eq_true, Bool.not_eq_true'] at ha hb
    have hxa := xapply_unevicted g cfg r A _ ha.1
    have hxb := xapply_unevicted g cfg r B _ hb.1
    have h2a := ha.2
    have h2b := hb.2
    rw [hxa] at h2a
    rw [hxb] at h2b
    simp only [xwalk, walk]
    by_cases hc : (Federation.admits honest A.fed (p.step tbls₀) && inside r A (p.step tbls₀) &&
        inside r B (p.step tbls₁)) = true
    · rw [if_pos hc, if_pos hc, List.map_cons, xfobs_unevicted mk g cfg r peers A _ ha.1,
        xfobs_unevicted mk g cfg r peers B _ hb.1, hxa, hxb, ih _ _ h2a h2b]
    · rw [if_neg hc, if_neg hc]
      rfl

end BtcPolicy.ExpirySilence
