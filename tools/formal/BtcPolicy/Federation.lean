import BtcPolicy.Kernel
import BtcPolicy.Authority
import BtcPolicy.Gates
/-! The federation composition: several honest nodes over one explicit relay inventory, each moved
by the kernel's own `Kernel.step` and nothing else. There is no second release machine here. A
stronger result about a federation is stated over `Federation.Execution`; `Kernel.Reachable` and
`Kernel.Execution` stay as they are, with their unconstrained environment events.

**What it establishes.** `Federation.project_execution`: the projection of a composed execution to an
honest node is a `Kernel.Execution` of that node, and a step that is not that node's stutters
(`Federation.stutter`). So `Kernel.hot_release_provenance` applies to an honest node of a federation
with its `hx` supplied (`Federation.hot_release_provenance`). `Federation.receipt_origin` is the first
fact about two signers read off one execution: a relay an honest node received under an honest
sender's name means that sender processed the request. `Federation.honest_exposure_provenance` derives
`Kernel.HonestExposureProvenance` for the whole partial inventory, with each signer's history its own
projection and the cumulative extracted set as the compromised list, by induction over the execution
(`Federation.part_origin`, `Federation.queued_release_provenance`); `Federation.no_exposed_quorum` is
`Kernel.no_exposed_quorum_without_normal` with that premise discharged. The message binding
(`Federation.HotBinding`), the absence of honest normal decisions and the bound on the extracted set
stay premises.

**Two message families.** A `Federation.Relay` is the Carrier relay, by sender and Carrier identity.
`SPN-35` says "one relay of the verbatim request to every peer"; the body and the recipient are not
carried, so two nodes' `accept` inputs for one identity are not tied to each other, and a request a
peer learns from a relay is an `accept` of that peer beside the delivery that counts the sender.
A partial is a `Kernel.Exp` row in the partial inventory `Fed.parts`. An honest node's partials enter
it in the step that queues them, one per input of the released candidate (`Federation.fanout`):
`SPN-38`'s cursor "records that a rung has been queued for transport, not that a peer received it",
so a queued partial has crossed the release boundary and reached nobody. `Step.deliverPartial` hands
one to a named node, which runs the kernel's `Event.receivePartial` on it: that node's kernel store
then holds it as far as `Kernel.receivePartial`'s guard admits, which is input 0 only, and no other
node holds it. `Federation.held` is the same node's possession on every input.

**Extracted keys.** `Fed.extracted` is the cumulative set of signers whose signing key the adversary
has copied (`Step.extract`), and only a signer in it can sign a partial outside an honest node's own
release (`Step.forge`). Nothing removes a signer from it: a node's death, or a host that stops
misbehaving, leaves a copied key copied, and `Federation.no_exposed_quorum` bounds this set, not the
hosts misbehaving at one instant. A key can be extracted from a node on the honest list, which then
keeps following its own rules. Every key is taken to be authorized by the coin: key rotation is not
modelled. A copied signing key gives partials, not relays: a relay under an honest node's name stays
that node's own (`Federation.relay_origin`), so channel-key theft from an honest node is outside.

**The network.** Both inventories only grow. Delivery reads them and removes nothing, so a replay is
the same delivery taken again, a drop is one never taken, and delay is any later step. Nothing
requires a delivery: there is no delivery guarantee, no fairness and no agreement here.

**Ideal authentication, a boundary and not a proof.** `Step.inject` may only name a sender outside
the honest list, and `Step.deliver` hands the kernel the sender the relay names. That is `NCH-5`'s
"possession of the channel key is proven per message by the envelope signature" taken as given, with
the signature scheme unmodelled. Authentication proves identity and not honesty: an injected relay
need not correspond to anything its sender processed. A partial's signer is read the same way:
`NCH-24`'s "signer equals sender" is taken as given, so a partial naming a signer outside
`Fed.extracted` is one that signer's honest node queued (`Federation.part_origin`), with the
signature scheme unmodelled.

**Domain.** The honest list is fixed for the whole execution, and a node outside it has no world
here, only a name on injected relays and, once extracted, on partials. Every step's `Env` is
arbitrary and per node, as in `Kernel.Execution`: clocks and chain views are neither shared nor
ordered across nodes, and no comparison between two nodes' samples appears. Thresholds and overlays
start unconstrained, also as there, and nothing says two nodes share a threshold. The extracted set
starts unconstrained too. An honest node's local alphabet leaves out `Event.adversaryExposes`, and
takes `Event.receipt` and `Event.receivePartial` only through a delivery. A node's death is its
taking no further step. -/

namespace BtcPolicy.Federation
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## State and steps -/

/-- One relay in the inventory: who it names as sender, and which Carrier. -/
@[req "DUR-5"]
structure Relay where
  sender : Nat
  cid : Nat
  deriving DecidableEq, Repr

/-- One federation's state: each honest node's `Kernel.World`, read at its own id, the relay
inventory, the partial inventory and the extracted signers. The function is total, and only an
honest id's value is ever read or written. -/
structure Fed where
  worlds : Nat → World
  net : List Relay
  /-- Every partial that has left a signer, honest or forged: `POL-18`'s "A partial that has left
  the node", for the whole federation. -/
  parts : List Exp := []
  /-- The signers whose key the adversary holds, cumulatively. -/
  extracted : List Nat := []

/-- A kernel event a node takes on its own, with no network input: every event but the three whose
source is outside it. `Event.receipt` arrives through `Step.deliver`. -/
def ownEvent : Event → Bool
  | .receipt .. | .adversaryExposes .. | .receivePartial .. => false
  | _ => true

/-- This node consumed the nonce of this Carrier, as far as the kernel can read that: a resident
Carrier or a retained tombstone. Holder decisions retire the Carrier before its outbox need have
drained, which is why a tombstone counts. -/
def consumed (n : Node) (cid : Nat) : Bool :=
  n.carriers.any (·.cid == cid) || n.tombstones.any (·.cid == cid)

inductive Step
  /-- A node takes one of its own kernel events: local processing. It establishes that this node
  processed something, not that any peer received it. -/
  | process (i : Nat) (env : Env) (e : Event)
  /-- `SPN-9`: "**At gate 10** the refusal propagates but does not stage", so this node consumes
  the nonce and relays with no kernel transition, no Carrier and no partial. `Kernel.Event.refuse`
  covers only a refusal that stages, and `Federation.unstaged_is_gate_ten` says this is the one
  such row. The kernel has nowhere to hold that nonce, so a later `accept` of the same Carrier stays
  in the alphabet, an overapproximation. -/
  | unstaged (i cid : Nat)
  /-- An honest node's relay of a Carrier it staged enters the inventory. -/
  | emit (i cid : Nat)
  /-- A relay naming a sender outside the honest list enters the inventory. -/
  | inject (m : Relay)
  /-- A relay in the inventory reaches a node, which runs the kernel's receipt on it. A copy
  reaching its own sender is in the alphabet: `Kernel.addSender` adds nothing for it. -/
  | deliver (i : Nat) (env : Env) (m : Relay)
  /-- A partial in the inventory reaches a node, which runs the kernel's `receivePartial` on it. It
  establishes that this node obtained it, not that any other node did. -/
  | deliverPartial (i : Nat) (env : Env) (x : Exp)
  /-- The adversary copies this signer's key. -/
  | extract (j : Nat)
  /-- A partial signed with an extracted key enters the inventory. -/
  | forge (x : Exp)
  deriving DecidableEq, Repr

/-- Which steps may be taken. `NCH-28`: "a node MUST NOT relay a request whose nonce it did not
consume", at `Step.emit`; a copy of a request whose nonce this node already consumed is not relayed
at gate 10 either, since `SPN-5` refuses it at gate 7, whose row propagates nothing. A relay reaches
a node only out of the inventory, and so does a partial. `Step.inject`'s guard is the authentication
boundary, and `Step.forge`'s is the same boundary for partials. -/
@[req "NCH-28"]
def admits (honest : List Nat) (f : Fed) : Step → Bool
  | .process i _ e => honest.contains i && ownEvent e
  | .unstaged i cid => honest.contains i && !consumed (f.worlds i).node cid
  | .emit i cid => honest.contains i && consumed (f.worlds i).node cid
  | .inject m => !honest.contains m.sender
  | .deliver i _ m => honest.contains i && f.net.contains m
  | .deliverPartial i _ x => honest.contains i && f.parts.contains x
  | .extract _ => true
  | .forge x => f.extracted.contains x.signer

/-- `SPN-5`'s table has one row that propagates a failure without staging it, which is what
`Step.unstaged` stands for. Row 22 stages the same set it propagates. -/
@[req "SPN-5"]
theorem unstaged_is_gate_ten :
    (Gates.rows.filter fun row => row.propagates == .yes && row.stages == .no).map (·.label) =
      ["10"] := by
  decide

/-- Advance one node by the kernel's own step. This is the only writer of `Fed.worlds`. -/
def advance (r : Rules) (f : Fed) (i : Nat) (env : Env) (e : Event) : Fed :=
  { f with worlds := fun j => if j = i then (step r env (f.worlds i) e).1 else f.worlds j }

/-- The partials a step's effects queue, as the rows `Kernel.step` appends to this world's exposure
for them: the same function of the same effects. -/
@[req "SPN-38"]
def outbox (w : World) (effs : List Effect) : List Exp :=
  effs.filterMap fun
    | .queuePartial m i h c => some { msg := m, input := i, signer := w.node.id, hot := h, cid := c }
    | .broadcast _ => none

/-- The other inputs of a queued row's candidate: one row per input after the first, each on that
input's own message, with the queued row's signer, class and commitment. The candidate is the one
with the row's commitment id and input-0 message in the world the row was queued in. -/
def others (w : World) (x : Exp) : List Exp :=
  match w.node.cands.find? (fun c => c.id == x.cid && sighash c.tx 0 == x.msg) with
  | some c => ((List.range c.tx.inputs.length).drop 1).map fun k =>
      { x with msg := sighash c.tx k, input := k }
  | none => []

/-- The partials a step sends, one per input. `NCH-23` says "it sends one message per released rung
per signed input to every peer". The kernel's queued row is input 0, where it stands for every
input (`Kernel.Effect.queuePartial`); here it is kept as it is and followed by its candidate's other
inputs (`Federation.others`), so each input's partial can be delivered, dropped or replayed on its
own. -/
@[req "NCH-23"]
def fanout (w : World) (effs : List Effect) : List Exp :=
  (outbox w effs).flatMap fun x => x :: others w x

def apply (r : Rules) (f : Fed) : Step → Fed
  | .process i env e =>
    { advance r f i env e with parts := f.parts ++ fanout (f.worlds i) (step r env (f.worlds i) e).2 }
  | .deliver i env m => advance r f i env (.receipt m.cid m.sender)
  | .deliverPartial i env x => advance r f i env (.receivePartial x.msg x.input x.signer x.cid)
  | .unstaged i cid | .emit i cid => { f with net := f.net ++ [⟨i, cid⟩] }
  | .inject m => { f with net := f.net ++ [m] }
  | .extract j => { f with extracted := f.extracted ++ [j] }
  | .forge x => { f with parts := f.parts ++ [x] }

/-- `Kernel.Execution`'s initial boundary at every honest id, with that id on the node, plus two
things. Both inventories are empty, and so are the tombstones, which `Kernel.Execution` leaves open:
a seeded tombstone would be a consumed nonce with no event behind it, and `Step.emit` reads it. -/
def Fresh (honest : List Nat) (f : Fed) : Prop :=
  f.net = [] ∧ f.parts = [] ∧ ∀ i ∈ honest,
    (f.worlds i).exposure = [] ∧ (f.worlds i).node.id = i ∧ (f.worlds i).node.armed = false ∧
      (f.worlds i).node.cands = [] ∧ (f.worlds i).node.carriers = [] ∧
      (f.worlds i).node.tombstones = []

/-- A composed history, newest first, each step with the state it was taken in. Proof evidence
only: no transition reads it. -/
abbrev Trace := List (Fed × Step)

/-- A reachable federation execution, retaining its trace. -/
inductive Execution (r : Rules) (honest : List Nat) : Trace → Fed → Prop
  | init (f : Fed) (h : Fresh honest f) : Execution r honest [] f
  | next {t f} (s : Step) (ha : admits honest f s = true) : Execution r honest t f →
      Execution r honest ((f, s) :: t) (apply r f s)

/-- A schedule run through `apply` from `f`, with no admission test. -/
def run (r : Rules) : Fed → List Step → Fed
  | f, [] => f
  | f, s :: ss => run r (apply r f s) ss

/-- The trace that schedule leaves on top of `t`, newest first, each step with the state it was
taken in. -/
def runTrace (r : Rules) : Trace → Fed → List Step → Trace
  | t, _, [] => t
  | t, f, s :: ss => runTrace r ((f, s) :: t) (apply r f s) ss

/-! ## The projection to one node -/

/-- Whose kernel event a step is, if it is one. -/
def actor : Step → Option (Nat × Env × Event)
  | .process i env e => some (i, env, e)
  | .deliver i env m => some (i, env, .receipt m.cid m.sender)
  | .deliverPartial i env x => some (i, env, .receivePartial x.msg x.input x.signer x.cid)
  | _ => none

/-- One node's own history out of a composed one, in `Kernel.History`'s form. -/
def project (i : Nat) : Trace → History
  | [] => []
  | (f, s) :: t =>
    match actor s with
    | some (j, env, e) =>
      if j = i then (f.worlds i, env, e) :: project i t else project i t
    | none => project i t

theorem apply_of_actor (r : Rules) (f : Fed) (s : Step) {j : Nat} {env : Env} {e : Event}
    (hs : actor s = some (j, env, e)) (i : Nat) :
    (apply r f s).worlds i = if i = j then (step r env (f.worlds j) e).1 else f.worlds i := by
  cases s <;> simp only [actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := hs
    rfl

theorem apply_no_actor (r : Rules) (f : Fed) (s : Step) (hs : actor s = none) (i : Nat) :
    (apply r f s).worlds i = f.worlds i := by
  cases s <;> first | rfl | simp [actor] at hs

/-- A step that is not this node's changes nothing this node reads and adds nothing to its
projection: network-only steps and other nodes' steps stutter locally. -/
theorem stutter (r : Rules) (f : Fed) (s : Step) (t : Trace) (i : Nat)
    (hs : ∀ env e, actor s ≠ some (i, env, e)) :
    (apply r f s).worlds i = f.worlds i ∧ project i ((f, s) :: t) = project i t := by
  cases hact : actor s with
  | none => exact ⟨apply_no_actor r f s hact i, by simp [project, hact]⟩
  | some x =>
    obtain ⟨j, env, e⟩ := x
    have hji : j ≠ i := fun h => hs env e (by rw [hact, h])
    constructor
    · rw [apply_of_actor r f s hact i, if_neg (Ne.symm hji)]
    · simp [project, hact, hji]

/-- The target: every honest node's projected execution is a valid `Kernel.Execution` ending at that
node's world in this federation state. The proof reads `Fresh` and that `Kernel.step` is the only
writer of a world, not which relays were delivered, so it holds of every schedule. -/
@[req "DUR-5"]
theorem project_execution {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i : Nat} (hi : i ∈ honest) :
    Kernel.Execution r (project i t) (f.worlds i) := by
  induction hx with
  | init f h =>
    obtain ⟨hexp, _, harmed, hcands, hcarriers, _⟩ := h.2.2 i hi
    have hw : f.worlds i = { node := (f.worlds i).node, exposure := [] } := by
      rw [← hexp]
    rw [hw]
    exact .init _ ⟨harmed, hcands, hcarriers⟩
  | @next t f s _ _ ih =>
    cases hact : actor s with
    | none =>
      rw [(stutter r f s t i (by simp [hact])).1, (stutter r f s t i (by simp [hact])).2]
      exact ih
    | some x =>
      obtain ⟨j, env, e⟩ := x
      by_cases hj : j = i
      · subst hj
        rw [apply_of_actor r f s hact j, if_pos rfl]
        simp only [project, hact, if_true]
        exact .next env e ih
      · have hne : ∀ env' e', actor s ≠ some (i, env', e') := by
          intro env' e' h
          rw [hact] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact hj h.1
        rw [(stutter r f s t i hne).1, (stutter r f s t i hne).2]
        exact ih

/-- A node's id has no writer, so an honest world is that id's for the whole execution. -/
theorem node_id {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i : Nat} (hi : i ∈ honest) : (f.worlds i).node.id = i := by
  induction hx with
  | init f h => exact (h.2.2 i hi).2.1
  | @next t f s _ _ ih =>
    cases hact : actor s with
    | none => rw [apply_no_actor r f s hact i]; exact ih
    | some x =>
      obtain ⟨j, env, e⟩ := x
      rw [apply_of_actor r f s hact i]
      split
      · rename_i h
        subst h
        rw [step_id]
        exact ih
      · exact ih

/-- `Kernel.hot_release_provenance` at an honest node of a federation: its execution premise is
discharged here, its accepted-only refusal rule is not. Other signers' rows and every other boundary
of that theorem stay as they are. -/
@[req "DUR-8"]
theorem hot_release_provenance {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) {i : Nat}
    (hi : i ∈ honest) (env : Env) (e : Event) (msg : Sighash) (cid : Nat)
    (he : Effect.queuePartial msg 0 true cid ∈ (step r env (f.worlds i) e).2) :
    (f.worlds i).node.armed = false ∧ NormalRelease r (project i t) i msg cid := by
  have h := Kernel.hot_release_provenance r hr (project_execution hx hi) env e msg cid he
  rw [node_id hx hi] at h
  exact h

/-! ## Where a relay comes from -/

/-- The kernel events that can consume a Carrier's nonce. -/
def ingress (cid : Nat) : Event → Bool
  | .accept c .. | .refuse c .. => c == cid
  | _ => false

theorem consumed_refuse (r : Rules) (env : Env) (n : Node) (c : Nat) (d : Bool) (E : Wall)
    (p : Option (Nat × Nat)) (cid : Nat) (h : consumed (refuse r env n c d E p) cid = true) :
    consumed n cid = true ∨ c = cid := by
  unfold refuse at h
  split at h
  · exact .inl h
  · split at h
    · exact .inl h
    · simp only [consumed, List.any_cons, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with (h | h) | h
      · exact .inr h
      · exact .inl (.inl h)
      · exact .inl (.inr h)

theorem consumed_accept (r : Rules) (env : Env) (n : Node) (c : Nat) (d : Bool) (E : Wall)
    (sp es : Cand) (cid : Nat) (h : consumed (accept r env n c d E sp es) cid = true) :
    consumed n cid = true ∨ c = cid := by
  unfold accept at h
  split at h
  · exact consumed_refuse r env n c d E _ cid h
  · split at h
    · exact .inl h
    · simp only [consumed, List.any_cons, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with (h | h) | h
      · exact .inr h
      · exact .inl (.inl h)
      · exact .inl (.inr h)

theorem consumed_receipt (r : Rules) (env : Env) (n : Node) (c s : Nat) (cid : Nat)
    (h : consumed (receipt r env n c s) cid = true) : consumed n cid = true := by
  unfold receipt at h
  split at h
  · exact h
  · rename_i k hk
    have hkm : k ∈ n.carriers := List.mem_of_find?_eq_some hk
    split at h
    · exact h
    · split at h
      · simp only [consumed, holderDecision, Carrier.tombstone, List.any_cons, Bool.or_eq_true,
          beq_iff_eq, List.any_eq_true, List.mem_filter] at h ⊢
        rcases h with ⟨x, ⟨hx, _⟩, hc⟩ | h | h
        · exact .inl ⟨x, hx, hc⟩
        · exact .inl ⟨k, hkm, by simpa using h⟩
        · exact .inr h
      · simp only [consumed, List.any_map, Bool.or_eq_true, List.any_eq_true,
          Function.comp_apply] at h ⊢
        rcases h with ⟨x, hx, hc⟩ | h
        · refine .inl ⟨x, hx, ?_⟩
          split at hc
          · rename_i hxc
            simp only [beq_iff_eq] at hxc hc ⊢
            have := (List.find?_some hk)
            simp only [beq_iff_eq] at this
            simpa [hxc, ← this] using hc
          · exact hc
        · exact .inr h

theorem consumed_tick (r : Rules) (env : Env) (n : Node) (cid : Nat)
    (h : consumed (tick r env n) cid = true) : consumed n cid = true := by
  simp only [consumed, tick, Bool.or_eq_true, List.any_eq_true, List.mem_filter, List.mem_append,
    List.mem_map] at h ⊢
  rcases h with ⟨x, ⟨hx, _⟩, hc⟩ | ⟨x, ⟨hx | ⟨k, ⟨hk, _⟩, rfl⟩, _⟩, hc⟩
  · exact .inl ⟨x, hx, hc⟩
  · exact .inr ⟨x, hx, hc⟩
  · exact .inl ⟨k, hk, by simpa [Carrier.tombstone] using hc⟩

/-- A step adds a consumed Carrier only by an ingress event naming it. -/
theorem consumed_step (r : Rules) (env : Env) (w : World) (e : Event) (cid : Nat)
    (h : consumed (step r env w e).1.node cid = true) :
    consumed w.node cid = true ∨ ingress cid e = true := by
  cases e with
  | accept c d E sp es =>
    rcases consumed_accept r env w.node c d E sp es cid h with h | h
    · exact .inl h
    · exact .inr (by simp [ingress, h])
  | refuse c d E p code =>
    rcases consumed_refuse r env w.node c d E p cid h with h | h
    · exact .inl h
    · exact .inr (by simp [ingress, h])
  | receipt c s => exact .inl (consumed_receipt r env w.node c s cid h)
  | tick => exact .inl (consumed_tick r env w.node cid h)
  | firePass =>
    simp only [step, firePass] at h
    split at h <;> exact .inl h
  | send c =>
    simp only [step, send] at h
    split at h <;> exact .inl h
  | settle tx =>
    simp only [step, settle] at h
    split at h <;> exact .inl h
  | packageAccepted c => exact .inl h
  | prune => exact .inl h
  | panic => exact .inl h
  | adversaryExposes m i s c => exact .inl h
  | receivePartial m i s c => exact .inl h
  | clawback x => exact .inl (by simpa [step, consumed] using h)

/-- This node processed this Carrier's request, by what the composed trace shows: an ingress event
in its own projection, or the unstaged refusal. Processing is all it says: no freeze, no signature,
and no claim about a peer (`DUR-5`). -/
def Processed (t : Trace) (i cid : Nat) : Prop :=
  (∃ g, (g, Step.unstaged i cid) ∈ t) ∨ ∃ w env e, (w, env, e) ∈ project i t ∧ ingress cid e = true

theorem Processed.cons {t : Trace} {i cid : Nat} (x : Fed × Step) (h : Processed t i cid) :
    Processed (x :: t) i cid := by
  rcases h with ⟨g, hg⟩ | ⟨w, env, e, hm, hi⟩
  · exact .inl ⟨g, List.mem_cons_of_mem x hg⟩
  · refine .inr ⟨w, env, e, ?_, hi⟩
    obtain ⟨f, s⟩ := x
    simp only [project]
    split
    · split
      · exact List.mem_cons_of_mem _ hm
      · exact hm
    · exact hm

/-- A Carrier an honest node's kernel state shows consumed has its ingress event in that node's own
projection. -/
theorem processed_of_consumed {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i cid : Nat} (hi : i ∈ honest)
    (hc : consumed (f.worlds i).node cid = true) : Processed t i cid := by
  induction hx with
  | init f h =>
    obtain ⟨_, _, _, _, hcarriers, htomb⟩ := h.2.2 i hi
    simp [consumed, hcarriers, htomb] at hc
  | @next t f s _ _ ih =>
    cases hact : actor s with
    | none =>
      rw [apply_no_actor r f s hact i] at hc
      exact (ih hc).cons _
    | some x =>
      obtain ⟨j, env, e⟩ := x
      rw [apply_of_actor r f s hact i] at hc
      split at hc
      · rename_i hij
        subst hij
        rcases consumed_step r env _ e cid hc with h | h
        · exact (ih h).cons _
        · refine .inr ⟨f.worlds i, env, e, ?_, h⟩
          simp [project, hact]
      · exact (ih hc).cons _

/-- `NCH-28` over a composed execution: a relay in the inventory that names an honest sender is that
sender's own, and that sender processed the request. A replayed relay has this same origin; one
sender's many deliveries are one origin here, so this is no one-send-per-receive correspondence. -/
@[req "NCH-28"]
theorem relay_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {m : Relay} (hm : m ∈ f.net) (hs : m.sender ∈ honest) :
    Processed t m.sender m.cid := by
  induction hx with
  | init f h => rw [h.1] at hm; cases hm
  | @next t f s ha hx ih =>
    cases s with
    | process i env e => exact (ih hm).cons _
    | deliver i env m' => exact (ih hm).cons _
    | unstaged i cid =>
      simp only [apply, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact (ih hm).cons _
      · exact .inl ⟨f, List.mem_cons_self⟩
    | emit i cid =>
      simp only [apply, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact (ih hm).cons _
      · simp only [admits, Bool.and_eq_true] at ha
        exact (processed_of_consumed hx hs ha.2).cons _
    | inject m' =>
      simp only [apply, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact (ih hm).cons _
      · simp only [admits, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at ha
        exact absurd hs ha
    | deliverPartial i env x => exact (ih hm).cons _
    | extract j => exact (ih hm).cons _
    | forge x => exact (ih hm).cons _

/-- The inventory only grows, whichever step runs. -/
theorem net_grows (r : Rules) (f : Fed) (s : Step) {m : Relay} (hm : m ∈ f.net) :
    m ∈ (apply r f s).net := by
  cases s <;> first
    | exact hm
    | exact List.mem_append_left _ hm

/-- A receipt in a node's projection came out of the inventory; there is no other source. -/
theorem receipt_in_net {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i c s : Nat} {w : World} {env : Env}
    (hm : (w, env, Event.receipt c s) ∈ project i t) : (⟨s, c⟩ : Relay) ∈ f.net := by
  induction hx with
  | init f h => cases hm
  | @next t f st ha _ ih =>
    simp only [project] at hm
    cases st with
    | process j env' e =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp only [admits, Bool.and_eq_true] at ha
          simp only [Prod.mk.injEq] at he
          rw [← he.2.2] at ha
          simp [ownEvent] at ha
        · exact net_grows r f _ (ih hm)
      · exact net_grows r f _ (ih hm)
    | deliver j env' m =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp only [Prod.mk.injEq, Event.receipt.injEq] at he
          simp only [admits, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at ha
          obtain ⟨_, _, h1, h2⟩ := he
          have : (⟨s, c⟩ : Relay) = m := by rw [h1, h2]
          rw [this]
          exact ha.2
        · exact ih hm
      · exact ih hm
    | unstaged j cid => exact net_grows r f _ (ih hm)
    | emit j cid => exact net_grows r f _ (ih hm)
    | inject m => exact net_grows r f _ (ih hm)
    | deliverPartial j env' x =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ih hm
      · exact ih hm
    | extract j => exact net_grows r f _ (ih hm)
    | forge x => exact net_grows r f _ (ih hm)

/-- A fact about two signers, read off one execution: if an honest node received a relay under an
honest sender's name, that sender processed the request. It does not say the sender froze, signed
or still holds anything (`DUR-5`), and it says nothing of a sender outside the honest list. The
kernel alone cannot state this: `Kernel.Execution` admits any `Event.receipt`. -/
@[req "DUR-5"]
theorem receipt_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i c s : Nat} {w : World} {env : Env}
    (hm : (w, env, Event.receipt c s) ∈ project i t) (hs : s ∈ honest) : Processed t s c :=
  relay_origin hx (receipt_in_net hx hm) hs

/-! ## Where a partial comes from -/

/-- The partial inventory and the extracted set only grow, whichever step runs. A candidate's
removal at a node (settlement, prune, a holder decision's retirement) and a node's death, which is
its taking no further step, remove no exposed authority and no copied key. -/
@[req "POL-18"]
theorem parts_grows (r : Rules) (f : Fed) (s : Step) {x : Exp} (hx : x ∈ f.parts) :
    x ∈ (apply r f s).parts := by
  cases s <;> first
    | exact hx
    | exact List.mem_append_left _ hx

theorem extracted_grows (r : Rules) (f : Fed) (s : Step) {j : Nat} (hj : j ∈ f.extracted) :
    j ∈ (apply r f s).extracted := by
  cases s <;> first
    | exact hj
    | exact List.mem_append_left _ hj

/-- Historical exposure persists: what any earlier state of an execution held in its partial
inventory or extracted set, the final state holds. -/
@[req "POL-18"]
theorem persists {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {g : Fed} {s : Step} (hg : (g, s) ∈ t) :
    (∀ x ∈ g.parts, x ∈ f.parts) ∧ ∀ j ∈ g.extracted, j ∈ f.extracted := by
  induction hx with
  | init f h => cases hg
  | @next t f s' _ _ ih =>
    rcases List.mem_cons.1 hg with he | hg
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨fun x hx => parts_grows r _ _ hx, fun j hj => extracted_grows r _ _ hj⟩
    · obtain ⟨h1, h2⟩ := ih hg
      exact ⟨fun x hx => parts_grows r _ _ (h1 x hx), fun j hj => extracted_grows r _ _ (h2 j hj)⟩

theorem mem_outbox {w : World} {effs : List Effect} {x : Exp} (h : x ∈ outbox w effs) :
    x.signer = w.node.id ∧ Effect.queuePartial x.msg x.input x.hot x.cid ∈ effs := by
  simp only [outbox, List.mem_filterMap] at h
  obtain ⟨e, he, hx⟩ := h
  cases e with
  | queuePartial m i h c =>
    simp only [Option.some.injEq] at hx
    subst hx
    exact ⟨rfl, he⟩
  | broadcast _ => simp at hx

theorem outbox_sub_fanout {w : World} {effs : List Effect} {x : Exp} (h : x ∈ outbox w effs) :
    x ∈ fanout w effs :=
  List.mem_flatMap.2 ⟨x, h, List.mem_cons_self⟩

/-- A row of the fan-out is a kernel row, or a row at a later input with a kernel row's signer. -/
theorem mem_fanout {w : World} {effs : List Effect} {x : Exp} (h : x ∈ fanout w effs) :
    x.signer = w.node.id ∧ (x ∈ outbox w effs ∨ x.input ≠ 0) := by
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 h
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨(mem_outbox hy).1, .inl hy⟩
  · refine ⟨?_, .inr ?_⟩ <;> simp only [others] at hx <;> split at hx <;>
      simp only [List.mem_map, List.not_mem_nil] at hx
    · obtain ⟨k, _, rfl⟩ := hx
      exact (mem_outbox hy).1
    · obtain ⟨k, hk, rfl⟩ := hx
      simp only [List.mem_drop_iff_getElem, List.getElem_range] at hk
      obtain ⟨j, _, rfl⟩ := hk
      simp

theorem mem_project_cons {i : Nat} {t : Trace} (y : Fed × Step) {a : World × Env × Event}
    (h : a ∈ project i t) : a ∈ project i (y :: t) := by
  obtain ⟨f, s⟩ := y
  simp only [project]
  split
  · split
    · exact List.mem_cons_of_mem _ h
    · exact h
  · exact h

theorem normalRelease_project_cons {r : Rules} {i : Nat} {t : Trace} (y : Fed × Step)
    {msg : Sighash} {cid : Nat} (h : NormalRelease r (project i t) i msg cid) :
    NormalRelease r (project i (y :: t)) i msg cid := by
  obtain ⟨g, hg, hp⟩ := h
  exact ⟨g, mem_project_cons y hg, hp⟩

/-- This partial's signer sent it at an honest step of the composed trace: the step in which that
node crossed its release boundary for it, at input 0 the kernel's queued row and at a later input
the same release's partial for that input (`Federation.fanout`). A queue is all it says: no
recipient. -/
def Queued (r : Rules) (t : Trace) (x : Exp) : Prop :=
  ∃ g env e, (g, Step.process x.signer env e) ∈ t ∧
    x ∈ fanout (g.worlds x.signer) (step r env (g.worlds x.signer) e).2

theorem Queued.cons {r : Rules} {t : Trace} {x : Exp} (y : Fed × Step) (h : Queued r t x) :
    Queued r (y :: t) x := by
  obtain ⟨g, env, e, hm, he⟩ := h
  exact ⟨g, env, e, List.mem_cons_of_mem y hm, he⟩

/-- An honest partial cannot be invented: a partial in the inventory either names an extracted
signer or was queued by its signer's honest node. A replay is a delivery of that same row and
adds no row, so one queue may stand behind many deliveries. -/
@[req "NCH-24"]
theorem part_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {x : Exp} (hm : x ∈ f.parts) :
    x.signer ∈ f.extracted ∨ (x.signer ∈ honest ∧ Queued r t x) := by
  induction hx with
  | init f h => rw [h.2.1] at hm; cases hm
  | @next t f s ha hx ih =>
    have lift (hm : x ∈ f.parts) :
        x.signer ∈ (apply r f s).extracted ∨ (x.signer ∈ honest ∧ Queued r ((f, s) :: t) x) := by
      rcases ih hm with h | ⟨hh, hq⟩
      · exact .inl (extracted_grows r f s h)
      · exact .inr ⟨hh, hq.cons _⟩
    cases s with
    | process i env e =>
      simp only [apply, List.mem_append] at hm
      rcases hm with hm | hm
      · exact lift hm
      · have hsig := (mem_fanout hm).1
        simp only [admits, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at ha
        rw [node_id hx ha.1] at hsig
        subst hsig
        exact .inr ⟨ha.1, f, env, e, List.mem_cons_self, hm⟩
    | deliver i env m => exact lift hm
    | deliverPartial i env y => exact lift hm
    | unstaged i cid => exact lift hm
    | emit i cid => exact lift hm
    | inject m => exact lift hm
    | extract j => exact lift hm
    | forge y =>
      simp only [apply, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact lift hm
      · simp only [admits, List.contains_eq_mem, decide_eq_true_eq] at ha
        exact .inl ha

/-- A queued hot partial at input 0 has its signer's normal opening in that signer's projected
history: `Kernel.hot_release_provenance` at the queuing step, carried to the end of the trace. -/
@[req "DUR-8"]
theorem queued_release_provenance {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) {x : Exp}
    (hs : x.signer ∈ honest) (hq : Queued r t x) (hh : x.hot = true) (h0 : x.input = 0) :
    NormalRelease r (project x.signer t) x.signer x.msg x.cid := by
  induction hx with
  | init f h =>
    obtain ⟨g, env, e, hm, _⟩ := hq
    cases hm
  | @next t f s _ hx ih =>
    obtain ⟨g, env, e, hm, he⟩ := hq
    rcases List.mem_cons.1 hm with heq | hm
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have he := (mem_outbox (((mem_fanout he).2.resolve_right (by rw [h0]; simp)))).2
      rw [hh, h0] at he
      have hp := (Federation.hot_release_provenance hr hx hs env e x.msg x.cid he).2
      simp only [project, actor, if_true]
      exact normalRelease_cons _ hp
    · exact normalRelease_project_cons _ (ih ⟨g, env, e, hm, he⟩)

/-- A partial a node received came out of the partial inventory, and so has the origin
`Federation.part_origin` gives it: a delivery refers to a queued or forged row, never to nothing. -/
@[req "NCH-24"]
theorem partial_receipt_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i : Nat} {w : World} {env : Env} {m : Sighash} {inp s c : Nat}
    (hm : (w, env, Event.receivePartial m inp s c) ∈ project i t) :
    ∃ x ∈ f.parts, x.msg = m ∧ x.input = inp ∧ x.signer = s ∧ x.cid = c := by
  induction hx with
  | init f h => cases hm
  | @next t f st ha _ ih =>
    have lift (h : ∃ x ∈ f.parts, x.msg = m ∧ x.input = inp ∧ x.signer = s ∧ x.cid = c) :
        ∃ x ∈ (apply r f st).parts, x.msg = m ∧ x.input = inp ∧ x.signer = s ∧ x.cid = c := by
      obtain ⟨x, hx, h⟩ := h
      exact ⟨x, parts_grows r f st hx, h⟩
    simp only [project] at hm
    cases st with
    | process j env' e =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp only [admits, Bool.and_eq_true] at ha
          simp only [Prod.mk.injEq] at he
          rw [← he.2.2] at ha
          simp [ownEvent] at ha
        · exact lift (ih hm)
      · exact lift (ih hm)
    | deliver j env' m' =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ih hm
      · exact ih hm
    | deliverPartial j env' y =>
      simp only [actor] at hm
      split at hm
      · rcases List.mem_cons.1 hm with he | hm
        · simp only [Prod.mk.injEq, Event.receivePartial.injEq] at he
          simp only [admits, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at ha
          obtain ⟨_, _, h1, h2, h3, h4⟩ := he
          exact ⟨y, ha.2, h1.symm, h2.symm, h3.symm, h4.symm⟩
        · exact ih hm
      · exact ih hm
    | unstaged j cid => exact lift (ih hm)
    | emit j cid => exact lift (ih hm)
    | inject m' => exact lift (ih hm)
    | extract j => exact lift (ih hm)
    | forge y => exact lift (ih hm)

/-! ## The exposure inventory of one federation -/

/-- Every honest node's exposure rows in one list: authority that left a node, not possession at any
node (`POL-18`, `DUR-28`). A node's world holds its own queued rows and a row for each partial
delivered to it, forged ones included; `Fed.parts` is the whole inventory, and
`Federation.inventory_matched` ties this list to it. -/
@[req "POL-18"]
def exposure (honest : List Nat) (f : Fed) : List Exp :=
  honest.flatMap fun i => (f.worlds i).exposure

/-- A world to read `Kernel.exposedQuorum` on: this node's threshold, the federation's inventory. -/
def inventoryWorld (honest : List Nat) (f : Fed) (i : Nat) : World :=
  { node := (f.worlds i).node, exposure := exposure honest f }

/-! ## Derived honest provenance -/

/-- Where a step's exposure rows come from: the world's own, its queued partials, or the one row
of a received or adversary-exposed partial. -/
theorem step_exposure (r : Rules) (env : Env) (w : World) (e : Event) {x : Exp}
    (h : x ∈ (step r env w e).1.exposure) :
    x ∈ w.exposure ∨ x ∈ outbox w (step r env w e).2 ∨
      (∃ m i s c, e = .receivePartial m i s c ∧
        x = { msg := m, input := i, signer := s, hot := true, cid := c }) ∨
      ∃ m i s c, e = .adversaryExposes m i s c := by
  cases e with
  | firePass =>
    simp only [step, outbox, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  | receivePartial m i s c =>
    simp only [step, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inr (.inl ⟨m, i, s, c, rfl, h⟩))
  | adversaryExposes m i s c => exact .inr (.inr (.inr ⟨m, i, s, c, rfl⟩))
  | accept | receipt | refuse | packageAccepted | prune | tick | panic =>
    exact .inl (by simpa [step] using h)
  | send c =>
    simp only [step] at h
    exact .inl h
  | settle tx => exact .inl (by simpa [step] using h)
  | clawback x => exact .inl (by simpa [step] using h)

/-- Each row of `xs` has a row of the partial inventory with its message, input, signer and
commitment. The class bit may differ: a received row is recorded hot whatever its sender's class. -/
def Matched (f : Fed) (xs : List Exp) : Prop :=
  ∀ x ∈ xs, ∃ y ∈ f.parts, y.msg = x.msg ∧ y.input = x.input ∧ y.signer = x.signer ∧ y.cid = x.cid

theorem parts_matched (f : Fed) : Matched f f.parts := fun x hx => ⟨x, hx, rfl, rfl, rfl, rfl⟩

/-- Every row in an honest node's world is in the partial inventory: its own queued partials and the
partials delivered to it. -/
theorem node_matched {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i : Nat} (hi : i ∈ honest) : Matched f (f.worlds i).exposure := by
  induction hx with
  | init f h =>
    intro x hm
    rw [(h.2.2 i hi).1] at hm
    cases hm
  | @next t f s ha hx ih =>
    intro x hm
    have old (hm : x ∈ (f.worlds i).exposure) :
        ∃ y ∈ (apply r f s).parts, y.msg = x.msg ∧ y.input = x.input ∧ y.signer = x.signer ∧
          y.cid = x.cid := by
      obtain ⟨y, hy, h⟩ := ih x hm
      exact ⟨y, parts_grows r f s hy, h⟩
    cases hact : actor s with
    | none =>
      rw [apply_no_actor r f s hact i] at hm
      exact old hm
    | some a =>
      obtain ⟨j, env, e⟩ := a
      rw [apply_of_actor r f s hact i] at hm
      split at hm
      · rename_i hij
        subst hij
        rcases step_exposure r env _ e hm with hm | hm | ⟨m, k, sg, c, rfl, rfl⟩ | ⟨m, k, sg, c, rfl⟩
        · exact old hm
        · cases s with
          | process j' env' e' =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl, rfl⟩ := hact
            exact ⟨x, List.mem_append_right _ (outbox_sub_fanout hm), rfl, rfl, rfl, rfl⟩
          | deliver j' env' m' =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl, rfl⟩ := hact
            simp [step, outbox] at hm
          | deliverPartial j' env' y =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl, rfl⟩ := hact
            simp [step, outbox] at hm
          | _ => simp [actor] at hact
        · cases s with
          | process j' env' e' =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl, rfl⟩ := hact
            simp [admits, ownEvent] at ha
          | deliver j' env' m' => simp [actor] at hact
          | deliverPartial j' env' y =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq, Event.receivePartial.injEq] at hact
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hact
            simp only [admits, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at ha
            exact ⟨y, ha.2, rfl, rfl, rfl, rfl⟩
          | _ => simp [actor] at hact
        · cases s with
          | process j' env' e' =>
            simp only [actor, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl, rfl⟩ := hact
            simp [admits, ownEvent] at ha
          | deliver j' env' m' => simp [actor] at hact
          | deliverPartial j' env' y => simp [actor] at hact
          | _ => simp [actor] at hact
      · exact old hm

/-- Every row of `Federation.exposure` is in the partial inventory. -/
theorem inventory_matched {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) : Matched f (exposure honest f) := by
  intro x hm
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 hm
  exact node_matched hx hi x hm

/-- `Kernel.HonestExposureProvenance`'s message-binding clause, read on the partial inventory: no
partial of a signer outside the extracted set, queued under a non-hot candidate, shares the target
message at input 0. The kernel names this "message binding outside the formal layer"; it stays a
premise here. `Ingress.hot_binding` derives it for the input-0 message of an admissible hot-class
member, over a trace whose acceptances are all checked, with a collision-free transaction identity. -/
@[req "DUR-8"]
def HotBinding (f : Fed) (msg : Sighash) : Prop :=
  ∀ x ∈ f.parts, x.signer ∉ f.extracted → x.msg = msg → x.input = 0 → x.hot = true

instance (f : Fed) (msg : Sighash) : Decidable (HotBinding f msg) := by
  unfold HotBinding
  infer_instance

/-- A world to read `Kernel.exposedQuorum` on over the whole partial inventory, at this node's
threshold. -/
def partsWorld (f : Fed) (i : Nat) : World := { node := (f.worlds i).node, exposure := f.parts }

/-- The derivation, for any world whose rows the partial inventory matches: every target input-0
row whose signer is outside the extracted set has that signer's execution and normal opening in
its own projected history. The premise of the kernel's counting theorem is not taken here; it is
proved by induction over the composed execution, from `Federation.part_origin` and
`Federation.queued_release_provenance`. -/
theorem provenance_of_matched {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) {msg : Sighash}
    (hb : HotBinding f msg) {w : World} (hw : Matched f w.exposure) :
    HonestExposureProvenance r (fun j => project j t) f.extracted w msg := by
  intro x hxm hmsg h0 hc
  obtain ⟨y, hy, ymsg, yin, ysig, ycid⟩ := hw x hxm
  rw [← ysig] at hc ⊢
  rw [← ycid]
  rcases part_origin hx hy with he | ⟨hs, hq⟩
  · exact absurd he hc
  · have hh := hb y hy hc (ymsg.trans hmsg) (yin.trans h0)
    refine ⟨f.worlds y.signer, project_execution hx hs, node_id hx hs, ?_⟩
    have hp := queued_release_provenance hr hx hs hq hh (yin.trans h0)
    rw [ymsg, hmsg] at hp
    exact hp

/-- The target of this layer: `Kernel.HonestExposureProvenance` follows for the whole partial
inventory of a composed execution, with each signer's history its own projection and the extracted
set as the compromised list. It reads any node's threshold, since the premise does not. -/
@[req "DUR-8"]
theorem honest_exposure_provenance {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) {msg : Sighash}
    (hb : HotBinding f msg) (n : Node) :
    HonestExposureProvenance r (fun j => project j t) f.extracted
      { node := n, exposure := f.parts } msg :=
  provenance_of_matched hr hx hb (parts_matched f)

/-- The same premise at an honest node's own world, whose rows are its releases and what it was
delivered. -/
@[req "DUR-8"]
theorem node_exposure_provenance {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) {msg : Sighash}
    (hb : HotBinding f msg) {i : Nat} (hi : i ∈ honest) :
    HonestExposureProvenance r (fun j => project j t) f.extracted (f.worlds i) msg :=
  provenance_of_matched hr hx hb (node_matched hx hi)

/-- `DUR-8`'s "never a signing quorum" over a composed execution: `Kernel.no_exposed_quorum_without_normal`
with its provenance premise derived. What stays: `hr`; `hb`, the message binding; `noNormal`, no honest
normal decision on this message in any projected history; and `bound`, fewer than `t` distinct
signers in the CUMULATIVE extracted set, whatever became of their hosts. It reads the whole partial
inventory, which holds every honest node's rows (`Federation.node_matched`). Possession, other
inputs and finalization are outside it, as they are outside the kernel theorem. -/
@[req "DUR-8"]
theorem no_exposed_quorum {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) (n : Node) (c : Cand)
    (hb : HotBinding f (sighash c.tx 0))
    (noNormal : NoHonestNormalDecision r (fun j => project j t) f.extracted (sighash c.tx 0))
    (bound : f.extracted.eraseDups.length < n.t) :
    exposedQuorum { node := n, exposure := f.parts } c = false :=
  no_exposed_quorum_without_normal r _ _ _ c (honest_exposure_provenance hr hx hb n) noNormal bound

/-! ## Possession on every input

A node's possession is its own signatures and the partials its store took, keyed as
`Authority.Sig`: message, input and signer, with the commitment dropped. It is read off the node's
own state and projected history, beside the kernel's store, which holds input 0 per candidate. -/

/-- The signatures this node made at ingress and still holds: its own signature on every input of
every resident candidate. `SPN-32` says "The node MUST sign the spend, the Escape and every rung at
ingress"; possession is node-local and leaves with the candidate. -/
@[req "SPN-32"]
def ownSigs (n : Node) : List Authority.Sig :=
  n.cands.flatMap fun c =>
    (List.range c.tx.inputs.length).map fun k => { msg := sighash c.tx k, input := k, signer := n.id }

/-- `NCH-24`'s store test on one partial, per input: a resident candidate with this commitment id,
whose transaction has this message at this input ("the rung is found by txid", "the input and
signer are in range"). At input 0 it is `Kernel.receivePartial`'s guard, with the range added. -/
@[req "NCH-24"]
def storable (n : Node) (m : Sighash) (k cid : Nat) : Bool :=
  n.cands.any fun c => c.id == cid && m == sighash c.tx k && decide (k < c.tx.inputs.length)

/-- One frame's delivery, with its commitment id, if the store test passed when it arrived. -/
def arrival (a : World × Env × Event) : List (Nat × Authority.Sig) :=
  match a.2.2 with
  | .receivePartial m k s cid =>
    if storable a.1.node m k cid then [(cid, { msg := m, input := k, signer := s })] else []
  | _ => []

/-- The partials delivered over this node's history `h`, newest first, that the store took when
each arrived and whose commitment's candidate stayed resident after every later step, `n` being
the node after the newest one: a candidate's removal drops what was delivered under it, and a
later registration of the same commitment starts empty. -/
def kept : History → Node → List (Nat × Authority.Sig)
  | [], _ => []
  | a :: h, n => (kept h a.1.node ++ arrival a).filter fun p => n.cands.any (·.id == p.1)

theorem mem_kept : ∀ {h : History} {n : Node} {p : Nat × Authority.Sig}, p ∈ kept h n →
    ∃ a ∈ h, a.2.2 = .receivePartial p.2.msg p.2.input p.2.signer p.1
  | [], _, _, hp => by cases hp
  | a :: h, n, p, hp => by
    simp only [kept, List.mem_filter, List.mem_append] at hp
    rcases hp.1 with hp | hp
    · obtain ⟨b, hb, he⟩ := mem_kept hp
      exact ⟨b, List.mem_cons_of_mem a hb, he⟩
    · refine ⟨a, List.mem_cons_self, ?_⟩
      obtain ⟨w, env, e⟩ := a
      cases e with
      | receivePartial m k s cid =>
        simp only [arrival] at hp
        split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          rfl
        · cases hp
      | _ => simp [arrival] at hp

def received (n : Node) (h : History) : List Authority.Sig := (kept h n).map Prod.snd

/-- Node `i`'s possession at the end of a composed trace: its own ingress signatures and the
partials its store took on every input, kept while their candidate stays resident
(`Federation.kept`). This is what the node holds, not what its own assembly reads (`Kernel.heldQuorum`, per candidate at input 0). -/
@[req "DUR-28"]
def held (i : Nat) (t : Trace) (f : Fed) : List Authority.Sig :=
  ownSigs (f.worlds i).node ++ received (f.worlds i).node (project i t)

/-- Possession comes from delivery: each signature an honest node holds is its own or a partial
of the inventory, with the same message, input and signer. -/
@[req "DUR-28"]
theorem held_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i : Nat} (hi : i ∈ honest) {x : Authority.Sig}
    (hm : x ∈ held i t f) : x.signer = i ∨ ∃ y ∈ f.parts, Authority.sig y = x := by
  rcases List.mem_append.1 hm with hm | hm
  · left
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.1 hm
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hc
    exact node_id hx hi
  · right
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨⟨w, env, e⟩, ha, he⟩ := mem_kept hp
    simp only at he
    subst he
    obtain ⟨y, hy, h1, h2, h3, _⟩ := partial_receipt_origin hx ha
    exact ⟨y, hy, by simp [Authority.sig, h1, h2, h3]⟩

/-- No Normal authorization from exposed authority: under `Federation.no_exposed_quorum`'s premises,
no list of signatures drawn from the partial inventory authorizes the candidate's transaction, at
any key set and with any user signatures. Input 0 is one of its inputs, and there fewer than `t`
signers exist (`Authority.unauthorized_of_input`). A new consequence beside the kernel's count, which
it does not change; its premises are that theorem's. -/
@[req "DUR-8"]
theorem no_exposed_authorization {r : Rules} (hr : r.refusedOpening = .acceptedOnly)
    {honest : List Nat} {t : Trace} {f : Fed} (hx : Execution r honest t f) (n : Node) (c : Cand)
    (hb : HotBinding f (sighash c.tx 0))
    (noNormal : NoHonestNormalDecision r (fun j => project j t) f.extracted (sighash c.tx 0))
    (bound : f.extracted.eraseDups.length < n.t) (keys : List Nat) (U : List Authority.UserSig)
    {R : List Authority.Sig} (hR : ∀ x ∈ R, ∃ y ∈ f.parts, Authority.sig y = x) :
    Authority.normal keys n.t c.tx U R = false := by
  have hq := no_exposed_quorum hr hx n c hb noNormal bound
  cases hne : c.tx.inputs with
  | nil => simp [Authority.normal, Authority.quorum, hne]
  | cons a as =>
    refine Authority.unauthorized_of_input (A := f.parts.map Authority.sig) (k := 0)
      (by simp [hne]) (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hR x hx
      exact List.mem_map.2 ⟨y, hy, rfl⟩
    · simp only [exposedQuorum, decide_eq_false_iff_not, Nat.not_le] at hq
      refine Nat.lt_of_le_of_lt (length_le_of_nodup_subset (nodup_eraseDups _) fun s hs => ?_) hq
      obtain ⟨_, hs⟩ := Authority.mem_signers.1 hs
      obtain ⟨y, hy, he⟩ := List.mem_map.1 hs
      simp only [Authority.sig, Authority.Sig.mk.injEq] at he
      rw [List.mem_eraseDups]
      exact List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, by simp [he.1, he.2.1]⟩, he.2.2⟩

/-! ## Duplicates -/

theorem eraseDups_length_append {l m : List Nat} (h : ∀ z ∈ m, z ∈ l) :
    (l ++ m).eraseDups.length = l.eraseDups.length := by
  apply Nat.le_antisymm
  · apply length_le_of_nodup_subset (nodup_eraseDups _)
    intro z hz
    rw [List.mem_eraseDups, List.mem_append] at hz
    rw [List.mem_eraseDups]
    rcases hz with hz | hz
    · exact hz
    · exact h z hz
  · apply length_le_of_nodup_subset (nodup_eraseDups _)
    intro z hz
    rw [List.mem_eraseDups] at hz
    rw [List.mem_eraseDups]
    exact List.mem_append_left _ hz

/-- A duplicate signature adds no signer authority: a row whose signer already has a row for its
message and input leaves `Kernel.exposedQuorum` where it was. A replayed delivery appends such a row
to its recipient's world, and a forged copy appends one to the inventory. -/
@[req "POL-18"]
theorem duplicate_row_counts_nothing (n : Node) (xs : List Exp) (x : Exp) (c : Cand)
    (h : ∃ y ∈ xs, y.msg = x.msg ∧ y.input = x.input ∧ y.signer = x.signer) :
    exposedQuorum { node := n, exposure := xs ++ [x] } c =
      exposedQuorum { node := n, exposure := xs } c := by
  obtain ⟨y, hy, hmsg, hin, hsig⟩ := h
  simp only [exposedQuorum, List.filter_append, List.map_append]
  rw [eraseDups_length_append]
  intro z hz
  simp only [List.mem_map, List.mem_filter, List.mem_singleton] at hz ⊢
  obtain ⟨x', ⟨rfl, hp⟩, rfl⟩ := hz
  exact ⟨y, ⟨hy, by rw [hmsg, hin]; exact hp⟩, hsig⟩

/-- `NCH-25`'s "A duplicate is an idempotent `ACCEPTED` and never displaces the first", on a
delivered partial: when every resident candidate it names already holds its signer, the node is
unchanged. -/
@[req "NCH-25"]
theorem duplicate_partial_holds_nothing_new (n : Node) (x : Exp)
    (h : ∀ c ∈ n.cands, c.id = x.cid → x.signer ∈ c.heldSigners) :
    Kernel.receivePartial n x.msg x.input x.signer x.cid = n := by
  have hc : (n.cands.map fun c =>
      if c.id == x.cid && x.input == 0 && x.msg == sighash c.tx 0 then
        { c with heldSigners := addHeld c.heldSigners x.signer } else c) = n.cands := by
    conv => rhs; rw [← List.map_id n.cands]
    apply List.map_congr_left
    intro c hcm
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [addHeld_of_held _ _ (h c hcm hcond.1.1)]
      rfl
    · rfl
  unfold Kernel.receivePartial
  rw [hc]

/-! ## Running a schedule -/

/-- Are these steps legal in order from here? -/
def legal (r : Rules) (honest : List Nat) : Fed → List Step → Bool
  | _, [] => true
  | f, s :: ss => admits honest f s && legal r honest (apply r f s) ss

def runFrom (r : Rules) : Fed → List Step → Fed
  | f, [] => f
  | f, s :: ss => runFrom r (apply r f s) ss

def record (r : Rules) : Trace → Fed → List Step → Trace
  | t, _, [] => t
  | t, f, s :: ss => record r ((f, s) :: t) (apply r f s) ss

theorem execution_of_legal {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {ss : List Step} (hl : legal r honest f ss = true) :
    Execution r honest (record r t f ss) (runFrom r f ss) := by
  induction ss generalizing t f with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

theorem mem_record {r : Rules} {t : Trace} {f : Fed} {ss : List Step} {x : Fed × Step}
    (h : x ∈ record r t f ss) : x ∈ t ∨ x.2 ∈ ss := by
  induction ss generalizing t f with
  | nil => exact .inl h
  | cons s ss ih =>
    rcases ih h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr List.mem_cons_self
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_project_actor {i : Nat} {t : Trace} {a : World × Env × Event} (h : a ∈ project i t) :
    ∃ g s, (g, s) ∈ t ∧ actor s = some (i, a.2.1, a.2.2) := by
  induction t with
  | nil => cases h
  | cons y t ih =>
    obtain ⟨g, s⟩ := y
    simp only [project] at h
    split at h
    · rename_i j env e hact
      split at h
      · rename_i hj
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨g, s, List.mem_cons_self, by rw [hact, hj]⟩
        · obtain ⟨g', s', hm, ha⟩ := ih h
          exact ⟨g', s', List.mem_cons_of_mem _ hm, ha⟩
      · obtain ⟨g', s', hm, ha⟩ := ih h
        exact ⟨g', s', List.mem_cons_of_mem _ hm, ha⟩
    · obtain ⟨g', s', hm, ha⟩ := ih h
      exact ⟨g', s', List.mem_cons_of_mem _ hm, ha⟩

/-- A normal opening is a holder decision on a receipt, so a trace with no relay delivered to anyone
has no honest normal decision in any projection. -/
theorem no_normal_without_receipt {r : Rules} {t : Trace} (comp : List Nat) (msg : Sighash)
    (h : ∀ g s, (g, s) ∈ t → ∀ i env c snd, actor s ≠ some (i, env, .receipt c snd)) :
    NoHonestNormalDecision r (fun j => project j t) comp msg := by
  intro self _ cid hn
  obtain ⟨a, ha, cid', snd, _, _, he, _⟩ := hn
  obtain ⟨g, s, hm, hact⟩ := mem_project_actor ha
  exact h g s hm self a.2.1 cid' snd (by rw [hact, he])

/-! ## The Hold-protected blocking cohort

The question: which honest signers can be shown, from their own histories, never to release a target
partial, whatever earlier normal decisions they took? `Federation.no_exposed_quorum` needs no honest
normal decision on the message in any history. Here a normal decision may open the target at a cohort
member; what keeps its partial withheld is `SPN-38`'s Hold before the node arms and `DUR-11`'s freeze
after it.

**One node.** `Federation.HoldProtected` reads one node's own history against `m`, an instant of that
node's own HotClock: every step the node takes unarmed reads a sample at or before `m`, and every target
acceptance it takes unarmed reads a sample whose Hold has not matured by `m`. The second clause covers
every commitment over the target message, the older ones included, since `Kernel.sighash` reads the
transaction and input and not the commitment. No other node's clock is read, and no sample is compared
with one of another node. `Federation.hold_protected_execution` derives that such a node queues no hot
partial for the target: before arming no target candidate's Hold matures at a fire pass, and after it
`Kernel.no_hot_partial_while_armed` holds, for candidates registered later too, since `Kernel.born`
freezes a hot candidate on an armed node. `Federation.arming_origin` says what arming is: a holder
decision on a received relay that brings a live Carrier's holder count to `t`, with its pair duress bit
set. Over a composed execution `Federation.receipt_origin` says who sent that relay.

**A cohort.** `Federation.cohort_no_exposed_quorum` counts. The cohort's members are honest, their keys
are not extracted, and each history is Hold-protected at an instant of its own. Every signer of a target
row in the partial inventory is then a key outside the cohort, so with `n` authorized keys and a cohort
of `n − t + 1` distinct members, fewer than `t` signers remain. It takes no premise on normal decisions
and no bound on the extracted set beyond the cohort's keys. What stays: `Kernel.Rules.holdCheck` at its
current value, `Federation.HotBinding`, the authorized key list, and the per-node timing. The theorem is
for one target message. It says nothing of other transactions, possession, the Escape, or a node
coerced into the normal PIN after its Hold matured. -/

/-- One frame of a node's history against `m`, an instant of that node's HotClock: an armed frame
passes; an unarmed frame reads a sample at or before `m`, and if it accepts a pair whose spend or
Escape carries `msg`, its sample's Hold (`SPN-38`, at this node's `hold_secs`) has not matured by
`m`. -/
@[req "SPN-38"]
def holdFrame (msg : Sighash) (m : Mono) (a : World × Env × Event) : Bool :=
  a.1.node.armed || (a.2.1.mono.notAfter m && match a.2.2 with
    | .accept _ _ _ sp es =>
      !(sighash sp.tx 0 == msg || sighash es.tx 0 == msg) || !a.2.1.mono.aged m a.1.node.holdSecs
    | _ => true)

/-- Every frame of this history passes `holdFrame`: the node arms, or stops, by `m` on its own
HotClock, and took every target acceptance before arming less than `hold_secs` before `m`. -/
@[req "SPN-38"]
def HoldProtected (msg : Sighash) (m : Mono) (h : History) : Prop :=
  ∀ a ∈ h, holdFrame msg m a = true

/-- Proof state: on an unarmed node, no resident hot target candidate's Hold matures by `m`. -/
def HoldInv (msg : Sighash) (m : Mono) (n : Node) : Prop :=
  n.armed = false → ∀ c ∈ n.cands, c.hot = true → sighash c.tx 0 = msg →
    c.acceptedAt.aged m n.holdSecs = false

theorem withWindow_acceptedAt (r : Rules) (sel : List (Nat × Bool)) (T : Wall) (slack : Secs)
    (c : Cand) : (withWindow r sel T slack c).acceptedAt = c.acceptedAt := by
  unfold withWindow; split <;> rfl

theorem step_holdSecs (r : Rules) (env : Env) (w : World) (e : Event) :
    (step r env w e).1.node.holdSecs = w.node.holdSecs := by
  cases e with
  | refuse cid d E pair code =>
    simp only [step, refuse]
    split
    · rfl
    · split <;> rfl
  | accept cid d E sp es =>
    simp only [step, accept, refuse]
    split
    · split
      · rfl
      · split <;> rfl
    · split <;> rfl
  | receipt cid s =>
    simp only [step, receipt]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | firePass => simp only [step, firePass]; split <;> rfl
  | send c => simp only [step, send]; split <;> rfl
  | settle tx => simp only [step, settle]; split <;> rfl
  | packageAccepted c => rfl
  | prune => rfl
  | tick => rfl
  | panic => rfl
  | adversaryExposes m i s c => rfl
  | receivePartial m i s c => rfl
  | clawback x => simp [step]

/-- A candidate after a step is a resident before it with the same class, transaction and
acceptance instant, or was born at this step's acceptance at its HotClock sample, with the
transaction and class of the spend or of the Escape that acceptance carried, or was born at this
step's claw-back at its HotClock sample, with that claw-back's transaction, not hot. -/
theorem cand_origin (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) :
    (∃ d ∈ w.node.cands, d.hot = c.hot ∧ d.tx = c.tx ∧ d.acceptedAt = c.acceptedAt) ∨
    (∃ cid dd E sp es, e = .accept cid dd E sp es ∧ c.acceptedAt = env.mono ∧
      ((c.tx = sp.tx ∧ c.hot = sp.hot) ∨ (c.tx = es.tx ∧ c.hot = es.hot))) ∨
    ∃ x, e = .clawback x ∧ c.acceptedAt = env.mono ∧ c.tx = x.tx ∧ c.hot = false := by
  have keep (hc : c ∈ w.node.cands) :
      ∃ d ∈ w.node.cands, d.hot = c.hot ∧ d.tx = c.tx ∧ d.acceptedAt = c.acceptedAt :=
    ⟨c, hc, rfl, rfl, rfl⟩
  have frame (f : Cand → Cand)
      (hf : ∀ d, (f d).hot = d.hot ∧ (f d).tx = d.tx ∧ (f d).acceptedAt = d.acceptedAt)
      (hc : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, d.hot = c.hot ∧ d.tx = c.tx ∧ d.acceptedAt = c.acceptedAt := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact ⟨d, hd, (hf d).1.symm, (hf d).2.1.symm, (hf d).2.2.symm⟩
  cases e with
  | accept cid dd E sp es =>
    simp only [step, accept] at hc
    split at hc
    · refine .inl (keep ?_)
      simp only [refuse] at hc
      split at hc
      · exact hc
      · split at hc
        · exact hc
        · exact hc
    · split at hc
      · exact .inl (keep hc)
      · have base (x : Cand) (hx : x ∈ register r w.node env sp es) :
            (∃ d ∈ w.node.cands, d.hot = x.hot ∧ d.tx = x.tx ∧ d.acceptedAt = x.acceptedAt) ∨
            ∃ cid' dd' E' sp' es', Event.accept cid dd E sp es = .accept cid' dd' E' sp' es' ∧
              x.acceptedAt = env.mono ∧
                ((x.tx = sp'.tx ∧ x.hot = sp'.hot) ∨ (x.tx = es'.tx ∧ x.hot = es'.hot)) := by
          rcases List.mem_cons.1 (mem_register hx) with rfl | hx
          · exact .inr ⟨cid, dd, E, sp, es, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact .inr ⟨cid, dd, E, sp, es, rfl, rfl, .inr ⟨rfl, rfl⟩⟩
          · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
        split at hc
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
          rw [withWindow_hot, withWindow_tx, withWindow_acceptedAt]
          exact (base x hx).imp_right Or.inl
        · exact (base c hc).imp_right Or.inl
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [withWindow_hot], by rw [withWindow_tx],
            by rw [withWindow_acceptedAt]⟩) hc
        · exact keep hc
  | refuse cid d E pair code =>
    refine .inl (keep ?_)
    simp only [step, refuse] at hc
    split at hc
    · exact hc
    · split at hc
      · exact hc
      · exact hc
  | firePass =>
    refine .inl ?_
    simp only [step, firePass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> simp) hc
  | packageAccepted cid =>
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | send cid =>
    refine .inl ?_
    simp only [step, send] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> simp) hc
  | settle tx =>
    refine .inl ?_
    simp only [step, settle] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> simp) hc
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | clawback x =>
    rcases mem_clawback (by simpa [step] using hc) with hc | ⟨rfl, -⟩
    · exact .inl (keep hc)
    · exact .inr (.inr ⟨x, rfl, rfl, rfl, rfl⟩)

theorem holdInv_step (r : Rules) (env : Env) (w : World) (e : Event) {msg : Sighash} {m : Mono}
    (hi : HoldInv msg m w.node) (hf : holdFrame msg m (w, env, e) = true) :
    HoldInv msg m (step r env w e).1.node := by
  intro ha c hc hh hmsg
  have ha0 : w.node.armed = false := by
    cases hb : w.node.armed
    · rfl
    · have := armed_sticky r env w e hb; rw [ha] at this; cases this
  rw [step_holdSecs]
  rcases cand_origin r env w e hc with ⟨d, hd, dh, dt, da⟩ | ⟨cid, dd, E, sp, es, rfl, hat, htx⟩ |
    ⟨x, rfl, -, -, hcold⟩
  · rw [← da]
    exact hi ha0 d hd (dh.trans hh) (by rw [dt]; exact hmsg)
  · simp only [holdFrame, ha0, Bool.false_or, Bool.and_eq_true] at hf
    have ht : (sighash sp.tx 0 == msg || sighash es.tx 0 == msg) = true := by
      rcases htx with ⟨h, -⟩ | ⟨h, -⟩
      · rw [← h, hmsg]; simp
      · rw [← h, hmsg]; simp
    have := hf.2
    simp only [ht, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
    rw [hat]
    exact this
  · rw [hcold] at hh; cases hh

/-- Only a fire pass queues a hot partial at input 0. -/
theorem hot_effect_firePass (r : Rules) (env : Env) (w : World) (e : Event) (msg : Sighash)
    (cid : Nat) (he : Effect.queuePartial msg 0 true cid ∈ (step r env w e).2) : e = .firePass := by
  cases e <;> simp only [step] at he ⊢ <;> try simp_all
  rename_i c
  simp only [send] at he
  split at he
  · simp at he
  · split at he <;> simp at he

theorem no_target_release_step (r : Rules) (hr : r.holdCheck = .hotClock) (env : Env)
    (w : World) (e : Event) (hw : Reachable r w) {msg : Sighash} {m : Mono}
    (hi : HoldInv msg m w.node) (hf : holdFrame msg m (w, env, e) = true) (cid : Nat) :
    Effect.queuePartial msg 0 true cid ∉ (step r env w e).2 := by
  intro he
  have fire := hot_effect_firePass r env w e msg cid he
  subst fire
  cases ha : w.node.armed
  · simp only [holdFrame, ha, Bool.false_or, Bool.and_eq_true] at hf
    simp only [step, firePass] at he
    split at he
    · simp at he
    · obtain ⟨c, hc, he⟩ := List.mem_map.1 he
      obtain ⟨hc, hd⟩ := List.mem_filter.1 hc
      simp only [Effect.queuePartial.injEq] at he
      obtain ⟨hmsg, _, hhot, _⟩ := he
      have hage := hi ha c hc hhot hmsg
      have hm : holdMatured r env w.node c = true := by
        simp only [due, Bool.and_eq_true] at hd
        exact hd.1.1.1.2
      simp only [holdMatured, hr, hhot] at hm
      rw [Mono.aged_of_notAfter hm hf.1] at hage
      cases hage
  · exact no_hot_partial_while_armed r env w hw ha _ he _ _ _ rfl

/-- `DUR-8`, `SPN-38`, `DUR-11`, on one node's own execution: a Hold-protected history queues no hot
partial for the target message at input 0, under any commitment, at any step. A normal decision may
have opened a target candidate; its Hold keeps it from being due until the node arms, and the freeze
does after. -/
@[req "DUR-8"]
theorem hold_protected_execution (r : Rules) (hr : r.holdCheck = .hotClock) {h : History}
    {w : World} (hx : Kernel.Execution r h w) {msg : Sighash} {m : Mono}
    (hp : HoldProtected msg m h) :
    HoldInv msg m w.node ∧
      ∀ a ∈ h, ∀ cid, Effect.queuePartial msg 0 true cid ∉ (step r a.2.1 a.1 a.2.2).2 := by
  induction hx with
  | init n hn =>
    refine ⟨fun _ c hc => ?_, fun a ha => ?_⟩
    · rw [hn.2.1] at hc; cases hc
    · cases ha
  | next env e hx ih =>
    obtain ⟨hi, hrel⟩ := ih (fun a ha => hp a (List.mem_cons_of_mem _ ha))
    have hf := hp _ List.mem_cons_self
    refine ⟨holdInv_step r env _ e hi hf, ?_⟩
    intro a ha cid
    rcases List.mem_cons.1 ha with rfl | ha
    · exact no_target_release_step r hr env _ e hx.reachable hi hf cid
    · exact hrel a ha cid

/-- `DUR-10`'s single writer of the arm bit: a node becomes armed only at a holder decision on a
received relay that brings a live Carrier's holder count to `t` (`Kernel.commits`), with that
Carrier's pair duress bit set. -/
@[req "DUR-10"]
theorem arming_origin (r : Rules) (env : Env) (w : World) (e : Event)
    (h0 : w.node.armed = false) (h1 : (step r env w e).1.node.armed = true) :
    ∃ cid sender k, e = .receipt cid sender ∧ w.node.carriers.find? (·.cid == cid) = some k ∧
      commits env w.node cid sender = true ∧
      pairDuress r w.node { k with relaySenders := addSender w.node.id k.relaySenders sender } =
        true := by
  cases e with
  | receipt cid s =>
    simp only [step, receipt] at h1
    split at h1
    · rw [h0] at h1; cases h1
    · rename_i k hk
      split at h1
      · rw [h0] at h1; cases h1
      · split at h1
        · rename_i hcommit
          simp only [holderDecision, h0, Bool.false_or] at h1
          exact ⟨cid, s, k, rfl, hk, hcommit, h1⟩
        · simp only at h1; rw [h0] at h1; cases h1
  | accept cid d E sp es =>
    simp only [step, accept, refuse] at h1
    split at h1
    · split at h1
      · rw [h0] at h1; cases h1
      · split at h1 <;> (try simp only at h1) <;> rw [h0] at h1 <;> cases h1
    · split at h1 <;> (try simp only at h1) <;> rw [h0] at h1 <;> cases h1
  | refuse cid d E pair code =>
    simp only [step, refuse] at h1
    split at h1
    · rw [h0] at h1; cases h1
    · split at h1 <;> (try simp only at h1) <;> rw [h0] at h1 <;> cases h1
  | firePass =>
    simp only [step, firePass] at h1
    split at h1 <;> (try simp only at h1) <;> rw [h0] at h1 <;> cases h1
  | send c =>
    simp only [step, send] at h1
    split at h1
    · rw [h0] at h1; cases h1
    · split at h1 <;> (try simp only at h1) <;> rw [h0] at h1 <;> cases h1
  | settle tx =>
    simp only [step, settle] at h1
    split at h1
    · rw [h0] at h1; cases h1
    · simp only at h1; rw [h0] at h1; cases h1
  | packageAccepted c | prune | tick | panic | adversaryExposes _ _ _ _ | receivePartial _ _ _ _ =>
    simp [step, packageAccepted, prune, tick, receivePartial, h0] at h1
  | clawback x => simp [step, h0] at h1

theorem mem_project_process {i : Nat} {t : Trace} {g : Fed} {env : Env} {e : Event}
    (h : (g, Step.process i env e) ∈ t) : (g.worlds i, env, e) ∈ project i t := by
  induction t with
  | nil => cases h
  | cons y t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [project, actor]
    · exact mem_project_cons y (ih h)

/-- A cohort member's signature on the target is nowhere in the partial inventory: the member is
honest, its key is not extracted, and its own history is Hold-protected at an instant of its own
HotClock. -/
@[req "DUR-8"]
theorem cohort_withholds {r : Rules} (hr : r.holdCheck = .hotClock) {honest : List Nat}
    {t : Trace} {f : Fed} (hx : Execution r honest t f) {msg : Sighash} (hb : HotBinding f msg)
    {i : Nat} (hi : i ∈ honest) (hext : i ∉ f.extracted) {m : Mono}
    (hp : HoldProtected msg m (project i t)) :
    ∀ x ∈ f.parts, x.msg = msg → x.input = 0 → x.signer ≠ i := by
  intro x hxm hmsg h0 hsig
  subst hsig
  rcases part_origin hx hxm with he | ⟨_, g, env, e, hm, he⟩
  · exact hext he
  · have hh := hb x hxm hext hmsg h0
    have he := (mem_outbox (((mem_fanout he).2.resolve_right (by rw [h0]; simp)))).2
    rw [hmsg, h0, hh] at he
    exact (hold_protected_execution r hr (project_execution hx hi) hp).2 _
      (mem_project_process hm) x.cid he

/-- `DUR-8`'s "never a signing quorum" for one target message, from a Hold-protected blocking
cohort. Every signer of a target input-0 row is honest or extracted, so on `keys`, and outside the
cohort; when `keys` has fewer distinct members than the cohort plus `t`, the rows reach no quorum.
No premise on normal decisions and no bound on the extracted set is taken: a node outside the cohort
may have released, and any key outside it may be copied. -/
@[req "DUR-8"]
theorem cohort_no_exposed_quorum {r : Rules} (hr : r.holdCheck = .hotClock) {honest : List Nat}
    {t : Trace} {f : Fed} (hx : Execution r honest t f) (n : Node) (c : Cand)
    (hb : HotBinding f (sighash c.tx 0)) (cohort : List Nat) (clock : Nat → Mono)
    (hc : ∀ i ∈ cohort, i ∈ honest ∧ i ∉ f.extracted ∧
      HoldProtected (sighash c.tx 0) (clock i) (project i t))
    (keys : List Nat) (hk : ∀ j, j ∈ honest ∨ j ∈ f.extracted → j ∈ keys)
    (hcount : keys.eraseDups.length < cohort.eraseDups.length + n.t) :
    exposedQuorum { node := n, exposure := f.parts } c = false := by
  have hS : ∀ s ∈ ((f.parts.filter fun x => x.msg == sighash c.tx 0 && x.input == 0).map
      Exp.signer).eraseDups, s ∈ keys ∧ s ∉ cohort := by
    intro s hs
    rw [List.mem_eraseDups] at hs
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hs
    obtain ⟨hxm, hm⟩ := List.mem_filter.1 hx'
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    refine ⟨?_, fun hcoh => ?_⟩
    · rcases part_origin hx hxm with he | ⟨hh, _⟩
      · exact hk _ (.inr he)
      · exact hk _ (.inl hh)
    · obtain ⟨hh, he, hp⟩ := hc _ hcoh
      exact cohort_withholds hr hx hb hh he hp x hxm hm.1 hm.2 rfl
  have hnd : (((f.parts.filter fun x => x.msg == sighash c.tx 0 && x.input == 0).map
      Exp.signer).eraseDups ++ cohort.eraseDups).Nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_eraseDups _, nodup_eraseDups _, ?_⟩
    intro a ha b hb' hab
    subst hab
    rw [List.mem_eraseDups] at hb'
    exact (hS a ha).2 hb'
  have hsub : ∀ z ∈ ((f.parts.filter fun x => x.msg == sighash c.tx 0 && x.input == 0).map
      Exp.signer).eraseDups ++ cohort.eraseDups, z ∈ keys.eraseDups := by
    intro z hz
    rw [List.mem_eraseDups]
    rcases List.mem_append.1 hz with hz | hz
    · exact (hS z hz).1
    · rw [List.mem_eraseDups] at hz
      exact hk _ (.inl (hc z hz).1)
  have hle := length_le_of_nodup_subset hnd hsub
  rw [List.length_append] at hle
  simp only [exposedQuorum, decide_eq_false_iff_not]
  omega

/-- A history no instant protects: an unarmed frame reads a HotClock sample at which the Hold of an
unarmed target acceptance in the same history has matured. -/
def holdBreach (msg : Sighash) (h : History) : Bool :=
  h.any fun a => !a.1.node.armed && h.any fun b => !b.1.node.armed &&
    (match b.2.2 with
     | .accept _ _ _ sp es => sighash sp.tx 0 == msg || sighash es.tx 0 == msg
     | _ => false) && b.2.1.mono.aged a.2.1.mono b.1.node.holdSecs

theorem not_holdProtected_of_breach {msg : Sighash} {h : History} (hb : holdBreach msg h = true)
    (m : Mono) : ¬ HoldProtected msg m h := by
  intro hp
  simp only [holdBreach, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨a, ha, ha0, ⟨wb, envb, evb⟩, hbm, ⟨⟨hb0, hacc⟩, hage⟩⟩ := hb
  simp only at hb0 hacc hage
  have fa := hp a ha
  have fb := hp _ hbm
  simp only [holdFrame, ha0, Bool.false_or, Bool.and_eq_true] at fa
  simp only [holdFrame, hb0, Bool.false_or, Bool.and_eq_true] at fb
  have hm := Mono.aged_of_notAfter hage fa.1
  have := fb.2
  cases evb with
  | accept cid d E sp es =>
    simp only at hacc this
    simp [hacc, hm] at this
  | _ => simp at hacc

/-! ## Fixtures -/

namespace Cases
open BtcPolicy.Kernel.RegistrationCases

/-- `RegistrationCases.A` at its own id: threshold 2 and hold 0. -/
def start (i : Nat) : World := { node := { A with id := i }, exposure := [] }
def fed0 : Fed := { worlds := start, net := [] }
def honest : List Nat := [1, 2, 3]

theorem fed0_fresh : Fresh honest fed0 := by
  unfold Fresh
  decide

def acceptAt (i : Nat) : Step := .process i env0 (.accept 10 false (Wall.sample 200) c1 e1)

/-- Acceptance at three nodes, their relays, two holder decisions, two fire passes, and then a
delivery to the third node after the others released. -/
def toDecisions : List Step :=
  [acceptAt 1, acceptAt 2, acceptAt 3, .emit 1 10, .emit 2 10, .emit 3 10,
   .deliver 1 env0 ⟨2, 10⟩, .deliver 2 env0 ⟨1, 10⟩]
def ordinary : List Step :=
  toDecisions ++ [.process 1 envFire .firePass, .process 2 envFire .firePass,
    .deliver 3 envFire ⟨1, 10⟩]

/-- The run and the state it reaches, by the rules given. `Exhibits.lean` holds them at `current`. -/
def ordinaryTrace (r : Rules) : Trace := record r [] fed0 ordinary
def ordinaryFinal (r : Rules) : Fed := runFrom r fed0 ordinary

/-- Node 1 accepts; node 2 only refuses at gate 10 and relays. -/
def unstagedRelay : List Step := [acceptAt 1, .unstaged 2 10, .deliver 1 env0 ⟨2, 10⟩]

/-- Node 1 accepts; a sender outside the honest list names this Carrier. -/
def injected : List Step := [acceptAt 1, .inject ⟨9, 10⟩, .deliver 1 env0 ⟨9, 10⟩]

/-- A hot partial over `c1` at input 0, under this signer: what node `s`'s fire pass queues in the
ordinary run. -/
def part (s : Nat) : Exp := { msg := sighash tx1 0, input := 0, signer := s, hot := true, cid := c1.id }

/-- The ordinary run, then node 2's partial delivered to node 1 alone, twice, and node 1's assembly
and send. -/
def authorized : List Step :=
  ordinary ++ [.deliverPartial 1 envFire (part 2), .deliverPartial 1 envFire (part 2),
    .process 1 envFire (.packageAccepted c1.id), .process 1 envFire (.send c1.id)]

/-- Node 2's relay reaches node 1 after the Carrier's expiry. -/
def lateRelay : List Step := [acceptAt 1, acceptAt 2, .emit 2 10, .deliver 1 envLate ⟨2, 10⟩]

/-- `RegistrationCases.A` at its own id with threshold 3. -/
def start3 (i : Nat) : World := { node := { A with id := i, t := 3 }, exposure := [] }
def fed3 : Fed := { worlds := start3, net := [] }

theorem fed3_fresh : Fresh honest fed3 := by
  unfold Fresh
  decide

/-- Threshold 3: node 2's relay reaches node 1 twice, then node 3's once. -/
def replayed : List Step :=
  [acceptAt 1, acceptAt 2, acceptAt 3, .emit 2 10, .emit 3 10, .deliver 1 env0 ⟨2, 10⟩,
   .deliver 1 env0 ⟨2, 10⟩]
def replayedThenThird : List Step := replayed ++ [.deliver 1 env0 ⟨3, 10⟩]

/-- Node 3 accepts under duress and arms; nodes 1 and 2 decide normally, release, and node 2's
partial reaches node 1. -/
def armedBeside : List Step :=
  [acceptAt 1, acceptAt 2, .process 3 env0 (.accept 10 true (Wall.sample 200) c1 e1),
   .emit 1 10, .emit 2 10, .emit 3 10,
   .deliver 1 env0 ⟨2, 10⟩, .deliver 2 env0 ⟨1, 10⟩, .deliver 3 env0 ⟨1, 10⟩,
   .process 1 envFire .firePass, .process 2 envFire .firePass, .deliverPartial 1 envFire (part 2)]

/-- Node 1 releases in the ordinary schedule; then node 3's key is copied, a partial is signed
with it, and it reaches node 1. Node 3 itself never releases. -/
def stolenPartial : List Step :=
  toDecisions ++ [.process 1 envFire .firePass, .extract 3, .forge (part 3),
    .deliverPartial 1 envFire (part 3)]

/-- Three nodes accept and none receives a relay; then the keys of honest node 3 and of signer 9
are copied and each signs a partial. Node 3 takes no further step. -/
def stolenQuorum : List Step :=
  [acceptAt 1, acceptAt 2, acceptAt 3, .extract 3, .extract 9, .forge (part 3), .forge (part 9)]

end Cases

end BtcPolicy.Federation
