import BtcPolicy.Kernel
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
sender's name means that sender processed the request.

**One message family.** A `Federation.Relay` is the Carrier relay, by sender and Carrier identity.
`SPN-35` says "one relay of the verbatim request to every peer"; the body and the recipient are not
carried, so two nodes' `accept` inputs for one identity are not tied to each other, and a request a
peer learns from a relay is an `accept` of that peer beside the delivery that counts the sender.
Partials do not travel: `Event.receivePartial` is outside this alphabet, so no peer's partial reaches
a node's held set, and `Exhibits.Composition.ordinary_run` reads that on a run. Delivery of partials
and the compromise bookkeeping are later work.

**The network.** The inventory only grows. Delivery reads it and removes nothing, so a replay is the
same `Step.deliver` taken again, a drop is one never taken, and delay is any later step. Nothing
requires a delivery: there is no delivery guarantee, no fairness and no agreement here.

**Ideal authentication, a boundary and not a proof.** `Step.inject` may only name a sender outside
the honest list, and `Step.deliver` hands the kernel the sender the relay names. That is `NCH-5`'s
"possession of the channel key is proven per message by the envelope signature" taken as given, with
the signature scheme unmodelled. Authentication proves identity and not honesty: an injected relay
need not correspond to anything its sender processed.

**Domain.** The honest list is fixed for the whole execution, and a node outside it has no world
here, only a name on injected relays. Every step's `Env` is arbitrary and per node, as in
`Kernel.Execution`: clocks and chain views are neither shared nor ordered across nodes, and no
comparison between two nodes' samples appears. Thresholds and overlays start unconstrained, also as
there, and nothing says two nodes share a threshold. An honest node's local alphabet leaves out
`Event.adversaryExposes` and `Event.receivePartial` and takes `Event.receipt` only through a delivery.
A node's death is its taking no further step. -/

namespace BtcPolicy.Federation
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## State and steps -/

/-- One relay in the inventory: who it names as sender, and which Carrier. -/
@[req "DUR-5"]
structure Relay where
  sender : Nat
  cid : Nat
  deriving DecidableEq, Repr

/-- One federation's state: each honest node's `Kernel.World`, read at its own id, and the relay
inventory. The function is total, and only an honest id's value is ever read or written. -/
structure Fed where
  worlds : Nat → World
  net : List Relay

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
  deriving DecidableEq, Repr

/-- Which steps may be taken. `NCH-28`: "a node MUST NOT relay a request whose nonce it did not
consume", at `Step.emit`; a copy of a request whose nonce this node already consumed is not relayed
at gate 10 either, since `SPN-5` refuses it at gate 7, whose row propagates nothing. A relay reaches
a node only out of the inventory. `Step.inject`'s guard is the authentication boundary. -/
@[req "NCH-28"]
def admits (honest : List Nat) (f : Fed) : Step → Bool
  | .process i _ e => honest.contains i && ownEvent e
  | .unstaged i cid => honest.contains i && !consumed (f.worlds i).node cid
  | .emit i cid => honest.contains i && consumed (f.worlds i).node cid
  | .inject m => !honest.contains m.sender
  | .deliver i _ m => honest.contains i && f.net.contains m

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

def apply (r : Rules) (f : Fed) : Step → Fed
  | .process i env e => advance r f i env e
  | .deliver i env m => advance r f i env (.receipt m.cid m.sender)
  | .unstaged i cid | .emit i cid => { f with net := f.net ++ [⟨i, cid⟩] }
  | .inject m => { f with net := f.net ++ [m] }

/-- `Kernel.Execution`'s initial boundary at every honest id, with that id on the node, plus two
things. The inventory is empty, and so are the tombstones, which `Kernel.Execution` leaves open: a
seeded tombstone would be a consumed nonce with no event behind it, and `Step.emit` reads it. -/
def Fresh (honest : List Nat) (f : Fed) : Prop :=
  f.net = [] ∧ ∀ i ∈ honest,
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

/-! ## The projection to one node -/

/-- Whose kernel event a step is, if it is one. -/
def actor : Step → Option (Nat × Env × Event)
  | .process i env e => some (i, env, e)
  | .deliver i env m => some (i, env, .receipt m.cid m.sender)
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
    obtain ⟨hexp, _, harmed, hcands, hcarriers, _⟩ := h.2 i hi
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
  | init f h => exact (h.2 i hi).2.1
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
    obtain ⟨_, _, _, _, hcarriers, htomb⟩ := h.2 i hi
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

/-- A fact about two signers, read off one execution: if an honest node received a relay under an
honest sender's name, that sender processed the request. It does not say the sender froze, signed
or still holds anything (`DUR-5`), and it says nothing of a sender outside the honest list. The
kernel alone cannot state this: `Kernel.Execution` admits any `Event.receipt`. -/
@[req "DUR-5"]
theorem receipt_origin {r : Rules} {honest : List Nat} {t : Trace} {f : Fed}
    (hx : Execution r honest t f) {i c s : Nat} {w : World} {env : Env}
    (hm : (w, env, Event.receipt c s) ∈ project i t) (hs : s ∈ honest) : Processed t s c :=
  relay_origin hx (receipt_in_net hx hm) hs

/-! ## The exposure inventory of one federation -/

/-- Every honest node's exposure rows in one list: authority that left a node, not possession at any
node (`POL-18`, `DUR-28`). No compromised signer's row is here yet. -/
@[req "POL-18"]
def exposure (honest : List Nat) (f : Fed) : List Exp :=
  honest.flatMap fun i => (f.worlds i).exposure

/-- A world to read `Kernel.exposedQuorum` on: this node's threshold, the federation's inventory. -/
def inventoryWorld (honest : List Nat) (f : Fed) (i : Nat) : World :=
  { node := (f.worlds i).node, exposure := exposure honest f }

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

end Cases

end BtcPolicy.Federation
