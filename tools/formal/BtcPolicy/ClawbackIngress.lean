import BtcPolicy.Kernel
import BtcPolicy.Encode
/-! The singleton retry and registration clauses of `SPN-50`/`SPN-51`.

`register` adds a response to the existing `Kernel.clawback` transition; `register_projection`
proves that its node is exactly that transition on every input. Earlier admission, expiry,
prevout, decoding, policy and class checks are outside this registration function. Its candidate
is supplied by `Ingress.checkClawback`. Signing material and transport effects are not represented.

`Key` binds supplied exact decoded PSBT bytes, not their parsed transaction fields. Response bytes
are also supplied, not serialized here. The acceptance log below models retention and matching,
not nonce admission, clock-based log pruning, refusal eligibility or a whole handler. Callers use
`lookup` after the earlier gates and before fresh evaluation; only successful fresh registration
uses `retain`. A retained replay returns the stored response and leaves the node alone.
`verdict` is what `Silence.respond` answers on the claw-back's post-check registration
(`Kernel.Event.clawback`), which the SILENCE walks cover (`Silence.respond_clawback_pub`,
`Silence.wfEvent_clawback_escapeRole`). `lookup`, `retain` and `replay` are not in those walks: no
SILENCE statement about the retained-replay log follows from these functions. -/
namespace BtcPolicy.ClawbackIngress
open Kernel Clocks

/-- Request role is distinct from the commitment's transaction class. -/
inductive Role where
  | spend | refresh | clawback
  deriving DecidableEq, BEq, Repr

/-- `SPN-50`: "the request role `clawback`, its commitment id, and its exact base64-decoded PSBT
bytes". Neither coordinator nonce nor coordinator signature participates. The same key binds a
cacheable evaluation refusal, whose eligibility still depends on its originating check. A spend
entry here denotes the role of a pair acceptance, not its full multi-member acceptance key. -/
@[req "SPN-50"]
structure Key where
  role : Role
  id : Nat
  psbt : Encode.Bytes
  deriving DecidableEq, BEq, Repr

structure Entry where
  key : Key
  accepted : Encode.Bytes
  deriving DecidableEq, Repr

/-- Only the retained matching key answers, verbatim. -/
@[req "SPN-50"]
def lookup (log : List Entry) (key : Key) : Option Encode.Bytes :=
  (log.find? (fun e => decide (e.key = key))).map (·.accepted)

/-- Successful fresh evaluation adds a key, retaining the commitment's first acceptance for this
request role. Existing entries and their response bytes are never replaced. Log expiry is upstream. -/
@[req "SPN-50"]
def retain (log : List Entry) (key : Key) (accepted : Encode.Bytes) : List Entry :=
  if (lookup log key).isSome then log
  else
    let first := (log.find? fun e => e.key.role == key.role && e.key.id == key.id).map (·.accepted)
    log ++ [⟨key, first.getD accepted⟩]

@[req "SPN-50"]
theorem role_separates (a b : Key) (h : a.role ≠ b.role) : a ≠ b := by
  intro e; exact h (congrArg Key.role e)

@[req "SPN-50"]
theorem bytes_separate (a b : Key) (h : a.psbt ≠ b.psbt) : a ≠ b := by
  intro e; exact h (congrArg Key.psbt e)

@[req "SPN-50"]
theorem lookup_exact (key : Key) (response : Encode.Bytes) :
    lookup [⟨key, response⟩] key = some response := by simp [lookup]

@[req "SPN-50"]
theorem lookup_other (a b : Key) (response : Encode.Bytes) (h : a ≠ b) :
    lookup [⟨a, response⟩] b = none := by simp [lookup, h]

/-- A retained acceptance cannot change any node field, even if the candidate was collected or
its release window closed after the first acceptance. Re-relay is not modelled here. -/
@[req "SPN-50"]
def replay (n : Node) (response : Encode.Bytes) : Node × Encode.Bytes := (n, response)

@[req "SPN-50"]
theorem replay_preserves (n : Node) (response : Encode.Bytes) :
    (replay n response).1 = n ∧ (replay n response).2 = response := by exact ⟨rfl, rfl⟩

@[req "SPN-50"]
theorem retain_keeps_entries (log : List Entry) (key : Key) (response : Encode.Bytes) :
    ∃ extra, retain log key response = log ++ extra := by
  unfold retain; split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩

/-- The registration identity test reads only id and pair membership. It deliberately does not
compare PSBT bytes, selected state, windows, release progress or an arm bit. -/
@[req "SPN-51"]
def paired (n : Node) (id : Nat) : Bool :=
  n.cands.any fun c => c.id == id && c.pair.isSome

/-- The structured registration refusal. This state-dependent check never creates a replay entry. -/
structure Refusal where
  code : Policy.Code
  check : String
  deriving DecidableEq, Repr

/-- After the earlier checks, a latched node refuses first; a resident pair id is incompatible.
`none` means registration succeeds, including freshly validated bytes over an already resident
unpaired singleton. The verdict reads the node alone, and no arm state. -/
@[req "SPN-51"]
def verdict (n : Node) (c : Cand) : Option Refusal :=
  if n.lockedDown then some ⟨.FRAUD_SUSPECTED, "lockdown"⟩
  else if paired n c.id then some ⟨.PSBT_INCONSISTENT, "candidate_identity"⟩
  else none

/-- The registration: a refusal leaves the node alone; otherwise the original singleton transition
runs. -/
@[req "SPN-51"]
def register (env : Env) (n : Node) (c : Cand) : Node × Option Refusal :=
  match verdict n c with
  | some rf => (n, some rf)
  | none => (Kernel.clawback env n c, none)

/-- The registration's answer is its verdict, under every environment. -/
@[req "SPN-51"]
theorem register_verdict (env : Env) (n : Node) (c : Cand) : (register env n c).2 = verdict n c := by
  unfold register; split <;> simp_all

@[req "SPN-51"]
theorem paired_resident (n : Node) (id : Nat) (h : paired n id = true) :
    n.cands.any (·.id == id) = true := by
  obtain ⟨c, hc, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨c, hc, (Bool.and_eq_true_iff.mp hp).1⟩

/-- Every node field projects to the old transition, under every environment and input. No
existing execution or proof about `Kernel.clawback` is replaced by the response enrichment. -/
@[req "SPN-51"]
theorem register_projection (env : Env) (n : Node) (c : Cand) :
    (register env n c).1 = Kernel.clawback env n c := by
  unfold register
  split
  · rename_i rf h
    unfold verdict at h
    split at h
    · rename_i hl; simp [Kernel.clawback, hl]
    · split at h
      · rename_i hp; simp [Kernel.clawback, paired_resident n c.id hp]
      · cases h
  · rfl

@[req "SPN-51"]
theorem refuses_pair (env : Env) (n : Node) (c : Cand)
    (hl : n.lockedDown = false) (hp : paired n c.id = true) :
    register env n c = (n, some ⟨.PSBT_INCONSISTENT, "candidate_identity"⟩) := by
  simp [register, verdict, hl, hp]

@[req "SPN-51"]
theorem lockdown_first (env : Env) (n : Node) (c : Cand) (hl : n.lockedDown = true) :
    register env n c = (n, some ⟨.FRAUD_SUSPECTED, "lockdown"⟩) := by
  simp [register, verdict, hl]

end BtcPolicy.ClawbackIngress
