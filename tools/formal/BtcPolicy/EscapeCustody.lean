import BtcPolicy.Recovery
/-! Abstract escape-wallet custody beside the composed run (`SEC-54`). Newly formalized behaviour,
not a protocol change. A holder is a natural-number identity; 0 is the Operator and any other
identity is an adversarial party or coalition. A key id denotes usable access, backups included.
There is no bound on holders, and keys held by different parties are not silently pooled.
Only a supplied k-of-m wallet is represented. Actual key usability, descriptor interpretation,
cryptography, diligence and inclusion remain environmental facts. -/
namespace BtcPolicy.EscapeCustody
open BtcPolicy.Kernel

structure Wallet where
  keys : List Nat
  k : Nat

/-- A nonempty threshold over the wallet's distinct key ids. -/
def Wallet.Valid (w : Wallet) : Prop := 0 < w.k ∧ w.k ≤ w.keys.eraseDups.length

/-- All usable access, including backups. A loss removes all such access for that holder permanently;
a copy cannot undo a stated permanent loss. Initial access and copies are environment inputs. -/
structure Custody where
  keys : Nat → List Nat
  lost : Nat → List Nat

/-- Count each distinct wallet key once, excluding every permanently lost key. -/
@[req "SEC-54"]
def heldKeys (w : Wallet) (c : Custody) (who : Nat) : List Nat :=
  ((c.keys who).filter fun k => w.keys.contains k && !(c.lost who).contains k).eraseDups

@[req "SEC-54"]
def capable (w : Wallet) (c : Custody) (who : Nat) : Bool :=
  decide (w.k ≤ (heldKeys w c who).length)

/-- The exact k-of-m threshold reading; key usability is supplied, never proved. -/
@[req "SEC-54"]
theorem capable_iff (w : Wallet) (c : Custody) (who : Nat) :
    capable w c who = true ↔ w.k ≤ (heldKeys w c who).length := by
  simp [capable]

/-- A loss covers the holder's backups too. -/
theorem lost_unusable (w : Wallet) (c : Custody) (who k : Nat) (h : k ∈ c.lost who) :
    k ∉ heldKeys w c who := by
  simp [heldKeys, List.mem_filter, h]

structure St where
  base : Recovery.St
  custody : Custody

inductive Step
  | base (s : Recovery.Step)
  | copy (who key : Nat)
  | lose (who key : Nat)
  deriving DecidableEq, Repr

abbrev Trace := List (St × Step)

/-- Erase only escape-custody steps, retaining the composed run's own states and steps. -/
def baseTrace : Trace → Recovery.Trace
  | [] => []
  | (st, .base s) :: T => (st.base, s) :: baseTrace T
  | _ :: T => baseTrace T

def admits (cfg : Recovery.Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace) : Step → Bool
  | .base s => Recovery.admits cfg r honest st.base (baseTrace T) s
  | .copy who k => !(st.custody.lost who).contains k
  | .lose _ _ => true

def apply (r : Rules) (st : St) : Step → St
  | .base s => { st with base := Recovery.apply r st.base s }
  | .copy who k =>
      if (st.custody.lost who).contains k then st else
      { st with custody := { st.custody with
          keys := fun p => if p == who then k :: st.custody.keys p else st.custody.keys p } }
  | .lose who k => { st with custody := {
      keys := fun p => if p == who then (st.custody.keys p).filter (· != k) else st.custody.keys p,
      lost := fun p => if p == who then k :: st.custody.lost p else st.custody.lost p } }

inductive Execution (cfg : Recovery.Cfg) (r : Rules) (honest : List Nat) : Trace → St → Prop
  | init (st : St) (h : Recovery.Fresh honest st.base) : Execution cfg r honest [] st
  | next {T st} (s : Step) (ha : admits cfg r honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (apply r st s)

/-- Custody adds no premise to any composed step and changes none of its state. -/
theorem to_recovery {cfg : Recovery.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) :
    Recovery.Execution cfg r honest (baseTrace T) st.base := by
  induction hx with
  | init st h => exact .init _ h
  | next s ha _ ih =>
    cases s with
    | base s => exact .next s ha ih
    | copy who k => simp only [apply]; split <;> exact ih
    | lose who k => exact ih

/-- No composed step (including every node, backend and Recovery step) reads or moves escape custody.
With identical projected histories, arbitrary custody assignments give the identical admission verdict
and next composed state. This is state independence, not a byte or timing claim. -/
@[req "SEC-54"]
theorem node_independent (cfg : Recovery.Cfg) (r : Rules) (honest : List Nat) (st : St) (T : Trace)
    (c : Custody) (s : Recovery.Step) :
    admits cfg r honest st T (.base s) = admits cfg r honest { st with custody := c } T (.base s) ∧
      (apply r st (.base s)).base = (apply r { st with custody := c } (.base s)).base ∧
      (apply r st (.base s)).custody = st.custody := ⟨rfl, rfl, rfl⟩

/-- Environment copy and loss leave the entire composed state alone. -/
theorem environment_keeps_base (r : Rules) (st : St) (who k : Nat) :
    (apply r st (.copy who k)).base = st.base ∧ (apply r st (.lose who k)).base = st.base := by
  simp only [apply]; split <;> simp

/-- No step can remove a permanent loss, including a later copy attempt. Together with
`lost_unusable`, this keeps that holder unable to use the key through any future steps. -/
@[req "SEC-54"]
theorem loss_sticky (r : Rules) (st : St) (s : Step) (who k : Nat) (h : k ∈ st.custody.lost who) :
    k ∈ (apply r st s).custody.lost who := by
  cases s with
  | base s => exact h
  | copy p q => simp only [apply]; split <;> exact h
  | lose p q =>
    simp only [apply]
    split <;> simp_all

inductive Outcome
  | denial | theft | loss
  deriving DecidableEq, Repr

/-- Only destination authority is classified. Denial additionally needs the supplied circumstance
"later than wanted"; timing is not derived here. Theft includes shared Operator/adversary authority.
Loss quantifies over every holder, not just the Operator and one coercer. -/
@[req "SEC-54"]
def Reads (w : Wallet) (c : Custody) : Outcome → Prop
  | .denial => capable w c 0 = true ∧ ∀ p, p ≠ 0 → capable w c p = false
  | .theft => ∃ p, p ≠ 0 ∧ capable w c p = true
  | .loss => ∀ p, capable w c p = false

/-- A submitted transaction shown confirmed by the supplied chain, and a custody reading at that
instant. That this transaction pays the supplied escape wallet is a separate checked-shape premise;
this predicate neither interprets a descriptor nor proves cryptographic spendability. -/
def Delivered (w : Wallet) (st : St) (tx : Tx) (o : Outcome) : Prop :=
  (∃ isEscape, (isEscape, tx) ∈ st.base.sent) ∧
    Settlement.confirmedAt st.base.sw.truth tx = true ∧ Reads w st.custody o

/-- Losing the Operator's authority alone does not imply Loss. -/
@[req "SEC-54"]
theorem retained_not_loss (w : Wallet) (c : Custody) (p : Nat) (h : capable w c p = true) :
    ¬ Reads w c .loss := by
  intro hl
  have := hl p
  simp_all

def legal (cfg : Recovery.Cfg) (r : Rules) (honest : List Nat) : Trace → St → List Step → Bool
  | _, _, [] => true
  | T, st, x :: xs => admits cfg r honest st T x && legal cfg r honest ((st, x) :: T) (apply r st x) xs

def record (r : Rules) : Trace → St → List Step → Trace × St
  | T, st, [] => (T, st)
  | T, st, x :: xs => record r ((st, x) :: T) (apply r st x) xs

theorem execution_of_legal {cfg : Recovery.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : St}
    (hx : Execution cfg r honest T st) {xs : List Step} (hl : legal cfg r honest T st xs = true) :
    Execution cfg r honest (record r T st xs).1 (record r T st xs).2 := by
  induction xs generalizing T st with
  | nil => exact hx
  | cons x xs ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next x hl.1 hx) hl.2

/-- The old run is retained exactly, after erasing the new environment moves. -/
def baseSteps : List Step → List Recovery.Step
  | [] => []
  | .base s :: xs => s :: baseSteps xs
  | _ :: xs => baseSteps xs

theorem record_projection (r : Rules) : ∀ (xs : List Step) (T : Trace) (st : St),
    baseTrace (record r T st xs).1 = (Recovery.record r (baseTrace T) st.base (baseSteps xs)).1 ∧
      (record r T st xs).2.base = (Recovery.record r (baseTrace T) st.base (baseSteps xs)).2 := by
  intro xs
  induction xs with
  | nil => intro T st; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro T st
    obtain ⟨h1, h2⟩ := ih ((st, x) :: T) (apply r st x)
    simp only [record]
    rw [h1, h2]
    cases x with
    | base s => exact ⟨rfl, rfl⟩
    | lose who k => exact ⟨rfl, rfl⟩
    | copy who k => simp only [apply]; split <;> exact ⟨rfl, rfl⟩

end BtcPolicy.EscapeCustody
