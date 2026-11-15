import BtcPolicy.LifecycleSilence
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.LifecycleSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.ReceiptExpiry (lookup evicts answer Answer Lookup)
open BtcPolicy.VariantSilence (VFed LStep Checks vheld)
open BtcPolicy.ReceiptLifecycle (DObs bornAt rebirthAt)
open BtcPolicy.LifecycleSilence
open BtcPolicy.Kernel.RegistrationCases (envAt)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (part honest)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep tblsD tblsN request)

/-! ### SILENCE over the lifecycle layer's receipt step

Research task `bps-8bbx.2`, the lifecycle tranche. The request `Exhibits.Ingress.req0` (signed expiry 200), presented
with PIN 1 at nodes 1, 2 and 3 from `EndToEnd.fed0` with empty Hot ledgers. PIN 1 is the duress PIN in the first
family (`tblsD`) and an ordinary PIN in the second (`tblsN`). Every step goes through `ReceiptLifecycle.xvapply`, with
the receivers' keys 1, 2 and 3: a delivered partial is looked up at its own sample, evicts an expired candidate or is
received and offered to the variant-bound store. -/

/-- The expiry-aware receipt's cap and window. -/
def cfg : Config := { cap := 1000, window := 600 }

/-- Wall 150, the holder decisions; wall 170, before the signed expiry; wall 201, one second past it; wall 230; wall
260, past the first family's `T = 250`. -/
def envD : Env := envAt 150 150
def envR : Env := envAt 170 165
def envE : Env := envAt 201 196
def envF : Env := envAt 230 225
def envW : Env := envAt 260 255

/-- The receivers' configured keys. -/
def keys : List Nat := honest

/-- Signer 2's Escape partial under a commitment id no node holds. -/
def missingCand : Exp := { part es0 2 with cid := 77 }

/-- Node 3 presents the request again under Carrier id 11, with PIN 1, at wall 170: a sample earlier than the
evicting receipts' 201. -/
def rereq : PStep := .input 3 envR (.request 11 1 (Wall.sample 200) sp0 es0)

/-- Nodes 1, 2 and 3 take the request; nodes 1 and 2 exchange relays and decide at wall 150, which arms both in the
first family at `T = 250` and neither in the second; node 3 never decides, and holds a duress Carrier in the first
family only. Signer 2's key is copied; its partials on both members and the partial under an unknown id are forged. -/
def setup : List LStep :=
  [(request 1, none), (request 2, none), (request 3, none), (.net (.emit 1 10), none), (.net (.emit 2 10), none),
   (.net (.deliver 1 envD ⟨2, 10⟩), none), (.net (.deliver 2 envD ⟨1, 10⟩), none),
   (.net (.extract 2), none), (.net (.forge (part sp0 2)), none), (.net (.forge (part es0 2)), none),
   (.net (.forge missingCand), none)]

/-- Signer 2's Escape partial under the Escape's hash 0 at node 1, armed in the first family, and at node 3, at wall
170 (steps 11 and 12); the partial under an unknown id at node 1 (13); at wall 201 signer 2's spend partial, then its
Escape partial, at node 3 (14 and 15); node 3's new request (16); signer 2's Escape partial at node 3 at wall 170
again (17); at node 1 signer 2's spend partial at wall 201 (18) and its Escape partial at wall 230 (19). -/
def deliveries : List LStep :=
  [(.net (.deliverPartial 1 envR (part es0 2)), some 0), (.net (.deliverPartial 3 envR (part es0 2)), some 0),
   (.net (.deliverPartial 1 envR missingCand), some 0), (.net (.deliverPartial 3 envE (part sp0 2)), none),
   (.net (.deliverPartial 3 envE (part es0 2)), some 0), (rereq, none),
   (.net (.deliverPartial 3 envR (part es0 2)), some 0), (.net (.deliverPartial 1 envE (part sp0 2)), none),
   (.net (.deliverPartial 1 envF (part es0 2)), some 0)]

/-- Signer 2's spend partial at node 1 at wall 260, past the first family's `T` (20); its Escape partial at node 1
at wall 170, a sample before that `T` (21). -/
def late : LStep := (.net (.deliverPartial 1 envW (part sp0 2)), none)
def back : LStep := (.net (.deliverPartial 1 envR (part es0 2)), some 0)

def sched : List LStep := setup ++ deliveries ++ [late, back]

/-- The two families walked together. -/
def walkX : List (XVObs × XVObs) :=
  xvwalk Silence.current Ledger.current cfg Kernel.current honest honest keys tblsD tblsN (VFed.init L0)
    (VFed.init L0) sched

/-- One family's labelled run after the schedule's first `k` steps. -/
def runX (tbls : Nat → Enrolment) (k : Nat) : VFed :=
  xvrun keys Ledger.current cfg Kernel.current (VFed.init L0) ((sched.take k).map fun p => (p.1.step tbls, p.2))

/-- Whether node `i` holds a record under `cid`, and whether its Hot ledger charges `cid`. -/
def residentAt (V : VFed) (i cid : Nat) : Bool := (V.lf.fed.worlds i).node.cands.any (·.id == cid)
def chargedAt (V : VFed) (i cid : Nat) : Bool := (V.lf.leds i).any (·.cid == cid)

/-- Signer 2's record on the Escape's input 0, and on the spend's. -/
def recEs : Nat × Authority.Sig := (es0.id, { msg := sighash es0.tx 0, input := 0, signer := 2 })
def recSp : Nat × Authority.Sig := (sp0.id, { msg := sighash sp0.tx 0, input := 0, signer := 2 })

/-- What each delivery shows, in the first family: receiver, answer, and whether decisions are shown. -/
def shownAt (k : Nat) : Option (Option (Nat × Answer × Bool)) :=
  (walkX[k]?).map fun y => y.1.delivery.map fun d => (d.receiver, d.answer, d.checks.isSome)

/-- **The lifecycle layer's receipt step inside the walk, under both PINs** (`DUR-1`, `NCH-24`, `NCH-25`).
`LifecycleSilence.xvfed_silence_fresh` at the values as they stand: the two families emit equal
`LifecycleSilence.XVObs` at every step of the walk, and the comparison computed on the walk agrees. The walk covers the
first 20 steps: a kept delivery, an evicting one, one under an unknown id, a re-registration birth and the new
lifetime's first record among them. The hidden states differ: nodes 1 and 2 are armed at `T = 250` in the first family
and neither in the second, and node 3 holds a duress Carrier in the first family only. The records at every honest
node, and the Held projection, are the same in both at the walk's end. -/
@[req "DUR-1"]
theorem lifecycle_silent :
    (∀ y ∈ walkX, y.1 = y.2) ∧
    walkX.all (fun y => y.1 == y.2) = true ∧ walkX.length = 20 ∧
    ((runX tblsD 7).lf.fed.worlds 1).node.armed = true ∧ ((runX tblsD 7).lf.fed.worlds 2).node.armed = true ∧
    ((runX tblsD 7).lf.fed.worlds 1).node.T = Wall.sample 250 ∧
    ((runX tblsN 7).lf.fed.worlds 1).node.armed = false ∧ ((runX tblsN 7).lf.fed.worlds 2).node.armed = false ∧
    ((runX tblsD 20).lf.fed.worlds 3).node.carriers.any (·.duress) = true ∧
    ((runX tblsN 20).lf.fed.worlds 3).node.carriers.any (·.duress) = false ∧
    honest.all (fun j => (runX tblsD 20).store j == (runX tblsN 20).store j &&
      vheld (runX tblsD 20) j == vheld (runX tblsN 20) j) = true := by
  refine ⟨xvfed_silence_fresh rfl rfl rfl rfl rfl rfl honest honest keys tblsD tblsN L0 L0_fresh L0_sweep sched, ?_⟩
  decide +kernel

/-- **Each delivery case, alike in both families** (`NCH-24`, `NCH-25`, `POL-18`). In the first family's walk, and
the same in the second's by `lifecycle_silent`:
- step 11, at node 1, and step 12, at node 3, live: found, decisions shown, signer 2's record kept;
- step 13, an unknown commitment id: `UNKNOWN_CANDIDATE`, no decision shown, nothing kept, no candidate created;
- step 14, node 3's spend past its expiry with no open Escape window beside it: the lookup evicts it, the answer is
  `UNKNOWN_CANDIDATE`, no decision is shown, and the unexposed charge goes with it (the refund);
- step 15, node 3's Escape the same way: evicted, nothing arrives, and the record step 12 kept is dropped with it. -/
@[req "NCH-24"]
theorem lifecycle_cases :
    [11, 12, 13, 14, 15].map shownAt =
      [some (some (1, .found, true)), some (some (3, .found, true)), some (some (1, .unknownCandidate, false)),
       some (some (3, .unknownCandidate, false)), some (some (3, .unknownCandidate, false))] ∧
    [tblsD, tblsN].all (fun tbls =>
      (runX tbls 12).store 1 == [recEs] && (runX tbls 13).store 3 == [recEs] &&
        (runX tbls 14).store 1 == [recEs] && !residentAt (runX tbls 14) 1 missingCand.cid &&
        lookup envE ((runX tbls 14).lf.fed.worlds 3).node sp0.id == .expired &&
        evicts envE ((runX tbls 14).lf.fed.worlds 3).node sp0.id && residentAt (runX tbls 14) 3 sp0.id &&
        chargedAt (runX tbls 14) 3 sp0.id && !residentAt (runX tbls 15) 3 sp0.id &&
        !chargedAt (runX tbls 15) 3 sp0.id && (runX tbls 15).store 3 == [recEs] &&
        evicts envE ((runX tbls 15).lf.fed.worlds 3).node es0.id && !residentAt (runX tbls 16) 3 es0.id &&
        (runX tbls 16).store 3 == []) = true := by
  decide +kernel

/-- **A re-registration birth after the evictions, then the new lifetime's first record** (`DUR-28`, `NCH-25`).
After step 15 node 3 holds neither member. Its new request at wall 170, a sample earlier than the evictions', births
both (step 16, `ReceiptLifecycle.bornAt`) under no id resident before it (`ReceiptLifecycle.rebirthAt` is false), and
keeps nothing. Signer 2's Escape partial at wall 170 is then found and kept again (step 17): the new lifetime's first
record. The same in both families. -/
@[req "NCH-25"]
theorem lifecycle_rebirth :
    shownAt 16 = some none ∧ shownAt 17 = some (some (3, .found, true)) ∧
    [tblsD, tblsN].all (fun tbls =>
      bornAt Ledger.current cfg Kernel.current (runX tbls 16).lf (rereq.step tbls) 3 sp0.id &&
        bornAt Ledger.current cfg Kernel.current (runX tbls 16).lf (rereq.step tbls) 3 es0.id &&
        !rebirthAt Ledger.current cfg Kernel.current (runX tbls 16).lf (rereq.step tbls) &&
        residentAt (runX tbls 17) 3 sp0.id && residentAt (runX tbls 17) 3 es0.id &&
        (runX tbls 17).store 3 == [] && (runX tbls 18).store 3 == [recEs]) = true := by
  decide +kernel

/-- **The delayed slot, inside the walk, under both PINs** (`SPN-41`: "the exemption is granted to the normal PIN's
inert slot too"). At wall 201 and at wall 230, past the signed expiry and before the first family's `T`, node 1's
Escape window is open: it closes at 290 in the first family and at 390 in the second, the inert slot. Node 1's
lookups are live, both families answer found and show the store's decisions at steps 18 and 19, and the spend's
record joins the Escape's. -/
@[req "SPN-41"]
theorem lifecycle_exemption :
    [18, 19].map shownAt = [some (some (1, .found, true)), some (some (1, .found, true))] ∧
    ((runX tblsD 18).lf.fed.worlds 1).node.cands.map (·.windowClose) = [none, some (Wall.sample 290)] ∧
    ((runX tblsN 18).lf.fed.worlds 1).node.cands.map (·.windowClose) = [none, some (Wall.sample 390)] ∧
    [tblsD, tblsN].all (fun tbls =>
      lookup envE ((runX tbls 18).lf.fed.worlds 1).node sp0.id == .live &&
        lookup envF ((runX tbls 19).lf.fed.worlds 1).node es0.id == .live &&
        (runX tbls 19).store 1 == [recEs, recSp] && (runX tbls 20).store 1 == [recEs, recSp]) = true := by
  decide +kernel

/-- **The horizon is `FedSilence.walk`'s, and it stays ended** (`DUR-7`). The walk stops at step 20, the first step
past the first family's `T`: node 1 there is armed with `T = 250` reached at wall 260, and in the second family it is
inside. The stop is sticky. Step 21 carries the backward sample wall 170, and from the state step 20 leaves the
deadline driver's read for it at node 1 is below `T`, so step 21 on its own is inside in both families; yet the walk
compares neither it nor any later step: a backward sample does not restart a comparison that has ended. -/
@[req "DUR-7"]
theorem lifecycle_horizon :
    sched.length = 22 ∧ walkX.length = 20 ∧
    Federation.admits honest (runX tblsD 20).lf.fed (late.1.step tblsD) = true ∧
    inside Kernel.current (runX tblsD 20).lf (late.1.step tblsD) = false ∧
    inside Kernel.current (runX tblsN 20).lf (late.1.step tblsN) = true ∧
    Federation.admits honest (runX tblsD 21).lf.fed (back.1.step tblsD) = true ∧
    inside Kernel.current (runX tblsD 21).lf (back.1.step tblsD) = true ∧
    inside Kernel.current (runX tblsN 21).lf (back.1.step tblsN) = true ∧
    ((runX tblsD 21).lf.fed.worlds 1).node.armed = true := by
  decide +kernel

/-! ### The leak the comparison detects -/

/-- Not a rule the protocol has had: the delivery observation also shows the store's decisions on an expired lookup
at a receiver that holds no duress Carrier. -/
def dobsLeak (keys : List Nat) (V : VFed) : Federation.Step → Option Nat → Option DObs
  | .deliverPartial i env x, h =>
    some { receiver := i, signer := x.signer, label := h, answer := answer env (V.lf.fed.worlds i).node x.cid,
           checks := if lookup env (V.lf.fed.worlds i).node x.cid = .live ∨
               (lookup env (V.lf.fed.worlds i).node x.cid = .expired ∧
                 (V.lf.fed.worlds i).node.carriers.all (!·.duress)) then
             some (VariantSilence.checks keys (V.store i) (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h)
             else none }
  | _, _ => none

/-- Step 14: signer 2's spend partial at node 3 at wall 201. -/
def step14 : LStep := (.net (.deliverPartial 3 envE (part sp0 2)), none)

/-- **A decision shown on hidden Carrier state is a difference the comparison sees.** Step 14 is admitted and inside
the horizon in both families, and node 3's lookup is expired in both. With decisions shown on an expired lookup at a
receiver that holds no duress Carrier, node 3 shows none in the first family and shows the store's decisions in the
second, and the two observations differ. -/
@[req "DUR-1"]
theorem expired_decisions_leak :
    sched.drop 14 = step14 :: sched.drop 15 ∧
    Federation.admits honest (runX tblsD 14).lf.fed (step14.1.step tblsD) = true ∧
    inside Kernel.current (runX tblsD 14).lf (step14.1.step tblsD) = true ∧
    inside Kernel.current (runX tblsN 14).lf (step14.1.step tblsN) = true ∧
    (dobsLeak keys (runX tblsD 14) (step14.1.step tblsD) step14.2).map (·.checks.isSome) = some false ∧
    (dobsLeak keys (runX tblsN 14) (step14.1.step tblsN) step14.2).map (·.checks.isSome) = some true ∧
    dobsLeak keys (runX tblsD 14) (step14.1.step tblsD) step14.2 ≠
      dobsLeak keys (runX tblsN 14) (step14.1.step tblsN) step14.2 := by
  decide +kernel

end BtcPolicy.Exhibits.LifecycleSilence
