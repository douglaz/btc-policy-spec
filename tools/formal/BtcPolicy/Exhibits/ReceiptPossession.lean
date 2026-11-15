import BtcPolicy.ReceiptPossession
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.ReceiptPossession
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envLate)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh part)
open BtcPolicy.Exhibits.CommonRun (inst onBook readFirst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (fire lad vm vm2)
open BtcPolicy.Exhibits.LadderRelease (row2)
open BtcPolicy.Exhibits.Ladder (r1low r2 R2)

/-! ### Possession on the expiry-aware lifecycle layer

Research task `bps-xmq1.5` (`BtcPolicy.ReceiptPossession`). Every run here is one of `ReceiptLifecycle`'s layer from
`Exhibits.EndToEnd.st0` at the instant `Exhibits.RungRelease.vm`, with empty Hot ledgers, under `Ledger.current` and
`Kernel.current`, the ladder configuration `Exhibits.Integrated.ilc`. Nodes 1 and 2 take the request with the Escape
`esP` (`Exhibits.Ingress.es0` with rungs `r1low` and `R2` above its base), the truth moves to the vault at a median of
200, both nodes fire and take a ladder pass, and node 2's rows of the base and of `R2` are handed to node 1. The
positive history meets every premise of `ReceiptPossession.possession_window`, each decided on the run, for the base at
node 2's fire pass and for `R2` at node 2's ladder pass; the theorem, not a decision, gives node 1's quorum. The
negative histories each fail one premise. -/

def pbudget : Config := { cap := 1000000, window := 600 }
def pcfg : RungAssembly.Cfg := { lc := ilc, witnesses := fun _ => [], test := Exhibits.Assembly.core [] }
def P0 : BtcPolicy.ReceiptLifecycle.State := { ls := { cs := { sw := (st0 (inst vm)).sw } }, leds := fun _ => [] }

theorem layer_p0_fresh : BtcPolicy.ReceiptLifecycle.Fresh honest P0 := by
  exact ⟨⟨⟨(st0_fresh (inst vm)).1, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩

/-- A schedule: each step with the label it names, or `none` for `ReceiptLifecycle.labelFor`'s. -/
abbrev Sched := List (RungAssembly.Step × Option (Option Nat))
def auto (ss : List RungAssembly.Step) : Sched := ss.map fun s => (s, none)
def fed (s : Federation.Step) : RungAssembly.Step := .base (.fed s)

def runS (ss : Sched) (n : Nat) : BtcPolicy.ReceiptLifecycle.Trace × BtcPolicy.ReceiptLifecycle.State :=
  BtcPolicy.ReceiptLifecycle.record pcfg.lc.pre.sweep.keys Ledger.current pbudget Kernel.current [] P0 (ss.take n)
def runP (ss : List RungAssembly.Step) (n : Nat) : BtcPolicy.ReceiptLifecycle.Trace × BtcPolicy.ReceiptLifecycle.State :=
  runS (auto ss) n
def legalP (ss : Sched) : Bool :=
  BtcPolicy.ReceiptLifecycle.legal pcfg Ledger.current pbudget Kernel.current honest [] P0 ss
def quorumAt (ss : Sched) (n : Nat) (g : Rung) : Bool :=
  Authority.quorum pcfg.lc.pre.sweep.keys 2 g.tx (BtcPolicy.ReceiptLifecycle.heldAt (runS ss n).2 1)

/-- The Escape: `es0` with rungs `r1low` (refused by `ilc`'s floor) and `R2` above its base. -/
def esP : Cand := { es0 with above := [⟨r1low, 11⟩, R2] }
/-- The base of `esP`, with its user-signature hash. -/
def gB : Rung := ⟨es0.tx, es0.baseSig⟩

/-- Nodes 1 and 2 take the request with `esP` under the duress PIN and exchange relays; the truth moves to the vault
at a median of 200; nodes 1 and 2 fire; node 2, then node 1, takes a ladder pass. -/
def raw : List Sweep.Step :=
  [.fed (.process 1 env0 (.accept 10 true (Wall.sample 200) sp0 esP)),
   .fed (.process 2 env0 (.accept 10 true (Wall.sample 200) sp0 esP)), .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩), .chain vm2, fire 1, fire 2, lad 2, lad 1]

/-- The positive history, 15 steps: `raw` read on the book with each pass's verdict filled in
(`LadderRelease.fill`), node 2's fire pass at step 10 and its ladder pass at step 11; then node 2's row of the base
(step 13) and its row of `R2` (step 14) handed to node 1 at the fire instant. -/
def hsteps : List RungAssembly.Step :=
  (LadderRelease.fill ilc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm raw).map onBook)).map .base ++
    [fed (.deliverPartial 1 envFire (part es0 2)), fed (.deliverPartial 1 envFire (row2 r2))]

/-- `hsteps` offered in order, one step per slot, and nothing after it. -/
def sched (u : Nat) : Option RungAssembly.Step := hsteps[u]?

/-- The environment a slot's federation step carries. -/
def envOf : Option RungAssembly.Step → Env
  | some (.base (.fed (.process _ env _))) => env
  | some (.base (.fed (.deliverPartial _ env _))) => env
  | _ => env0

set_option synthInstance.maxSize 4096 in
theorem layer_run : legalP (auto hsteps) = true ∧ hsteps.length = 15 := by
  decide +kernel

theorem layer_play {n : Nat} (hn : n ≤ 15) :
    BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0 sched n = runP hsteps n := by
  exact BtcPolicy.ReceiptPossession.play_list layer_run.1 n (by rw [layer_run.2]; exact hn)

set_option synthInstance.maxSize 4096 in
/-- What the run shows at the slots the rung path reads: node 2's ladder pass offered at slot 11, admitted, its
account over the layer's sweep history listing rung 2 (`R2`) for its Escape; the delivery of node 2's row of `R2` to
node 1 offered at slot 14 and at no other slot of `[12, 14]`, its chain view read off node 1's observation and every
envelope of the row labelled with `R2`'s hash; node 1 retaining compatible material under the Escape's commitment at
every slot of `[12, 15]`; and node 1's threshold and latch at slot 15. -/
theorem layer_rung_facts :
    Possession.passOf 2 .ladderPass (sched 11) = true ∧
      BtcPolicy.ReceiptLifecycle.admits pcfg Ledger.current pbudget Kernel.current honest (runP hsteps 11).2
        (runP hsteps 11).1 (.base (.fed (.process 2 (envOf (sched 11)) .ladderPass))) = true ∧
      Possession.RungReady pcfg Kernel.current (runP hsteps 11).2.ls
        (BtcPolicy.ReceiptLifecycle.forget Ledger.current pbudget (runP hsteps 11).1) 1 2 (envOf (sched 11)) es0.id R2 ∧
      Possession.rowOf 2 es0.id R2 0 = row2 r2 ∧
      Possession.deliverOf 1 (row2 r2) (sched 12) = false ∧ Possession.deliverOf 1 (row2 r2) (sched 13) = false ∧
      Possession.deliverOf 1 (row2 r2) (sched 14) = true ∧
      Settlement.viewOk (runP hsteps 14).2.ls.cs.sw 1 (envOf (sched 14)) = true ∧
      (∀ z ∈ (runP hsteps 14).2.envs, z.1 = row2 r2 → z.2 = some R2.userSig) ∧
      (∀ u ∈ [12, 13, 14, 15], Possession.Retains (runP hsteps u).2.ls 1 es0.id R2) ∧
      R2.tx.inputs.length = 1 ∧ 1 ∈ pcfg.lc.pre.sweep.keys ∧ 2 ∈ pcfg.lc.pre.sweep.keys ∧ 1 ∈ honest ∧
      ((runP hsteps 15).2.ls.cs.sw.fed.worlds 1).node.t = 2 ∧
      (∃ c ∈ ((runP hsteps 15).2.ls.cs.sw.fed.worlds 1).node.cands, c.id = es0.id ∧ c.ladder[2]? = some R2 ∧
        2 ≤ c.track.latch) := by
  unfold Possession.RungReady Possession.Retains
  decide +kernel

/-- **The premises hold on the useful run: a rung** (`DUR-28`). `ReceiptPossession.possession_window` applied to
`hsteps`, offered slot by slot (`ReceiptPossession.play_list`), with node 2 the one contributor (`S = [2]`), node 1
the receiver counted by its own signature, and `R2` (rung 2, `ReceiptPossession.Pass.rung 1`) released at node 2's
ladder pass: the pass window is slot 11, the delivery window `[12, 14]`, the retention window `[12, 15]`. The theorem,
not a decision, gives node 1's quorum on `r2` at slot 15 at node 1's threshold in its possession on the layer
(`ReceiptLifecycle.heldAt`), and with it a finalization of node 1's Escape at rung 2 or above
(`ReceiptPossession.final_of_quorum`). -/
@[req "DUR-28"]
theorem layer_possession :
    Authority.quorum pcfg.lc.pre.sweep.keys 2 R2.tx
        (BtcPolicy.ReceiptLifecycle.heldAt (runP hsteps 15).2 1) = true ∧
      ∃ c ∈ ((runP hsteps 15).2.ls.cs.sw.fed.worlds 1).node.cands, c.id = es0.id ∧
        ∃ m', BtcPolicy.ReceiptLifecycle.finalAt pcfg (runP hsteps 15).2 1 c = some m' ∧ 2 ≤ m' := by
  obtain ⟨hp11, ha11, hr11, hrow, hd12, hd13, hd14, hview, hlab, hret, hlen, hk1, hk2, hh1, ht15, c, hc, hcid, hcl,
    hlat⟩ := layer_rung_facts
  have hq : Authority.quorum pcfg.lc.pre.sweep.keys 2 R2.tx (BtcPolicy.ReceiptLifecycle.heldAt
      (BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0 sched
        (11 + 0 + 2 + 2)).2 1) = true := by
    refine BtcPolicy.ReceiptPossession.possession_window (cfg := pcfg) (g := Ledger.current) (lcfg := pbudget)
      (r := Kernel.current) (honest := honest) (st0 := P0) (sched := sched) (S := [2]) (j := 1) (cid := es0.id)
      (t := 2) (gr := R2) (t0 := 11) (B₁ := 0) (B₂ := 2)
      layer_p0_fresh rfl (.rung 1) hh1 hk1 (by decide) (by decide) (fun s hs => by simp at hs; subst hs; exact hk2)
      (by decide) (fun h => by rw [h] at hlen; cases hlen)
      (fun s hs => ⟨11, by omega, by omega, by simp at hs; subst hs; exact hp11⟩) ?_ ?_ ?_ ?_
    · intro s hs u h1 h2 _ env he
      simp at hs; subst hs
      obtain rfl : u = 11 := by omega
      have henv : env = envOf (sched 11) := by rw [he]; rfl
      subst henv
      rw [layer_play (by omega)]
      exact ⟨ha11, hr11⟩
    · intro s hs k hk
      simp at hs; subst hs
      rw [hlen] at hk
      obtain rfl : k = 0 := by omega
      exact ⟨14, by omega, by omega, by rw [hrow]; exact hd14⟩
    · intro s hs k hk u h1 h2 _ env he
      simp at hs; subst hs
      rw [hlen] at hk
      obtain rfl : k = 0 := by omega
      rw [hrow] at he ⊢
      have hdu : Possession.deliverOf 1 (row2 r2) (sched u) = true := by rw [he]; simp [Possession.deliverOf]
      obtain rfl | rfl | rfl : u = 12 ∨ u = 13 ∨ u = 14 := by omega
      · rw [hd12] at hdu; cases hdu
      · rw [hd13] at hdu; cases hdu
      · have henv : env = envOf (sched 14) := by rw [he]; rfl
        subst henv
        rw [layer_play (by omega)]
        exact ⟨hview, hlab⟩
    · intro u h1 h2
      rw [layer_play (by omega)]
      exact hret u (by
        obtain rfl | rfl | rfl | rfl : u = 12 ∨ u = 13 ∨ u = 14 ∨ u = 15 := by omega
        all_goals simp)
  rw [layer_play (by omega)] at hq
  refine ⟨hq, c, hc, hcid, BtcPolicy.ReceiptPossession.final_of_quorum hcl hlat ?_⟩
  rw [ht15]
  exact hq

set_option synthInstance.maxSize 4096 in
/-- What the run shows at the slots the base path reads: node 2's fire pass offered at slot 10, admitted, and the
base's release conditions holding there for its Escape (`Possession.BaseReady`); the delivery of node 2's row of the
base to node 1 offered at slot 13 and at no other slot of `[11, 13]`, its chain view read off node 1's observation and
every envelope of the row labelled with the base's hash; node 1 retaining compatible material under the Escape's
commitment at every slot of `[11, 14]`; and node 1's threshold at slot 14. -/
theorem layer_base_facts :
    Possession.passOf 2 .firePass (sched 10) = true ∧
      BtcPolicy.ReceiptLifecycle.admits pcfg Ledger.current pbudget Kernel.current honest (runP hsteps 10).2
        (runP hsteps 10).1 (.base (.fed (.process 2 (envOf (sched 10)) .firePass))) = true ∧
      Possession.BaseReady Kernel.current (runP hsteps 10).2.ls 2 (envOf (sched 10)) es0.id gB ∧
      Possession.rowOf 2 es0.id gB 0 = part es0 2 ∧
      Possession.deliverOf 1 (part es0 2) (sched 11) = false ∧ Possession.deliverOf 1 (part es0 2) (sched 12) = false ∧
      Possession.deliverOf 1 (part es0 2) (sched 13) = true ∧
      Settlement.viewOk (runP hsteps 13).2.ls.cs.sw 1 (envOf (sched 13)) = true ∧
      (∀ z ∈ (runP hsteps 13).2.envs, z.1 = part es0 2 → z.2 = some gB.userSig) ∧
      (∀ u ∈ [11, 12, 13, 14], Possession.Retains (runP hsteps u).2.ls 1 es0.id gB) ∧
      gB.tx.inputs.length = 1 ∧ ((runP hsteps 14).2.ls.cs.sw.fed.worlds 1).node.t = 2 ∧
      (∃ c ∈ ((runP hsteps 14).2.ls.cs.sw.fed.worlds 1).node.cands, c.id = es0.id ∧ c.ladder[0]? = some gB) := by
  unfold Possession.BaseReady Possession.Retains
  decide +kernel

/-- **The premises hold on the useful run: the base** (`DUR-21`, `DUR-28`). `ReceiptPossession.possession_window`
applied to `hsteps` with node 2 the one contributor, node 1 the receiver, and the base released at node 2's fire pass
(`ReceiptPossession.Pass.fire`, under `Possession.BaseReady`): the pass window is slot 10, the delivery window
`[11, 13]`, the retention window `[11, 14]`. The theorem gives node 1's quorum on the base at slot 14, and with it a
finalization of node 1's Escape. -/
@[req "DUR-28"]
theorem layer_base_possession :
    Authority.quorum pcfg.lc.pre.sweep.keys 2 gB.tx
        (BtcPolicy.ReceiptLifecycle.heldAt (runP hsteps 14).2 1) = true ∧
      ∃ c ∈ ((runP hsteps 14).2.ls.cs.sw.fed.worlds 1).node.cands, c.id = es0.id ∧
        ∃ m', BtcPolicy.ReceiptLifecycle.finalAt pcfg (runP hsteps 14).2 1 c = some m' := by
  obtain ⟨hp10, ha10, hr10, hrow, hd11, hd12, hd13, hview, hlab, hret, hlen, ht14, c, hc, hcid, hcl⟩ :=
    layer_base_facts
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk1, hk2, hh1, -⟩ := layer_rung_facts
  have hq : Authority.quorum pcfg.lc.pre.sweep.keys 2 gB.tx (BtcPolicy.ReceiptLifecycle.heldAt
      (BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0 sched
        (10 + 0 + 2 + 2)).2 1) = true := by
    refine BtcPolicy.ReceiptPossession.possession_window (cfg := pcfg) (g := Ledger.current) (lcfg := pbudget)
      (r := Kernel.current) (honest := honest) (st0 := P0) (sched := sched) (S := [2]) (j := 1) (cid := es0.id)
      (t := 2) (gr := gB) (t0 := 10) (B₁ := 0) (B₂ := 2)
      layer_p0_fresh rfl .fire hh1 hk1 (by decide) (by decide) (fun s hs => by simp at hs; subst hs; exact hk2)
      (by decide) (fun h => by rw [h] at hlen; cases hlen)
      (fun s hs => ⟨10, by omega, by omega, by simp at hs; subst hs; exact hp10⟩) ?_ ?_ ?_ ?_
    · intro s hs u h1 h2 _ env he
      simp at hs; subst hs
      obtain rfl : u = 10 := by omega
      have henv : env = envOf (sched 10) := by rw [he]; rfl
      subst henv
      rw [layer_play (by omega)]
      exact ⟨ha10, hr10⟩
    · intro s hs k hk
      simp at hs; subst hs
      rw [hlen] at hk
      obtain rfl : k = 0 := by omega
      exact ⟨13, by omega, by omega, by rw [hrow]; exact hd13⟩
    · intro s hs k hk u h1 h2 _ env he
      simp at hs; subst hs
      rw [hlen] at hk
      obtain rfl : k = 0 := by omega
      rw [hrow] at he ⊢
      have hdu : Possession.deliverOf 1 (part es0 2) (sched u) = true := by rw [he]; simp [Possession.deliverOf]
      obtain rfl | rfl | rfl : u = 11 ∨ u = 12 ∨ u = 13 := by omega
      · rw [hd11] at hdu; cases hdu
      · rw [hd12] at hdu; cases hdu
      · have henv : env = envOf (sched 13) := by rw [he]; rfl
        subst henv
        rw [layer_play (by omega)]
        exact ⟨hview, hlab⟩
    · intro u h1 h2
      rw [layer_play (by omega)]
      exact hret u (by
        obtain rfl | rfl | rfl | rfl : u = 11 ∨ u = 12 ∨ u = 13 ∨ u = 14 := by omega
        all_goals simp)
  rw [layer_play (by omega)] at hq
  obtain ⟨m', hm', -⟩ := BtcPolicy.ReceiptPossession.final_of_quorum (m := 0) hcl (Nat.zero_le _)
    (by rw [ht14]; exact hq)
  exact ⟨hq, c, hc, hcid, m', hm'⟩

/-! ### Where one premise fails -/

/-- `hsteps`' first 13 steps: both of node 2's passes are taken, and the run stops before node 1 is handed either
row. -/
def cut : List RungAssembly.Step := hsteps.take 13

set_option synthInstance.maxSize 4096 in
theorem layer_cut_facts :
    (∀ u < 13, Possession.deliverOf 1 (row2 r2) cut[u]? = false ∧ Possession.deliverOf 1 (part es0 2) cut[u]? = false) ∧
      cut.length = 13 ∧ quorumAt (auto cut) 13 R2 = false ∧ quorumAt (auto cut) 13 gB = false ∧
      row2 r2 ∈ (runP cut 13).2.ls.cs.sw.fed.parts ∧ part es0 2 ∈ (runP cut 13).2.ls.cs.sw.fed.parts := by
  decide +kernel

/-- **Starvation: the deliveries are never offered** (the delivery service fails). The schedule offers `hsteps`' first
13 steps and then nothing: node 2's releases of the base and of `R2` are taken and their rows stay in the inventory at
every later slot, the delivery of either row to node 1 is offered at no slot, and node 1's possession on the layer has
no quorum on either at any slot from 13 on. -/
@[req "DUR-28"]
theorem layer_starved :
    (∀ u : Nat, Possession.deliverOf 1 (row2 r2) cut[u]? = false ∧ Possession.deliverOf 1 (part es0 2) cut[u]? = false) ∧
      ∀ u : Nat, 13 ≤ u →
        Authority.quorum pcfg.lc.pre.sweep.keys 2 R2.tx (BtcPolicy.ReceiptLifecycle.heldAt
          (BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0 (fun v => cut[v]?)
            u).2 1) = false ∧
        Authority.quorum pcfg.lc.pre.sweep.keys 2 gB.tx (BtcPolicy.ReceiptLifecycle.heldAt
          (BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0 (fun v => cut[v]?)
            u).2 1) = false ∧
        row2 r2 ∈ (BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0
          (fun v => cut[v]?) u).2.ls.cs.sw.fed.parts := by
  obtain ⟨hd, hlen, hq, hqB, hp, -⟩ := layer_cut_facts
  have h13 : BtcPolicy.ReceiptPossession.play pcfg Ledger.current pbudget Kernel.current honest P0
      (fun v => cut[v]?) 13 = runP cut 13 := by
    have hl : BtcPolicy.ReceiptLifecycle.legal pcfg Ledger.current pbudget Kernel.current honest [] P0
        (cut.map fun s => (s, none)) = true := by
      rw [cut, List.map_take]
      exact BtcPolicy.ReceiptPossession.legal_take layer_run.1 13
    exact BtcPolicy.ReceiptPossession.play_list hl 13 (Nat.le_of_eq hlen.symm)
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · by_cases h : u < 13
    · exact hd u h
    · rw [List.getElem?_eq_none (by omega)]; exact ⟨rfl, rfl⟩
  · have he := BtcPolicy.ReceiptPossession.play_after (cfg := pcfg) (g := Ledger.current) (lcfg := pbudget)
      (r := Kernel.current) (honest := honest) (st0 := P0) (ss := cut) (u - 13)
    rw [hlen, show 13 + (u - 13) = u by omega, h13] at he
    rw [he]
    exact ⟨hq, hqB, hp⟩

/-- `hsteps`' first 13 steps, then node 2's rows of `R2` and of the base handed to node 1 at the late instant (wall
201), past the Escape's expiry. -/
def early : List RungAssembly.Step :=
  cut ++ [fed (.deliverPartial 1 envLate (row2 r2)), fed (.deliverPartial 1 envLate (part es0 2))]

set_option synthInstance.maxSize 4096 in
/-- **Expiry before receipt** (the delivery's lookup evicts). On `early`, a legal run of the layer, the first late
delivery is admitted and taken, and node 1's lookup at its sample evicts the Escape: no resident under the commitment
remains and the lookup now finds nothing. The second delivery finds nothing to store against. Node 1's store holds no
record, there is no quorum on `R2` or on the base, and both rows are in node 1's exposure history and in the inventory:
prior exposure without possession. -/
@[req "NCH-24"]
theorem layer_expired_first :
    legalP (auto early) = true ∧
      ReceiptExpiry.evictsAt (runP early 13).2.lf (.deliverPartial 1 envLate (row2 r2)) = true ∧
      ((runP early 14).2.ls.cs.sw.fed.worlds 1).node.cands.any (·.id == es0.id) = false ∧
      ((runP early 15).2.ls.cs.sw.fed.worlds 1).node.cands.any (·.id == es0.id) = false ∧
      ((runP early 15).2.store 1).length = 0 ∧
      quorumAt (auto early) 15 R2 = false ∧ quorumAt (auto early) 15 gB = false ∧
      { row2 r2 with hot := true } ∈ ((runP early 15).2.ls.cs.sw.fed.worlds 1).exposure ∧
      { part es0 2 with hot := true } ∈ ((runP early 15).2.ls.cs.sw.fed.worlds 1).exposure ∧
      row2 r2 ∈ (runP early 15).2.ls.cs.sw.fed.parts := by
  decide +kernel

/-- `hsteps`, then node 2's row of the base handed to node 1 again at the late instant. -/
def late : List RungAssembly.Step := hsteps ++ [fed (.deliverPartial 1 envLate (part es0 2))]

set_option synthInstance.maxSize 4096 in
/-- **Eviction after receipt** (retention fails after the quorum). On `late`, a legal run of the layer, node 1 holds
the quorum on `R2` at slot 15; the redelivery at the late instant evicts the Escape, node 1's store keeps no record
under it (`ReceiptLifecycle.evict_clears`, the store's residency filter), and the quorum is gone, while both rows stay
in the inventory and in node 1's exposure history. -/
@[req "NCH-25"]
theorem layer_evicted_after :
    legalP (auto late) = true ∧ quorumAt (auto late) 15 R2 = true ∧
      ReceiptExpiry.evictsAt (runP late 15).2.lf (.deliverPartial 1 envLate (part es0 2)) = true ∧
      ((runP late 16).2.ls.cs.sw.fed.worlds 1).node.cands.any (·.id == es0.id) = false ∧
      ((runP late 16).2.store 1).length = 0 ∧
      quorumAt (auto late) 16 R2 = false ∧ quorumAt (auto late) 16 gB = false ∧
      row2 r2 ∈ (runP late 16).2.ls.cs.sw.fed.parts ∧
      { row2 r2 with hot := true } ∈ ((runP late 16).2.ls.cs.sw.fed.worlds 1).exposure := by
  decide +kernel

/-- `hsteps`, then node 1's prune at the late instant, past the Escape's expiry. -/
def pruned : List RungAssembly.Step := hsteps ++ [fed (.process 1 envLate .prune)]

set_option synthInstance.maxSize 4096 in
/-- **Pruning after receipt** (retention fails after the quorum). On `pruned`, a legal run of the layer, node 1 holds
the quorum on `R2` at slot 15; its prune removes every resident under the Escape's commitment, its store keeps no
record under it, and the quorum is gone, while the rows stay in the inventory. -/
@[req "NCH-25"]
theorem layer_pruned_after :
    legalP (auto pruned) = true ∧ quorumAt (auto pruned) 15 R2 = true ∧
      ((runP pruned 16).2.ls.cs.sw.fed.worlds 1).node.cands.any (·.id == es0.id) = false ∧
      ((runP pruned 16).2.store 1).length = 0 ∧
      quorumAt (auto pruned) 16 R2 = false ∧ row2 r2 ∈ (runP pruned 16).2.ls.cs.sw.fed.parts := by
  decide +kernel

/-- `hsteps`' first 13 steps, then node 2's key extracted, then node 2's row of `R2` handed to node 1 under a label
naming another variant (hash 999, not `R2`'s 12). -/
def mis : Sched :=
  auto (cut ++ [fed (.extract 2)]) ++ [(fed (.deliverPartial 1 envFire (row2 r2)), some (some 999))]

set_option synthInstance.maxSize 4096 in
/-- **An incompatible variant** (the label premise fails). On `mis`, a legal run of the layer, the delivery whose
label names a variant other than the one node 1 retains for `R2` is admitted and taken, its store test fails at node 1
(`VariantReceipt.storable`), no record is kept and there is no quorum on `R2`, while the row is in node 1's exposure
history: prior exposure without possession. The same row under `R2`'s own hash is kept on `hsteps` (step 14). -/
@[req "NCH-24"]
theorem layer_label_mismatch :
    legalP mis = true ∧
      VariantReceipt.storable pcfg.lc.pre.sweep.keys ((runS mis 14).2.ls.cs.sw.fed.worlds 1).node (row2 r2).msg 0 2
        es0.id (some 999) = false ∧
      ((runS mis 15).2.store 1).length = 0 ∧ quorumAt mis 15 R2 = false ∧
      { row2 r2 with hot := true } ∈ ((runS mis 15).2.ls.cs.sw.fed.worlds 1).exposure := by
  decide +kernel

end BtcPolicy.Exhibits.ReceiptPossession
