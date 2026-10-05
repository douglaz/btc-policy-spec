import Lean
import BtcPolicy.Req
import BtcPolicy.Render
/-! The gate and the two emitters, as library functions so the gate walks their constants with
the rest of the library (`ADR-0023` decision 3). The executable roots `Gate.lean`, `Render.lean`
and `Values.lean` are one import and one `main` each, and `tools/check_formal.sh` holds them to
exactly that.

## The gate

For every constant a project module declares, tagged or not, in every namespace, `Explore`
included, it collects the axioms the constant depends on and refuses anything outside `propext`,
`Classical.choice`, `Quot.sound`: that refuses `sorryAx` and `native_decide`'s minted axiom
transitively. Tagged only would leave an untagged `csimp` lemma proved by `sorry`, which
reroutes the emitters past a tagged definition. It refuses an axiom the project declares itself,
written or minted, anywhere: the `Explore` exemption there once was is where a hand-written axiom
named like the minted one could hide. It refuses an `implemented_by` or `extern` attribute on any
project constant, as Lean recorded it. It refuses a tagged declaration under `BtcPolicy.Explore`, a tag that is
not an identifier, and an empty index, because a gate over nothing is `DEF-16`'s green check. It
prints the requirement index — one JSON object per tagged declaration — for the documents' gates.
Exit 0 = every project constant is within policy. -/

open Lean

namespace BtcPolicy.Exe

/-- `lake exe render` — one JSON object per marked region, for `tools/check_regions.py`. -/
def renderMain : IO UInt32 := do
  for r in BtcPolicy.Render.regions do
    IO.println (Json.mkObj [("decl", r.decl), ("kind", r.kind), ("home", r.home), ("text", r.text)]).compress
  return 0

/-- `lake exe values` — one JSON object per emitted value, for `tools/check_copies.py`. -/
def valuesMain : IO UInt32 := do
  for v in BtcPolicy.Render.values do
    IO.println (Json.mkObj [("decl", v.decl), ("req", v.req), ("part", v.part), ("value", v.value)]).compress
  return 0


def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def axiomsOf (env : Environment) (n : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<gate>", fileMap := default }
  let (axioms, _) ← (collectAxioms n : CoreM (Array Name)).toIO ctx { env := env }
  pure axioms

/-- Lean 4.30.0 names the axiom it mints for `native_decide` `<decl>._native.native_decide.ax_…`.
Named here only for the refusal message: every project axiom is refused, minted or written. -/
def isNativeDecideAxiom (a : Name) : Bool :=
  match a with
  | .str (.str (.str _ "_native") "native_decide") ax => ax.startsWith "ax_"
  | _ => false

/-- `XXX-n` or `ADR-nnnn`. -/
def wellFormedId (s : String) : Bool :=
  match s.splitOn "-" with
  | [prefix_, num] =>
      prefix_.length > 0 && prefix_.all Char.isUpper && num.length > 0 && num.all Char.isDigit
  | _ => false

/-- A constant is the project's when the module that declares it is `BtcPolicy` or under it —
whatever namespace the declaration chose. The gate and the emitters live in `BtcPolicy.Exe`, so
they are walked too; the three executable roots hold one `main` each and `tools/check_formal.sh`
holds them to that, since an executable root cannot be imported here. -/
def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`BtcPolicy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

unsafe def gateMain : IO UInt32 := do
  enableInitializersExecution
  -- `lake exe` sets no LEAN_PATH for the program it runs; run from `tools/formal`.
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  withImportModules #[{ module := `BtcPolicy }] {} (trustLevel := 0) fun env => do
    let mut found : Array (Name × String) := #[]
    let mut failures := 0
    for (n, info) in env.constants.toList do
      if let some req := BtcPolicy.reqAttr.getParam? env n then
        found := found.push (n, req)
        if (`BtcPolicy.Explore).isPrefixOf n then
          IO.eprintln s!"FAIL  {n} is tagged @[req \"{req}\"] inside BtcPolicy.Explore"
          failures := failures + 1
        if !(wellFormedId req) then
          IO.eprintln s!"FAIL  {n} is tagged @[req \"{req}\"], which is not an identifier"
          failures := failures + 1
        -- A theorem is never conformance (decision 2): the textual scan sees the source, this
        -- sees the tag as Lean read it, string escapes and all.
        if req.startsWith "CNF-" then
          IO.eprintln s!"FAIL  {n} is tagged @[req \"{req}\"], a conformance item; a theorem is never conformance"
          failures := failures + 1
      if inProject env n then
        let isAxiom := match info with | .axiomInfo _ => true | _ => false
        -- No project axiom, tagged or not, in any namespace, minted or written: the one
        -- exemption there was, `native_decide` under `Explore`, was where a hand-written axiom
        -- named like the minted one could hide (ADR-0023 decision 3 and its considered options).
        if isAxiom then
          let how := if isNativeDecideAxiom n then " (minted by native_decide)" else ""
          IO.eprintln s!"FAIL  {n} is an axiom{how}; the project declares none"
          failures := failures + 1
        -- The axiom policy holds for every project constant, not only tagged ones: a `csimp`
        -- lemma proved by `sorry` is untagged, yet it reroutes the emitters past a tagged
        -- definition (bps-few, 2026-09-17).
        let ax ← axiomsOf env n
        let bad := ax.filter (fun a => !(allowed.contains a))
        if !bad.isEmpty then
          IO.eprintln s!"FAIL  {n} depends on {bad.toList}"
          failures := failures + 1
        -- The emitters print what the kernel proved about: no compiled-evaluation override,
        -- read from the attributes as Lean recorded them, so a macro that expands to one is
        -- seen where a source grep is not.
        if (Compiler.implementedByAttr.getParam? env n).isSome then
          IO.eprintln s!"FAIL  {n} has an implemented_by attribute; the emitters must print what the kernel proved about"
          failures := failures + 1
        if (getExternAttrData? env n).isSome then
          IO.eprintln s!"FAIL  {n} has an extern attribute; the emitters must print what the kernel proved about"
          failures := failures + 1
    let tagged := found.qsort (fun a b => a.1.toString < b.1.toString)
    if tagged.isEmpty then
      IO.eprintln "FAIL: no @[req] declarations found; a gate over nothing is not a gate"
      return 1
    -- The axiom policy was already checked above, over every project constant; a tagged
    -- declaration is one of them.
    for (n, req) in tagged do
      let axioms ← axiomsOf env n
      let kind := if (env.find? n).any (·.isTheorem) then "theorem" else "def"
      let row := Json.mkObj [
        ("req", req), ("decl", n.toString), ("kind", kind),
        ("axioms", Json.arr (axioms.map (Json.str ·.toString))) ]
      IO.println row.compress
    IO.eprintln s!"{tagged.size} tagged declarations, {failures} constants outside the policy"
    return (if failures == 0 then 0 else 1)

end BtcPolicy.Exe
