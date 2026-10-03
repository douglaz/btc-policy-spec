import BtcPolicy.Timelock
import BtcPolicy.Shapes
import BtcPolicy.Budget
import BtcPolicy.BumpTarget
import BtcPolicy.Freshness
import BtcPolicy.Preimage
import BtcPolicy.Cursor
import BtcPolicy.Coverage
import BtcPolicy.Gates
import BtcPolicy.Trace
/-! The marked regions and the emitted values (`ADR-0023` decisions 1 and 5).

A **region** is what the lines between `<!-- formal: <decl> -->` and `<!-- /formal -->` in a
document must contain, computed from the declaration named. Every region here but `spn5Gates` is
`render`: an arithmetic table is compared line for line, because a `match` region compares only
backticked and bold tokens and would not see a bare number change; `spn5Gates` is `match`. `home`
names where the region sits: a requirement id, or an ADR (`"ADR-0014"`) for a region the
requirement's owner keeps there. A region inside a list item carries the item's indent in its
emitted lines, and its markers are indented the same way in the document.

An **emitted value** is a scalar or formula string a declaration owns, which `tools/check_copies.py`
compares to the figure inline in the owning sentence and in every copy of it. The Lean constant
cannot read the Markdown; the gate reads both. -/

namespace BtcPolicy.Render

structure Region where
  decl : String
  kind : String
  home : String
  text : String

structure Value where
  decl : String
  req : String
  value : String
  part : String

/-! ## `SPN-38`'s boundary table -/

def capCell : Option Nat → String
  | none => "none"
  | some c => toString c

/-- One row: the five inputs, the cap under the anchor as it stands, and the cap the withdrawn
cursor anchor would give, so the rows that distinguish the two are visible (`F51`). -/
def spn38Row (r : Cursor.Row) : String :=
  let (q, i, f, a, l, _) := r
  let onCurrent := Cursor.quotaRungCap Cursor.current q i f a l
  let onCursor := Cursor.quotaRungCap .onCursor q i f a l
  s!"| {q} | {i} | {f} | {a} | {l} | {capCell onCurrent} | {capCell onCursor} |"

@[req "SPN-38"]
def spn38Table : Region :=
  { decl := "BtcPolicy.Render.spn38Table", kind := "render", home := "SPN-38",
    text := "\n".intercalate
      ([ "| peer quota | inputs per variant | release floor | lowest admissible | last rung index | quota rung cap | cap if anchored on the cursor (`F51`) |",
         "|---|---|---|---|---|---|---|" ] ++ Cursor.rows.map spn38Row) }

/-! ## `ADR-0014`'s delayed-holder timeline -/

/-- The rows as the ADR states them: the instant, the event, and the accounting note. The numbers
are the declaration's (`Budget.timeline`); the prose is carried here so the table is pure
`render`. -/
def adr0014Rows : List (Nat × String × String) :=
  let tl := Budget.timeline
  [ (tl.firstAccept, "Every node accepts a hot spend of `V`, expiry " ++ toString tl.firstExpiry,
      "Reservation time " ++ toString tl.firstAccept ++ "; Carrier deadline " ++ toString tl.firstExpiry ++ "; no holder quorum"),
    (tl.firstHold, "The Hold ends", "The pair is still closed; no partial has left"),
    (tl.firstComplete, "Peer transport recovers; relays establish holder quorum",
      "Within the fire window and both Carrier bounds; first release and completion of `V`"),
    (tl.boundary, "First reservation's boundary", "Still charged at equality"),
    (tl.secondAccept, "First reservation ages out; every node accepts a disjoint spend of `V`, expiry " ++ toString tl.secondExpiry,
      "Fresh reservation; immediate holder quorum"),
    (tl.secondComplete, "The second Hold ends", "Second release and completion of `V`") ]

@[req "POL-20"]
def adr0014Timeline : Region :=
  { decl := "BtcPolicy.Render.adr0014Timeline", kind := "render", home := "ADR-0014",
    text := "\n".intercalate
      ([ "  | Time (seconds) | Event | Accounting and authority |", "  |---|---|---|" ] ++
       adr0014Rows.map fun (when, event, note) => s!"  | {when} | {event} | {note} |") }

/-! ## `SPN-5`'s gate table: the three decided columns -/

/-- A `match` region: the `#` column is the key, the gate and refusal columns are prose the
declaration does not emit (left empty here, so nothing in them is compared), and the three
columns `Gates.rows` decides are backticked so the gate compares them cell by cell. -/
@[req "SPN-5"]
def spn5Gates : Region :=
  { decl := "BtcPolicy.Render.spn5Gates", kind := "match", home := "SPN-5",
    text := "\n".intercalate (Gates.rows.map fun row =>
      s!"| {row.label} |  |  | {Gates.nonceCell row.nonce} | {Gates.propagatesCell row.propagates} | {Gates.stagesCell row.stages} |") }

/-! ## `ADR-0023`'s published trace exhibit -/

/-- Two lowercase hex digits. -/
def hexByte (b : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 b)
  if s.length < 2 then "0" ++ s else s

def hexOf (bs : Encode.Bytes) : String := String.join (bs.map hexByte)

/-- 32 bytes to a line, on fuel so the recursion is structural. -/
def chunksAux : Nat → Encode.Bytes → List Encode.Bytes
  | 0, _ => []
  | _, [] => []
  | n + 1, bs => bs.take 32 :: chunksAux n (bs.drop 32)

def chunks (bs : Encode.Bytes) : List Encode.Bytes := chunksAux bs.length bs

/-- The hex, then a `#` comment in the column `08-wire-contract.md` uses. -/
def commented (hex comment : String) : String := hex.pushn ' ' (68 - hex.length) ++ "# " ++ comment

def kernelLabel : Trace.KernelEvent → String
  | .accept cid _ _ _ _ => s!"accept cid {cid}"
  | .refuse cid _ _ _ _ => s!"refuse {cid}"
  | .receipt cid s => s!"receipt cid {cid} from {s}"
  | .firePass => "firePass"
  | .packageAccepted c => s!"packageAccepted cand {c}"
  | .send c => s!"send cand {c}"
  | .settle tx => s!"settle tx {tx.id}"
  | .prune => "prune"
  | .tick => "tick"
  | .panic => "panic"
  | .adversaryExposes _ _ s c => s!"adversaryExposes signer {s} cid {c}"
  | .receivePartial _ _ s c => s!"receivePartial cid {c} from {s}"

def effectLabel : Kernel.Effect → String
  | .queuePartial _ _ _ c => s!"queuePartial cid {c}"
  | .broadcast tx => s!"broadcast tx {tx}"

/-- A kernel entry's label names its event, then each effect it carries after `emits`. -/
def entryLabel : Trace.Entry → String
  | .kernel _ ev effs =>
    "kernel " ++ kernelLabel ev ++
      (if effs.isEmpty then "" else ", emits " ++ ", ".intercalate (effs.map effectLabel))
  | .delivery .. => "delivery"
  | .watchtower .. => "watchtower"
  | .vaultServe .. => "vaultServe"
  | .vaultRepair .. => "vaultRepair"
  | .vaultAttempt .. => "vaultAttempt"
  | .alerts .. => "alerts"
  | .package .. => "package"
  | .vaultRepairFailed .. => "vaultRepairFailed"

/-- One entry's frame, the comment on its first line. -/
def entryLines (k : Nat) (e : Trace.Entry) : List String :=
  match chunks (Encode.var (Trace.encEntry e)) with
  | [] => []
  | c :: cs => commented (hexOf c) s!"entry {k}: {entryLabel e}" :: cs.map hexOf

/-- The digest of the published bytes, computed once outside Lean and held here as an opaque
literal: `check_vectors.py` recomputes it from the preimage the regions gate holds to
`Trace.framed_flatten`. -/
def traceDigest : String := "044512aa477ac903226ee0c1fc346101d8d95f20dbd7c1e24238c037c8b79fe1"

/-- The `sha256 =` block: the frame of `Trace.published` line by line, entry by entry. -/
@[req "ADR-0023"]
def traceVector : Region :=
  let fr := Trace.framed Trace.published
  let n := Trace.published.entries.length
  { decl := "BtcPolicy.Render.traceVector", kind := "render", home := "ADR-0023",
    text := "\n".intercalate
      ([ "```vector", "preimage =",
         commented (hexOf (fr.headD [])) s!"version {Trace.version}, {n} entries" ] ++
       ((List.range n).zip Trace.published.entries).flatMap (fun (k, e) => entryLines (k + 1) e) ++
       [ s!"sha256 = {traceDigest}", "```" ]) }

/-- Every region a document may carry. A region emitted and rendered nowhere is a red gate. -/
def regions : List Region := [spn38Table, adr0014Timeline, spn5Gates, traceVector]

/-! ## Emitted values

Every `decl` is a tagged declaration — `tools/check_copies.py` refuses one the requirement index
does not carry, as the regions gate does — and `part` names a field of it where the value is one
field of a structure. -/

def shapesText : String :=
  ", ".intercalate (Shapes.shapes.map fun (t, n) => s!"{t}-of-{n}")

def v (decl req value : String) (part : String := "") : Value :=
  { decl := decl, req := req, value := value, part := part }

def values : List Value :=
  [ v "BtcPolicy.Timelock.defaultNSequence" "CHN-4" (toString Timelock.defaultNSequence),
    v "BtcPolicy.Timelock.defaultUnits" "CHN-4" (toString Timelock.defaultUnits),
    v "BtcPolicy.Timelock.secondsPerUnit" "CHN-4" (toString Timelock.secondsPerUnit),
    v "BtcPolicy.Timelock.typeFlagBit" "CHN-4" (toString Timelock.typeFlagBit),
    v "BtcPolicy.Timelock.defaultDays" "CHN-4" (toString Timelock.defaultDays),
    v "BtcPolicy.Shapes.minT" "CHN-2" (toString Shapes.minT),
    v "BtcPolicy.Shapes.coefficient" "CHN-2" (toString Shapes.coefficient),
    v "BtcPolicy.Shapes.offset" "CHN-2" (toString Shapes.offset),
    v "BtcPolicy.Shapes.maxT" "CHN-2" (toString Shapes.maxT),
    v "BtcPolicy.Shapes.maxN" "CHN-2" (toString Shapes.maxN),
    v "BtcPolicy.Shapes.nodeLimit" "CHN-2" (toString Shapes.nodeLimit),
    v "BtcPolicy.Shapes.shapes" "CHN-2" shapesText,
    v "BtcPolicy.Budget.upperMultiple" "POL-20" (toString Budget.upperMultiple),
    v "BtcPolicy.Budget.c0Numerator" "POL-20" (toString Budget.c0Numerator),
    v "BtcPolicy.Budget.c0Formula" "POL-20" Budget.c0Formula,
    v "BtcPolicy.Budget.coefFormula" "POL-20" Budget.coefFormula,
    v "BtcPolicy.Budget.fullToleranceFormula" "POL-20" Budget.fullToleranceFormula,
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.t) "t",
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.n) "n",
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.window) "window",
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.hold) "hold",
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.slack) "slack",
    v "BtcPolicy.Budget.params" "POL-20" (toString Budget.params.horizon) "horizon",
    v "BtcPolicy.Budget.intervalStart" "POL-20" (toString Budget.intervalStart),
    v "BtcPolicy.Budget.intervalEnd" "POL-20" (toString Budget.intervalEnd),
    v "BtcPolicy.Budget.statedLength" "POL-20" (toString Budget.statedLength),
    v "BtcPolicy.Budget.statedTotalV" "POL-20" (toString Budget.statedTotalV),
    v "BtcPolicy.Budget.withdrawnNumerator" "POL-20" (toString Budget.withdrawnNumerator),
    v "BtcPolicy.Budget.withdrawnDenominator" "POL-20" (toString Budget.withdrawnDenominator),
    v "BtcPolicy.BumpTarget.anchorStep" "DUR-30" (toString BumpTarget.anchorStep),
    v "BtcPolicy.BumpTarget.quantum" "DUR-30" (toString BumpTarget.quantum),
    v "BtcPolicy.Freshness.past" "NCH-12" (toString Freshness.past),
    v "BtcPolicy.Freshness.future" "NCH-12" (toString Freshness.future),
    v "BtcPolicy.Freshness.pruneOffset" "NCH-13" (toString Freshness.pruneOffset),
    v "BtcPolicy.Preimage.width" "MAN-16" (toString Preimage.width),
    v "BtcPolicy.Preimage.publishedEntropy" "MAN-16" (toString Preimage.publishedEntropy),
    v "BtcPolicy.Preimage.publishedHex" "MAN-16" (toString Preimage.publishedHex),
    v "BtcPolicy.Preimage.publishedBytes" "MAN-16" (toString Preimage.publishedBytes),
    v "BtcPolicy.Coverage.floorPct" "MAN-9" (toString Coverage.floorPct),
    v "BtcPolicy.Coverage.ceilingPct" "MAN-9" (toString Coverage.ceilingPct),
    v "BtcPolicy.Cursor.reserve" "SPN-38" (toString Cursor.reserve),
    v "BtcPolicy.Cursor.minimum" "SPN-38" (toString Cursor.minimum),
    v "BtcPolicy.Cursor.affordableFormula" "SPN-38" Cursor.affordableFormula,
    v "BtcPolicy.Cursor.saturatingFormula" "SPN-38" Cursor.saturatingFormula,
    v "BtcPolicy.Cursor.zeroRule" "SPN-38" Cursor.zeroRule,
    v "BtcPolicy.Cursor.startFormula" "SPN-38" Cursor.startFormula,
    v "BtcPolicy.Cursor.capFormula" "SPN-38" Cursor.capFormula,
    v "BtcPolicy.Cursor.anchorSentence" "SPN-38" Cursor.anchorSentence,
    v "BtcPolicy.VaultUnspent.deltaWindow" "WTC-6" (toString VaultUnspent.deltaWindow),
    v "BtcPolicy.VaultUnspent.settledDepth" "WTC-7" (toString VaultUnspent.settledDepth) ]

end BtcPolicy.Render
