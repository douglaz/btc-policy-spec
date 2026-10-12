import Lean
/-! `@[req "POL-20"]` — the one link between a Lean declaration and the requirement it formalizes
(`ADR-0023`). The gate reads the tags to emit the requirement index, against which the identifier,
copies and regions gates check the documents. There is no other manifest: the declaration list the
citation gate reads carries no identifier. -/

open Lean

namespace BtcPolicy

syntax (name := req) "req " str : attr

/-- The requirement identifier a declaration formalizes. One declaration, one identifier. -/
initialize reqAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `req
    descr := "the requirement identifier (e.g. \"POL-20\") this declaration formalizes"
    getParam := fun _ stx =>
      match stx with
      | `(attr| req $s:str) => pure s.getString
      | _ => throwError "expected @[req \"XXX-n\"]"
  }

end BtcPolicy
