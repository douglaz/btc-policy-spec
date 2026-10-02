import Lean
/-! `@[req "POL-20"]` — the one link between a Lean declaration and the requirement it formalizes
(`ADR-0023`). The gate enumerates tagged declarations to enforce the axiom policy and to emit the
requirement index the documents are checked against. There is no other manifest. -/

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
