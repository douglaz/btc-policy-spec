# The formal layer models a claim over every execution, about this set's own rules

Status: accepted 2026-10-05. Specification-repository decision by the specification owner. It
sets which claims earn a Lean model. `ADR-0023` keeps how a formalized clause lives in Lean once
it has one.

A formal model costs a module, its gates and its upkeep on every amendment. It pays where reading
cannot check a claim and a test can only sample it. It pays nothing where the model only restates
a definition, or where the truth lives in software this set does not specify.

## Decision

A claim gets a Lean model when all four hold.

1. **It ranges over executions.** It is stated over every interleaving, reorg, clock correction,
   node or arithmetic input the set admits, not over one example.
2. **Its failure costs something.** Breaking it costs funds, recovery or a guarantee the set
   states, not wording.
3. **It is about this set's own rules.** Where Bitcoin Core or cryptography is the authority
   (script execution, BIP143 message bytes, descriptor parsing, hash and signature security), a
   Lean model proves only a model of that authority. There the evidence is protocol vectors and
   regtest runs, and the formal layer carries the authority's behaviour as a named assumption.
4. **It has a control that fails.** Either a guard parameter whose withdrawn value goes red in
   `Exhibits.lean`, or a planted mutation that CI applies and asserts is refused. A recorded
   defect is one source of such a control, not a precondition for the model.

## Consequences

A claim that fails any of 1–3 stays in prose, the vectors or the conformance checklist. A
boundary the formal layer already names (per-input possession, the federation, the decoded PSBT)
is a candidate under this test. Each one enters through a bead that names its control.
