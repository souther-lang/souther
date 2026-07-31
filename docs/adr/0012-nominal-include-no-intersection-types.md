# ADR-0012: Field composition is nominal `include`; no structural intersection types

Status: Accepted. Surface syntax superseded by ADR-0030 — the `include X` keyword became a
`...X` spread. The semantics below (nominal, flattened fields, inherited invariants, no
intersection types) are unchanged.

## Context

The spec DSL writes shared fields as `data Submitted = TravelRequestCommon AND submittedAt` — "has all of TravelRequestCommon's fields, and adds submittedAt." A structural reading of `AND` would suggest an intersection type (`A & B`, "a value that is both A and B"), but that reading does not fit a language built on nominal closed construction.

## Decision

Field composition is `include`: it flattens another data's fields, inherits its invariants, and is **not** inheritance (no subtype relation, no assignment compatibility — the two only share fields). Souther has union types but deliberately has **no** structural intersection types (`A & B`).

## Consequences

`include` gives exactly what the DSL's `AND` means: flatten the fields (`x.applicant`, not `x.common.applicant`), carry the included invariants into the composed data's construction, and error on a field-name collision. It is not a subtype, so `Submitted` is not assignable where `TravelRequestCommon` is expected. When you want to keep the shared fields as one nested value instead, use an ordinary field (`common: TravelRequestCommon`).

Admitting `A & B` as a type would break the foundation: it leaves undetermined who constructs the value and which invariants are checked, defeating closed construction (ADR-0002) and the invariant guarantee (ADR-0003). The DSL's `AND` is nominal field composition, not structural intersection, and `include` expresses it with nothing left over. Leaving intersection types out is a design choice to keep construction paths closed, not a missing feature.

## References

- Specification: `[#field-spread]`, `[#union-intersection]`
- ADR-0002 (closed construction paths), ADR-0003 (invariant violations abort in the domain)
