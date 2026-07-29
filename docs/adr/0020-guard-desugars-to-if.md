# ADR-0020: `guard ... else` is sugar for `if`

Status: Accepted (the keyword is `guard` since ADR-0071; it was `require` when this was decided)

## Context

`guard <cond> else <value>` returns an early value from a behavior's implementation when a precondition fails. It could be a distinct statement form, or sugar over an existing expression. The choice affects how many places in the pipeline construct values.

## Decision

`guard <cond> else <value>` is sugar for `if <cond> then <rest-of-body> else <value>`. Desugaring happens at parse time, so every later stage (type check, construction-permission check, backend) sees only `if`.

## Consequences

Defining `guard` as sugar keeps value construction in one syntactic family — expressions. If `guard` were a separate statement, whatever checks construction permission (ADR-0002) and invariant checking would have to walk that position separately from expressions; forgetting to walk it would let a permission-unchecked, invariant-breaking value be built. Desugaring makes that accident syntactically impossible.

This relies on branches being allowed to differ in type: `if <cond> then <rest> else <value>` puts the early value and the rest of the body in the two branches, which is why `if` permits its branches to have different (data) types.

## References

- Specification: `[#if]`, `[#guard]`
- ADR-0071 (the keyword is `guard`)
