# ADR-0080: An invariant clause may be named, and what fails is one clause

Status: Accepted (decided 2026-07-30). Takes up what ADR-0070 left open — "an invariant with several
clauses is all-or-nothing" — and closes issue #209.

## Context

An invariant is one boolean expression, and its clauses have no identity. Two things follow from that,
one inside the domain and one at the boundary.

Inside, an attempted construction (ADR-0070) runs the whole invariant and takes one `else` value. Where
a type carries rules that depart differently, the attempt cannot be used and the rules are written a
second time as guards. `crm`'s `QuoteLines` says a quote has at least one line and no product twice;
`buildQuote` answers `NoLines` for the first and `DuplicateProduct` for the second, so it restates both.
Measured across the seven models of souther-examples: 20 multi-clause invariants, 18 of them ranges
(`value >= a && value <= b`) — one rule with one meaningful failure — and of the two that are genuinely
separate rules, one is reached only through a decoder. `QuoteLines` is the one site in the domain.

At the boundary the same absence costs more, and it costs it everywhere. Issue #83 mapped the clauses a
Raoh constraint states exactly onto that constraint, so a violation carries `too_short` with `min`
rather than one `invariant_violation` for every rule in the model. What it could not map fell into a
single `refine` over the whole invariant, reporting `invariant_violation` with the rejecting type and
nothing about which of its rules broke. A product data was outside the mapping altogether — its
invariant has no single value to constrain — and its failure was built with the three-argument
`Result.fail`, so it carried **no metadata at all**: a `MessageResolver` keyed on the shared code could
not tell which type had rejected the value, let alone which rule.

Both are the same missing thing. In most systems the rule is already a separate declaration and has an
identity for free: Clojure `spec` reports the chain of named specs in `explain-data`'s `:via`, Zod
carries a `code` per issue, Bean Validation answers with the constraint annotation's own type. Souther's
invariant is one expression, so the identity was never there. Eiffel is the closest prior art for the
form — an assertion clause is tagged (`invariant non_empty: count > 0`) and the violation report names
the tag — though Eiffel's tags only report and never select a branch. Ada is on the other side: a
subtype has one predicate, one `Predicate_Failure`, and no classification.

## Decision

**A clause may be named, and a failure is one clause.**

```
data QuoteLines = List<QuoteLine>
    invariant nonEmpty = List.length(value) >= 1
    invariant uniqueProducts = List.allUniqueBy(.product, value)

guard QuoteLines(List.map(r -> toLine(r), lines)) as ls else
    | nonEmpty       -> NoLines
    | uniqueProducts -> DuplicateProduct
```

The name is spelled with `=`, as everything else defined as something is (ADR-0026): the clause's
content is an expression, not a type. `invariant <expr>` keeps its meaning exactly, so no existing
source changes; an unnamed clause aborts inside the domain and fails the decode outside it without
saying which rule it was, and no arm can name it. Naming a clause is what makes it recoverable — there
is no second modifier.

Clauses are checked in the order they are declared, and the first that does not hold is the one the
failure names. That makes declaration order observable, the same way a sequence of guards and the arms
of a `match` already are: an empty list reports `nonEmpty` rather than `minimumTotal` because the author
put the more informative rule first. Reordering the clauses of a published type is therefore a breaking
change, and where several clauses fail only the first is reported.

The arms are total over what can fail. Every named clause has an arm; `| _ -> …` is written when the
type has a clause carrying no name, and only then. That is why `_` cannot be a clause's name: the arm
reading it would be that wildcard, so the clause could never be answered by name — refused where the
clause is declared rather than left to be met at an attempt.

Mixing named and unnamed clauses stays legal at the declaration — forbidding it would split a type that
has an internal-consistency rule beside classifiable ones for no modelling reason — and the constraint
sits at the attempt instead. The cost is that adding an unnamed clause to an all-named type breaks the
mapping sites: acceptable, because adding a clause to a published type is already a change to what the
type accepts, and today it is silent, showing up only as more aborts and more decode failures.

## What the failure carries, and where

`__construct`'s failure side becomes `souther.runtime.InvariantFailure` — the rejecting type, as its
declaring module and its name, and the clause, which is null where it was declared without one. The
module is carried apart from the name because a type is its module and its name — module is package
(ADR-0058) — so two modules may each declare an `Id` and metadata keyed on the name alone would answer
for either. #83's `{type}` was the simple name, which held only until such a pair existed. Three
destinations read it and they now agree:

- an attempted construction departs by the arm answering that clause;
- a derived decoder reports it as `invariant_violation` with `{module, type, clause}` in the metadata,
  which is where a product data's failure gains metadata it never had;
- an abort names it in the message, and so does the compile-time check of a constant construction.

This does not walk back ADR-0070's decision that the failure carries nothing. What crosses is the
identifier of a rule the type declares, not a value: the arms are a lookup on which clause failed, the
name a business failure gets is still the one written in the arm, and nothing of the failure is in scope
there.

A clause's name is never an issue's `code`. The code stays Raoh's — the shared `invariant_violation`, or
the constraint's own where the clause maps onto one — so a `MessageResolver` written against Raoh's
vocabulary keeps working and the name is metadata it may switch on. A clause that maps onto a Raoh
constraint therefore does not carry its name at the boundary: the constraint's metadata is Raoh's to
build, and `too_small` with `{min, actual}` is worth more to a client than the author's identifier.

## Raoh's constraints, and the order they can be chained in

The clause set is the natural unit for the constraint mapping too, so the mapping was extended to the
collections Raoh already states: `List.length(value)` bounds become `nonempty` / `minSize` / `maxSize` /
`fixedSize`, `List.allUniqueBy(x -> x, value)` becomes `unique`, and `Map.size(value)` bounds become the
record decoder's. A `Set` is not among them: Souther decodes one as a list and drops the duplicates while
mapping it, so a constraint before that mapping would count the duplicates and after it there is no
typed decoder left to chain onto. A uniqueness under a projection other than the identity is not among
them either — Raoh has no `uniqueBy` — and that is exactly the clause `QuoteLines` needs a name for.

Recognition reads the DISCHARGE representation of the invariant, not the one the backend emits from.
`List.allUniqueBy` is a self-hosted prelude helper, so by emission it has become the fold it is derived
from; #83 never met this because `String.length` is a builtin and `String.matches` an intrinsic, and
neither is expanded. This is the same distinction ADR-0067's expansion policy draws, applied to a second
reader.

Raoh chains a constraint with `flatMap` and `refine` answers the plain `Decoder`, so a typed constraint
cannot follow a refine in the chain. That decides an order question the other way from #83: mapped
clauses can no longer all be hoisted in front of the refines, because a value breaking an earlier
unmapped clause and a later mapped one would then be reported as the later one, and the boundary and an
attempted construction would name different rules for the same value. So the chain follows declaration
order, and a mapped clause declared after an unmapped one gives up its Raoh code to keep its place in
the order. Within one clause the conjuncts still map individually — they are one rule, and one rule is
what an arm and an issue name, so which conjunct reported it is not a question anyone asks.

## Consequences

The restatement `crm`'s `buildQuote` carried is gone, and with it the drift it could hide: the
discharge check verifies the length restatement (it knows `List.length(List.map(f, xs))` is
`List.length(xs)`) but not the uniqueness one, whose term is the mapped list.

`__construct`'s published generic signature changes from `Result<T, String>` to
`Result<T, InvariantFailure>`. Java reaches a type through its decoder rather than through
`__construct`, so nothing in the documented surface moves; a caller that used the entry directly reads
a typed failure instead of a message.

The boundary error of an existing model can change in two ways, both toward saying more: a product
data's invariant failure gains `{type}` (and `{clause}` once named), and a collection rule that used to
be `invariant_violation` becomes Raoh's own code. A type mixing a mapped clause after an unmapped one
reports the unmapped one where it used to report the mapped one — the declaration order, now.

The LSP's per-clause discharge answer carries the clause's name, so what it shows says both how the
clause discharges and what an attempt departs by.

## References

- Specification: `[#invariant-clause-name]`, `[#invariant-mvp]`, `[#attempt-departures]`,
  `[#decoder-error]`, `[#invariant-discharge-capability]`
- ADR-0070 (a construction may be attempted), ADR-0003 (a violation aborts), ADR-0007 (failure is not a
  language concept), ADR-0026 (`:` types, `=` defines), ADR-0067 (a name is resolved once, and what an
  expansion is a representation of)
- Eiffel assertion tags (ECMA-367) — the same spelling, for reporting only
- Clojure `spec` (`explain-data`'s `:via`), Zod issue codes, Bean Validation constraint descriptors —
  identity a rule has for free when it is its own declaration
- Ada RM 3.2.4 (`Predicate_Failure`) — one predicate, one failure, no classification
- Issues #209, #83
