# ADR-0070: A construction may be attempted, and what fails is not a value

Status: Accepted (decided 2026-07-29; the keyword is `guard` since ADR-0071, and was `require` here). Answers the in-language half of issue #20, which ADR-0003 left open, and closes issue #162.

## Context

An invariant is checked on every construction path, and inside the domain a violation aborts (ADR-0003). There is no form that answers "it did not hold", so the only way to keep an out-of-range value off a constructor is to check the same rule again first:

```
let domainOf (email: EmailAddress): List<DomainName> =
    match List.get(1, String.split("@", String.lowercase(email.value))) with
        | Some d ->
            if String.matches(domainPattern(), d)     // DomainName's own invariant, restated
            then [ DomainName(d) ]
            else []
        | None -> []
```

The invariant that makes the type worth having is the invariant the caller duplicates to stay off the aborting path. The `crm` example names the pattern with a helper `let` so the two readings are at least one rule; that is a convention, not a check, and the discharge procedure cannot verify it either — `String.matches` is outside the checked fragment, so a drifted restatement is silent.

Across a module boundary the guard cannot be written at all. A helper `let` an invariant names is not exposable — `exposing` names specification statements, and a helper is not one — and promoting it to a behavior puts it out of the invariant's reach, because an invariant calls a `let` and never a behavior. Both exits were measured on `develop`; they cancel. An importing module is left copying the invariant's literal into a module that cannot see it, or accepting the abort.

## Decision

**A construction may be attempted, and its invariant decides a branch.**

```
if T(v) as x then <expr> else <expr>
guard T(v) as x else <case>
```

The invariant runs — `T`'s own and every invariant a `...` spread brought in. Holding, the value is built and `x` names it in the success branch; failing, the else branch is taken and no value is built. `guard` stays sugar for `if` (ADR-0020), so the base form is the `if` and a helper `let` with no departure case reaches it too.

The binder is scoped to the success branch alone. Nothing carries the failure: there is no `Option`, no `Result`, no reason value. The name a business failure gets is the one the writer puts in `else`, and a writer may put none there (`else []`).

An attempt requires `constructs T` like any other construction — it mints a value on its success branch, and that is exactly what `constructs` is for reading (ADR-0002). A type with no invariant may not be attempted: the else branch could not be reached, so it is a compile error rather than a branch that is not one.

`T(v)` on its own still aborts. What is added is a form the writer chooses at the site, which is what ADR-0003 already says about turning an unmet rule into a value — "that is a business judgment written explicitly with `guard ... else`". This lets that judgment be written without restating the rule.

## Why the failure carries nothing

The obvious shape, and the one issue #162 proposed, is the decoder's `Result`. Every mainstream language with this construct returns a value: Swift's `init?` answers an Optional, Rust's `TryFrom` a `Result`, F#'s `tryCreate` an option, Elm's `fromString` a `Maybe`, Zod's `safeParse` and pydantic the same shape. Souther is in the minority here, deliberately.

None of those languages decides, as a language rule, where a nameless failure goes. Souther does. ADR-0003 routes an invariant violation to an abort *because* it has no business vocabulary; handing it back as a nameless value would make the absence of a name a licence rather than the reason. ADR-0007 keeps failure from being a language-level concept, and ADR-0011 refuses `Option` in a behavior's output for the same reason — "might not be found" is `-> Member | NoSuchMember`, not `Option<Member>`. A form that produced a value would have to answer to all three.

Ada, the one language in the survey that does decide where a failed constraint goes, is on this side: `X'Valid` yields True when "the predicate of the nominal subtype of X evaluates to True" and is explicitly "not considered to be a read of X; hence, it is not an error to check the validity of invalid data" (RM 13.9.2), and a membership test `X in S` evaluates the subtype's predicate the same way (RM 4.5.2). Clojure's `s/valid?` and Scala refined's `Validate.isValid` sit beside their value-returning siblings for the same reason.

A plain predicate — `holds T(v)` answering a `Bool` — was the first form considered and was dropped. It leaves the test and the construction as two expressions that must agree, which is the duplication this ADR exists to remove, and it makes the compiler tie them back together with a syntactic discharge rule. Binding removes the second mention instead of checking it. `Result`-shaped forms also do not compose with `guard`: `guard` takes a condition, so an attempt answering a value would nest, and a behavior with six guards (`buildQuote` in the `crm` example) would become six nested matches instead of six flat lines. The binding form keeps the flat sequence.

## Consequences

The rule is written once, and where it could not be written at all — across a module boundary — the attempt names the type, which the declaring module does expose, rather than the helper, which it cannot.

A construction inside an attempt is exempt from the possible-violation warning (E2011): what that warning reports is a possible abort, and an attempt takes its else branch instead. It is the only way to silence that warning for an invariant the checked fragment cannot express. A violation the compiler *decides* is still reported — E2010 for the interval fragment, the constant check for the rest — because with the outcome settled at compile time there was never a branch. The success branch seeds the discharge procedure with the built value's invariant, as an input of that type does.

Codegen needed no new generated member. `__construct` already answers a `Result` and `ConstraintViolation.orThrow` is what turns it into an abort; the decoder already branches on the same `Result` to make a Raoh failure. The attempt is a third destination for a value that was there all along, and `__construct` is public for an exposed type, so the cross-module case needs no new visibility.

Nothing changes on the Java surface, and no behavior's output type changes.

An invariant with several clauses is all-or-nothing. Where a writer wants a different departure per clause — `crm`'s `QuoteLines` reports `NoLines` and `DuplicateProduct` separately from one two-clause invariant — the restatement stays. Splitting that is a separate question about whether a type may declare more than one named invariant.

Newtype arithmetic (`a - b` re-wrapping into a newtype) is not a construction expression, so it cannot be attempted; a writer who wants that writes the construction out, `T(a.value - b.value)`.

## References

- Specification: `[#attempted-construction]`, `[#guard]`, `[#if]`, `[#invariant-discharge]`, `[#violation-destination]`
- ADR-0002 (construction permission), ADR-0003 (invariant violations abort), ADR-0007 (business results are an unmarked sum), ADR-0011 (Option is not a surface type), ADR-0020 (`guard` desugars to `if`)
- Ada RM 13.9.2 (`'Valid`), Ada RM 4.5.2 (membership tests) — a predicate asked without the assignment that would raise
- Clojure `spec` (`valid?` / `conform` / `explain`), Scala `refined` (`Validate.isValid`)
- Swift failable initializers, Rust `TryFrom`, F# `tryCreate`, Elm `fromString` — the value-returning majority this diverges from
- Issues #20, #162
