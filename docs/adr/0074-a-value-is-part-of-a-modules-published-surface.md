# ADR-0074: A value is part of a module's published surface

Status: Accepted. Refines ADR-0005.

## Context

ADR-0072 gave a value a name. It stayed module-local, which left the second half of issue #163 open: an example row could name the record it was stated against, but only from the module that wrote the record out. So the module that reads the rule still restated the record — and naming a record means naming every type inside it. `activity.sou` imported twenty-four names, ten of which existed for one fixture, and its import list said nothing true about what the module does.

`exposing` refused a `let` on the ground that a helper is not a specification statement (ADR-0005). That is right about a helper and wrong about a value. A limit a rule is written against, and the representative record its examples are stated with, are part of what a module offers.

## Decision

**`exposing` may name a value** — a `let` with no parameter list. A helper is still not published: it takes arguments, and a function does not cross into another module as a value (ADR-0004 closes the same door at the boundary). The line follows the definition's own shape, which is the line ADR-0072 already draws between the two.

**A published value is substituted where it is named**, in the reading module as in the declaring one. So publishing one adds no class, no field and no method: what travels is the declaration, which is what a jar already carries for a data's invariant. What the value builds is built by the behavior that names it and belongs in that behavior's `constructs` — for another module's type, what ADR-0059 already allows.

**A published value's names are resolved where it was written** (ADR-0067). The reading module need not import the types the value's body mentions, which is the whole point: an importer names the value, not what it is made of.

**A published value may not build a type its module keeps to itself.** The exposed-surface rule of issue #187, applied to what a value *is*. What its body reached for on the way is not asked — requiring that would put every inner type back in the reader's import list.

## Consequences

Issue #163 closes. Moving the CRM's `NegotiationReview` fixture to the module that declares the type takes `activity.sou` from twenty-four imported names to fifteen, and the ten the issue names — `OpportunityName`, `Needs`, `PainPoint`, `BusinessCase`, `DecisionCriterion`, `DecisionMakers`, `PerceivedRisk`, `QuoteNumber`, `Amount`, `CurrencyCode` — are gone. The file loses forty-four lines with it.

What a jar carries grows by what the declarations need, not by the module's implementation. It already published the helpers an invariant calls, for the same reason: a declaration that cannot be read without a body carries that body. A published value and the definitions it reaches join them; a `let` neither reaches is still not carried.

ADR-0005's sentence about `exposing` is refined rather than dropped. A helper stays out of the behavior list and out of the published surface, so the list of behaviors still does not diverge from the spec DSL's. What changes is that `exposing` is no longer only that list: it is what the module offers, and a value is part of it.

Publishing a *helper* is a separate question and is not decided here. It would put an executable body under a compatibility contract, need cross-module expansion and a form for a recursive helper, and let a reader compose calculation without going through a behavior — none of which a value raises.

## References

- Specification: `[#exposed-values]`, `[#exposed-surface]`, `[#published-modules]`
- Issue #163 (a fixture cannot be named), issue #187 (an exposed surface may not rest on what is kept)
- ADR-0072 (a `let` with no parameter list is a value), ADR-0005 (a helper is not a behavior), ADR-0067 (a name is resolved once), ADR-0059 (construction is closed to declared paths, not to the declaring module), ADR-0004 (derived codecs — why a function has no representation)
