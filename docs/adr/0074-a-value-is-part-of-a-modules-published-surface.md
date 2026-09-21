# ADR-0074: A value is part of a module's published surface

Status: Accepted. Refines ADR-0005.

## Context

ADR-0072 gave a value a name. It stayed module-local, which left the second half of issue #163 open: an example row could name the record it was stated against, but only from the module that wrote the record out. So the module that reads the rule still restated the record — and naming a record means naming every type inside it. `activity.sou` imported twenty-four names, ten of which existed for one fixture, and its import list said nothing true about what the module does.

`exposing` refused a `let` on the ground that a helper is not a specification statement (ADR-0005). That is right about a helper and wrong about a value. A limit a rule is written against, and the representative record its examples are stated with, are part of what a module offers.

## Decision

**`exposing` may name a value** — a `let` with no parameter list that implements no behavior. A helper is not a value: it takes arguments, and a function does not cross into another module as a value (ADR-0004 closes the same door at the boundary). Publishing a helper is a separate decision (ADR-0075), and what it means for a value is not changed by it. Neither is the `let` that satisfies a behavior taking nothing: what a reader reaches is the behavior, which it calls, and the module publishes its specification rather than the body it was given (ADR-0005). The line follows the definition's own shape, which is the line ADR-0072 already draws between the two.

**A value has one executable home, the module that declares it.** Inside that module a reference to it is a call to its own method. From another module a reference to it is a call to a public entry the declaring module publishes for it: a class `$Values` with one static method per published value, taking nothing and answering with the value. Neither reference copies the body or moves it. A value that names two values that each name two more would otherwise be a tree that doubles with every link, and a chain published across a module boundary would reach the limit of a method that the same chain in one module does not.

The entry is a definition of the declaring module like a row's operand: its body is a reference to the value and nothing else, so the region that reads the reference decides what the value needs and builds each of those once. No second account of a value's dependencies is kept for it. Constants have an entry as well, since the reader does not know which values fold and which do not.

**A reader is typed by the answer the declaring module settled.** What a call to an entry answers with is what the value's own check came to, and it is read from one place whether the declaring module is compiled in the same run or is a jar: from that module's check in the first case and from what it recorded in its metadata in the second. The body a jar also carries is for the analyses, which read a value by its template, and is not what the reader's executable representation rests on. What the value builds is built where it is declared, and a behavior that names it does not originate it; whatever the value builds is still what ADR-0059 lets that behavior's `constructs` name.

**A published value's names are resolved where it was written** (ADR-0067), and what crosses is *closed* over names and not over bodies: every helper in it is expanded, and every value it names stays a reference under the name of the module that declares it, carried along with it. A reader that spells one of those names the same way reaches its own definition and not the published one, so `pricing.standard = Amount(base)` read in a module with its own `base` still answers the published number. The values a published one names are not offered to the importer: they can be written by nobody but the definitions that carry them. Sharing a private value between exports is given up, in exchange for a type the module keeps to itself never being named from outside it.

**A published value may reach a recursive helper.** The value runs where it is declared, so the helper it calls is the declaring module's own method and is never the reader's to emit. Nothing of the helper crosses on the value's behalf, which is why there is nothing to refuse: a recursive helper is lowered to a method (ADR-0038) and stays one, in the module that wrote it.

**Only what the module exposes is called from outside.** The public methods of `$Values` are the values the module lists in `exposing`, and the answers it records are for those and nothing else. A module that lists nothing is public to Java and offers no name for another Souther module to import, so it has no entry for a value either. A private value that a published helper names is not offered: the helper is expanded into its reader with what it names, as ADR-0075 has it, and the value comes along as a copy in that expansion. Running a helper where it is declared, so that nothing it names is copied, is the same idea applied to helpers and is a decision of its own.

**A published value may not build a type its module keeps to itself.** The exposed-surface rule of issue #187, applied to what a value *is*. It is read from the value closed rather than from the shape it was written as: `let published = privateValue` builds whatever `privateValue` builds, and a helper call builds whatever the helper does. What its body reached for on the way is not asked — requiring that would put every inner type back in the reader's import list.

## Consequences

Issue #163 closes. Moving the CRM's `NegotiationReview` fixture to the module that declares the type takes `activity.sou` from twenty-four imported names to fifteen, and the ten the issue names — `OpportunityName`, `Needs`, `PainPoint`, `BusinessCase`, `DecisionCriterion`, `DecisionMakers`, `PerceivedRisk`, `QuoteNumber`, `Amount`, `CurrencyCode` — are gone. The file loses forty-four lines with it.

What a jar carries grows by what the declarations need, not by the module's implementation. It already published the helpers an invariant calls, for the same reason: a declaration that cannot be read without a body carries that body. A published value and the definitions it reaches join them; a `let` neither reaches is still not carried. It also carries what each value was settled as, and the boundary revision moved with it: a jar written before has no entry to call and no answer to type the call with.

A jar's classes for a value are public where they have to be and no wider. Only the entry is public; the class its body lives on stays package-private, so the module's own types that are not exposed are reached only by code of the module. This is what makes a value built of such a type readable from another module at all — copied into the reader, its body would name a class the reader may not touch.

ADR-0005's sentence about `exposing` is refined rather than dropped. A helper stays out of the behavior list and out of the published surface, so the list of behaviors still does not diverge from the spec DSL's. What changes is that `exposing` is no longer only that list: it is what the module offers, and a value is part of it.

Publishing a *helper* is ADR-0075's decision and is not changed here. A helper still travels as a body its reader expands, so a type its body names that its module keeps to itself is named in the reader; that is the one place a body still crosses, and it is not resolved by this decision.

## References

- Specification: `[#exposed-values]`, `[#exposed-surface]`, `[#published-modules]`
- Issue #163 (a fixture cannot be named), issue #187 (an exposed surface may not rest on what is kept)
- ADR-0072 (a `let` with no parameter list is a value), ADR-0005 (a helper is not a behavior), ADR-0067 (a name is resolved once), ADR-0059 (construction is closed to declared paths, not to the declaring module), ADR-0004 (derived codecs — why a function has no representation)
