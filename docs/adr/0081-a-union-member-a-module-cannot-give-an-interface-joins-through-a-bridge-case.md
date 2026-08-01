# ADR-0081: A union member a module cannot give an interface to joins through a bridge case

Status: Accepted (decided 2026-08-01). Amends ADR-0057, which left this available.

## Context

The commonest shape a model asks a behavior for is "the amount, or the reason there is none". The value it answers with is usually a primitive or a type another bounded context owns — money, a deadline, a count. Neither could be a member of a behavior's output union, so every such behavior declared a type whose only job was to hold the value.

Two sites in the `hr` example, one of each kind. `payroll.computeTaxableAmount` wanted `-> Yen | DeductionsExceedGross` and declared `data TaxableAmount = Yen`; the wrapper then travelled downstream into `withholdingTaxOf : (taxable: TaxableAmount, …)`, and the behavior had to be renamed as well, since a behavior capitalises into a class of the same name as its own wrapper. `filing.deadlineFor` wanted `-> Date | NoStatutoryDeadline` and declared `data FilingDeadline = Date`. Neither wrapper is a concept anybody in the domain has a word for.

Two rules were refusing them, and they turn out to be one. `successType` required every member to be a data type, which stopped the primitive. Behind it, the generated result union stopped the imported type (E1606, ADR-0057). The reason is the same in both: a case class receives the unions it belongs to when *its own* module is generated, and neither `java.lang.Long` nor a class an imported module already emitted can be given an interface from here.

ADR-0057 recorded that reason and listed **wrapper cases** among the alternatives, rejected "for now" because within one `switch` a local case would arrive as the value itself and an imported one wrapped. It closed with: *it stays available if cross-context unions turn out to be worth that*. This is that measurement.

## Decision

**A union member a module cannot give its interface to joins the union through a bridge case the module emits.** Three rules settle every shape.

**A member is nominal, tells itself apart at run time, and has a `match` arm form.** The primitives and named data types meet all three, a data whether the module declares it or imports it. A collection meets none of them: its type argument is erased, so `List<Order>` and `List<Item>` are one runtime type and no arm could choose between them; that there is also no arm form to write is the surface showing the same fact. `Option` and function types are outside for the same reason.

**Each effective member goes by a name of its own.** Effective members are the written members with each named sum expanded to its leaves, since a leaf is what an arm names and what the `"type"` discriminator carries. Two types written the same cannot be members of one union — the check is on the expanded set, so a leaf of an imported sum clashing with a local type is caught as directly as `up.Yen | other.Yen`.

**A member the module declares implements the union itself; any other reaches it through a bridge case.** A bridge case is `<MemberName>Case`, a record of one component `value`, one per member per module, implementing every result union of that module the member belongs to.

Bridge cases introduce no new module-wide membership dependency. Souther already generates each local case class against all the behavior result interfaces it belongs to; a bridge case follows the same module-local generation rule for a value whose class it does not own. What differs is not what membership means but which module owns a class it can be put on.

| Member | Where its result-union membership sits |
| --- | --- |
| a data this module declares | the case class itself |
| a primitive, or an imported data | a bridge case this module emits |

Belonging to a union does not change a member's external representation. A bridge case therefore has no codec of its own: a consumer switches to it, takes the value out, and uses the codec the member already carries.

The bridge case is a JVM form and nothing else. It is not a Souther type, it is not written in a `match` arm or an `example` row, and it does not appear in an external representation.

### The two boundaries

Inside a body every value is a Souther value. The union's JVM form exists across `apply` and nowhere else, and the two meet at exactly two places.

- **Inject** — a behavior returns, and the Souther value it answers with becomes a member of its declared union.
- **Project** — a caller receives that member and reads the Souther value back out.

`project(inject(v))` is `v`. Both walk the union's members, which are known where they are emitted, so neither asks a value whether it happens to be wrapped, and `inject` is never applied to a bridge case — the property is one the IR has rather than one each dispatch site has to maintain.

Projection is done at the call and not at the `match` arm that reads the result. Not every result is matched: a body may answer with a call's result directly, and the callee module's bridge cases are not members of this module's union. Projected at the call, the value is a Souther value again and this behavior's own return puts it into its own bridge case.

### A declared sum still refuses an imported case

E1606 stays for `data S = A | B` with an imported case, and its reason moves from the JVM to the model. A named sum introduces a type name: it is written in a parameter, in a field, in another sum. An anonymous output union introduces none — it is the shape of one behavior's answer and nobody names it. Answering with a value another context owns is not the same act as making that type a word of this module's vocabulary.

## Alternatives considered

**A non-sealed generated interface, or returning `Object`.** The behaviour Souther promises Java is that one value arrives and an exhaustive `switch` reads it. Giving that up in the commonest output shape a model has is the wrong direction.

**Wrapping every member of a mixed union.** This removes the asymmetry ADR-0057 named — within such a `switch` every case would arrive wrapped. Rejected: adding one imported member to an existing all-local union would then change how its local cases are received, so a Java consumer breaks on a change to a case it does not use. That is worse than the asymmetry it removes.

**Whole-program membership** (ADR-0057). Still rejected, and this decision does not need it. A bridge case is the consumer's own class, so the imported module is not regenerated and resolving an import from a published jar stays available — the property that rejected whole-program membership does not arise here.

## Consequences

- E1606 narrows to a declared sum's cases, and its message states the model reason rather than the generation-order one.
- The union-returning core functions (`Int.divide`, `String.toInt`, …) can now be written as core declarations; ADR-0053's "deferred, needs a language-rule change" no longer holds. Moving them is a separate change.
- A Java consumer of a behavior answering with an imported type or a primitive writes one more pattern layer for that case (`case YenCase(var y)`). Which members are the module's own is visible in the `switch`, which is the module boundary showing up where ADR-0057 said translation shows it.
- Two members written the same in one union is newly refusable, because such a union is newly writable.

## References
- Specification: `[#union-member]`, `[#unmarked-output]`, `[#primitive-arm]`, `[#jvm-anonymous-union]`, `[#bridge-case]`, `[#e1606]`
- ADR-0057 (a behavior's output union is built from its own module's cases — amended here)
- ADR-0024 (an exposed composition declares its output; a module's bytecode is a function of its own source)
- ADR-0008, ADR-0049 (the generated `<BehaviorName>Result`)
- ADR-0053 (the compiler-integrated stdlib set, one entry of which this releases)
- Issue #242, and finding F33 of souther-lang/souther-examples
