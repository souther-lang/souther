# ADR-0101: A diagnostic says the values it carries

Status: Accepted

## Context

Four diagnostics reported in one week hold a value a reader needs and do not print it. `E2011`
evaluates each named clause of an invariant and reports that "the guards do not establish it",
naming none of the five clauses it just judged. `E2010` does the same, and where the clause came
in through a spread it names neither the clause nor the type that declared it. `E1004` collides a
field against a map it has just filled from two spread groups and reports the collision against
"a field of" the taking data, which in the common case declares no such field. `E2105` cites
`spec 19.5`, a rendered section number that neither `souther doc` nor the MCP server accepts as a
name, and the two sentences that say so exist twice — once in the catalog and once hard-coded in
`Backend.java`, where a fix to one leaves the other behind.

These were filed as four defects. They are one. Nothing in the machinery relates a diagnostic to
the values it is about:

```java
public static Builder of(DiagnosticCode code, String messageKey)
public Builder args(Object... args)
```

`messageKey` is a free string, so a code may be paired with any wording and a wording reached from
any code. `args` is untyped and unbounded, so a site may hand three values to a message that spells
two, or spell a value no site hands it. The catalog and the site agree by review and by nothing
else.

`CompileException.of(diagnostic, legacyBody)` compounds it. Two hundred and nineteen sites pass a
second, hand-written English sentence so that `getMessage()` keeps its old shape. Every one of them
therefore writes its message twice, once as a key with arguments and once as a Java string. `E2105`
is what that costs: the same rule, spelled twice, and the citation wrong in both.

The surface is 148 codes, 538 catalog keys — 220 reached as a message, 89 as a hint, 57 titles —
and 257 sites. `EveryShippedMessageCatalogIsCompleteAndValidTest` already holds the catalog to
twelve properties: the locales define the same keys, they use the same arguments, every message is a
pattern the formatter accepts, every key the compiler names exists, no example message is defined
and never shown. Every one of them is a property of the *text*. None of them can be a property of
the *values*, because at the point the catalog is checked there are no values — only `Object[]`.

Two earlier decisions took this far and stopped. The code carries its own `titleKey`, so a code and
a title cannot disagree between two sites reporting one rule. `RetiredDiagnosticCode` keeps what a
number once meant separate from what a compile can emit, so a number is never reused. Both are the
same move — put the invariant where the type is — applied to the two things a diagnostic names.
What it was never applied to is what a diagnostic *says*.

## Decision

**A diagnostic message is a record whose components are the values it is about, and every component
appears in the text.**

A message is declared as a record in a sealed hierarchy grouped by area, carrying the code it
reports:

```java
/** E1004 */
@Code(DiagnosticCode.E1004)
record SpreadFieldCollision(FieldName field, TypeName from, TypeName heldBy)
        implements DataMessage {}
```

```properties
data.spread-field-collision=Field `{field}` from `...{from}` conflicts with the one `...{heldBy}` supplies.
```

The catalog key is derived from where the record is declared — the area, then the record's name in
kebab — so it is not a string a site chooses, two records cannot name one key, and a record without
a key does not compile. The code is read off the record. A site writes:

```java
Diagnostic.at(inc.name().region()).say(new SpreadFieldCollision(field, from, heldBy))
```

`Diagnostic.of(DiagnosticCode, String)`, `Builder#args(Object...)` and the `legacyBody` parameter
are removed. `getMessage()` renders the same record in English, so a message exists once.

The build holds every message to six rules, over every shipped locale:

1. every message is a record and names the rule it reports;
2. every record's derived key is in the catalog;
3. **every component of a record appears in its own text as `{name}`**;
4. every `{name}` in a text is a component of that record, and a brace holding anything else is
   refused rather than shown;
5. no catalog key is unreferenced by any record;
6. every code has at least one record.

Rule 1 is why the messages are records at all rather than a convention: a leaf of the hierarchy that
is not one carries no components, so every rule under it is silent about it. Rule 4 reads the entry
through the same parser the renderer reads it through — written twice, the two disagree about
`{held_by}` and about a brace nothing closes, which is the drift this whole area exists to remove.

Rule 2 is the new one and the reason for the rest. A value a diagnostic holds is a value a reader
sees, and the alternative — carrying it and not showing it — is not expressible. Rules 1, 3 and part
of 4 restate what the catalog test already checks; they move into it rather than beside it.

Placeholders are named, not numbered. Two messages in the catalog take five arguments and thirteen
take four; at that width `{0}` and `{3}` are a spelling only the site can decode, and a translator
cannot check their work. A named placeholder is also what makes rule 2 legible: the check reads the
component's name in the sentence.

There is no opt-out. A value that should not be shown is not a component: a position is a `Region`,
a value shown only in a hint belongs to the hint's own record, and a value that selects between two
wordings makes two records. The last of these is deliberate — `%select{...}` and its equivalents buy
one catalog entry at the cost of a sentence no reader of the source can read.

Severity moves onto the code, and `Builder#warning()` is deleted. The nine warning codes — E1913,
E1915, E1916, E1918, E1919 through E1922, and E2011 — are each raised once and always as a warning,
so a rule is an error or a warning by its identity and not by the site that raises it.

`--format json` gains a `values` object beside the rendered `message`, keyed by component name. A
tool that wants the clause reads `clause`; before this it would have had to parse English. Each value
is written as the text it renders as, so what a component's Java type is stays a fact about the
compiler rather than part of that interface.

What tells two diagnostics apart carries the message too. The store keeps one report per identity,
and a message holds its values as components rather than in the old array, so an identity that read
only the code, the place and that array answered that two reports of one rule about different values
were one and dropped one of them.

### What was weighed

*Leave it to review, and write the rule down.* This is what Rust's diagnostic guidelines and Elm's
philosophy are, and both produce good messages. It is also what Souther already had — the messages
are well written, and four of them still omitted the value. A rule not held by a mechanism is held
by whoever last read the diff.

*Keep positional arguments and type only their count.* Generic keys — `Msg3<A, B, C>` — give javac
the arity and the types for a tenth of the work. They cannot express rule 2: `{0}` names nothing, so
"the text uses this value" degrades to "the text uses three of something".

*Migrate new diagnostics only.* Cheap, and it leaves #509, #512 and #514 outside the mechanism
along with every diagnostic written before today — which is all of them.

*Generate the records from a declaration file.* One file listing code, key, and argument names
answers the same requirement, and adds a generation step to the build for a hierarchy that is
already written in the language the sites are written in.

## Consequences

Three hundred and ten declarations and 257 sites move at once, and the old constructors go with
them; there is no state in which a site may still write an untyped diagnostic. A migration this
wide is not reviewable as a Java diff, so what is reviewed is the rendered output: every diagnostic
the test corpus emits is captured before the change, in both locales and both formats, and must
come back byte-identical except where the wording was deliberately fixed.

Adding a diagnostic gains a step — declare the record — and loses two: choosing a key and writing
the English sentence twice.

`E2011` and `E2010` gain the clause, `E1004` gains the group that supplied the field, `E2105` loses
its citation. Each is a component the record now requires, which is why they are fixed here rather
than separately.

A message whose wording turns on a value becomes two records and two catalog entries. The catalog
grows; the sentences become readable in the source.

Rule 4 will find catalog keys no record names. Each is either a message that stopped being raised —
delete — or one whose site was never migrated — declare. The count is not known until the rules run.

## References

- `[#compile-errors]` — the rules these diagnostics report
- Issues #509, #512, #514 — three diagnostics that hold a value and do not print it
- GHC's structured `GhcMessage` and its diagnostic codes; Clang's `.td` diagnostic declarations;
  Rust's `#[derive(Diagnostic)]` — three compilers that put the values in the type, and the prior
  art for doing so
