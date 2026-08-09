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
a key does not compile. The code is read off the record the same way. Both derivations are functions
of the message's type and neither is a method on the message: a record component generates an
accessor, so a method would be one a message could answer for itself. A component named `key` did
exactly that, and every reader asking which entry to render was handed the key's value instead. A
component named `reports` would have let a site report whatever code it was passed, past an
annotation saying otherwise. `Message` declares nothing, so there is nothing for a component to
stand in front of. A site writes:

```java
Diagnostic.at(inc.name().region()).say(new SpreadFieldCollision(field, from, heldBy))
```

`Diagnostic.of(DiagnosticCode, String)`, `Builder#args(Object...)` and the `legacyBody` parameter
are removed. `getMessage()` renders the same record in English, so a message exists once.

The build holds every message to seven rules, over every shipped locale:

1. every message is a record and names the rule it reports;
2. every record's derived key is in the catalog;
3. **every component of a record appears in its own text as `{name}`**;
4. every `{name}` in a text is a component of that record, and a brace holding anything else is
   refused rather than shown;
5. no catalog key is unreferenced by any record;
6. every declared record is built by some site;
7. every code is reported by a record that rule 6 found a site for.

Rules 6 and 7 are one property in two halves, and the second is worth nothing without the first.
Read off the records that are *declared*, rule 7 says only that every code has a declaration
carrying it — which stays true when the sites that reported a rule move to another number and the
record they used is left behind. Read off the records some site *builds*, it says what it is meant
to: nothing sends a reader to that chapter any more. A declared message nothing builds is also a
sentence shipped in every catalog that no compile can produce, which is rule 6 on its own.

Rule 1 is why the messages are records at all rather than a convention: a leaf of the hierarchy that
is not one carries no components, so every rule under it is silent about it. Rule 4 reads the entry
through the same parser the renderer reads it through — written twice, the two disagree about
`{held_by}` and about a brace nothing closes, which is the drift this whole area exists to remove.

Rule 3 is the new one and the reason for the rest. A value a diagnostic holds is a value a reader
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
compiler rather than part of that interface. The message, each hint and each secondary label all
carry one: a diagnostic points at more than one place and says something about each, and writing it
for one of the three leaves a reader of this interface parsing a sentence for the others.

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

### Migration

Three hundred and ten declarations and 257 sites moved, and `of(DiagnosticCode, String)`,
`args(Object...)`, the keyed `hint`, `secondary` and `secondaryIn`, and the `labelKey`/`labelArgs`
pair that carried a secondary label are gone with them. A diagnostic now holds one thing that says
what it is about, and there is no second way to build one.

A migration this wide is not reviewable as a Java diff, so what is reviewed is the rendered output:
every diagnostic the test corpus emits is captured before a change, in both locales and both
formats, and has to come back byte-identical except where the wording was deliberately fixed. Over
2,197 compilations that is 26,912 rendered lines, and they came back unchanged.

The areas moved by rule rather than by file — an area is what a key's first segment names, and one
file raises diagnostics of several. The parse area went last, because what it says is chosen while
the parser runs rather than written at a site. Three things had to be settled there.

`expect(kind, rule)` took the code as an argument: which part of the language is being read decides
which rule a missing token breaks, and 89 sites passed one of four codes. That parameter is now the
reading itself — a declaration, an expression, a pattern, an example — and the message follows from
it. The four messages say one sentence under four codes, which is the shape the model asks for: the
wording is the same and the chapter the reader is sent to is not.

`parse.expr` was raised with three codes for four mistakes, and said "I expected an expression here."
for all of them — including the one about a pattern. It is four messages now, each saying what was
wanted where it was wanted.

Two entries could not say what they carried. `parse.behavior.colon` wrote `behavior {0} :` and its
one site passed no arguments, so a reader was shown the placeholder; the sentence no longer names
the behavior. `parse.option.positional` was raised for two different mistakes and could state only
the first, so the second was invisible; it is two entries.

What stays keyed is not a diagnostic. `run.*` is what the `run` subcommand answers a shell with,
and `tok.*`, `kind.*` and `diag.*` are phrases written into the sentences above — a token category
is localized where the sentence is rendered, because the parser that names it has no language.

### Once it has moved

Adding a diagnostic gains a step — declare the record — and loses two: choosing a key and writing
the English sentence twice.

`E2011` and `E2010` gain the clause, `E1004` gains the group that supplied the field, `E2105` loses
its citation. Each is a component the record now requires, which is why they are fixed here rather
than separately.

A message whose wording turns on a value becomes two records and two catalog entries. The catalog
grows; the sentences become readable in the source.

Rule 6 is held from the codes' side, and it is what says a rule stopped being reported: a code
whose site moved to another number leaves nothing that sends a reader to its chapter, and the
number alone does not say so.

Rule 5 found catalog keys no record names. Each was either a message that had stopped being raised
or one whose site was never migrated.

## References

- `[#compile-errors]` — the rules these diagnostics report
- Issues #509, #512, #514 — three diagnostics that hold a value and do not print it
- GHC's structured `GhcMessage` and its diagnostic codes; Clang's `.td` diagnostic declarations;
  Rust's `#[derive(Diagnostic)]` — three compilers that put the values in the type, and the prior
  art for doing so
