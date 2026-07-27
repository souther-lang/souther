# ADR-0065: A data is a Java record on the JVM

Status: Accepted.

## Context

A generated data class was a final class with fields and, when the data was exposed, a public record-style accessor per field. That reads well from Java: `issue.id()` is what a record's accessor call looks like, and the runtime's `Ok` / `Err` — which *are* records — are read the same way, so the boundary looked consistent.

It does not read from Kotlin. Kotlin turns a Java `getX()` into a property and leaves `x()` a method call, so a Kotlin caller writes `issue.id().value()`. Worse than the verbosity, `issue.id` — what a Kotlin author writes first — resolves to the backing field and reports `Cannot access 'field id: IssueId': it is package-private in 'example.issuetracker.Issue'`. The message names a field where the accessor was meant, so it reads as a visibility problem to fix rather than a call to write.

Making the field private does not fix that. Kotlin still resolves the field and reports `it is private in 'X'` — measured, not assumed. Kotlin only stops resolving the field when the class file says the name is a record component.

Three ways to give a Kotlin author `issue.id` were measured against jackson-databind 2.19.4 and kotlinc 2.2.21:

| generated shape | Kotlin `issue.id` | Jackson can construct | Jackson can serialize |
|---|---|---|---|
| as it was | error naming the field | no (no Creator) | no (no properties) |
| add bean `getX()` beside `x()` | property, non-null | no | yes, under getter names |
| a record | property | yes, through the canonical constructor | yes, under component names |

A record therefore hands frameworks two paths the previous shape refused: building a value without the invariant `__construct` runs, and writing a JSON shape that is not the one the `encoder` declares. Both were weighed and accepted. Construction authority is governed by declaration, not by visibility (ADR-0059), and a framework willing to call `setAccessible` could already reach the constructor; what Souther guarantees is what a decoder admits, not what reflection cannot forge. A value forged that way does not stay on the Java side — a behavior takes generated types, so it can be handed straight in — and that is the cost being accepted, not an oversight. If it has to be closed later, the canonical constructor of an invariant-bearing type can check and throw, leaving `__construct` the `Result`-returning path.

What a record adds beyond the Kotlin read is a Java read: javac deconstructs the value in a record pattern, including a case of a sum inside an exhaustive `switch`, which is the shape a Java consumer already uses for `Ok` / `Err`.

## Decision

**A data class and a unit class are generated as records: `java.lang.Record` as the superclass, a `Record` attribute naming the fields as components in declaration order, a `toString` in the record form, and a public accessor per component on every data rather than only on an exposed one. The canonical constructor stays non-public.**

The backing field becomes `private`, as a record's is, so the generated code of the module reads a field through its accessor as an importing module already did.

Nullness is stated per accessor. Kotlin applies a class's `@NullMarked` to every member except a record component's accessor, which it types from the component — measured on both shapes — so each accessor carries `@NonNull` on its return type at every position of it, and the component repeats it for a reflective reader.

A field may not be named after a no-argument method of `Object`, which is a compile error where the field is written. `toString` would emit a second `toString()` and the class would not load.

## Consequences

- Kotlin reads a data as data: `issue.id.value`, non-null, no error naming a field.
- Java gains record patterns over generated types, and a `switch` over a sum can deconstruct each case without a `default`.
- `toString` exists, where before a data printed as a hash. It has to: `java.lang.Record` declares it abstract, so a data without one would throw `AbstractMethodError` when anything printed it. This rules out generating the record shape for only some data.
- `equals` / `hashCode` stay as they were, comparing a `Decimal` by value rather than by scale. Being a record does not dictate what equality means, and a Java reader who assumes the canonical semantics sees a difference exactly there.
- `Class.isRecord()` and `getRecordComponents()` answer, so a framework that maps records — jOOQ's `into(Class)`, Jackson — engages with generated types where it previously failed. That is the trade named above, in both directions.
- Nothing existing breaks: `issue.id()` still resolves, so Java and Kotlin code written against the old shape compiles unchanged. The Clojure boundary reads a sum through `getPermittedSubclasses` and `instance?`, neither of which the change touches.
