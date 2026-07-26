# ADR-0057: A behavior's output union is built from its own module's cases

Status: Accepted (decided 2026-07-26). Records the reason behind E1606, replacing the JVM claim that stood in for it.

## Context

A behavior whose output is an anonymous union (`-> 出荷指示 | 在庫不足`) gets a generated sealed interface, `<Behavior名>Result`, that its leaf cases implement (ADR-0008, ADR-0049). A Java caller receives one value and matches it with a `switch` that needs no `default`.

E1606 rejects such a union when one of its cases was declared in an imported module. That happens in two ordinary shapes once a domain is split into bounded contexts: a behavior declaring an imported failure case in its own output, and a `>->` whose departed case comes from an imported stage.

The reason recorded in the compiler was that the JVM cannot do it — that a sealed type in the unnamed module permits only same-package subclasses. That claim was measured on JDK 25 and does not hold for classfiles read from the classpath (issue #95): the same-package rule is enforced by javac when it *declares* a sealed type in source, and a cross-package `permits` read from a classfile loads and still gives a Java consumer an exhaustive `switch`.

The premise was wrong, but so was the conclusion drawn from testing only the `permits` side. Both sides of a sealed hierarchy have to hold: the union lists its cases, and each case class implements the union. Souther puts that interface on the case class when the case's **own** module is generated — `inv.Shortage` comes out of `inv` with `implements inv.AllocateResult` and nothing else. For it to be a member of `ship.出荷するResult`, the class `inv` already emitted would have to implement an interface `ship` declares.

Lifting E1606 and compiling the pair shows what that costs. The union is emitted permitting only the local case, the imported value is not a member of it, and a Java consumer's exhaustive `switch` compiles and then fails:

```
union ship.AllocateAndShipResult permits=[class ship.Shipped]
inv.Shortage ifaces=[interface inv.AllocateResult]
javac: the exhaustive switch compiles
java.lang.ClassCastException: class inv.Shortage cannot be cast to
  class ship.AllocateAndShipResult
```

Making it work is possible: every module is compiled in one run today, so the backend could collect union memberships across the whole program and give `inv.Shortage` the extra interface. The cost is that `inv`'s bytecode would then depend on which modules import it — compiled alone it is one class, compiled beside `ship` it is another. ADR-0024 already refuses the same property in the other direction, requiring an exposed composition to declare its output so a far-away change cannot grow a published surface silently. It would also settle the question of resolving an import from a published jar, where the imported module's classes are not the importer's to regenerate.

## Decision

**A behavior's output union is built from cases declared in its own module.** A case declared elsewhere is rejected (E1606), and the reason is that a case class's union memberships are settled by its own module's generation, not that the JVM forbids the `permits` entry.

A module that consumes another's failure case translates it: match the imported behavior's result and return a case of this module. That translation is the module boundary showing up in the code, and it is what a bounded context does with another context's vocabulary.

## Alternatives considered

**Whole-program membership.** Collect every union across all modules, then generate each case class with the interfaces its consumers need. Rejected: a module's output stops being a function of its own source, and jar-level imports become unavailable.

**A non-sealed generated interface.** Rejected: it does not address this. Sealed or not, a class that does not implement the interface is not a subtype — the `ClassCastException` above is unchanged.

**Wrapper cases.** Generate, in the consuming module's package, a record wrapping each imported case (`ship.ShortageCase(inv.Shortage value)`) and put that in the union. This keeps the exhaustive `switch` and leaves the imported module untouched. Rejected for now: within one `switch`, a local case arrives as the value itself and an imported one arrives wrapped, so the Java surface of a union depends on where each case came from. It stays available if cross-context unions turn out to be worth that.

## Consequences

- E1606 stays, with its message and hint stating the settled-at-generation reason and the translation to perform.
- Naming an imported behavior is unaffected: it composes as a `>->` stage and is injected as a `requires` dependency (issue #96), including across a module boundary. Only mixing an imported case into a union declared here is refused.
- A module's generated classes remain a function of its own source. Resolving an import from a published jar stays open as a future direction.
