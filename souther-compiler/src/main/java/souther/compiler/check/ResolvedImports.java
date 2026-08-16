package souther.compiler.check;

import souther.compiler.types.Denotation;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a module's import lines turned out to mean here, settled once.
 *
 * <p>The answer the contest between claims produced, kept as a value. It used to be a local of the
 * walk that assembled the scope: projected into the two namespaces and then dropped, so anything
 * downstream that needed to know what an import brought in had the lines and the modules they name
 * and worked it out again. Four passes did, and they did not agree with the walk or with each
 * other — a module that declares a behavior and does not expose it was refused where the scope is
 * assembled and borrowed anyway where signatures are collected, so an author was told the module
 * does not offer the name and then told two modules were offering it.
 *
 * <p>One result per spelling, and the four things a reader wants are projections of it. Held as
 * four tables instead, a helper could be in the one that says what a name reaches and out of the
 * one that says what may be read from the module that has it, and nothing would say which was
 * right. What a spelling means and what may be done about it are one fact.
 *
 * <p>The result itself does not leave. What is offered is the four answers, each already held
 * against the subject's declarations — a reader handed the results themselves could take the leave
 * out of a claim that lost its spelling to a {@code let} written here, which is the capability the
 * projection exists to withhold. A projection nobody is obliged to use is a rule kept by whoever
 * remembers it.
 *
 * <p>What is here is what the lines settled, and not what the module means as a whole: the
 * subject's own declarations are not in it. They are what the projections are held against — a
 * declaration written here takes the spelling in the namespace it is in, and the import keeps the
 * other one, which is what lets a `let` and a data of one name each answer where they belong after
 * the collision has been reported.
 */
public final class ResolvedImports {

    private final Map<String, ResolvedImport> byName;

    ResolvedImports(Map<String, ResolvedImport> byName) {
        this.byName = Collections.unmodifiableMap(new LinkedHashMap<>(byName));
    }

    /** Nothing was imported — a module resolved on its own. */
    public static final ResolvedImports NONE = new ResolvedImports(Map.of());

    /**
     * What the lines contributed to the type namespace.
     *
     * <p>A data and nothing else: a behavior and a definition are names in the value namespace, and
     * an import of one says nothing about what a type name denotes. A spelling every claim on which
     * failed is here as standing for nothing, so a use of it takes the error type and says nothing
     * more.
     */
    public Map<String, Denotation> types() {
        Map<String, Denotation> out = new LinkedHashMap<>();
        byName.forEach((spelling, resolved) -> {
            if (resolved.held().asAType()) {
                return;   // the declaration written here is what the spelling denotes
            }
            switch (resolved) {
                case ResolvedImport.Brings(Scoping.Brought.ADeclaration(var type), var _) ->
                        out.put(spelling, new Denotation.Denotes(type));
                case ResolvedImport.Brings _ -> { }
                case ResolvedImport.BringsNothing _ ->
                        out.put(spelling, Denotation.STANDS_FOR_NOTHING);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /**
     * What the lines contributed to the value namespace.
     *
     * <p>A data is not here. It reaches the value namespace as the construction of what it denotes,
     * which the type namespace answers for — so putting it here as well would be one arrival with
     * two answers, and which of them a reader got would depend on the order the two were consulted.
     */
    public Map<String, Reach> values() {
        Map<String, Reach> out = new LinkedHashMap<>();
        byName.forEach((spelling, resolved) -> {
            if (resolved.held().asAValue()) {
                return;   // the declaration written here is what the spelling reaches
            }
            switch (resolved) {
                case ResolvedImport.Brings(Scoping.Brought.ABehavior(ValueName.Behavior named),
                        var _) -> out.put(spelling, new Reach.Reaches(named));
                case ResolvedImport.Brings(Scoping.Brought.AHelper(var leave), var _) ->
                        out.put(spelling, new Reach.Reaches(
                                new ValueName.Helper(leave.module(), leave.name())));
                case ResolvedImport.Brings(
                        Scoping.Brought.ALibraryOperation(ValueName.Stdlib named), var _) ->
                        out.put(spelling, new Reach.Reaches(named));
                case ResolvedImport.Brings _ -> { }
                case ResolvedImport.BringsNothing _ ->
                        out.put(spelling, Reach.STANDS_FOR_NOTHING);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /**
     * The behaviors the lines brought in, by the bare name this module writes for each.
     *
     * <p>What a pass collecting borrowed signatures reads. It walked the lines itself and asked
     * each module whether it declares a behavior of the name — which is a different question, and
     * answers yes for a module that declares one and does not offer it.
     */
    public Map<String, ValueName.Behavior> behaviors() {
        Map<String, ValueName.Behavior> out = new LinkedHashMap<>();
        byName.forEach((spelling, resolved) -> {
            if (!resolved.held().asAValue()
                    && resolved instanceof ResolvedImport.Brings(
                            Scoping.Brought.ABehavior(ValueName.Behavior named), var _)) {
                out.put(spelling, named);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /**
     * The leave each surviving claim carries, by the bare name this module writes for it.
     *
     * <p>What may be read from another module is what this module was left with, and not what that
     * module offers. Asked of the module again, a definition it publishes could be read under a
     * spelling no line got — the claim having lost a contest, or come in on a line that was
     * refused — and the leave would be granted a second time to a claim that did not stand.
     */
    public Map<String, ModuleUniverse.InSight.Read.PublishedHelper> leaves() {
        Map<String, ModuleUniverse.InSight.Read.PublishedHelper> out = new LinkedHashMap<>();
        byName.forEach((spelling, resolved) -> {
            if (!resolved.held().asAValue()
                    && resolved instanceof ResolvedImport.Brings(
                            Scoping.Brought.AHelper(var leave), var _)) {
                out.put(spelling, leave);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /** Two of these say the same thing when every spelling settled the same way. Written out
     *  because this ends up inside an answer a compilation remembers, and an answer that never
     *  equals the last one is one nothing that read it is kept past. */
    @Override
    public boolean equals(Object other) {
        return other instanceof ResolvedImports resolved && byName.equals(resolved.byName);
    }

    @Override
    public int hashCode() {
        return byName.hashCode();
    }

    @Override
    public String toString() {
        return "ResolvedImports" + byName;
    }
}
