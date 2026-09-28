package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * What stays fixed while one definition is checked: the module's symbol table, the {@code data} an
 * invariant or a codec is written against, the injected behaviors a body may call, and whether the
 * expression being checked is a value being given to a {@code ?} field — the one place an optional is
 * made (ADR-0011).
 *
 * <p>None of them changes as the walk descends into an expression, so they travel together rather than
 * as separate parameters threaded through every method. What does change — the variable environment and
 * the expected type pushed down from the surrounding context — is passed separately.
 *
 * <p>Two of them are what a check reads about names and neither is read off the other.
 * {@link Symbols} is what a name written here means and what this module's world holds;
 * {@link DeclarationAccess} is what a check asks of a declaration it did not write, wherever it was
 * written. Held side by side because one check needs both and because a carrier that answered the
 * second through the first would be answering what a declaration says out of the tree it was
 * written in.
 */
public record CheckContext(Symbols symbols, DeclarationAccess declarations,
                           Hir.Data data,
                           Map<ValueName.Behavior, ReqSig> reqs,
                           Map<ValueName.Behavior, ReqSig> callees, boolean makingAnOptional,
                           Preserved preserved,
                           Map<BindingId, ValueName.Behavior> dependencies,
                           List<BindingOwner> within,
                           OccurrenceLineage lineage) {

    public CheckContext {
        if (symbols == null || declarations == null) {
            throw new IllegalArgumentException("a check reads what a name written here means and"
                    + " what the declarations it is written against answer, so it is handed"
                    + " somewhere to read both");
        }
    }

    /** A context with no behavior callable by name — every position where only injected behaviors
     *  are in sight — that makes no optional and keeps no call standing. */
    public CheckContext(Symbols symbols, DeclarationAccess declarations, Hir.Data data,
                        Map<ValueName.Behavior, ReqSig> reqs) {
        this(symbols, declarations, data, reqs, Map.of(), false, Preserved.NONE, Map.of(),
                List.of(), OccurrenceLineage.ORIGINAL);
    }

    // Each question asked of the declarations, for a reader that asks one of them.

    public PublishedDeclarations published() {
        return declarations.published();
    }

    public DeclarationKinds kinds() {
        return declarations.kinds();
    }

    public NewtypeInners inners() {
        return declarations.inners();
    }

    public EffectiveFieldTypes fieldTypes() {
        return declarations.fieldTypes();
    }

    public FieldLayout layout() {
        return declarations.layout();
    }

    /**
     * The same, elaborating what {@code expansion} put here.
     *
     * <p>Which copy of a helper's body a fork stands in is known here and nowhere later: the
     * expansion is the node being elaborated, and what comes out of it is a body with the call site
     * substituted through. Recovered afterwards from the bindings a fork's condition happens to
     * read, a fork deciding by something with no name in it — a rule that reduced to a constant —
     * is a fork nothing can say the copy of.
     */
    public CheckContext inside(BindingOwner expansion, ValueName expanded, ExpansionSite at) {
        List<BindingOwner> deeper = new ArrayList<>();
        deeper.add(expansion);
        deeper.addAll(within);
        // Both said again, and neither read off the other. What a binding belongs to is the inlining
        // pass's answer, which is what the rules a call supplied are filed under; what a construct is
        // a copy of is the calls the source wrote. A bridge between them would put one reader's
        // counting inside the other's identity, and the counting is the thing a construct's name has
        // to be free of.
        return same().within(List.copyOf(deeper), lineage.copiedInto(expanded, at));
    }

    /**
     * The same, elaborating the build of {@code value} that was made for the region {@code at}.
     *
     * <p>A build adds one step to which copy a construct stands in and nothing to what its bindings
     * belong to: the value's body is written into the body it is built for, and only the copy is
     * different.
     */
    public CheckContext building(ValueName value, MaterialisationSite at) {
        return same().within(within, lineage.builtFor(value, at));
    }

    /**
     * Which construct of the model {@code origin} is, here.
     *
     * <p>The two halves put together where both are in hand: the construct is the node's, and the
     * copy is the walk's. Asked of the context rather than built at each node, so a node built
     * without one cannot come out saying it stands in the body as written while it stands in a copy.
     */
    public ConstructOccurrence occurrenceOf(SourceConstructOrigin origin) {
        return new ConstructOccurrence(origin, lineage);
    }

    /**
     * This context, to change one thing about.
     *
     * <p>Every {@code the same context, but} above goes through this, so what one of them does not
     * name it keeps. Written out a constructor call at a time, each of them left out whatever was
     * added last -- and the day that was which copy of a body a fork stands in, a fork inside a
     * helper stopped saying so as soon as the value it was in reached a field.
     */
    private Same same() {
        return new Same(symbols, declarations, data, reqs, callees, makingAnOptional,
                preserved, dependencies, within, lineage);
    }

    /** One context being written out of another. */
    private record Same(Symbols symbols, DeclarationAccess declarations,
                        Hir.Data data,
                        Map<ValueName.Behavior, ReqSig> reqs,
                        Map<ValueName.Behavior, ReqSig> callees, boolean makingAnOptional,
                        Preserved preserved,
                        Map<BindingId, ValueName.Behavior> dependencies,
                        List<BindingOwner> within,
                        OccurrenceLineage lineage) {

        CheckContext data(Hir.Data other) {
            return built(other, reqs, callees, makingAnOptional, preserved, dependencies, within, lineage);
        }

        CheckContext callees(Map<ValueName.Behavior, ReqSig> callable) {
            return built(data, reqs, callable, makingAnOptional, preserved, dependencies, within, lineage);
        }

        CheckContext makingAnOptional(boolean making) {
            return built(data, reqs, callees, making, preserved, dependencies, within, lineage);
        }

        CheckContext preserved(Preserved kept) {
            return built(data, reqs, callees, makingAnOptional, kept, dependencies, within, lineage);
        }

        CheckContext dependencies(Map<BindingId, ValueName.Behavior> bound) {
            return built(data, reqs, callees, makingAnOptional, preserved, bound, within, lineage);
        }

        CheckContext within(List<BindingOwner> expansion, OccurrenceLineage copy) {
            return built(data, reqs, callees, makingAnOptional, preserved, dependencies, expansion,
                    copy);
        }

        private CheckContext built(Hir.Data data, Map<ValueName.Behavior, ReqSig> reqs,
                                   Map<ValueName.Behavior, ReqSig> callees,
                                   boolean makingAnOptional, Preserved preserved,
                                   Map<BindingId, ValueName.Behavior> deps,
                                   List<BindingOwner> within, OccurrenceLineage lineage) {
            return new CheckContext(symbols, declarations, data, reqs, callees,
                    makingAnOptional, preserved, deps, within, lineage);
        }
    }

    /**
     * Which behavior each of an implementation's trailing parameters stands for.
     *
     * <p>A {@code let} implementing a behavior takes its {@code depends on} as parameters, so a
     * body naming one names a binding — and what that binding is is the behavior the clause
     * resolved to. Held by the binding and not by the name it was written under: an implementation
     * chooses its own parameter names, and two modules may declare a behavior of one name.
     */
    public ValueName.Behavior dependencyOf(BindingId binding) {
        return dependencies.get(binding);
    }

    /** The same context, told which behavior each trailing parameter of the definition being
     *  checked stands for. */
    public CheckContext withDependencies(
            Map<BindingId, ValueName.Behavior> bound) {
        return same().dependencies(bound);
    }

    /** No {@code data} in scope and no behaviors — the context an invariant-free, injection-free
     *  expression is checked in. */
    public static CheckContext of(Symbols symbols, DeclarationAccess declarations) {
        return new CheckContext(symbols, declarations, null, Map.of());
    }

    /** The same, for a reader that has not been handed the compilation's answers to what the
     *  declarations wrap and what their fields hold, as {@link DeclarationAccess#asWritten} reads
     *  them. */
    public static CheckContext of(Symbols symbols, PublishedDeclarations published,
                                  DeclarationKinds kinds) {
        return of(symbols, DeclarationAccess.asWritten(symbols, published, kinds));
    }

    /**
     * The context a data's invariant is elaborated in — the one reading of it that runs.
     *
     * <p>Every field named and nothing else. A clause may name the fields, the language's own
     * operations and a {@code let} it reaches, and it may not call a behavior (spec
     * §invariant-expressions), so there is nothing for {@code reqs} or {@code callees} to answer:
     * a table of behaviors here would be a permission the language does not give, offered to a
     * reading that cannot use it. It makes no optional — a clause states a condition rather than
     * building a value — and it keeps no call standing, which is what an executable reading is.
     *
     * <p>Named rather than written out where it is needed. This context and the one below decide
     * what a clause means; assembled twice they were assembled differently, which is what put a
     * behavior table on the emitter's reading and left it off the checker's.
     */
    public static CheckContext executableInvariant(Symbols symbols, DeclarationAccess declarations,
                                                   Hir.Data data) {
        return new CheckContext(symbols, declarations, data, Map.of());
    }

    /**
     * The context a behavior's {@code ensures} is elaborated in — the one reading of it that runs.
     *
     * <p>No {@code data}: a rule is written against the behavior's parameters and its answer, and
     * the fields it reaches it reaches through them. Otherwise the invariant fragment unchanged
     * (spec §ensures), so the rest is what {@link #executableInvariant} says.
     */
    public static CheckContext executableEnsures(Symbols symbols, DeclarationAccess declarations) {
        return new CheckContext(symbols, declarations, null, Map.of());
    }

    /** The same context checking a different {@code data}'s invariant, decoder, or encoder. */
    public CheckContext forData(Hir.Data other) {
        return same().data(other);
    }

    /** The same context with the behaviors a body may call by name in scope — the ones that require
     *  nothing (spec {@code [#calling-a-behavior]}). */
    public CheckContext withCallees(Map<ValueName.Behavior, ReqSig> callable) {
        return same().callees(callable);
    }

    /**
     * The same context, checking the value a {@code ?} field is being given.
     *
     * <p>This is what says an optional may be *made* here, rather than the expected type saying it: a
     * model can now write the type's name (issue #202), so an expected optional no longer means a field
     * asked for one. It travels with the context because the permission reaches the branches of the
     * value — a field may be given one thing or nothing by a rule — and stops at anything that is not
     * that value.
     */
    public CheckContext makingAnOptional(boolean making) {
        return same().makingAnOptional(making);
    }

    /**
     * The same context, typing a representation that keeps some calls standing.
     *
     * <p>Here rather than passed where a call is typed, because it does not change as the walk
     * descends: which representation is being typed is decided before any of it, and a body does not
     * become another representation part-way down.
     */
    public CheckContext preserving(Preserved kept) {
        return same().preserved(kept);
    }

    /**
     * The same context, typing the representation the invariant-discharge analysis reads: the
     * language's own operations kept standing, because that is what the analysis has rules about.
     *
     * <p>Said once, though two trees are typed that way — a behavior's body and the invariants of the
     * declarations it builds. They are two halves of one representation, and a line drawn in one of
     * them and not the other is an analysis that quietly sees less.
     */
    public CheckContext forDischarge() {
        return preserving(Preserved.byTheLanguagesOwnOperations());
    }

    /**
     * The same, where a value of the module is built and means what its template is.
     *
     * <p>Typed by what the value's own check settled, which is what a build is held to.
     */
    public CheckContext forDischarge(Preserved.SettledValues settledValues) {
        return preserving(Preserved.byTheLanguagesOwnOperations()
                .withValuesBuiltAsTemplates(settledValues));
    }

}
