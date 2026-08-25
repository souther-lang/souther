package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The invariants of the declarations the discharge check reads: each clause typed once, over the
 * fields it is written against, and read at a value by putting what each field is being given where
 * that field is read.
 *
 * <p>That reading is what lets the check hold one representation. A clause belongs to a declaration
 * and the values belong to a body, and a clause read over its own tree and a body read over another
 * would be two term grammars that have to be kept naming the same value the same way. A field is a
 * binding, so putting a value there is a substitution, and what comes out is an expression of the
 * body's own kind.
 *
 * <p>Everything here is remembered, because both the seeding and every construction ask the same
 * declaration the same questions.
 */
final class Clauses {

    private final Symbols symbols;
    private final Map<TypeSymbol, List<Hir.InvariantClause>> inTheAnalysisRepresentation;
    private final Map<Hir.Data, Map<String, Type>> fields = new HashMap<>();
    private final Map<TypeSymbol.AtModule, Map<String, BindingId>> bindings =
            new HashMap<>();
    /** Remembered per declaration, not per clause: a clause an include brings in is one expression
     * reached under two names, and what it types to is read against the fields of the one asking. */
    private final Map<TypeSymbol, Map<Hir.Expr, TypedClause>> typed = new HashMap<>();
    private final Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> effective = new HashMap<>();
    /** Which of a declaration's own fields each typed clause reads — what a construction has to have
     * filled for the clause to be read at all. */
    private final Map<Core, Set<BindingId>> readsFields = new IdentityHashMap<>();

    /**
     * @param inTheAnalysisRepresentation the clauses of the module being checked, in the
     *        representation the discharge rules are written at ({@link InliningPolicy#DISCHARGE}). A
     *        type another module declares is not among them and its clauses are read off its
     *        declaration, which says what its author wrote whether that module was compiled here or
     *        published and read back (spec §invariant-discharge-representation). What can be
     *        discharged against a clause is the same either way.
     */
    Clauses(Symbols symbols,
            Map<TypeSymbol, List<Hir.InvariantClause>> inTheAnalysisRepresentation) {
        this.symbols = symbols;
        this.inTheAnalysisRepresentation = inTheAnalysisRepresentation;
    }

    /** Every invariant that applies to {@code named}, each in the analysis representation where this
     * module declares it. */
    List<Hir.InvariantClause> of(TypeSymbol.AtModule named, Hir.Data data) {
        return effective.computeIfAbsent(named, name ->
                TypeOps.effectiveInvariants(name, data, symbols, inTheAnalysisRepresentation::get));
    }

    private final Map<TypeSymbol.AtModule, List<TypeOps.Declared>> declaredClauses =
            new HashMap<>();

    /** What {@code data}'s fields are. */
    Map<String, Type> fieldsOf(Hir.Data data) {
        return fields.computeIfAbsent(data, d -> TypeOps.fieldTypes(d, symbols));
    }

    /**
     * Which binding each of {@code named}'s fields is — what a clause reads, and what a construction
     * fills.
     *
     * <p>Keyed by the name and not by the declaration, because that is what the binding is a function
     * of: two modules may declare one spelling, and a reader with both in sight would otherwise have
     * them answer alike.
     */
    Map<String, BindingId> bindingsOf(TypeSymbol.AtModule named, Hir.Data data) {
        return bindings.computeIfAbsent(named, name -> TypeOps.fieldBindings(name, data, symbols));
    }

    /**
     * {@code clause} as the checker types it: over {@code named}'s own fields, each a binding, in
     * the representation this check reads. Asked once per clause, because typing one walks it.
     *
     * <p>{@link TypedClause.Stopped} where typing it did not finish. This used to answer null for
     * that, saying it was the same answer as a clause naming something outside the fragment; it is
     * not, and it never was — the elaborator does not answer null of its own accord, so every one of
     * those was an exception caught here and dropped.
     */
    TypedClause typed(Hir.Expr clause, TypeSymbol.AtModule named, Hir.Data data) {
        return typed.computeIfAbsent(named, _ -> new IdentityHashMap<>())
                .computeIfAbsent(clause, written -> {
                    try {
                        return new TypedClause.Typed(Elaborator.elaborate(written,
                                DataChecker.fieldScope(named, data, symbols),
                                CheckContext.of(symbols).forData(data).forDischarge(),
                                Type.BOOL));
                    } catch (RuntimeException why) {
                        // Recorded rather than dropped. Measured over the whole suite, every null
                        // this used to answer was one of these — the elaborator never answers null
                        // of its own accord — so what was being lost was the whole of it.
                        InvariantChecker.gaveUp("typing a clause of " + named, why);
                        return new TypedClause.Stopped();
                    }
                });
    }

    /**
     * What a clause of {@code data} states where each field is given what {@code given} says, or
     * {@code null} where it states nothing this check can read.
     *
     * <p>A field nothing was given — one a construction leaves out — leaves the clause naming a value
     * that is not there, and the clause is left to the run-time check rather than read against
     * nothing.
     */
    Core statedAt(Hir.Expr clause, TypeSymbol.AtModule named, Hir.Data data, Map<BindingId, Core> given) {
        // Fail-open: a clause with no form leaves its run-time check standing, whichever way the
        // form went missing. Which of the two it was matters to a reader that publishes a sentence
        // about the clause, and this is not one.
        Core stated = typed(clause, named, data).orNull();
        if (stated == null) {
            return null;
        }
        return given.keySet().containsAll(fieldsRead(stated, named, data))
                ? substituted(stated, given) : null;
    }

    /**
     * Every clause of {@code named}, each stated where its fields are given what {@code given} says,
     * and the ones that state nothing this check can read left out.
     *
     * <p>Both directions ask this. What a clause guarantees where the value already exists and what
     * it owes where one is being built are the same clauses read the same way, and they differ only
     * in what the fields are given — a read of each field, or the value each is being handed.
     */
    StatedClauses statedAt(TypeSymbol.AtModule named, Hir.Data data, Map<BindingId, Core> given) {
        List<Stated> stated = new ArrayList<>();
        int declared = 0;
        for (TypeOps.Declared inv : declared(named, data)) {
            declared++;
            Core one = statedAt(inv.clause().expr(), named, data, given);
            if (one != null) {
                stated.add(new Stated(Clause.of(inv), one));
            }
        }
        return new StatedClauses(List.copyOf(stated), stated.size() == declared);
    }

    /**
     * The clauses of one declaration as they read here, and whether they are all of them.
     *
     * <p>The second because leaving one out is not visible in the first. A clause that states
     * nothing this can read is dropped, and a caller handed the rest has no way to tell a
     * declaration whose every clause was read from one whose clauses it is holding some of — the
     * two are the same list with different things missing from it. Said here, where the dropping
     * happens, rather than counted again by whoever needs to know.
     *
     * @param everyClauseStated whether every clause the declaration writes is in {@code clauses}.
     *                          A caller that asked for none of them was not asked to lose any and
     *                          is told so
     */
    record StatedClauses(List<Stated> clauses, boolean everyClauseStated) {

        /** What a reading told to leave a declaration's clauses out gets: none of them, and nothing
         * lost. */
        static final StatedClauses NONE_ASKED_FOR = new StatedClauses(List.of(), true);
    }

    /**
     * One clause as it reads at a construction, beside the clause it is a reading of.
     *
     * <p>A check that judges the clauses one at a time has something to say about the one it could
     * not settle, and what it says it by is what {@link Clause} holds — which the clauses were
     * flattened out of before reaching here, leaving every unproven clause reported as "the
     * invariant".
     */
    record Stated(Clause clause, Core expr) {}

    /** Every clause of {@code named}, each with the declaration that wrote it. */
    List<TypeOps.Declared> declared(TypeSymbol.AtModule named, Hir.Data data) {
        return declaredClauses.computeIfAbsent(named, name ->
                TypeOps.declaredInvariants(name, data, symbols, inTheAnalysisRepresentation::get));
    }

    /** Which of {@code data}'s own fields {@code clause} reads, remembered: a clause is read at every
     * construction of its type, and what it reads does not change between them. */
    private Set<BindingId> fieldsRead(Core clause, TypeSymbol.AtModule named, Hir.Data data) {
        return readsFields.computeIfAbsent(clause, read -> {
            Set<BindingId> declared = new HashSet<>(bindingsOf(named, data).values());
            Set<BindingId> found = new HashSet<>();
            readsOf(read, binding -> {
                if (declared.contains(binding)) {
                    found.add(binding);
                }
            });
            return Set.copyOf(found);
        });
    }

    /** {@code e} with each binding {@code given} names replaced by the value it was given. */
    static Core substituted(Core e, Map<BindingId, Core> given) {
        if (e instanceof Core.Read r) {
            Core value = given.get(r.binding());
            return value != null ? value : r;
        }
        return Core.mapAll(e, child -> substituted(child, given),
                // A name slot holds a binding and nothing else, so a value put there would be
                // something the reader of that slot cannot load. Only another name may stand there.
                name -> substituted(name, given) instanceof Core.Read r ? r : name);
    }

    /** Every binding {@code e} reads, at any depth. */
    private static void readsOf(Core e, java.util.function.Consumer<BindingId> f) {
        if (e instanceof Core.Read r) {
            f.accept(r.binding());
        }
        Core.forEachChild(e, child -> readsOf(child, f));
    }
}
