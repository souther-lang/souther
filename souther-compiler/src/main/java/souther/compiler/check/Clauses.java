package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
    private final Map<TypeName, List<Ast.InvariantClause>> inTheAnalysisRepresentation;
    private final Map<Ast.Data, Map<String, Type>> fields = new HashMap<>();
    private final Map<Ast.Data, Map<String, BindingId>> bindings = new HashMap<>();
    private final Map<Ast.Expr, Optional<Core>> typed = new IdentityHashMap<>();

    /**
     * @param inTheAnalysisRepresentation the clauses of the module being checked, in the
     *        representation the discharge rules are written at ({@link InliningPolicy#DISCHARGE}). A
     *        type another module declares is absent, and its clause is read off the declaration in
     *        the settled form — where the operations have already become the folds they are, so it
     *        falls outside the fragment.
     */
    Clauses(Symbols symbols,
            Map<TypeName, List<Ast.InvariantClause>> inTheAnalysisRepresentation) {
        this.symbols = symbols;
        this.inTheAnalysisRepresentation = inTheAnalysisRepresentation;
    }

    /** Every invariant that applies to {@code named}, each in the analysis representation where this
     * module declares it. */
    List<Ast.InvariantClause> of(TypeName named, Ast.Data data) {
        return TypeOps.effectiveInvariants(named, data, symbols, inTheAnalysisRepresentation::get);
    }

    /** What {@code data}'s fields are. */
    Map<String, Type> fieldsOf(Ast.Data data) {
        return fields.computeIfAbsent(data, d -> TypeOps.fieldTypes(d, symbols));
    }

    /** Which binding each of {@code data}'s fields is — what a clause reads, and what a construction
     * fills. */
    Map<String, BindingId> bindingsOf(Ast.Data data) {
        return bindings.computeIfAbsent(data, d -> TypeOps.fieldBindings(d, symbols));
    }

    /** The type of {@code field} read from {@code owner}, or null where that is not a field of a
     * declaration this module can see. */
    Type fieldType(Type owner, String field) {
        return owner instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.Data data
                ? fieldsOf(data).get(field) : null;
    }

    /**
     * {@code clause} as the checker types it: over the declaration's own fields, each a binding, in
     * the representation this check reads. Asked once per clause, because typing one walks it.
     *
     * <p>Null where the clause is not one this compiler could type there. That is the same answer as
     * a clause naming something outside the fragment — the run-time check stands for it — and it is
     * an answer rather than a failure because a declaration this check cannot read is not a
     * declaration an author wrote wrongly.
     */
    Core typed(Ast.Expr clause, Ast.Data data) {
        return typed.computeIfAbsent(clause, written -> {
            try {
                return Optional.ofNullable(Elaborator.elaborate(written,
                        DataChecker.fieldScope(data, symbols),
                        CheckContext.of(symbols).forData(data)
                                .preserving(Preserved.byTheLanguagesOwnOperations()),
                        Type.BOOL));
            } catch (RuntimeException _) {
                return Optional.empty();
            }
        }).orElse(null);
    }

    /**
     * What a clause of {@code data} states where each field is given what {@code given} says, or
     * {@code null} where it states nothing this check can read.
     *
     * <p>A field nothing was given — one a construction leaves out — leaves the clause naming a value
     * that is not there, and the clause is left to the run-time check rather than read against
     * nothing.
     */
    Core statedAt(Ast.Expr clause, Ast.Data data, Map<BindingId, Core> given) {
        Core stated = typed(clause, data);
        if (stated == null) {
            return null;
        }
        Set<BindingId> declared = new HashSet<>(bindingsOf(data).values());
        boolean[] whole = {true};
        readsOf(stated, binding -> {
            if (declared.contains(binding) && !given.containsKey(binding)) {
                whole[0] = false;
            }
        });
        return whole[0] ? substituted(stated, given) : null;
    }

    /** {@code e} with each binding {@code given} names replaced by the value it was given. */
    static Core substituted(Core e, Map<BindingId, Core> given) {
        if (e instanceof Core.Read r) {
            Core value = given.get(r.binding());
            return value != null ? value : r;
        }
        return Core.mapChildren(e, child -> substituted(child, given),
                // A name slot holds a binding and nothing else, so a value put there would be
                // something the reader of that slot cannot load. Only another name may stand there.
                name -> substituted(name, given) instanceof Core.Read r ? r : name,
                nd -> (Core.NewData) Core.mapChildren(nd, child -> substituted(child, given),
                        name -> substituted(name, given) instanceof Core.Read r ? r : name));
    }

    /** Every binding {@code e} reads, at any depth. */
    private static void readsOf(Core e, java.util.function.Consumer<BindingId> f) {
        if (e instanceof Core.Read r) {
            f.accept(r.binding());
        }
        Core.forEachChild(e, child -> readsOf(child, f));
    }
}
