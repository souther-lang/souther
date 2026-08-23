package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a type guarantees of a value, asked one position at a time.
 *
 * <p>The one reading of a declaration. A value of type {@code T} was built through {@code T}'s
 * checked constructor, so what {@code T} states holds of it; that argument is the same for a
 * behavior's parameter, for what a {@code match} arm binds, for what an attempt built, and for what
 * a combinator hands a closure. Each of those has a reader, and none of them may come to a different
 * answer about what the declaration says — so the answer is here and the readers ask.
 *
 * <p><b>A question about a position, not a walk over positions.</b> Everything a walk would carry —
 * how deep to go, which names to leave out, what a stop costs, what is being measured — is missing
 * on purpose. A caller that wants the positions beneath one asks {@link At.Declared#beneath} and
 * decides for itself whether to go there. Held the other way, the depth a walk could afford would be
 * part of what a declaration means, and two callers that could afford different depths would be two
 * readings of the model.
 *
 * <p>Nothing here mentions {@link Known}, a path, or a {@link InvariantChecker.Gathering}. Reading a
 * clause as an assumption cannot consult what was already known ({@link Predicates.Discharge}), so
 * there is nothing for a caller's knowledge to change about the answer.
 */
final class TypeGuarantees {

    private final Symbols symbols;

    private final Clauses clauses;

    private final Predicates predicates;

    TypeGuarantees(Symbols symbols, Clauses clauses, Predicates predicates) {
        this.symbols = symbols;
        this.clauses = clauses;
        this.predicates = predicates;
    }

    /**
     * What the type of the value at {@code root} guarantees of it, and what positions are beneath it.
     *
     * <p>The clauses are the declaration's, rebased onto this very value: a rule written about a
     * field is a rule about that field of this value, and where it is established and where it is
     * owed differ only in direction.
     */
    At at(Core root, Denotations denotations) {
        if (!(root.type() instanceof Type.Ref ref)
                || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data)) {
            // Either not a declaration of its own — a container or an optional, whose element is a
            // value that need not be there, or a type nothing is written under at all — or a choice
            // between declarations, which is the only kind that reaches here holding a rule at all.
            // A construction picks one of the cases, so a rule written on one of them refuses values
            // of that case and not every value of this.
            return new At.Undeclared();
        }
        Map<String, Type> fields = clauses.fieldsOf(data);
        Map<String, BindingId> bindings = clauses.bindingsOf(ref.name(), data);
        Map<BindingId, Core> given = new HashMap<>();
        fields.forEach((name, type) -> {
            BindingId field = bindings.get(name);
            if (field != null) {
                given.put(field, new Core.FieldAccess(root, name, type, root.pos()));
            }
        });
        Clauses.StatedClauses stated = clauses.statedAt(ref.name(), data, given);
        List<TypeGuarantee> guarantees = new ArrayList<>();
        for (Clauses.Stated one : stated.clauses()) {
            guarantees.add(read(one, denotations));
        }
        return new At.Declared(ref.name(), List.copyOf(guarantees), stated.everyClauseStated(),
                beneath(data, fields, bindings, given));
    }

    /**
     * One clause, read as something that holds of this value.
     *
     * <p>What each part of it came to is read here and kept, rather than handed to a caller as it
     * happens. A reader told mid-reading is a reader the reading has to know about; a reader given
     * the parts afterwards is one this does not.
     */
    private TypeGuarantee read(Clauses.Stated one, Denotations denotations) {
        // Where this clause becomes a rule of the model something can be attributed to. Settled here
        // so that no reader of the reading has to decide which of the rules of the model it holds.
        RuleRef.Invariant rule = new RuleRef.Invariant(one.clause().ref());
        List<TypeGuarantee.Part> parts = new ArrayList<>();
        Predicates.Owed owed = predicates.assumed(one.expr(), denotations, false,
                (part, said) -> parts.add(new TypeGuarantee.Part(part, said)));
        List<Quantified> quantified = new ArrayList<>();
        predicates.quantifiedBy(one.expr(), denotations, true, quantified);
        return new TypeGuarantee(rule, one.expr(), owed, quantified, parts);
    }

    /**
     * The positions under a declaration.
     *
     * <p>A newtype's {@code .value} is the same location as the newtype, so what its base guarantees
     * is guaranteed of this very atom: {@code data Outer = Inner} carries Inner's invariant. It is at
     * no path of its own — wearing a name is not being somewhere else — which is what an empty
     * {@link At.Beneath#field} says.
     */
    private List<At.Beneath> beneath(Hir.Data data, Map<String, Type> fields,
                                     Map<String, BindingId> bindings, Map<BindingId, Core> given) {
        List<At.Beneath> out = new ArrayList<>();
        if (data.newtype()) {
            BindingId held = bindings.get("value");
            Core value = held == null ? null : given.get(held);
            out.add(value == null ? new At.Beneath("", null, fields.get("value"))
                    : new At.Beneath("", value, value.type()));
            return out;
        }
        for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
            Core value = given.get(field.getValue());
            if (value != null) {
                out.add(new At.Beneath(field.getKey(), value, value.type()));
            }
        }
        return out;
    }

    /**
     * Whether any rule is written anywhere under {@code type}.
     *
     * <p>A question about the model and not about any walk, which is what makes it the right one to
     * ask where a reader stops: the reader's own reach is what is being decided, so reading that
     * would answer that whatever was not read had nothing in it.
     */
    boolean anyRuleUnder(Type type) {
        return anyRuleUnder(type, new HashSet<>());
    }

    /** {@code seen} stops a type that holds its own kind. A name met on the way here was read where
     * it was met, so what it holds is accounted for and reaching it again adds nothing. */
    private boolean anyRuleUnder(Type type, Set<TypeSymbol> seen) {
        if (type instanceof Type.Ref ref) {
            if (!seen.add(ref.name())) {
                return false;
            }
            return switch (symbols.declarations().declaration(ref.name().key())) {
                // A unit data holds nothing and may write no rule about it (spec §unit-data), so a
                // sum of them is a type nothing is written under — which is what makes an
                // enumeration a position this still speaks for.
                case Hir.UnitData _ -> false;
                case Hir.SumData sum -> AtomSpace.subjectAtoms(Type.ref(sum.declares()), symbols).stream()
                        .anyMatch(each -> anyRuleUnder(Type.ref(each), seen));
                case Hir.Data data -> !clauses.declared(ref.name(), data).isEmpty()
                        || TypeOps.fieldTypes(data, symbols).values().stream()
                                .anyMatch(each -> anyRuleUnder(each, seen));
                case null, default -> false;
            };
        }
        boolean[] found = {false};
        Type.forEachChild(type, child -> found[0] |= anyRuleUnder(child, seen));
        return found[0];
    }

    /** What stands at one position. */
    sealed interface At {

        /**
         * A position whose type declares rules of its own, with what they guarantee here.
         *
         * @param name             the declaration, which is what a caller keeping track of the ones
         *                         it has entered files under
         * @param guarantees       what each of its clauses states of this value
         * @param everyClauseStated whether every clause of the declaration could be read at all. A
         *                          clause stating nothing a reader can use is gone before any
         *                          reading sees it, and which position it was about goes with it, so
         *                          a caller answering for the rules it was handed would answer for a
         *                          rule it never saw
         * @param beneath          the positions under this one
         */
        record Declared(TypeSymbol name, List<TypeGuarantee> guarantees, boolean everyClauseStated,
                        List<Beneath> beneath) implements At {

            public Declared {
                guarantees = List.copyOf(guarantees);
                beneath = List.copyOf(beneath);
            }
        }

        /** A position with no declaration of its own to read, so nothing is stated here of every
         * value that stands at it. What is written under its type may still be worth asking about
         * ({@link TypeGuarantees#anyRuleUnder}). */
        record Undeclared() implements At {}

        /**
         * A position under another.
         *
         * @param field the name it is reached by, or empty where it is this same position wearing a
         *              name
         * @param value what stands there, or null where the declaration names a field this could not
         *              read a value for
         * @param type  what stands there is of this type, which is answerable even where the value
         *              is not
         */
        record Beneath(String field, Core value, Type type) {}
    }
}
