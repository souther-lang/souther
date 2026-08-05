package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation).
 *
 * <p>This is the table that decides how much of a model the language tracks rather than leaves to a
 * run-time check, and it is stated per operation because that is the level an author writes at. It is
 * data and lookups and nothing else: what a rule is <em>used for</em> — seeding a closure's element,
 * carrying a predicate to the container something was built from, naming a size — is the walk's, and
 * lives with the walk.
 *
 * <p>Every rule is keyed by the operation a call reaches, not by how it was written: a module that
 * imported an operation writes it bare and one that did not writes it qualified, and they are the
 * same operation. It is also keyed by the operation a call still reaches when this tree is read,
 * which is not every name an author can write — {@code List.fold} is rewritten to
 * {@code List.foldFrom} before any of this, so a rule under that name could not be looked up.
 * {@code InvariantCombinatorRulesTest} holds the table to both halves of that.
 */
final class DischargeRules {

    /** The library operation written {@code qualified}, as what a name reaching it denotes. */
    private static ValueName op(String qualified) {
        return new ValueName.Stdlib(qualified);
    }

    /** A stdlib combinator whose closure (argument {@code closureArg}) is handed each element of its
     * container argument ({@code listArg}) as closure parameter {@code elementParam} — mirrors
     * {@link TotalityChecker}'s table, so a construction inside a {@code List.map} or
     * {@code List.foldFrom} closure is analyzed with the element bound to the container's element
     * type. */
    record Combinator(int closureArg, int elementParam, int listArg) {}

    private static final Map<ValueName, Combinator> COMBINATORS = Map.ofEntries(
            Map.entry(op("List.foldFrom"), new Combinator(0, 1, 2)),
            Map.entry(op("List.foldr"), new Combinator(0, 1, 2)),
            Map.entry(op("List.map"), new Combinator(0, 0, 1)),
            Map.entry(op("List.filter"), new Combinator(0, 0, 1)),
            Map.entry(op("List.all"), new Combinator(0, 0, 1)),
            Map.entry(op("List.any"), new Combinator(0, 0, 1)),
            Map.entry(op("List.find"), new Combinator(0, 0, 1)),
            Map.entry(op("List.partition"), new Combinator(0, 0, 1)),
            Map.entry(op("List.concatMap"), new Combinator(0, 0, 1)),
            Map.entry(op("List.filterMap"), new Combinator(0, 0, 1)),
            Map.entry(op("List.sortBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.groupBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.indexBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.allUniqueBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.indexedMap"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.fold"), new Combinator(0, 2, 2)),
            Map.entry(op("Map.map"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.filter"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.update"), new Combinator(1, 0, 2)),
            Map.entry(op("Map.upsert"), new Combinator(2, 0, 3)),
            Map.entry(op("Set.fold"), new Combinator(0, 1, 2)),
            Map.entry(op("Set.map"), new Combinator(0, 0, 1)),
            Map.entry(op("Set.filter"), new Combinator(0, 0, 1)),
            Map.entry(op("Set.partition"), new Combinator(0, 0, 1)),
            Map.entry(op("Option.map"), new Combinator(0, 0, 1)));

    /** The operations the table has a rule for, for the test that holds it to being reachable. */
    static Set<String> combinatorNames() {
        Set<String> names = new LinkedHashSet<>();
        COMBINATORS.keySet().forEach(operation -> names.add(operation.name()));
        return names;
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two. */
    private static final Set<ValueName> SIZE_CALLS = Set.of(
            op("List.length"), op("String.length"), op("Set.size"), op("Map.size"));

    /**
     * What a construction of a container keeps of the container it was built from.
     *
     * <ul>
     * <li>{@code PERMUTES} — the same elements in another order. Everything survives.
     * <li>{@code SUBSET} — some of the same elements. Nothing new is there, so a property of every
     *     element survives and the size can only fall.
     * <li>{@code MAPS} — one new element for each. As many as before, and nothing is known of what
     *     they are.
     * <li>{@code COLLAPSES} — at most one new element for each. Neither the elements nor the count.
     * </ul>
     */
    enum Shape {
        PERMUTES, SUBSET, MAPS, COLLAPSES;

        /** Whether the result has exactly as many as the container it was built from. */
        boolean keepsSize() {
            return this == PERMUTES || this == MAPS;
        }
    }

    /** Which argument a container was built from, and what the building keeps of it. */
    record Built(int from, Shape shape) {}

    private static final Map<ValueName, Built> BUILT_FROM = Map.ofEntries(
            Map.entry(op("List.reverse"), new Built(0, Shape.PERMUTES)),
            Map.entry(op("List.sort"), new Built(0, Shape.PERMUTES)),
            Map.entry(op("List.sortBy"), new Built(1, Shape.PERMUTES)),
            Map.entry(op("List.map"), new Built(1, Shape.MAPS)),
            Map.entry(op("List.indexedMap"), new Built(1, Shape.MAPS)),
            Map.entry(op("Map.map"), new Built(1, Shape.MAPS)),
            Map.entry(op("List.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.distinct"), new Built(0, Shape.SUBSET)),
            Map.entry(op("List.take"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.drop"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Set.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Map.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.filterMap"), new Built(1, Shape.COLLAPSES)),
            Map.entry(op("Set.map"), new Built(1, Shape.COLLAPSES)));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.member} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    record Carried(int container, Set<Shape> through) {}

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List.all"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.allUniqueBy"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.any"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("List.member"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Set.contains"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Map.containsKey"), new Carried(1, Set.of(Shape.PERMUTES)));

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, Integer> PROJECTION_OF = Map.of(op("List.allUniqueBy"), 0);

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link #combinator} already answers of any combinator, and how
     * far the statement travels is what {@link #carried} already answers of any predicate — so a
     * quantifier is the name and nothing else. {@code List.all} is the only one the library has. */
    private static final Set<ValueName> QUANTIFIERS = Set.of(op("List.all"));

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property but about what a predicate <em>says</em>: {@code List.isEmpty(xs)} and
     * {@code List.length(xs) == 0} are one statement, so a guard writing either discharges a clause
     * writing the other. Without it the two would be unrelated, which is an accident of which one the
     * author reached for. */
    private static final Map<ValueName, ValueName> EMPTINESS = Map.of(
            op("List.isEmpty"), op("List.length"),
            op("Set.isEmpty"), op("Set.size"),
            op("Map.isEmpty"), op("Map.size"),
            op("String.isEmpty"), op("String.length"));

    /**
     * The library's function forms of the arithmetic operators, and the operator each one is. They
     * reach the same kernel in the same argument order — {@code Int.add} is {@code IntMath.addExact},
     * which is what {@code +} emits — so the two spellings compute one value and are read as one term.
     * {@code divide} is absent: it answers a union rather than a number.
     */
    private static final Map<ValueName, Ast.BinOp> OPERATOR_CALLS = Map.of(
            op("Int.add"), Ast.BinOp.ADD,
            op("Int.subtract"), Ast.BinOp.SUB,
            op("Int.multiply"), Ast.BinOp.MUL,
            op("Decimal.add"), Ast.BinOp.ADD,
            op("Decimal.subtract"), Ast.BinOp.SUB,
            op("Decimal.multiply"), Ast.BinOp.MUL);

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool.not");

    static Combinator combinator(ValueName operation) {
        return COMBINATORS.get(operation);
    }

    static Built builtFrom(ValueName operation) {
        return BUILT_FROM.get(operation);
    }

    static Carried carried(ValueName operation) {
        return CARRIED.get(operation);
    }

    /** Which argument of {@code operation} is the projection its predicate is stated over, or null
     * where it is stated over the element itself. */
    static Integer projectionOf(ValueName operation) {
        return PROJECTION_OF.get(operation);
    }

    static boolean isSize(ValueName operation) {
        return SIZE_CALLS.contains(operation);
    }

    static boolean isQuantifier(ValueName operation) {
        return QUANTIFIERS.contains(operation);
    }

    /** The size call an emptiness check means, or null where {@code operation} is not one. */
    static ValueName sizeMeantBy(ValueName operation) {
        return EMPTINESS.get(operation);
    }

    /** The operator {@code operation} is, where it is one written as a function, else null. */
    static Ast.BinOp operator(ValueName operation) {
        return OPERATOR_CALLS.get(operation);
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render
     * it. */
    static boolean readsAsATerm(ValueName operation) {
        return isSize(operation) || BUILT_FROM.containsKey(operation)
                || CARRIED.containsKey(operation) || isQuantifier(operation)
                || NOT.equals(operation);
    }

    /** The container a size is really the size of: an operation that keeps the size of what it was
     * built from is peeled away, so {@code List.length(List.map(f, xs))} is the atom
     * {@code List.length(xs)}. How the elements are made has no bearing on how many there are, which
     * is why the closure does not enter the key. */
    static Core sizeSource(Core e) {
        if (e instanceof Core.PreservedCall call) {
            Built built = builtFrom(call.operation());
            if (built != null && built.shape().keepsSize() && built.from() < call.args().size()) {
                return sizeSource(call.args().get(built.from()));
            }
        }
        return e;
    }

    private DischargeRules() {}
}
