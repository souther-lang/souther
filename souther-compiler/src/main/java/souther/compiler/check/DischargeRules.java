package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation).
 *
 * <p>These are the tables that decide how much of a model the language tracks rather than leaves to a
 * run-time check, and each is stated per operation because that is the level an author writes at. It
 * is data and lookups and nothing else: what a rule is <em>used for</em> — carrying a predicate to
 * the container something was built from, naming a size — is the walk's, and lives with the walk.
 *
 * <p>Every rule is keyed by the operation a call reaches, not by how it was written: a module that
 * imported an operation writes it bare and one that did not writes it qualified, and they are the
 * same operation. What the operations do to the closure they are handed is not here but in
 * {@link Combinators}, which the totality check reads as well and neither of the two states.
 */
final class DischargeRules {

    /** The library operation written {@code qualified}, as what a name reaching it denotes. */
    private static ValueName op(String qualified) {
        return new ValueName.Stdlib(qualified);
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
            Map.entry(op("List.mapIndexed"), new Built(1, Shape.MAPS)),
            Map.entry(op("Map.mapValues"), new Built(1, Shape.MAPS)),
            Map.entry(op("List.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.distinct"), new Built(0, Shape.SUBSET)),
            Map.entry(op("List.take"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.drop"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Set.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Map.filterEntries"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.distinctBy"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Map.remove"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Set.remove"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Map.intersection"), new Built(0, Shape.SUBSET)),
            Map.entry(op("Map.difference"), new Built(0, Shape.SUBSET)),
            Map.entry(op("Set.intersection"), new Built(0, Shape.SUBSET)),
            Map.entry(op("Set.difference"), new Built(0, Shape.SUBSET)),
            Map.entry(op("Map.updateIfPresent"), new Built(2, Shape.MAPS)),
            Map.entry(op("List.filterMap"), new Built(1, Shape.COLLAPSES)),
            Map.entry(op("Set.map"), new Built(1, Shape.COLLAPSES)));

    /**
     * The constructions this says nothing of, in three groups. Each reason is about what a shape can
     * say, not about the operation being uninteresting.
     *
     * <p>What they answer holds something other than what they read. A map's keys and its entry
     * pairs are not its values, {@code fromList} takes the values out of pairs, {@code groupBy}
     * answers lists of the elements rather than the elements, {@code concat} reads the lists inside
     * its argument, {@code zipShortest} pairs two lists, and {@code flatMap} makes any number of
     * elements from each — which is neither the elements nor a count.
     *
     * <p>They put in what the container they read did not hold. Nothing that held of every element
     * still does, and the size can rise; a shape says neither of those.
     *
     * <p>They answer the same elements in a container of another kind. That is true and unsayable:
     * every statement the check makes names the kind it is about — {@code List.length} and
     * {@code List.all}, or {@code Set.size} and {@code Set.contains} — so nothing said of the one is
     * a statement about the other, and a rule between them would carry nothing. A statement that
     * spans kinds is what would have to exist first.
     */
    private static final Set<ValueName> NOTHING_KEPT = Set.of(
            op("Map.keys"), op("Map.toList"), op("Map.fromList"), op("List.groupBy"),
            op("List.concat"), op("List.zipShortest"), op("List.flatMap"),
            op("Map.insert"), op("Set.insert"), op("Map.union"), op("Set.union"),
            op("List.append"), op("Map.updateOrInsert"),
            op("Map.values"), op("Set.toList"), op("Set.fromList"), op("List.indexBy"));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.contains} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    record Carried(int container, Set<Shape> through) {}

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List.all"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.allDistinctBy"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.any"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("List.contains"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Set.contains"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Map.containsKey"), new Carried(1, Set.of(Shape.PERMUTES)));

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, Integer> PROJECTION_OF = Map.of(op("List.allDistinctBy"), 0);

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link Combinators} already answers of any combinator, and how
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

    /** The predicates over a string this says nothing of. Each states something of the characters a
     * string holds in the order it holds them, and what a rule could carry such a statement through
     * is a construction of a container from a container — which a string is not one of, its length
     * being all this names of it. */
    private static final Set<ValueName> NOTHING_SAID_OF_A_STRING = Set.of(
            op("String.contains"), op("String.startsWith"), op("String.endsWith"),
            op("String.matches"));

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

    /** The operations over two numbers that are the function form of no operator: the language
     * writes no {@code min}, {@code max}, {@code floorMod} or {@code compare}, so there is no second
     * spelling for a term to be read as one of. */
    private static final Set<ValueName> NOT_AN_OPERATOR = Set.of(
            op("Int.min"), op("Int.max"), op("Int.floorMod"), op("Int.compare"),
            op("Decimal.min"), op("Decimal.max"));

    /**
     * A question these rules ask of an operation, and what being in its range means.
     *
     * <p>A table with no row for an operation says two things at once: that nothing is true of it,
     * and that nobody looked. Which of the two it is, is what a question's range settles — what an
     * operation is declared to be puts it in range, and an operation in range answers, either with a
     * rule or by being named among the ones there is nothing to say of. So the library gaining an
     * operation is the library asking a question, and it is unanswered until someone answers it.
     * {@code AnOperationTheLibraryGainsIsAnsweredForTest} holds each question to its range.
     */
    enum Question {
        /** What a construction kept of the container it was built from ({@link #BUILT_FROM}). Asked
         * of an operation that answers a container and is given one. A string is not in range: a
         * shape says what became of a container's elements, and of a string this names only its
         * length. */
        BUILT("what it keeps of the container it is built from"),
        /** What a predicate says of a container, and how far that statement travels
         * ({@link #CARRIED}, {@link #EMPTINESS}, {@link #QUANTIFIERS}). */
        PREDICATE("what it says of the container it reads"),
        /** Whether the number it answers is a size the domain can name ({@link #SIZE_CALLS}). */
        SIZE("whether the number it answers is a size"),
        /** Which operator it is the function form of ({@link #OPERATOR_CALLS}). Asked of an operation
         * over two numbers answering a number of the same kind. */
        OPERATOR("which operator it computes");

        private final String asked;

        Question(String asked) {
            this.asked = asked;
        }

        @Override
        public String toString() {
            return asked;
        }
    }

    /** Whether a construction over {@code t} is one whose elements a shape can speak of. */
    private static boolean holdsElements(Type t) {
        return t instanceof Type.ListOf || t instanceof Type.SetOf || t instanceof Type.MapOf;
    }

    /** Whether {@code t} is something the check can name the size of — a container, or a string. */
    private static boolean hasASize(Type t) {
        return holdsElements(t) || t == Type.Prim.STRING;
    }

    /** The questions an operation declared with {@code signature} is in range of. */
    static Set<Question> asked(Prelude.Signature signature) {
        Type result = signature.result();
        if (result == null) {
            return Set.of();
        }
        Set<Question> asked = new LinkedHashSet<>();
        List<Type> params = signature.params();
        if (holdsElements(result) && params.stream().anyMatch(DischargeRules::holdsElements)) {
            asked.add(Question.BUILT);
        }
        if (params.stream().anyMatch(DischargeRules::hasASize)) {
            if (result == Type.Prim.BOOL) {
                asked.add(Question.PREDICATE);
            }
            if (result == Type.Prim.INT) {
                asked.add(Question.SIZE);
            }
        }
        if ((result == Type.Prim.INT || result == Type.Prim.DECIMAL)
                && params.size() == 2 && params.stream().allMatch(result::equals)) {
            asked.add(Question.OPERATOR);
        }
        return asked;
    }

    /** Whether {@code operation} has a rule answering {@code question}. */
    static boolean answers(ValueName operation, Question question) {
        return switch (question) {
            case BUILT -> BUILT_FROM.containsKey(operation);
            case PREDICATE -> CARRIED.containsKey(operation) || EMPTINESS.containsKey(operation);
            case SIZE -> SIZE_CALLS.contains(operation);
            case OPERATOR -> OPERATOR_CALLS.containsKey(operation);
        };
    }

    /** Whether {@code operation} is one of those {@code question} has nothing to say of. */
    static boolean nothingToSay(ValueName operation, Question question) {
        return nothingSaidOf(question).contains(operation);
    }

    /** The operations {@code question} is asked of and has nothing to say of. */
    static Set<ValueName> nothingSaidOf(Question question) {
        return NOTHING_TO_SAY.getOrDefault(question, Set.of());
    }

    private static final Map<Question, Set<ValueName>> NOTHING_TO_SAY = Map.of(
            Question.BUILT, NOTHING_KEPT,
            Question.PREDICATE, NOTHING_SAID_OF_A_STRING,
            Question.OPERATOR, NOT_AN_OPERATOR);

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool.not");

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

    /** The one container {@code e} asks the size of, or null where it is not a size call over one
     * argument. Asked rather than tested, so no reader spells the shape of a size call itself. */
    static Core sizeArgOf(Core e) {
        return e instanceof Core.PreservedCall call && isSize(call.operation())
                && call.args().size() == 1 ? call.args().get(0) : null;
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
