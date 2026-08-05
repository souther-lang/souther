package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Set;

/**
 * Everything the checks ask of a standard-library operation, each with the operations it is asked
 * of.
 *
 * <p>A table with no row for an operation says two things at once: that nothing is true of it, and
 * that nobody looked. That is how {@code List.distinctBy} came to be credited by neither the
 * totality check nor the discharge one — a valid recursive helper rejected, a guard that stopped
 * discharging, and nothing said about a missing row. What settles which of the two a silence is, is
 * the range: what an operation is declared to be puts it in range of a question, and an operation in
 * range answers — with a rule, or by being named among the ones there is nothing to say of, with the
 * reason. So the library gaining an operation is the library asking these questions, and each is
 * unanswered until someone answers it.
 *
 * <p>A range is read off the declaration and nothing else, so it holds an operation nobody thought
 * of. Where the answer too is read off the declaration the rule is derived rather than written
 * ({@link Combinators}), and the range is still stated here: a signature the derivation gets nothing
 * out of is a decision, not a gap, and is written down as one.
 *
 * <p>{@code AnOperationTheLibraryGainsIsAnsweredForTest} holds every question to its range, both
 * ways round.
 */
enum Question {

    /** What it hands its closure ({@link Combinators}). Asked of an operation that takes a function:
     * the closure is handed the contents of a container argument, or it is handed nothing a
     * container holds and that is said. */
    COMBINATOR("what it hands its closure") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.params().stream().anyMatch(t -> t instanceof Type.FnOf);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return Combinators.of(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return Combinators.HANDS_ITS_CLOSURE_NOTHING;
        }
    },

    /** What it keeps of the container it was built from ({@link DischargeRules#builtFrom}). Asked of
     * an operation that answers a container and is given one. A string is not in range: a shape says
     * what became of a container's elements, and of a string this names only its length. */
    BUILT("what it keeps of the container it is built from") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return holdsElements(signature.result())
                    && signature.params().stream().anyMatch(Question::holdsElements);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.builtFrom(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOTHING_KEPT;
        }
    },

    /** Where a predicate reads its container and how far its statement travels
     * ({@link DischargeRules#carried}). Asked of an operation that answers a {@code Bool} about a
     * container or a string. */
    PREDICATE_CARRY("where the predicate it states reads its container, and how far that travels") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.BOOL
                    && signature.params().stream().anyMatch(Question::hasASize);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.carried(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOTHING_CARRIED;
        }
    },

    /** Which size call a predicate over one container means, where it means one
     * ({@link DischargeRules#sizeMeantBy}). Asked of a predicate of a single container or string:
     * that is the shape an emptiness check has, and the question is whether this one is that. */
    EMPTINESS("which size call it means") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.BOOL && signature.params().size() == 1
                    && hasASize(signature.params().get(0));
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.sizeMeantBy(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_AN_EMPTINESS_CHECK;
        }
    },

    /** Whether it states its predicate of <em>every</em> element ({@link DischargeRules#isQuantifier}).
     * Asked of an operation that answers a {@code Bool} about a container by applying a predicate to
     * what the container holds — which says nothing yet about how many elements it has to hold of. */
    QUANTIFICATION("whether it states its predicate of every element") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.BOOL
                    && signature.params().stream().anyMatch(Question::hasASize)
                    && signature.params().stream().anyMatch(
                            t -> t instanceof Type.FnOf fn && fn.result() == Type.Prim.BOOL);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.isQuantifier(operation);
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_A_QUANTIFIER;
        }
    },

    /** Which argument is the projection its predicate is stated over
     * ({@link DischargeRules#projectionOf}). Asked of an operation that answers a {@code Bool} about
     * a container by computing something other than a truth value from each element — which is what
     * a projection is. */
    PROJECTION("which argument is the projection it is stated over") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.BOOL
                    && signature.params().stream().anyMatch(Question::hasASize)
                    && signature.params().stream().anyMatch(
                            t -> t instanceof Type.FnOf fn && fn.result() != Type.Prim.BOOL);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.projectionOf(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_STATED_OVER_A_PROJECTION;
        }
    },

    /** Whether the number it answers is a size the domain can name ({@link DischargeRules#isSize}). */
    SIZE("whether the number it answers is a size") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.INT
                    && signature.params().stream().anyMatch(Question::hasASize);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.isSize(operation);
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_A_SIZE;
        }
    },

    /** Which operator it is the function form of ({@link DischargeRules#operator}). Asked of an
     * operation over two numbers answering a number of the same kind. */
    OPERATOR("which operator it computes") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            Type result = signature.result();
            return (result == Type.Prim.INT || result == Type.Prim.DECIMAL)
                    && signature.params().size() == 2
                    && signature.params().stream().allMatch(result::equals);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.operator(operation) != null;
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_AN_OPERATOR;
        }
    };

    private final String asked;

    Question(String asked) {
        this.asked = asked;
    }

    /** Whether an operation declared with {@code signature} is one this is asked of. */
    abstract boolean asksOf(Prelude.Signature signature);

    /** Whether {@code operation} has a rule answering this. */
    abstract boolean answeredFor(ValueName operation);

    /** The operations this is asked of and has nothing to say of. */
    abstract Set<ValueName> nothingSaidOf();

    /** The questions an operation declared with {@code signature} is in range of. A declaration that
     * leaves its result to its body is in range of nothing: what these ask about is what it answers,
     * and it has not said. */
    static List<Question> askedOf(Prelude.Signature signature) {
        if (signature.result() == null) {
            return List.of();
        }
        return List.of(values()).stream().filter(q -> q.asksOf(signature)).toList();
    }

    /** Whether a construction over {@code t} is one whose elements a shape can speak of. */
    private static boolean holdsElements(Type t) {
        return t instanceof Type.ListOf || t instanceof Type.SetOf || t instanceof Type.MapOf;
    }

    /** Whether {@code t} is something the check can name the size of — a container, or a string. */
    private static boolean hasASize(Type t) {
        return holdsElements(t) || t == Type.Prim.STRING;
    }

    @Override
    public String toString() {
        return asked;
    }
}
