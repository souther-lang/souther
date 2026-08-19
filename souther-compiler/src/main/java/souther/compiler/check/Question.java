package souther.compiler.check;

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
            return Combinators.answered().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return Combinators.answered();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return Combinators.HANDS_ITS_CLOSURE_NOTHING;
        }
    },

    /**
     * Whether it walks a container from a seed through its closure, and where the seed arrives
     * ({@link Reductions}). Asked of an operation given a container, taking a closure that answers
     * what the operation answers and takes a value of that type, beside a plain argument of it —
     * which is the shape a walk from a seed has and is not what makes an operation one. A closure
     * applied once, or applied to something the operation built rather than to the accumulator it
     * carries, is declared the same way.
     *
     * <p>The container is part of the range and not only of the answer. This asks whether an
     * operation walks <em>a container</em>, so one given none is outside it rather than in it with
     * nothing to say — an operation declared {@code ((A) -> A, A) -> A} repeats a step over no
     * elements and is a different question, which nobody has had to ask yet.
     *
     * <p>Beside {@link #COMBINATOR} and not folded into it. What an operation hands its closure is
     * read off the declaration; that it hands it the same closure again with what came back is not,
     * and a range that took the first as an answer for the second would let the second go missing in
     * silence.
     */
    REDUCTION("whether it reduces a container from a seed through its closure") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            Type result = signature.result();
            if (result == null || signature.params().stream().noneMatch(Question::holdsElements)) {
                return false;
            }
            boolean carriesItBack = signature.params().stream().anyMatch(
                    t -> t instanceof Type.FnOf fn && result.equals(fn.result())
                            && fn.params().contains(result));
            return carriesItBack && signature.params().stream().anyMatch(
                    t -> !(t instanceof Type.FnOf) && result.equals(t));
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return Reductions.answered().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return Reductions.answered();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return Reductions.REDUCES_NOTHING;
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
            return DischargeRules.builtOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.builtOperations();
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
            return DischargeRules.carryingOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.carryingOperations();
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
        Set<ValueName> answeredOperations() {
            return DischargeRules.emptinessChecks();
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
        Set<ValueName> answeredOperations() {
            return DischargeRules.quantifiers();
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
            return DischargeRules.projections().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.projections();
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
        Set<ValueName> answeredOperations() {
            return DischargeRules.sizeCalls();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.NOT_A_SIZE;
        }
    },

    /**
     * Whether it answers the order of its two arguments ({@link DischargeRules#decidesOrder}). Asked
     * of an operation answering an {@code Int} from two values of one type — which is what an order
     * is answered from, whatever the values are ordered by.
     */
    ORDER("whether it answers the order of its two arguments") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() == Type.Prim.INT
                    && signature.params().size() == 2
                    && signature.params().get(0).equals(signature.params().get(1));
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.decidesOrder(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.orderings();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.DECIDES_NO_ORDER;
        }
    },

    /**
     * What holds of the number it answers wherever it is called ({@link DischargeRules#boundsOn}).
     * Asked of an operation answering a number from a number: a bound is stated against the arguments,
     * so an operation given none has nothing for a row to bound its result against.
     */
    BOUNDS("what bounds the number it answers") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return isANumber(signature.result())
                    && signature.params().stream().anyMatch(Question::isANumber);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.boundedOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.boundedOperations();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.BOUNDS_NOTHING;
        }
    },

    /**
     * What it states through the measure that counts what it shifted and what it answered apart
     * ({@link DischargeRules#shiftBy}). Asked of an operation answering a value of the kind one of
     * its arguments is, given a number — which is the shape moving a value by an amount has.
     */
    MEASURE("what it states through the measure counting the two apart") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return signature.result() != null && !isANumber(signature.result())
                    && signature.params().contains(signature.result())
                    && signature.params().stream().anyMatch(Question::isANumber)
                    && isCounted(signature.result());
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.shiftingOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.shiftingOperations();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.SHIFTS_BY_NOTHING_MEASURABLE;
        }
    },

    /**
     * Whether it answers one of the values it was given, and in which cases
     * ({@link DischargeRules#chosenBy}). Asked of an operation answering a number from a number: what
     * such an operation answers may be one of its arguments, decided by the arguments.
     */
    CHOICE("whether it answers one of its arguments, and in which cases") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return isANumber(signature.result())
                    && signature.params().stream().anyMatch(Question::isANumber);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.choosingOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.choosingOperations();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.CHOOSES_NOTHING;
        }
    },

    /**
     * Whether the number it answers is a number it was given ({@link DischargeRules#answersItsArgument}).
     * Asked of an operation answering a number from a number, which is the shape a value re-expressed
     * has — the result may be one of the arguments read again rather than a number computed from them.
     */
    FORM("whether the number it answers is one it was given") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return isANumber(signature.result())
                    && signature.params().stream().anyMatch(Question::isANumber);
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.formOperations().contains(operation);
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.formOperations();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return DischargeRules.ANSWERS_NO_ARGUMENT_OF_ITS_OWN;
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
        Set<ValueName> answeredOperations() {
            return DischargeRules.operatorForms();
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

    /** The operations there is a rule about, for the check that a rule answers a question its
     * operation is asked — a rule under a name nothing asks is a rule nothing reaches. */
    abstract Set<ValueName> answeredOperations();

    /** The operations this is asked of and has nothing to say of. */
    abstract Set<ValueName> nothingSaidOf();

    /**
     * The questions an operation declared with {@code signature} is in range of.
     *
     * <p>Each reads the declaration for what it asks about and no more. A declaration that leaves
     * its result to its body — which the library allows a helper with parameters to do — has said
     * nothing about what it answers, so the questions about that are not asked of it; what it hands
     * its closure is a question about its arguments, and is.
     */
    static List<Question> askedOf(Prelude.Signature signature) {
        return List.of(values()).stream().filter(q -> q.asksOf(signature)).toList();
    }

    /** Whether this is asked of the library operation named {@code qualified}. A sugar has no
     * declaration of its own and is asked what the call it becomes is asked: it is that call, with
     * some of its arguments already supplied. */
    boolean asksOfOperation(String qualified) {
        Prelude.Rewrite rewrite = Prelude.rewriteOf(qualified);
        Prelude.PreludeEntry entry =
                Prelude.entry(rewrite == null ? qualified : rewrite.target().qualified());
        return entry != null && asksOf(entry.signature());
    }

    /** Whether a construction over {@code t} is one whose elements a shape can speak of. Read where
     * the rules are bound as well: what a rule about a container may be written over is the same
     * question as what puts an operation in range of one. */
    static boolean holdsElements(Type t) {
        return t instanceof Type.ListOf || t instanceof Type.SetOf || t instanceof Type.MapOf;
    }

    /**
     * Whether the library counts two values of {@code t} apart as a number.
     *
     * <p>What makes moving a value by an amount a question with an answer. A list shortened by three
     * and a string padded to a width are shifts as much as a date a day on is, and neither says
     * anything <em>through a measure</em>, because the library has none that counts two lists or two
     * strings apart — a size counts one of them. So the range is read off the declarations, and the
     * day the library gains such a measure the operations of that kind come into range and are asked.
     */
    private static boolean isCounted(Type t) {
        return Prelude.entries().values().stream().anyMatch(entry -> {
            List<Type> counted = entry.signature().params();
            return isANumber(entry.signature().result()) && counted.size() == 2
                    && counted.get(0).equals(t) && counted.get(1).equals(t);
        });
    }

    /** Whether {@code t} is one of the kinds of number the domain relates arithmetically. Read where
     * the numeric rules are bound as well: what such a rule may be written about is the same question
     * as what puts an operation in range of one. */
    static boolean isANumber(Type t) {
        return t == Type.Prim.INT || t == Type.Prim.DECIMAL;
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
