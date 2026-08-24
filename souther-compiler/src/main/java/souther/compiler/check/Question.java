package souther.compiler.check;

import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.OperationSubject;
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
            return OperationFacts.saysNothingOf(OperationSubject.COMBINATOR);
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

    /**
     * Whether it accumulates what its container holds ({@link Accumulations}). Asked of an operation
     * answering a value of the type one of its container arguments holds: the question is whether
     * that answer is the elements started from an identity and carried through one binary combine
     * over the accumulator and an element, both of the type it answers.
     *
     * <p>The range is read off the shape of the declaration and not off what the answer could be
     * used for. {@code (List<'a>) -> 'a} says of {@code List.sum} exactly what it says of
     * {@code String.concat}: an operation that answers one of the thing it was given many of. Which
     * of those a check can carry as a number is asked after the answer, by the check that needs one
     * — a range drawn where the numeric domain stops would put the library's own reading of
     * {@code concat} out of reach of the question it is an answer to.
     *
     * <p>Beside {@link #REDUCTION} and not folded into it. A reduction is handed its step and its
     * seed as arguments, so what it walks is read off the call; an accumulation is handed neither,
     * and a range that took the one for the other would ask nothing of an operation whose whole
     * meaning is what it does not take.
     */
    ACCUMULATION("whether it accumulates what its container holds, and from what through what") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            Type result = signature.result();
            return result != null && signature.params().stream().anyMatch(
                    t -> holdsElements(t) && result.equals(Terms.elementType(t)));
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return Accumulations.of(operation) != null;
        }

        @Override
        Set<ValueName> answeredOperations() {
            return Accumulations.answered();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return Accumulations.NO_SIMPLE_ACCUMULATION;
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
            return OperationFacts.saysNothingOf(OperationSubject.BUILT);
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
            return OperationFacts.saysNothingOf(OperationSubject.PREDICATE_CARRY);
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
            return OperationFacts.saysNothingOf(OperationSubject.EMPTINESS);
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
            return OperationFacts.saysNothingOf(OperationSubject.QUANTIFICATION);
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
            return OperationFacts.saysNothingOf(OperationSubject.PROJECTION);
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
            return OperationFacts.saysNothingOf(OperationSubject.SIZE);
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
            return OperationFacts.saysNothingOf(OperationSubject.ORDER);
        }
    },

    /**
     * What holds of the number it answers wherever it is called ({@link DischargeRules#boundsOn}).
     * Asked of every operation answering a number.
     *
     * <p>Of the result and not of the arguments. This once asked only where an argument was a number
     * too, on the reasoning that a bound is stated against the arguments and an operation given none
     * has nothing to bound its result against. {@code Int.abs} is the counter-example standing in
     * the same table: its bound names no argument, and a constant end is as much a bound as one an
     * argument decides. What the narrower range cost was every operation counting or reading a value
     * of another kind — a size, the hour of a time — which could then be asked nothing here, so what
     * was true of one was written wherever a reader happened to want it (#1016).
     *
     * <p>A bound that does name an argument is still held to a signature that has one:
     * {@link DischargeRules#holdBound} reads the argument it names, so an operation given no number
     * cannot declare one — which is where that requirement belongs, since it is about a fact and a
     * declaration agreeing rather than about which operations are asked.
     */
    BOUNDS("what bounds the number it answers") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return isANumber(signature.result());
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
            return OperationFacts.saysNothingOf(OperationSubject.BOUNDS);
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
                    && hasAMeasureCountingTwoApart(signature.result());
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
            return OperationFacts.saysNothingOf(OperationSubject.MEASURE);
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
            return OperationFacts.saysNothingOf(OperationSubject.CHOICE);
        }
    },

    /**
     * What it answers, counted, in what its arguments are counted as
     * ({@link DischargeRules#answersAFormOf}). Asked of an operation whose result counts and that
     * was given something that counts, which is the shape a value re-expressed has — the result may
     * be arithmetic over what it was given rather than a number of its own.
     *
     * <p>Counted and not a number, so the dates are in range. {@code Date.daysBetween} answers a
     * number from two values that are not numbers, and {@code Date.addDays} a value that is not one
     * — asked of numbers alone, neither is even a question, and the operations this exists for
     * would have been out of range of it.
     */
    FORM("what it answers, counted, in what its arguments are counted as") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            return countsToANumber(signature.result())
                    && signature.params().stream().anyMatch(Question::countsToANumber);
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
            return OperationFacts.saysNothingOf(OperationSubject.FORM);
        }
    },

    /**
     * What number it computes, and at which result it answers it
     * ({@link DischargeRules#numericResult}). Asked of an operation whose first two arguments are
     * numbers and which answers a number of that kind — as its result, or as one case of the union
     * its result is.
     *
     * <p>The case is in range for the reason the result is. An operation answering {@code Int |
     * DivisionByZero} computes exactly the arithmetic its {@code Int}-answering counterpart does,
     * and the shape of the result says which inputs it declines rather than what it computes; asked
     * only of a bare numeric result, every such operation fell out of range and the arithmetic it
     * computes was readable through no surface (#959).
     */
    NUMERIC_RESULT("what number it computes, and where it answers it") {
        @Override
        boolean asksOf(Prelude.Signature signature) {
            Type number = numberAnsweredBy(signature.result());
            return number != null && signature.params().size() >= 2
                    && number.equals(signature.params().get(0))
                    && number.equals(signature.params().get(1));
        }

        @Override
        boolean answeredFor(ValueName operation) {
            return DischargeRules.numericResult(operation) != null;
        }

        @Override
        Set<ValueName> answeredOperations() {
            return DischargeRules.numericResultOperations();
        }

        @Override
        Set<ValueName> nothingSaidOf() {
            return OperationFacts.saysNothingOf(OperationSubject.NUMERIC_RESULT);
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
    private static boolean hasAMeasureCountingTwoApart(Type t) {
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

    /**
     * Whether values of {@code t} count to a number.
     *
     * <p>Wider than {@link #isANumber} and asked where the arithmetic is over counts rather than
     * over numbers a model wrote: a date is not a number and counts days, so a difference of two of
     * them is a number of days. Asked of {@link Carrier}, which is the one table saying which types
     * have an order with counts under it — a second answer here would be a second table, and a type
     * that is a carrier to one of them and not to the other is what that costs.
     *
     * <p>Asked without the declarations, which is what a reading of the library's own signatures
     * has: {@link Carrier#ofPrimitive} answers where the type settles it and leaves a name
     * unanswered. The names in those signatures are the error unions and {@code RoundingMode}, and
     * a form is written over none of them.
     */
    static boolean countsToANumber(Type t) {
        Carrier carrier = Carrier.ofPrimitive(t);
        return carrier != null && carrier.counts();
    }

    /**
     * The number a result of {@code t} answers — {@code t} itself where it is one, and the number a
     * union carries where exactly one of its cases is a number.
     *
     * <p>Exactly one, and not the first found. A union carrying two numbers would answer its number
     * at two cases, and which of them a rule about the operation was written for is a question the
     * table has no column for — so it is out of range, and stays out until something says which.
     */
    static Type numberAnsweredBy(Type t) {
        if (isANumber(t)) {
            return t;
        }
        if (!(t instanceof Type.Union union)) {
            return null;
        }
        Type found = null;
        for (souther.compiler.types.TypeSymbol member : union.members()) {
            Type.Prim prim = member.primitiveKind();
            if (prim != null && isANumber(prim)) {
                if (found != null) {
                    return null;
                }
                found = prim;
            }
        }
        return found;
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
