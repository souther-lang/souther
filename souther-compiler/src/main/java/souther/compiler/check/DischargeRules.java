package souther.compiler.check;

import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.Cardinality;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.ElementShape;

import souther.compiler.semantics.ArgumentRef;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation), and what each guarantees of what it answers
 * (spec §invariant-discharge-guarantees).
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
 *
 * <p>A rule answers a call, not a position in one. Which argument it reads is written as {@link ArgumentRef}
 * and settled here, so no reader turns a number back into an argument and none has to ask whether the
 * number was one this call has. What makes that safe is the binding below: every row is held to the
 * declaration it was written for before any of them is read.
 */
final class DischargeRules {

    /** The operation {@code name} of the library module published as {@code alias}, as what a name
     * reaching it denotes. Written as the two values it is, so that a row here says which library it
     * is about without a reader splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two.
     *
     * <p>Shared with the partition, which draws a boundary on the same calls ({@link
     * NumericMeasures}). Two lists would let a rule be discharged here and reported as one the model
     * does not state there. */
    private static final Set<ValueName> SIZE_CALLS = NumericMeasures.calls();

    /** The argument the signature already says the elements come from, where the operation takes a
     * closure at all — so a rule about such an operation writes no position of its own. */
    private static final ArgumentRef CONTAINER = new ArgumentRef.TheContainer();

    /** The closure itself, for a rule stated over what the closure answers. */
    private static final ArgumentRef CLOSURE = new ArgumentRef.TheClosure();

    /** The argument at {@code position}, for an operation whose signature does not say which one it
     * is: one that takes no closure, or one given two containers. */
    private static ArgumentRef at(int position) {
        return new ArgumentRef.At(position);
    }


    /** The container {@code call} built its result from, and what the building kept of it. */
    record Source(Core container, ElementShape shape, Cardinality size) {}

    /**
     * The containers a construction's result is never smaller than.
     *
     * <p>Written on its own and not as a {@link ElementShape}, because none of these establishes an element
     * relation to a single source that a shape states. It is not that they keep nothing:
     * {@code List.append(a, b)} keeps every element of both, and holds neither {@code a}'s alone nor
     * {@code b}'s, so neither of the two is what it was built from; an insert puts in an element or
     * an entry the container it read did not hold. The cardinality is a separate fact and survives
     * either way — which is why these sat among the constructions nothing is known of, their bound
     * discarded with an element rule that was never the same statement.
     *
     * <p>No more than the bound. A union answers one of what both sides hold and an insert of
     * something already there adds nothing, so neither answers the sum of what it read; appending
     * does, and stating it for that one alone would be a second rule for one operation. The bound is
     * what they share, and it is what a lower-bound invariant asks for.
     */
    private static final Map<ValueName, List<ArgumentRef>> NO_SMALLER_THAN = Map.of(
            op("List", "append"), List.of(at(0), at(1)),
            op("Set", "union"), List.of(at(0), at(1)),
            op("Map", "union"), List.of(at(0), at(1)),
            op("Set", "insert"), List.of(at(1)),
            op("Map", "insert"), List.of(at(2)));

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
     * still does, which is what a shape would have had to say. How many there are is said instead by
     * {@link #NO_SMALLER_THAN}, which those of them whose result is never smaller than a source it
     * names are in.
     *
     * <p>They answer the same elements in a container of another kind. That is true and unsayable:
     * every statement the check makes names the kind it is about — {@code List.length} and
     * {@code List.all}, or {@code Set.size} and {@code Set.contains} — so nothing said of the one is
     * a statement about the other, and a rule between them would carry nothing. A statement that
     * spans kinds is what would have to exist first.
     */
    static final Set<ValueName> NOTHING_KEPT = Set.of(
            op("Map", "keys"), op("Map", "toList"), op("Map", "fromList"), op("List", "groupBy"),
            op("List", "concat"), op("List", "zipShortest"), op("List", "flatMap"),
            op("Map", "insert"), op("Set", "insert"), op("Map", "union"), op("Set", "union"),
            op("List", "append"), op("Map", "updateOrInsert"),
            op("Map", "values"), op("Set", "toList"), op("Set", "fromList"), op("List", "indexBy"));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.contains} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    record Carried(ArgumentRef container, Set<ElementShape> through) {}

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List", "all"), new Carried(CONTAINER, Set.of(ElementShape.PERMUTES, ElementShape.SUBSET)),
            op("List", "allDistinctBy"), new Carried(CONTAINER, Set.of(ElementShape.PERMUTES, ElementShape.SUBSET)),
            op("List", "any"), new Carried(CONTAINER, Set.of(ElementShape.PERMUTES)),
            op("List", "contains"), new Carried(at(1), Set.of(ElementShape.PERMUTES)),
            op("Set", "contains"), new Carried(at(1), Set.of(ElementShape.PERMUTES)),
            op("Map", "containsKey"), new Carried(at(1), Set.of(ElementShape.PERMUTES)));

    /** Where a predicate reads its container at a call, and how far its statement travels. */
    record Carrying(Core.PreservedCall stated, ArgumentRef at, Set<ElementShape> through) {

        Core container() {
            return CallArguments.of(at, stated);
        }

        /** {@code call} — a call to the same operation — with the container it reads replaced. */
        Core.PreservedCall over(Core.PreservedCall call, Core container) {
            if (!call.operation().equals(stated.operation())) {
                throw new IllegalStateException("a rule read for " + stated.operation()
                        + " was asked to rewrite a call to " + call.operation());
            }
            return CallArguments.replacedIn(at, call, container);
        }
    }

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, ArgumentRef> PROJECTION_OF =
            Map.of(op("List", "allDistinctBy"), CLOSURE);

    /** The projection a predicate at a call is stated over, as the block it answers with. */
    record Projection(Core.PreservedCall stated, ArgumentRef at, Core.Block projection) {

        /** The call this was read for, stated over {@code value} instead. */
        Core.PreservedCall over(Core value) {
            return CallArguments.replacedIn(at, stated, value);
        }
    }

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link Combinators} already answers of any combinator, and how
     * far the statement travels is what {@link #carried} already answers of any predicate — so a
     * quantifier is the name and nothing else. {@code List.all} is the only one the library has. */
    private static final Set<ValueName> QUANTIFIERS = Set.of(op("List", "all"));

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property but about what a predicate <em>says</em>: {@code List.isEmpty(xs)} and
     * {@code List.length(xs) == 0} are one statement, so a guard writing either discharges a clause
     * writing the other. Without it the two would be unrelated, which is an accident of which one the
     * author reached for. */
    private static final Map<ValueName, ValueName> EMPTINESS = Map.of(
            op("List", "isEmpty"), op("List", "length"),
            op("Set", "isEmpty"), op("Set", "size"),
            op("Map", "isEmpty"), op("Map", "size"),
            op("String", "isEmpty"), op("String", "length"));

    /** The predicates whose statement this carries nowhere. A predicate over a string states
     * something of the characters it holds in the order it holds them, and what would carry such a
     * statement is a construction of a container from a container — which a string is not one of,
     * its length being all this names of it. An emptiness check states a size, which travels as a
     * size does ({@link #EMPTINESS}) and not as a property of elements. */
    static final Set<ValueName> NOTHING_CARRIED = Set.of(
            op("String", "contains"), op("String", "startsWith"), op("String", "endsWith"),
            op("String", "matches"),
            op("List", "isEmpty"), op("Set", "isEmpty"), op("Map", "isEmpty"), op("String", "isEmpty"));

    /** The predicates of a single container that are not emptiness checks. The library has none:
     * every one-argument predicate it declares over a container or a string is one, and one that was
     * not would be named here with what it says instead. */
    static final Set<ValueName> NOT_AN_EMPTINESS_CHECK = Set.of();

    /** The predicates that apply a predicate to what a container holds without stating it of every
     * element. {@code List.any} states it of some, so what it says of the container says nothing
     * about the element a closure is handed. */
    static final Set<ValueName> NOT_A_QUANTIFIER = Set.of(op("List", "any"));

    /** The predicates that compute something other than a truth value from each element and are not
     * stated over it. The library has none: {@code allDistinctBy} is the only such predicate and its
     * projection is its closure's answer. */
    static final Set<ValueName> NOT_STATED_OVER_A_PROJECTION = Set.of();

    /** The numbers answered about a container that are not one of its sizes. The library has none:
     * every {@code Int} it answers about a container is how many it holds. */
    static final Set<ValueName> NOT_A_SIZE = Set.of();

    /**
     * The operations answering a number this bounds nothing of, in two groups.
     *
     * <p>Their result is not bounded by their arguments at all. The arithmetic and its function forms
     * answer a number that may be anywhere, and what relates it to the operands is that it <em>is</em>
     * the operands' arithmetic, which a term already reads ({@link #NUMERIC_RESULTS}). A comparison
     * answers a sign, and what that sign says is the order it decides ({@link #ORDERS}) rather than a
     * range it lies in.
     *
     * <p>Their result is one of the arguments, decided by the arguments. A bound on such a result is
     * what {@link #CHOOSES} derives from the case it is in — stating it here as well would be one
     * operation answering to two tables, and the two would come apart the day the library changes
     * which argument it answers.
     *
     * <p>{@code Decimal.round} answers a value at another scale, which is a bound of a shape a row
     * cannot state: how far it moved depends on the scale it was handed. {@code Decimal.fromInt}
     * answers the number it was given, which {@link #ANSWERS_ITS_ARGUMENT} states as the stronger
     * thing it is — the two values are one, not one within reach of the other.
     */
    static final Set<ValueName> BOUNDS_NOTHING = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"),
            op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
            op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp"),
            op("Decimal", "fromInt"), op("Decimal", "round"));

    /** The operations that move a value by an amount the measures this has cannot count. A month and
     * a year are not a fixed number of days, so a date shifted by either stands at a distance no rule
     * here can write. */
    static final Set<ValueName> SHIFTS_BY_NOTHING_MEASURABLE = Set.of(
            op("Date", "addMonths"), op("Date", "addYears"));

    /** A relation between two arguments: {@code left rel right}. What a case of a piecewise
     * definition is reached under, written in the arguments the operation was given and in nothing
     * else. */
    record ArgumentsStand(ArgumentRef left, Rel rel, ArgumentRef right) {}

    private static ArgumentsStand where(ArgumentRef left, Rel rel, ArgumentRef right) {
        return new ArgumentsStand(left, rel, right);
    }

    /** One case of an operation's definition: the argument it answers there, and what holds of the
     * arguments where it does. */
    record Choice(ArgumentRef answers, List<ArgumentsStand> given) {}

    private static Choice answers(ArgumentRef argument, ArgumentsStand... given) {
        return new Choice(argument, List.of(given));
    }

    /**
     * An operation's definition, as the cases it is written in.
     *
     * <p>The list is exhaustive: the conditions of its cases cover everything the operation can be
     * given, so what holds in every case holds of the result. That is the whole of what makes a
     * reading of these sound, and it is a claim about the list rather than about any row in it — a
     * case left out does not make the others wrong, it makes a clause provable that the values can
     * fail. So the cases are written as the library writes them, in the order it writes them, and
     * each is held to a program that reaches it.
     */
    record Choices(List<Choice> cases) {}

    private static Choices choices(Choice... cases) {
        return new Choices(List.of(cases));
    }

    /**
     * The operations that answer one of the values they were given, as the cases they are defined in.
     *
     * <p>Each is the library's own definition read back: {@code min(a, b)} is {@code a} where
     * {@code a < b} and {@code b} otherwise, and {@code clamp(lo, hi, n)} is written as a chain of
     * two conditions, so the second and third cases carry the denial of what stands before them.
     * Carrying it is not tidiness — {@code clamp} does not ask that {@code lo} be below {@code hi},
     * and where it is not, the case that answers {@code hi} is reached with {@code n} above
     * {@code lo}. A rule that said the result is between the two would prove a clause the values
     * fail.
     *
     * <p>Stated here rather than as bounds on the result ({@link #BOUNDS_ON_THE_RESULT}) because
     * what these answer depends on the arguments, and a bound that does not may not be written for
     * them. The bounds a case gives — a smaller of two is no greater than either — follow from the
     * case and are derived where the cases are read, so they are not a second table to keep in step
     * with this one.
     *
     * <p>Read through {@link #chosenBy} in one place ({@link Choice}), which turns a case into an arm
     * written in the values a call was given. A reader wanting the cases asks there and is never
     * handed a row: what a row names is an argument of an operation, and a second reading of that is
     * a second answer to keep in step.
     */
    private static final Map<ValueName, Choices> CHOOSES = Map.of(
            op("Int", "min"), choices(
                    answers(at(0), where(at(0), Rel.LT, at(1))),
                    answers(at(1), where(at(0), Rel.GE, at(1)))),
            op("Decimal", "min"), choices(
                    answers(at(0), where(at(0), Rel.LT, at(1))),
                    answers(at(1), where(at(0), Rel.GE, at(1)))),
            op("Int", "max"), choices(
                    answers(at(0), where(at(0), Rel.GT, at(1))),
                    answers(at(1), where(at(0), Rel.LE, at(1)))),
            op("Decimal", "max"), choices(
                    answers(at(0), where(at(0), Rel.GT, at(1))),
                    answers(at(1), where(at(0), Rel.LE, at(1)))),
            op("Int", "clamp"), choices(
                    answers(at(0), where(at(2), Rel.LT, at(0))),
                    answers(at(1), where(at(2), Rel.GE, at(0)), where(at(2), Rel.GT, at(1))),
                    answers(at(2), where(at(2), Rel.GE, at(0)), where(at(2), Rel.LE, at(1)))),
            op("Decimal", "clamp"), choices(
                    answers(at(0), where(at(2), Rel.LT, at(0))),
                    answers(at(1), where(at(2), Rel.GE, at(0)), where(at(2), Rel.GT, at(1))),
                    answers(at(2), where(at(2), Rel.GE, at(0)), where(at(2), Rel.LE, at(1)))));

    /**
     * The operations answering a number that answer none of their arguments back, in three groups.
     *
     * <p>They compute a new number. The arithmetic and its function forms are this: what
     * {@code a + b} answers is neither {@code a} nor {@code b}, whatever they are.
     *
     * <p>They answer something about the arguments. {@code compare} answers a sign, {@code floorMod}
     * a remainder, {@code abs} a distance, {@code toInt} the whole number a value rounds to, and
     * {@code round} a value at another scale — none of which is one of the values handed in, though
     * each of the last four is one where the argument already had that shape. That the answer
     * <em>can</em> be an argument is not what this asks: a case is one the operation is defined by,
     * and reading a coincidence as a case would state a condition the definition does not have.
     *
     * <p>{@code Decimal.fromInt} answers the number it was given in another type, which
     * {@link souther.compiler.semantics.OperationFact.AnswersItsArgument} states unconditionally. A
     * case would put a condition on a statement that has none.
     */
    static final Set<ValueName> CHOOSES_NOTHING = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"), op("Int", "floorMod"),
            op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"), op("Decimal", "round"),
            op("Decimal", "fromInt"));


    /**
     * The operations answering a number from a number that answer none of them back, in three groups.
     *
     * <p>They compute a new number from their operands. The arithmetic and its function forms are
     * this, and what they answer is already read as arithmetic over the operands themselves
     * ({@link #NUMERIC_RESULTS}) rather than as one of them.
     *
     * <p>They answer something about the arguments rather than one of them: {@code compare} a sign,
     * {@code floorMod} a remainder, {@code abs} a distance with the sign dropped, {@code toInt} the
     * whole number a value rounds to, {@code round} a value at another scale. What such a result is
     * bounded by is {@link #BOUNDS_ON_THE_RESULT}, which is a different statement from being a value
     * that was already there.
     *
     * <p>They answer one of their arguments, and which one depends on the arguments. That is
     * {@link #CHOOSES}, and a rule that dropped the condition would say {@code Int.min(a, b)} is
     * {@code a}.
     */
    static final Set<ValueName> ANSWERS_NO_ARGUMENT_OF_ITS_OWN = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"), op("Int", "floorMod"),
            op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"), op("Decimal", "round"),
            op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
            op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp"));

    /** Where an operation answers a number: as its result, or as one case of the union its result
     * is. Two positions and not two tables — what an operation computes is one question, and the
     * surface a value arrives on is what {@link NumericMeaning} exists to stop deciding rules. */
    sealed interface Answered {

        /** The result itself is the number. */
        record Directly() implements Answered {}

        /**
         * One case of the union carries it, told apart by what that case carries.
         *
         * <p>By the type and not by the name of the case. What a primitive-headed case binds is the
         * primitive itself (spec §primitive-arm), so the type is what the arm's pattern already
         * settled and a name would be a second spelling of it.
         */
        record InTheCaseCarrying(Type carried) implements Answered {}
    }

    /**
     * What number an operation computes, given its arguments.
     *
     * <p>A method rather than an enum the reader switches on: what a row says is which arithmetic
     * this is, and the arithmetic is a {@link NumericMeaning}, so a row answers with one. A reader
     * that turned a tag back into a meaning would be a second place deciding which arguments go
     * where.
     */
    sealed interface Computes {

        /** The number a call handing over {@code args} computes. */
        NumericMeaning of(List<Core> args);

        /**
         * What each argument has to be for this row to be about the operation, in the order the
         * operation takes them.
         *
         * <p>The row reads arguments by position — the second one is what it divides by — so the
         * positions are what a declaration can drift out from under. A count alone does not catch
         * it: an operation whose scale and mode swapped places still takes four arguments, and what
         * would change is only which of them this reads as the scale. Written here and held to the
         * declaration before any call is read ({@link #bindNumericResults}).
         */
        List<Reads> reads();

        /** Arithmetic the language also writes as an operator. The two reach one kernel in one
         * argument order — {@code Int.add} is {@code IntMath.addExact}, which is what {@code +}
         * emits — so they compute one value and are read as one term. */
        record TheOperator(BinOp op) implements Computes {
            @Override
            public NumericMeaning of(List<Core> args) {
                return new NumericMeaning.Operator(op, args.get(0), args.get(1));
            }

            @Override
            public List<Reads> reads() {
                return TWO_OF_ITS_OWN;
            }
        }

        /** A division of whole numbers truncated toward zero — the quotient {@code /} answers,
         * reached where the divisor is one the model admits as zero. */
        record ATruncatingQuotient() implements Computes {
            @Override
            public NumericMeaning of(List<Core> args) {
                return new NumericMeaning.TruncatingQuotient(args.get(0), args.get(1));
            }

            @Override
            public List<Reads> reads() {
                return TWO_OF_ITS_OWN;
            }
        }

        /** What that division leaves. The language writes no operator for it. */
        record ATruncatingRemainder() implements Computes {
            @Override
            public NumericMeaning of(List<Core> args) {
                return new NumericMeaning.TruncatingRemainder(args.get(0), args.get(1));
            }

            @Override
            public List<Reads> reads() {
                return TWO_OF_ITS_OWN;
            }
        }

        /** A division of decimals rounded where the call says to round it. Not {@code /} over
         * {@code Decimal}, which rounds at a significant-digit precision the run time sets. */
        record AQuotientRoundedToAScale() implements Computes {
            @Override
            public NumericMeaning of(List<Core> args) {
                return new NumericMeaning.RoundedQuotient(
                        args.get(0), args.get(1), args.get(2), args.get(3));
            }

            @Override
            public List<Reads> reads() {
                return List.of(Reads.THE_NUMBER_IT_ANSWERS, Reads.THE_NUMBER_IT_ANSWERS,
                        Reads.A_SCALE, Reads.A_ROUNDING_MODE);
            }
        }
    }

    /** Two numbers of the kind the operation answers, which is what all the arithmetic over a pair
     * of them takes. */
    private static final List<Reads> TWO_OF_ITS_OWN =
            List.of(Reads.THE_NUMBER_IT_ANSWERS, Reads.THE_NUMBER_IT_ANSWERS);

    /**
     * What one argument of a numeric operation is, as far as a row about it needs to know.
     *
     * <p>Not a type. What the row needs held is the argument's <em>part</em> in the arithmetic, and
     * two of the three answer differently for different operations — the number an operation
     * answers is {@code Int} for one and {@code Decimal} for another, and a row saying "a number"
     * would be held to neither.
     */
    enum Reads {

        /** A number of the kind the operation answers. */
        THE_NUMBER_IT_ANSWERS,

        /** How many places the answer is rounded to, which is a count and so an {@code Int}. */
        A_SCALE,

        /** Which way it rounds there. */
        A_ROUNDING_MODE;

        /** Whether an argument declared {@code at} is this, for an operation answering
         * {@code answered}. */
        boolean heldBy(Type at, Type answered) {
            return switch (this) {
                case THE_NUMBER_IT_ANSWERS -> at.equals(answered);
                case A_SCALE -> at == Type.Prim.INT;
                case A_ROUNDING_MODE -> at instanceof Type.Ref(souther.compiler.types.TypeSymbol name)
                        && name.module().equals(souther.compiler.types.TypeSymbol.RUNTIME)
                        && name.name().equals("RoundingMode");
            };
        }
    }

    /**
     * Which case of the union came back, as a condition on what the operation was given.
     *
     * <p>What a union-answering operation's other case <em>means</em>. {@code Int.divide} comes back
     * as {@code DivisionByZero} exactly where the divisor is zero, and that is one fact with two
     * readings: an arm taking that case has established the condition, and an arm taking the number
     * has established its denial. Written once as the condition rather than twice as two rules, so
     * the two cannot come apart.
     *
     * <p>About which case came back and not about whether a number was answered, which are two
     * things. {@code Int.divide} answers no number for the one pair whose quotient no {@code Int}
     * holds either — it aborts (spec §stdlib-int), and an abort comes back as no case at all, so no
     * arm is reached and there is nothing for a condition to say. A row that named the overflow here
     * would put it on the {@code DivisionByZero} arm, which is a fact that arm has not established.
     * What is written down is the case selection, and it is exactly right for that.
     *
     * <p>Declared whatever the numeric domain can hold of it. That a divisor is not zero is a
     * disequality, which a domain reasoning in ranges reads little from — and what an operation
     * guarantees is not decided by what a reader does with it. Written down where it is true, it is
     * read by whatever can read it and by whatever comes to be able to.
     *
     * @param argument which argument the condition is about
     * @param op       how it stands to {@code than}
     * @param than     the number it stands against
     */
    record TheOtherCaseWhen(ArgumentRef argument, BinOp op, long than) {}

    /**
     * What an operation computes, where it answers it, and when it answers nothing.
     *
     * @param unless the condition under which the union comes back as a case other than the
     *               number's, or null for an operation whose result is the number itself
     */
    record NumericResult(Answered at, Computes computes, TheOtherCaseWhen unless) {}

    /**
     * The number each operation computes, and the result it answers it at.
     *
     * <p>What the table answers is which arithmetic an operation is, and not which operator it is
     * the function form of. The narrower question left every operation answering {@code Int |
     * DivisionByZero} out of the table for the shape of its result, and the arithmetic it computed
     * unreadable through the only surface an author has when the divisor is not a literal they can
     * argue about (#959). The result position is a column here rather than a second table, because
     * an operation computing a quotient computes one whether the zero divisor is an abort or a case.
     *
     * <p>{@code Decimal.divide} states its scale and its mode, so the number it computes is not the
     * one {@code /} over {@code Decimal} computes: that operator rounds to a significant-digit
     * precision the run time sets (spec §stdlib-decimal). The two are different arithmetic and are
     * two rows' worth of meaning, not one — and the operator's is a row nothing writes, since it is
     * the operator and reaches {@link NumericMeaning.Operator} where it stands.
     */
    private static final Map<ValueName, NumericResult> NUMERIC_RESULTS = Map.of(
            op("Int", "add"), directly(new Computes.TheOperator(BinOp.ADD)),
            op("Int", "subtract"), directly(new Computes.TheOperator(BinOp.SUB)),
            op("Int", "multiply"), directly(new Computes.TheOperator(BinOp.MUL)),
            op("Decimal", "add"), directly(new Computes.TheOperator(BinOp.ADD)),
            op("Decimal", "subtract"), directly(new Computes.TheOperator(BinOp.SUB)),
            op("Decimal", "multiply"), directly(new Computes.TheOperator(BinOp.MUL)),
            op("Int", "divide"),
                    inTheCaseCarrying(Type.INT, new Computes.ATruncatingQuotient(), byZero()),
            op("Int", "truncatingRemainder"),
                    inTheCaseCarrying(Type.INT, new Computes.ATruncatingRemainder(), byZero()),
            op("Decimal", "divide"),
                    inTheCaseCarrying(Type.DECIMAL, new Computes.AQuotientRoundedToAScale(),
                            byZero()));

    private static NumericResult directly(Computes computes) {
        return new NumericResult(new Answered.Directly(), computes, null);
    }

    private static NumericResult inTheCaseCarrying(Type carried, Computes computes,
                                                   TheOtherCaseWhen unless) {
        return new NumericResult(new Answered.InTheCaseCarrying(carried), computes, unless);
    }

    /** The condition every division comes back as {@code DivisionByZero} under. */
    private static TheOtherCaseWhen byZero() {
        return new TheOtherCaseWhen(at(1), BinOp.EQ, 0);
    }

    /**
     * The operations answering a number that compute no arithmetic of their own, in three groups.
     *
     * <p>They answer one of the values they were given. {@code min}, {@code max} and {@code clamp}
     * are this, and which one they answer is {@link #CHOOSES}. Stating it here as well would be one
     * operation answering to two tables.
     *
     * <p>They answer something about the arguments that is not arithmetic over them: {@code compare}
     * answers a sign, which is the order it decides ({@link #ORDERS}). {@code Decimal.compare} is
     * not here: it answers an {@code Int} from two {@code Decimal}s, so the number it answers is not
     * the kind its arguments are and this is not asked of it.
     *
     * <p>{@code floorMod} answers a remainder and is here all the same. It is the remainder of a
     * <em>floored</em> division, and the language writes no floored divide for its quotient to be
     * read as — so what is known of it is the bound {@link #BOUNDS_ON_THE_RESULT} states, and
     * relating it to its dividend is a rule nothing here has. Its truncating counterpart is
     * {@code truncatingRemainder}, which is in the table above.
     */
    static final Set<ValueName> COMPUTES_NO_ARITHMETIC_OF_ITS_OWN = Set.of(
            op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
            op("Int", "floorMod"), op("Int", "compare"),
            op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp"));


    /**
     * The operations answering a number from two values of one type whose sign is not their order.
     *
     * <p>Arithmetic and a choice between two values are not orders at all: what {@code Int.subtract}
     * answers has the sign of one and says how far apart they are as well, which is what a term
     * already reads it as, and {@code min} answers one of the two rather than anything about the
     * pair. {@code DateTime.minutesBetween} is the one that has to be told apart: it counts whole
     * minutes, so a zero says the two are less than a minute apart rather than that they are equal,
     * and a non-negative count does not say the second is not the earlier. Its strict signs do state
     * the order, and a rule that holds for four of the six relations is not this one.
     */
    static final Set<ValueName> DECIDES_NO_ORDER = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Int", "min"), op("Int", "max"), op("Int", "floorMod"),
            op("DateTime", "minutesBetween"));

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool", "not");

    /** The operations each table has a rule for. What is asked of them is {@link Question}'s to
     * settle; these are so it can hold a rule to being one an operation is asked for. */
    static Set<ValueName> builtOperations() {
        return Bound.buildsItsResultFrom();
    }

    static Set<ValueName> carryingOperations() {
        return Bound.CARRIERS.keySet();
    }

    /**
     * The kinds of container the library builds, each with the shape the building has — {@code
     * "List.SUBSET"}, {@code "Map.MAPS"}.
     *
     * <p>For the test that holds a carrying rule to every shape. A shape no construction of a kind
     * has is a cell no program can be written for, and which cells those are is the library's to say:
     * a set holds its elements in no order, so nothing permutes one, and that stops being true the day
     * an operation says otherwise. Read off the building table, whose every row already answers to a
     * program that fires it.
     */
    static Set<String> constructionKinds() {
        Set<String> kinds = new LinkedHashSet<>();
        Bound.buildsItsResultFrom().forEach(operation -> {
            BuiltFrom built = Bound.buildsItsResultFrom(operation);
            Prelude.PreludeEntry entry = operation instanceof ValueName.Stdlib library
                    ? Prelude.entry(library.qualified()) : null;
            String kind = entry == null ? null : kindOf(entry.signature().result());
            if (kind != null) {
                kinds.add(kind + "." + built.shape());
            }
        });
        return kinds;
    }

    /** What a container type is a container of, as the namespace its operations are written under. */
    private static String kindOf(Type built) {
        if (built instanceof Type.ListOf) {
            return "List";
        }
        if (built instanceof Type.SetOf) {
            return "Set";
        }
        return built instanceof Type.MapOf ? "Map" : null;
    }

    static Set<ValueName> emptinessChecks() {
        return EMPTINESS.keySet();
    }

    static Set<ValueName> quantifiers() {
        return QUANTIFIERS;
    }

    static Set<ValueName> projections() {
        return Bound.PROJECTIONS.keySet();
    }

    static Set<ValueName> sizeCalls() {
        return SIZE_CALLS;
    }

    static Set<ValueName> numericResultOperations() {
        return NUMERIC_RESULTS.keySet();
    }

    static Set<ValueName> orderings() {
        return Bound.statesTheOrder();
    }

    static Set<ValueName> formOperations() {
        return Bound.answersItsArgument();
    }

    /** Those of them the read-through table has, by name, for the test that holds each to a
     * construction it discharges. */
    static Set<String> formNames() {
        Set<String> names = new LinkedHashSet<>();
        formOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> boundedOperations() {
        return Bound.boundsOnTheResult();
    }

    static Set<ValueName> choosingOperations() {
        return Bound.CHOICES.keySet();
    }

    /** Those of them the choosing table has, by name, for the test that holds each case to a
     * program that reaches it. */
    static Set<String> choosingNames() {
        Set<String> names = new LinkedHashSet<>();
        choosingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> shiftingOperations() {
        return Bound.shiftsBy();
    }

    /** Those of them the shifting table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> shiftingNames() {
        Set<String> names = new LinkedHashSet<>();
        shiftingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    /** What {@code e} states through a measure, or null where it is not a shift this has a rule
     * about. */
    static souther.compiler.semantics.OperationFact.ShiftsBy shiftBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.shiftsBy(call.operation()) : null;
    }

    /** Whether {@code operation} counts what two values stand apart by — the other side of the row a
     * shift is written in, read off that row rather than listed again. A measure named in a second
     * place is a measure the day somebody adds a shift and updates one of them. */
    static boolean isAMeasure(ValueName operation) {
        return Bound.measures().contains(operation);
    }

    /** The cases {@code e} is defined in, or null where it is not a call to an operation that
     * answers one of the values it was given. */
    static Choices chosenBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.CHOICES.get(call.operation()) : null;
    }

    /**
     * The bounding table's rows, by the name of the operation each is about — one entry per row, so
     * an operation bounded at both ends appears twice.
     *
     * <p>For the test that holds each row to a construction it discharges. By row and not by
     * operation: one program needs one of an operation's rows, so a set of names would be satisfied
     * by a rule that had been written for one end and never fired for the other.
     */
    static List<String> boundedRows() {
        List<String> rows = new ArrayList<>();
        for (ValueName operation : Bound.boundsOnTheResult()) {
            Bound.boundsOnTheResult(operation).forEach(bound -> rows.add(operation.toString()));
        }
        return rows;
    }

    /**
     * The bounds {@code call}'s result has here: the operation's rows, less those whose condition on
     * the arguments this call does not meet.
     *
     * @param constant what an argument reads as, or null where it reads as no constant. Asked of the
     *                 caller because what a value is read as is the reading's answer and not a
     *                 property of the syntax at the call.
     */
    static List<souther.compiler.semantics.ResultBound> boundsOn(Core.PreservedCall call,
                                      Function<Core, BigDecimal> constant) {
        List<souther.compiler.semantics.ResultBound> rows =
                Bound.boundsOnTheResult(call.operation());
        List<souther.compiler.semantics.ResultBound> holding = new ArrayList<>(rows.size());
        for (souther.compiler.semantics.ResultBound row : rows) {
            if (CallArguments.holds(row.provided(), call, constant)) {
                holding.add(row);
            }
        }
        return holding;
    }

    /** The argument whose number {@code e} answers, or null where it is not a call this reads as one
     * of its arguments. The value itself and not a term for it: what it is read as is the form the
     * argument already has, which is the caller's to build. */
    static Core answersItsArgument(Core e) {
        if (!(e instanceof Core.PreservedCall call)) {
            return null;
        }
        ArgumentRef reads = Bound.answersItsArgument(call.operation());
        return reads == null ? null : CallArguments.of(reads, call);
    }

    /** Those of them the building table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> builtNames() {
        Set<String> names = new LinkedHashSet<>();
        builtOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    /**
     * The tables, held to the declarations they were written for.
     *
     * <p>A row names an argument of an operation, and what an operation's arguments are is the
     * library's to say. Where the two disagree there is nothing to be done at a call — the rule is
     * about an argument that is not there, or is not the kind of thing the rule is about — so it is
     * said here, once, before any call is read, rather than met as a missing answer at whichever
     * reader arrives first.
     *
     * <p>Every row of every table, not the row a call happens to reach: a rule that disagrees with a
     * declaration is wrong whether or not a program calls it, and finding out when one does is the
     * same silence deferred.
     *
     * <p>A numeric rule names no part of what an operation hands a closure, since such an operation
     * hands none, so it is bound with no derived position for a written one to be held against.
     *
     * <p>Read on the first ask and not before, as {@link Combinators} and {@link Preserved} are: what
     * this requires of the library is required of a check that reads these rules, and a checker that
     * reads none must not be held to it.
     */
    private static final class Bound {

        private static Set<ValueName> buildsItsResultFrom() {
            return souther.compiler.semantics.OperationFacts.buildsItsResultFrom();
        }

        private static BuiltFrom buildsItsResultFrom(ValueName operation) {
            return souther.compiler.semantics.OperationFacts.buildsItsResultFrom(operation);
        }
        private static final Map<ValueName, Carried> CARRIERS =
                bind(CARRIED, Carried::container, CONTAINER, Question::holdsElements,
                        "the container a predicate reads");
        private static final Map<ValueName, ArgumentRef> PROJECTIONS =
                bind(PROJECTION_OF, Function.identity(), CLOSURE, t -> t instanceof Type.FnOf,
                        "the projection a predicate is stated over");
        private static final Map<ValueName, List<ArgumentRef>> LOWER_BOUNDS =
                bindEach(NO_SMALLER_THAN, CONTAINER, Question::holdsElements,
                        "a container the result is no smaller than");
        /** What the declarations came to, held to the library. The list is walked whole, so a fact
         *  nothing here looks up is one this has held all the same. */
        private static final List<souther.compiler.semantics.OperationFacts.Declared> SEMANTICS =
                OperationFactBinder.bindAll();

        /**
         * What the language declares an operation answers.
         *
         * <p>Here rather than at the call site so that asking runs the binding above, which is what
         * the rest of this holder does for the tables beside it. The answer itself is the
         * declaration's; what asking through here adds is that it has been held to the library
         * first.
         */
        private static ArgumentRef answersItsArgument(ValueName operation) {
            return souther.compiler.semantics.OperationFacts.answersItsArgument(operation);
        }

        /** The operations declared to answer one of their arguments, for the checks that hold each
         *  of them to firing. */
        private static Set<ValueName> answersItsArgument() {
            return souther.compiler.semantics.OperationFacts.answersItsArgument();
        }

        private static Set<ValueName> statesTheOrder() {
            return souther.compiler.semantics.OperationFacts.statesTheOrderOfItsArguments();
        }

        private static souther.compiler.semantics.PositiveOrder statesTheOrder(
                ValueName operation) {
            return souther.compiler.semantics.OperationFacts
                    .statesTheOrderOfItsArguments(operation);
        }

        private static Set<ValueName> shiftsBy() {
            return souther.compiler.semantics.OperationFacts.shiftsBy();
        }

        private static souther.compiler.semantics.OperationFact.ShiftsBy shiftsBy(
                ValueName operation) {
            return souther.compiler.semantics.OperationFacts.shiftsBy(operation);
        }

        /** The measures the shifts are stated through, read off those rather than listed again. A
         *  measure named in a second place is a measure the day somebody adds a shift and updates
         *  one of them. */
        private static Set<ValueName> measures() {
            Set<ValueName> out = new LinkedHashSet<>();
            shiftsBy().forEach(operation -> out.add(shiftsBy(operation).measure()));
            return out;
        }

        private static Set<ValueName> boundsOnTheResult() {
            return souther.compiler.semantics.OperationFacts.boundsOnTheResult();
        }

        private static List<souther.compiler.semantics.ResultBound> boundsOnTheResult(
                ValueName operation) {
            return souther.compiler.semantics.OperationFacts.boundsOnTheResult(operation);
        }
        private static final Map<ValueName, Choices> CHOICES = bindChoices(CHOOSES);
        private static final Map<ValueName, NumericResult> ARITHMETIC =
                bindNumericResults(NUMERIC_RESULTS);
    }

    /**
     * As {@link #bind}, for the arithmetic an operation computes: it takes as many arguments as the
     * row hands over, and it answers its number where the row says it does.
     *
     * <p>The result position is the half a signature can disagree with silently. A row saying the
     * number arrives in the case carrying {@code Int} is read at an arm, and an arm that never
     * matches is an arm that reports nothing — so a union that gained a case, or lost the one the
     * row names, would leave the operation with a meaning no program reaches and no diagnostic
     * anywhere. Held here, before any call is read.
     */
    private static Map<ValueName, NumericResult> bindNumericResults(
            Map<ValueName, NumericResult> rules) {
        rules.forEach((operation, rule) -> {
            Prelude.PreludeEntry entry = Prelude.entry(((ValueName.Stdlib) operation).qualified());
            if (entry == null) {
                throw new IllegalStateException("a rule about what number it computes is written for "
                        + operation + ", which the library does not declare");
            }
            Prelude.Signature signature = entry.signature();
            Type answers = Question.numberAnsweredBy(signature.result());
            List<Reads> reads = rule.computes().reads();
            if (signature.params().size() != reads.size()) {
                throw new IllegalStateException(operation + " takes " + signature.params().size()
                        + " argument(s), and the arithmetic written for it reads " + reads.size());
            }
            for (int i = 0; i < reads.size(); i++) {
                if (!reads.get(i).heldBy(signature.params().get(i), answers)) {
                    throw new IllegalStateException("argument " + (i + 1) + " of " + operation
                            + " is " + Type.show(signature.params().get(i))
                            + ", which the arithmetic written for it reads as " + reads.get(i));
                }
            }
            switch (rule.at()) {
                case Answered.Directly ignored -> {
                    if (!Question.isANumber(signature.result())) {
                        throw new IllegalStateException(operation + " answers "
                                + Type.show(signature.result())
                                + ", so the number it computes is not its result");
                    }
                }
                case Answered.InTheCaseCarrying(Type carried) -> {
                    if (!(signature.result() instanceof Type.Union(Set<TypeSymbol> members))) {
                        throw new IllegalStateException(operation + " answers "
                                + Type.show(signature.result())
                                + ", which has no case for the number it computes to arrive in");
                    }
                    if (!carried.equals(answers)) {
                        throw new IllegalStateException(operation + " answers no case carrying "
                                + Type.show(carried));
                    }
                    if (rule.unless() == null) {
                        throw new IllegalStateException(operation + " answers its number as one case"
                                + " of a union, so when the other case comes back is what that case"
                                + " means and is not written down");
                    }
                    // The condition names no case, so it says what every case that is not the
                    // number's says — which is one statement only where there is one such case. A
                    // union that gained a third would have an arm establishing a condition it was
                    // not taken under, which is a wrong fact rather than a missing one, and nothing
                    // downstream could tell: an arm is read the same way whichever case it names.
                    // Where a second failure is wanted, the condition is what has to name its case.
                    if (members.size() != 2) {
                        throw new IllegalStateException(operation + " answers "
                                + members.size() + " cases, and when it answers no number is"
                                + " written as one condition — which says what one other case"
                                + " means and cannot say what several do");
                    }
                }
            }
            if (rule.unless() != null) {
                bind(Map.of(operation, rule.unless().argument()), Function.identity(), null,
                        Question::isANumber, "the argument a failure is decided by");
            }
        });
        return rules;
    }

    /**
     * As {@link #bind}, for a rule stating a shift through a measure: the amount is a number, the
     * value shifted is of the type the measure counts, and the measure counts two of what the
     * operation answers. A rule pairing an operation with a measure of something else would state a
     * relation between two values that have none.
     */
    static void holdShift(ValueName operation, souther.compiler.semantics.OperationFact.ShiftsBy
            shift) {
        holdToTheDeclaration(operation, shift.amount(), null, Question::isANumber,
                "the amount a shift moves by");
        Prelude.PreludeEntry counts = Prelude.entry(shift.measure().qualified());
        if (counts == null) {
            throw new IllegalStateException("the rule about " + operation + " counts through "
                    + shift.measure().qualified() + ", which the library does not declare");
        }
        Prelude.PreludeEntry shifted = Prelude.entry(((ValueName.Stdlib) operation).qualified());
        List<Type> counted = counts.signature().params();
        if (counted.size() != 2 || !Question.isANumber(counts.signature().result())
                || !counted.get(0).equals(shifted.signature().result())
                || !counted.get(1).equals(shifted.signature().result())) {
            throw new IllegalStateException(shift.measure().qualified()
                    + " does not count two of what " + operation + " answers apart as a number");
        }
        holdToTheDeclaration(operation, shift.of(), null,
                t -> t.equals(shifted.signature().result()), "the value a shift moves from");
    }

    /** As {@link #bind}, for the arguments a case names: the one it answers, and the two sides of
     * each condition it is reached under. */
    private static Map<ValueName, Choices> bindChoices(Map<ValueName, Choices> rules) {
        rules.forEach((operation, choices) -> choices.cases().forEach(choice -> {
            List<ArgumentRef> named = new ArrayList<>();
            named.add(choice.answers());
            choice.given().forEach(stands -> {
                named.add(stands.left());
                named.add(stands.right());
            });
            named.forEach(one -> bind(Map.of(operation, one), Function.identity(), null,
                    Question::isANumber, "an argument a case of the definition names"));
        }));
        return rules;
    }

    /** As {@link #bind}, for the arguments a bound names: the one the result is bounded against, and
     * the one a condition on the rule reads. Each is a separate claim about a separate argument. */
    static void holdBound(ValueName operation, souther.compiler.semantics.ResultBound bound) {
        List<ArgumentRef> named = new ArrayList<>();
        if (bound.against() != null) {
            named.add(bound.against());
        }
        if (bound.provided()
                instanceof souther.compiler.semantics.ResultBound.Provided.ConstantAboveZero
                constant) {
            named.add(constant.argument());
        }
        named.forEach(one -> holdToTheDeclaration(operation, one, null, Question::isANumber,
                "an argument a bound on the result names"));
    }

    /** As {@link #bind}, for a rule that names more than one argument: each is held to the
     * declaration on its own, since each is a separate claim about a separate argument. */
    static Map<ValueName, List<ArgumentRef>> bindEach(Map<ValueName, List<ArgumentRef>> rules, ArgumentRef derived,
                                                Predicate<Type> required, String what) {
        rules.forEach((operation, reads) -> reads.forEach(one ->
                bind(Map.of(operation, one), Function.identity(), derived, required, what)));
        return rules;
    }

    /**
     * {@code rules}, once every row has been held to the operation it is about: the operation is one
     * the library declares, the argument it names is one that declaration has, and what stands there
     * is what the rule is about. A row naming a part of something the signature says the operation
     * does not hand is caught by {@link ArgumentRef}; one that writes a position the signature already
     * answers is caught here, since two answers to one question are what come apart later.
     */
    static <T> Map<ValueName, T> bind(Map<ValueName, T> rules, Function<T, ArgumentRef> reads,
                                      ArgumentRef derived, Predicate<Type> required, String what) {
        rules.forEach((operation, rule) ->
                holdToTheDeclaration(operation, reads.apply(rule), derived, required, what));
        return rules;
    }

    /** The same, for one rule. Asked per rule so that whatever holds a whole declaration source can
     *  walk it and hold each of them, rather than reaching for a table of its own. */
    static void holdToTheDeclaration(ValueName operation, ArgumentRef at, ArgumentRef derived,
                                     Predicate<Type> required, String what) {
        // Every row here is about an operation the library declares, so the key says which
        // library and which operation rather than a spelling this would have to take apart.
        if (!(operation instanceof ValueName.Stdlib library)) {
            throw new IllegalStateException("a rule about " + what + " is written for "
                    + operation + ", which is not a library operation");
        }
        Prelude.PreludeEntry entry = Prelude.entry(library.qualified());
        if (entry == null) {
            throw new IllegalStateException("a rule about " + what + " is written for "
                    + library.qualified() + ", which the library does not declare");
        }
        List<Type> params = entry.signature().params();
        int position = CallArguments.positionIn(at, operation);
        if (position < 0 || position >= params.size()) {
            throw new IllegalStateException(library.qualified() + " takes " + params.size()
                    + " argument(s), and the rule about " + what + " reads argument "
                    + (position + 1));
        }
        if (!required.test(params.get(position))) {
            throw new IllegalStateException("argument " + (position + 1) + " of "
                    + library.qualified() + " is not " + what);
        }
        if (at instanceof ArgumentRef.At && derived != null && Combinators.of(operation) != null
                && CallArguments.positionIn(derived, operation) == position) {
            throw new IllegalStateException("the rule about " + what + " for "
                    + library.qualified()
                    + " writes the argument its signature already answers — say which part it is"
                    + " rather than where, so the two cannot come apart");
        }
    }


    /**
     * The container {@code call} built its result from, and where each element of what it answers
     * came from — the lineage itself, for a reader that has an answer per alternative.
     *
     * <p>Beside {@link #builtFrom} and not instead of it. The four words are what a reader asking
     * "does what I know survive this" wants, and they are a projection; a reader that can say
     * something different about each of the things an element may be wants what the projection was
     * read off. Null where the elements came from more than one place, as the projection is refused
     * there: without one container there is nothing to ask the question of.
     */
    static Kept keptFrom(Core.PreservedCall call) {
        BuiltFrom built = Bound.buildsItsResultFrom(call.operation());
        if (built == null || built.outputs().size() != 1 || built.lineage().source() == null) {
            return null;
        }
        return new Kept(CallArguments.of(built.from(), call), built.lineage());
    }

    /** A construction's source container and the lineage of the elements it answers. */
    record Kept(Core container, ElementLineage lineage) {}

    /** The container {@code call} built its result from, or null where the check has no rule about
     * what the operation keeps. */
    static Source builtFrom(Core.PreservedCall call) {
        BuiltFrom built = Bound.buildsItsResultFrom(call.operation());
        return built == null ? null
                : new Source(CallArguments.of(built.from(), call), built.shape(), built.size());
    }

    /**
     * The containers {@code e}'s result is no smaller than, in the order the rule names them.
     *
     * <p>{@code a ++ b} is here beside the table rather than in it. The library declares
     * {@code List.append} as {@code a ++ b}, so the two spellings are one operation and a rule about
     * one is a rule about the other; and a {@code String} has no {@code append} at all, so the
     * operator is the only spelling its concatenation has. A rule keyed by operation reaches neither,
     * both being written as an operator and not as a call.
     */
    static List<Core> noSmallerThan(Core e) {
        if (e instanceof Core.Binary b && b.op() == BinOp.CONCAT) {
            return List.of(b.left(), b.right());
        }
        if (!(e instanceof Core.PreservedCall call)) {
            return List.of();
        }
        List<ArgumentRef> reads = Bound.LOWER_BOUNDS.get(call.operation());
        if (reads == null) {
            return List.of();
        }
        List<Core> containers = new ArrayList<>(reads.size());
        for (ArgumentRef one : reads) {
            containers.add(CallArguments.of(one, call));
        }
        return containers;
    }

    /** Where {@code call} reads the container it states its predicate of, or null where it is not a
     * predicate this carries anywhere. */
    static Carrying carried(Core.PreservedCall call) {
        Carried carried = Bound.CARRIERS.get(call.operation());
        return carried == null ? null : new Carrying(call, carried.container(), carried.through());
    }

    /** The projection {@code call}'s predicate is stated over, or null where it is stated over the
     * element itself — or where what stands in that argument is not a block this can read. */
    static Projection projectionOf(Core.PreservedCall call, Denotations at) {
        ArgumentRef reads = Bound.PROJECTIONS.get(call.operation());
        if (reads == null) {
            return null;
        }
        Core.Block projection = Terms.blockOf(CallArguments.of(reads, call), at);
        return projection == null ? null : new Projection(call, reads, projection);
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

    /** What {@code operation} computes and where it answers it, or null where the table says
     * nothing of it. */
    static NumericResult numericResult(ValueName operation) {
        // An expression that calls nothing is asked this, and answering it is what says so. The
        // tables are immutable maps, which refuse a null key rather than answering for it, and a
        // reader that guarded the call itself would be one guard per reader.
        return operation == null ? null : Bound.ARITHMETIC.get(operation);
    }

    /** The operator {@code operation} is, where it answers one directly and the language writes it
     * as an operator too — else null. What a call to it is read as where it stands. */
    static BinOp operator(ValueName operation) {
        NumericResult result = numericResult(operation);
        return result != null && result.at() instanceof Answered.Directly
                && result.computes() instanceof Computes.TheOperator written
                ? written.op() : null;
    }

    /** Which argument a positive answer from {@code operation} names as the greater, or null where
     * its sign is not an order. */
    static souther.compiler.semantics.PositiveOrder orderStatedBy(ValueName operation) {
        return Bound.statesTheOrder(operation);
    }

    /** Whether {@code operation} answers the order of its two arguments as a sign. */
    static boolean decidesOrder(ValueName operation) {
        return orderStatedBy(operation) != null;
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render
     * it. */
    static boolean readsAsATerm(ValueName operation) {
        return isSize(operation) || builtOperations().contains(operation)
                || carryingOperations().contains(operation) || isQuantifier(operation)
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
            Source built = builtFrom(call);
            if (built != null && built.size() == Cardinality.SAME) {
                return sizeSource(built.container());
            }
        }
        return e;
    }

    private DischargeRules() {}
}
