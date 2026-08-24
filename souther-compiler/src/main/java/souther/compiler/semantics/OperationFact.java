package souther.compiler.semantics;

/**
 * One thing that is true of one of the language's operations.
 *
 * <p>Kinds are kept apart because they are different statements, not because a reader wants them
 * apart. That an operation answers the number it was given, that it moves a value by an amount, and
 * that the sign of its answer states which of its arguments is the greater are three propositions,
 * and one operation may carry several: {@code Date.addDays} both answers a date shifted by its
 * amount and states how far the two stand apart. Folded into one case per operation, a fact could
 * only be added by widening whatever case was already there.
 *
 * <p>Sealed, so the procedures that hold these to the library's declarations answer for a kind
 * added rather than passing over it.
 */
public sealed interface OperationFact {

    /**
     * The result is the number an argument already is, and this says which argument.
     *
     * <p>Such a call is read into the form its argument has rather than given an atom of its own, so
     * a rule about the argument settles one about the call. {@code Decimal.fromInt(n)} is the one
     * the library has: every {@code Int} is a {@code Decimal} exactly, and the widening states
     * nothing of its own.
     *
     * <p>Not a choice among arguments. What a choice answers is one of two values, decided by the
     * arguments, and which one it is has to be reasoned about case by case; this answers one value
     * unconditionally, in another type. Read as a choice with one candidate, every value-preserving
     * conversion would be filed under selection, and the two stop being one question the moment the
     * library gains a conversion that is not a widening.
     */
    record AnswersItsArgument(ArgumentRef argument) implements OperationFact {

        public AnswersItsArgument {
            java.util.Objects.requireNonNull(argument, "this one names an argument");
        }
    }

    /**
     * The sign of what the operation answers states which of its two arguments is the greater.
     *
     * <p>Zero states the equality and a negative answer the relation the other way, so one of these
     * is the whole of what such an operation says about the pair. Which relation a rule writing one
     * states then follows from where the sign stands against zero and from nothing else.
     *
     * <p>The direction is not the same for all of them: {@code compare(a, b)} is positive where
     * {@code a} is the greater, and {@code daysBetween(from, to)} counts forward from its first
     * argument, so it is positive where the second one is.
     */
    record StatesTheOrderOfItsArguments(PositiveOrder order) implements OperationFact {

        public StatesTheOrderOfItsArguments {
            java.util.Objects.requireNonNull(order, "this one says which way round");
        }
    }

    /**
     * The operation answers the value at {@code of} moved by {@code amount}, and how far it moved is
     * {@code per} of what {@code measure} counts.
     *
     * <p>What a shift states is not a bound on what it answers — a date is not a number — so it is
     * written in the one language there is about such values, which is the number a measure answers
     * of two of them. That number is what a rule over a pair of dates is written in as well, so the
     * two meet without either being restated.
     */
    record ShiftsBy(souther.compiler.types.ValueName.Stdlib measure, ArgumentRef of,
                    ArgumentRef amount, java.math.BigDecimal per) implements OperationFact {

        public ShiftsBy {
            java.util.Objects.requireNonNull(measure, "a shift is stated through a measure");
            java.util.Objects.requireNonNull(of, "and moves something");
            java.util.Objects.requireNonNull(amount, "by something");
            java.util.Objects.requireNonNull(per, "at some rate");
        }
    }

    /**
     * Something that holds of the number the operation answers, wherever it is called.
     *
     * <p>One fact per bound rather than a list in one: an operation with two bounds carries two
     * statements, and they are added and read one at a time.
     */
    record BoundsItsResult(ResultBound bound) implements OperationFact {

        public BoundsItsResult {
            java.util.Objects.requireNonNull(bound, "this one states a bound");
        }
    }

    /**
     * The operation builds a container out of another, and this says where its elements came from
     * and how many of them there are.
     */
    record BuildsItsResultFrom(BuiltFrom built) implements OperationFact {

        public BuildsItsResultFrom {
            java.util.Objects.requireNonNull(built, "this one says what it was built from");
        }
    }

    /**
     * The operation's result is never smaller than what {@code container} holds.
     *
     * <p>One fact per container it is no smaller than: {@code a ++ b} is as long as either half, and
     * that is two statements about one operation rather than a list inside one.
     *
     * <p>Not a statement about the elements. {@code List.append} keeps every element of both and
     * holds neither's alone, so neither is what it was built from; an insert puts in something the
     * container it read did not hold. The count survives either way, which is why these had been
     * filed among the constructions nothing is known of and their bound discarded with an element
     * statement that was never the same one.
     */
    record ResultIsNoSmallerThan(ArgumentRef container) implements OperationFact {

        public ResultIsNoSmallerThan {
            java.util.Objects.requireNonNull(container, "this one names a container");
        }
    }

    /**
     * The operation is a predicate over what {@code container} holds, and its statement survives a
     * construction of the shapes in {@code through}.
     *
     * <p>{@code List.all} holds of any sublist of a list it holds of; {@code List.contains} does
     * not, and neither survives a mapping — what a mapped element is, the mapping alone does not
     * say.
     */
    record ReadsItsContainer(ArgumentRef container, java.util.Set<ElementShape> through)
            implements OperationFact {

        public ReadsItsContainer {
            java.util.Objects.requireNonNull(container, "this one names a container");
            through = java.util.Set.copyOf(through);
        }
    }

    /**
     * The predicate is stated over a projection of each element, and {@code projection} is where it
     * is written.
     *
     * <p>A mapping keeps a projection when the closure copies that field from the element
     * unchanged, so the predicate holds of the mapped container exactly when it holds of what was
     * mapped, over the field it came from.
     */
    record IsStatedOverAProjection(ArgumentRef projection) implements OperationFact {

        public IsStatedOverAProjection {
            java.util.Objects.requireNonNull(projection, "this one names where it is written");
        }
    }

    /**
     * The operation states its predicate of <em>every</em> element, so what it says of a container
     * is what holds of each element a closure is handed.
     *
     * <p>The name and nothing else. Which argument is the predicate and which the container the
     * signature already answers, and how far the statement travels {@link ReadsItsContainer}
     * already does.
     */
    record StatesItsPredicateOfEveryElement() implements OperationFact {}

    /**
     * The operation asks whether a container is empty, and says the same thing as {@code size}
     * against nought.
     *
     * <p>Not what an operation does to a property but what a predicate <em>says</em>:
     * {@code List.isEmpty(xs)} and {@code List.length(xs) == 0} are one statement, so a rule writing
     * either settles a clause writing the other. Without it the two would be unrelated, which is an
     * accident of which one the author reached for.
     */
    record MeansTheSameAsASizeOfNought(souther.compiler.types.ValueName size)
            implements OperationFact {

        public MeansTheSameAsASizeOfNought {
            java.util.Objects.requireNonNull(size, "this one names the size it means");
        }
    }

    /** The operation computes a number, and this says which arithmetic and where it answers it. */
    record ComputesANumber(NumericResult result) implements OperationFact {

        public ComputesANumber {
            java.util.Objects.requireNonNull(result, "this one says what it computes");
        }
    }

    /**
     * The operation answers one of the values it was given, and this is one case of the definition
     * it is written in: which argument it answers there, and what has to hold of the arguments for
     * that case to be reached.
     *
     * <p>The cases of one operation are exhaustive between them: their conditions cover everything
     * it can be given, so what holds in every case holds of the result. That is what makes reading
     * them sound, and it is a claim about the set rather than about any one of them — a case left
     * out does not make the others wrong, it makes a clause provable that the values can fail. So
     * they are declared as the library writes them, in the order it writes them.
     */
    record IsDefinedByCases(Case one) implements OperationFact {

        public IsDefinedByCases {
            java.util.Objects.requireNonNull(one, "this one states a case");
        }
    }

    /** One case of a piecewise definition: the argument it answers, and what the arguments stand as
     *  for it to be reached. */
    record Case(ArgumentRef answers, java.util.List<ArgumentsStand> given) {

        public Case {
            java.util.Objects.requireNonNull(answers, "a case answers an argument");
            given = java.util.List.copyOf(given);
        }
    }

    /**
     * There is nothing to say of this operation under {@code subject}.
     *
     * <p>A decision and not a gap. An operation the library declares is in range of whatever its
     * signature puts it in range of, and a silence there says two things at once — that nothing is
     * true of it, and that nobody looked. {@code List.distinctBy} was credited by neither check for
     * exactly that reason, with nothing said about the missing row.
     *
     * <p>So the absence is declared beside the presences, and the reason is written where it is
     * declared. What the reason is about is the operation: a map's keys are not its values, a
     * whole-minute count between two moments does not state their order, what {@code a + b} answers
     * may be anywhere.
     */
    record SaysNothingOf(OperationSubject subject) implements OperationFact {

        public SaysNothingOf {
            java.util.Objects.requireNonNull(subject, "a silence is about something");
        }
    }

    /** A relation between two arguments: {@code left rel right}. What a case is reached under,
     *  written in the arguments the operation was given and in nothing else. */
    record ArgumentsStand(ArgumentRef left, souther.compiler.numeric.NumericDomain.Rel rel,
                          ArgumentRef right) {

        public ArgumentsStand {
            java.util.Objects.requireNonNull(left, "a relation has two sides");
            java.util.Objects.requireNonNull(rel, "and stands some way");
            java.util.Objects.requireNonNull(right, "a relation has two sides");
        }
    }
}
