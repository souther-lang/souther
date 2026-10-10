package souther.compiler.semantics;

import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

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
 *
 * <p><b>A kind is here because a reader in the compiler takes it as a proposition.</b> Whether the
 * statement is that something holds or that it does not is beside the point; what earns a kind its
 * place is that something below the binding reads its value as a statement about the operation and
 * acts on it. That a question about an operation was considered and closed without a rule is such a
 * statement only where a reader acts on the closing: what an observation of an answer comes to,
 * closed with the proposition the domain has no words for, is what the reading of a condition stops
 * on and says ({@link LeavesUnsaid}). A closing nothing here reads belongs to the completeness check
 * that asks the question, and is not declared, bound or filed here.
 *
 * <p><b>The authoring vocabulary, and nothing below the binding reads it.</b> An argument is named
 * here as {@link ArgumentRef}, a word; another operation as a {@link souther.compiler.types.ValueName},
 * a name. Neither says the library has such an operation or such an argument. What holds these to
 * the library ({@code check.OperationFactBinder}) answers with a value of another kind, in which
 * every argument and every operation has been read against its declaration, and every reader of a
 * fact reads that one. So a kind added here is a kind the binder must say what it comes to bound,
 * which the exhaustive switch there refuses to leave unsaid.
 */
public sealed interface OperationFact {

    /**
     * What the operation answers, counted, is this much of what its arguments are counted as.
     *
     * <p>Exact and unconditional: {@code count(result) = Σ cᵢ·count(argᵢ) + k} at every call.
     * {@code Decimal.fromInt(n)} is {@code n}; {@code Date.daysBetween(from, to)} is
     * {@code -from + to}; {@code Date.addDays(days, date)} is {@code date + days}. Such a call is
     * read into that form rather than given an atom of its own, so a rule about the arguments
     * settles one about the call.
     *
     * <p><b>Counted, so a date takes part.</b> What a date's count is belongs to its carrier, and
     * the arithmetic here is over counts and not over values — which is what lets a difference of
     * two dates be a number of days while neither of them is a number. Written as a relation
     * between values, the two dates would have had nothing to say and the fact would have been
     * unstateable for the operations it exists for.
     *
     * <p>Not a choice among arguments. What a choice answers is one of two values, decided by the
     * arguments, and which one it is has to be reasoned about case by case; this answers one value
     * unconditionally. Read as a choice with one candidate, every value-preserving conversion would
     * be filed under selection, and the two stop being one question the moment the library gains a
     * conversion that is not a widening.
     *
     * <p><b>Not for arithmetic the language composes.</b> {@code Int.add(a, b)} answers
     * {@code a + b} and is not declared here: {@code Terms.asOperator} reads such a call as the
     * operator it stands for, so a fact would be a second path saying what the grammar already
     * says.
     */
    record AnswersAFormOfItsArguments(
            souther.compiler.numeric.LinearForm<ArgumentRef> form)
            implements OperationFact {

        public AnswersAFormOfItsArguments {
            Objects.requireNonNull(form, "this one says what it answers");
            if (form.coefs().isEmpty()) {
                throw new IllegalArgumentException(
                        "a form of its arguments names one: a result that is a constant whatever it"
                                + " was given is a bound and not this");
            }
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
            Objects.requireNonNull(order, "this one says which way round");
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
    record ShiftsBy(souther.compiler.types.ValueName.Stdlib.Operation measure, ArgumentRef of,
                    ArgumentRef amount, java.math.BigDecimal per) implements OperationFact {

        public ShiftsBy {
            Objects.requireNonNull(measure, "a shift is stated through a measure");
            Objects.requireNonNull(of, "and moves something");
            Objects.requireNonNull(amount, "by something");
            Objects.requireNonNull(per, "at some rate");
        }
    }

    /**
     * The operation answers how many whole units lie between its two arguments, counting forward
     * from {@code from} to {@code to}, where one unit is {@code perUnit} steps of the order the
     * arguments are counted on.
     *
     * <p>The count is truncated toward zero: a {@code to} fifty-nine steps before {@code from} is no
     * unit before it, and the answer is nought. So the answer is no form of the two arguments, and
     * what is stated of it is stated through the difference of the two. With {@code d} the number of
     * steps from {@code from} to {@code to}, the count is at least {@code n} exactly where
     * {@code d} is at least {@code perUnit * n} for a positive {@code n}, and where {@code d} is at
     * least {@code perUnit * n - (perUnit - 1)} for any other.
     */
    record CountsWholeUnitsBetween(ArgumentRef from, ArgumentRef to, long perUnit)
            implements OperationFact {

        public CountsWholeUnitsBetween {
            Objects.requireNonNull(from, "a count of units starts somewhere");
            Objects.requireNonNull(to, "and ends somewhere");
            if (perUnit < 2) {
                throw new IllegalArgumentException(
                        "a unit is more than one step of the order, or the count is the difference"
                                + " and states a form instead: " + perUnit);
            }
        }
    }

    /**
     * Something that holds of the number the operation answers, wherever it is called.
     *
     * <p>One fact per bound rather than a list in one: an operation with two bounds carries two
     * statements, and they are added and read one at a time.
     */
    record BoundsItsResult(ResultBound<ArgumentRef> bound) implements OperationFact {

        public BoundsItsResult {
            Objects.requireNonNull(bound, "this one states a bound");
        }
    }

    /**
     * The operation builds a container out of another, and this says where its elements came from
     * and how many of them there are.
     */
    record BuildsItsResultFrom(BuiltFrom<ArgumentRef> built) implements OperationFact {

        public BuildsItsResultFrom {
            Objects.requireNonNull(built, "this one says what it was built from");
        }
    }

    /**
     * Every element of the operation's answer is inside what a closure answered on an element of
     * {@code lineage}'s source, and nothing is said of how many there are.
     *
     * <p>Where an element came from, apart from how many of them the answer has. A
     * {@link BuildsItsResultFrom} says both, and its rows are also the table the invariant
     * discharge reads, so an operation whose count is neither as many as its source nor no more
     * ({@code List.flatMap} answers any number for each element) cannot be a row there. Declared
     * here it is read by the readers that follow a value back to the position it was made from,
     * and by nothing that reasons about the answer's size or what survives the construction.
     *
     * <p>Only the lineages a value is made from, which are the closure's answer and what is inside
     * it. The very elements of an argument are a statement about the answer's count as well, and
     * stay a {@link BuildsItsResultFrom}.
     */
    record ElementsComeFrom(ElementLineage<ArgumentRef> lineage) implements OperationFact {

        public ElementsComeFrom {
            Objects.requireNonNull(lineage, "this one says where the elements came from");
            if (!(lineage instanceof ElementLineage.ClosureResult<ArgumentRef>
                    || lineage instanceof ElementLineage.InsideClosureResult<ArgumentRef>)
                    || lineage.source().elements() != 1) {
                throw new IllegalArgumentException(
                        "an element made from one element of an argument is what this says: "
                                + lineage);
            }
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
            Objects.requireNonNull(container, "this one names a container");
        }
    }

    /**
     * The elements of the operation's answer stand in the order of the elements of {@code source}
     * they came from: one stands before another where what it came from stood before what the
     * other came from.
     *
     * <p>The order and nothing else. Where the elements came from is {@link BuildsItsResultFrom},
     * and the two together are what a reader computing the answer itself needs: as many answers of
     * the closure as elements, each on a different one ({@link ElementLineage.ClosureResult} with
     * {@link SizeAgainstItsSource#SAME}), in the order they stand in, is the answer written out.
     */
    record KeepsTheOrderOf(ArgumentRef source) implements OperationFact {

        public KeepsTheOrderOf {
            Objects.requireNonNull(source, "this one names what the order is of");
        }
    }

    /**
     * The operation's answer holds the image of every element of the argument {@code image} names,
     * and holds nothing else: an element of the answer is one of those images, and each of those
     * is in the answer. The image is the element itself, or what the closure answered on it.
     *
     * <p>The answer as a set of values, whichever kind of container holds them and however many
     * times. That a set made of a list holds each value once, and a set of what a closure made holds
     * each answer once, are what {@link BuildsItsResultFrom} does not say: it says where an element
     * came from, and an operation that kept some of what it was given has that too. What a reader
     * asking whether some element of the answer meets a statement needs is the other half, that no
     * element of the source was left out, and with it the statement about some element of the
     * answer is the statement about some element of the source.
     *
     * <p>No count, as {@link ElementsComeFrom} has none. How many elements the answer holds is
     * what a set that holds each value once is the number of different ones of, and no reader of
     * this takes a count from it.
     */
    record HoldsTheImageOfEveryElement(ElementLineage<ArgumentRef> image) implements OperationFact {

        public HoldsTheImageOfEveryElement {
            Objects.requireNonNull(image, "this one says what the answer holds an image of");
            if (!(image instanceof ElementLineage.SameAs<ArgumentRef>
                    || image instanceof ElementLineage.ClosureResult<ArgumentRef>)
                    || image.source().elements() != 1) {
                throw new IllegalArgumentException(
                        "the element itself or the closure's answer on it, of one element of an"
                                + " argument, is what this says: " + image);
            }
        }
    }

    /**
     * The operation answers the pieces {@code string} falls into where {@code separator} stands in
     * it, each once and in order, the empty ones too: a string that is no longer than one piece is
     * its own, and the code points of the pieces together are those of the string but for each
     * place the separator stood.
     *
     * <p>Said of a separator that is one code point, and only then. A longer one can stand across
     * where a shorter one is looked for, and what is left between two of its occurrences is not
     * what is left of the string with a code point taken out. Whether a call's separator is one is
     * a question about the call and is asked where it is read, as what a constant argument reads
     * as.
     *
     * <p>Nothing here counts the pieces. How many there are is the number of times the separator
     * stands in the string and is no number the language says.
     */
    record HoldsThePiecesOf(ArgumentRef separator, ArgumentRef string) implements OperationFact {

        public HoldsThePiecesOf {
            Objects.requireNonNull(separator, "this one names the separator");
            Objects.requireNonNull(string, "and the string it stands in");
        }
    }

    /**
     * The operation answers what {@code into} holds with {@code value} put in: every element of the
     * answer is one of {@code into}'s or {@code value}, it holds at most one element more than
     * {@code into}, and of {@code into}'s it holds each as many times as {@code into} does or fewer.
     *
     * <p>A set put a value it holds answers the set; a map put a value under a key it has answers it
     * with the value under that key replaced. Both are this statement, which says what each element
     * of the answer was and nothing about which of {@code into}'s it gave up.
     *
     * <p>An axiom of a kernel, read by the proofs of what the library's written operations build out
     * of what they are handed, and by nothing a reader of a condition is handed.
     */
    record PutsAValueIn(ArgumentRef value, ArgumentRef into) implements OperationFact {

        public PutsAValueIn {
            Objects.requireNonNull(value, "this one names the value put in");
            Objects.requireNonNull(into, "and what it is put in");
        }
    }

    /**
     * The operation answers a map every key of which is a key {@code map} was keyed by — the same
     * value, filed under in the answer as it was there.
     *
     * <p>Its own statement and not something a reader works out from the elements. What
     * {@link BuildsItsResultFrom} says is where the values came from, and a map whose values a
     * closure rewrote keeps every key it had ({@code Map.mapValues}), while an answer holding the
     * very values of a map may hold them under keys it did not have. So which keys an answer has is
     * said here, of the operations that keep them, and a key is followed into an answer only where
     * this says so.
     */
    record KeepsTheKeysOf(ArgumentRef map) implements OperationFact {

        public KeepsTheKeysOf {
            Objects.requireNonNull(map, "this one names the map the keys were kept from");
        }

        /**
         * What this says of {@code operation}, which takes {@code arity} arguments, as a statement
         * beside what a map answers asked whether it holds a key: any value the answer holds as a
         * key, {@code map} holds as one. What a proof of it shows, and what a proof of another
         * operation takes of it.
         */
        public LawProposition<ArgumentRef> states(ValueName.Stdlib.Operation operation,
                                                  int arity) {
            List<LawSubject<ArgumentRef>> own = new ArrayList<>();
            for (int at = 0; at < arity; at++) {
                own.add(new LawSubject.Argument<>(new ArgumentRef.At(at)));
            }
            LawSubject<ArgumentRef> any = new LawSubject.Argument<>(new ArgumentRef.Every(0));
            return new LawProposition.Any<>(List.of(
                    holdsTheKey(any, new LawSubject.AnswerOf<>(operation, own)).denied(),
                    holdsTheKey(any, new LawSubject.Argument<>(map))));
        }

        private static LawProposition<ArgumentRef> holdsTheKey(LawSubject<ArgumentRef> key,
                                                              LawSubject<ArgumentRef> in) {
            return new LawProposition.Observed<>(new LawSubject.AnswerOf<>(
                    ValueName.Stdlib.operation("Map", "containsKey"), List.of(key, in)),
                    new SideAnswered(AnswerAspect.TRUTH, true));
        }
    }

    /**
     * What an observation of the operation's answer comes to over its arguments ({@link
     * OperationLaw}).
     *
     * <p>One kind for every observation, because each is the same statement: a side of the answer,
     * or how many it holds, is a proposition or a number of what the operation was handed. That a
     * filter holds something where some element was kept, that a take holds something where it was
     * asked for some and handed some, and that a list of a map's keys holds something where the map
     * does are three laws of one shape, and a reader carries each across a call by one rule.
     *
     * <p>Not every observation of every answer has one declared. Where what the operation is
     * declared to build already says it — an answer as many as its one source is empty where that
     * source is — the law is derived there and declaring it again is refused, so the two cannot
     * disagree.
     */
    record HasALaw(OperationLaw<ArgumentRef> law) implements OperationFact {

        public HasALaw {
            Objects.requireNonNull(law, "this one states a law");
        }
    }

    /**
     * The observation {@code observed} of the operation's answer comes to {@code why}, which no
     * statement over the arguments can say.
     *
     * <p>Read by the reading of a condition, which stops there on a fact about the domain rather
     * than on a law nobody wrote: what a trimmed string being empty comes to is known, and is a
     * proposition this compiler has no words for.
     */
    record LeavesUnsaid(OperationLaw.Observed observed, Unsayable why) implements OperationFact {

        public LeavesUnsaid {
            Objects.requireNonNull(observed, "this one names an observation");
            Objects.requireNonNull(why, "and what it comes to");
        }
    }

    /**
     * A law of an operation the library writes in the language, stated to be proved against its
     * body: {@code states}, which is a law only once proved, and what a walk the body makes carries
     * at every step of it ({@code carries}), which the proof goes by.
     *
     * <p>Never a law on its own say-so. A law declared beside a body is a second account of what the
     * body does and is refused there; this is the same statement as an obligation, which the body
     * discharges or leaves open. A clause of {@code carries} names the walk's parts with
     * {@link ArgumentRef.Carried}, {@link ArgumentRef.Walked} and {@link ArgumentRef.Every}, and may
     * name what other operations answer ({@link LawSubject.AnswerOf}).
     */
    record IsALemma(OperationLaw<ArgumentRef> states, List<LawProposition<ArgumentRef>> carries)
            implements OperationFact {

        public IsALemma {
            Objects.requireNonNull(states, "a lemma states something");
            carries = List.copyOf(carries);
        }
    }

    /**
     * What an operation the library writes answers stands to what it was handed, and to what
     * other operations answer on those, as {@code holds} says — stated to be proved against its
     * body, with what a walk the body makes carries at every step of it ({@code carries}).
     *
     * <p>A lemma, as {@link IsALemma} is, about a statement no law can make: one naming what other
     * operations answer, the answer itself among them ({@link LawSubject.AnswerOf} of the operation
     * handed its own arguments), and holding of every value ({@link ArgumentRef.Every}). Proved, it
     * is read by the proofs of the library's other operations where they call this one, as what is
     * stated of a kernel beside others is ({@link IsRelated}); by no reader of a condition.
     */
    record IsRelatedInALemma(LawProposition<ArgumentRef> holds,
                             List<LawProposition<ArgumentRef>> carries) implements OperationFact {

        public IsRelatedInALemma {
            Objects.requireNonNull(holds, "a lemma states something");
            carries = List.copyOf(carries);
        }
    }

    /**
     * What a kernel answers stands to what other kernels answer on its arguments as {@code holds}
     * says, wherever it answers: a key a map holds is one only where the map holds something; an
     * insert holds one more than its map unless the key was there.
     *
     * <p>An axiom about a kernel, as a law of one is, and held to what it computes the same way. Not
     * a law: a law says what one observation of an answer comes to over the arguments alone, and
     * this names other answers ({@link LawSubject.AnswerOf}), the answer itself among them, and may
     * hold of every value ({@link ArgumentRef.Every}). Read by the proofs of what the library's
     * written operations keep, and by nothing a reader of a condition is handed.
     */
    record IsRelated(LawProposition<ArgumentRef> holds) implements OperationFact {

        public IsRelated {
            Objects.requireNonNull(holds, "a relation states something");
        }
    }

    /**
     * The operation answers a list of what {@code map} holds: its keys, its values, or its entries
     * as pairs of a key and the value filed under it.
     *
     * <p>Which part is what a reader of an element of the answer needs, and it is not the elements
     * of the map: a map's element is its value, and a list of its keys holds none of those. So this
     * is its own statement rather than a {@link BuildsItsResultFrom}, which says an answer holds an
     * argument's elements.
     */
    record ListsAPartOf(ArgumentRef map, MapPart part) implements OperationFact {

        public ListsAPartOf {
            Objects.requireNonNull(map, "this one names the map listed");
            Objects.requireNonNull(part, "and which of what it holds");
        }
    }

    /**
     * The operation answers what {@code container} holds accumulated: started from an identity and
     * carried through one step over what it has so far and an element, both of the type it answers.
     *
     * <p>Which argument holds them is named rather than looked for. A signature says which one it
     * could be — an argument whose elements are of the type the operation answers — and says it of
     * as many arguments as fit, so an operation given two such containers has a signature that
     * admits two readings and a fact that admits one. Held to the signature where the declarations
     * are bound, so a name that does not fit is refused where it is written.
     */
    record AccumulatesItsContainer(ArgumentRef container, Accumulation how)
            implements OperationFact {

        public AccumulatesItsContainer {
            Objects.requireNonNull(container, "this one names a container");
            Objects.requireNonNull(how, "and what walking it comes to");
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
            Objects.requireNonNull(container, "this one names a container");
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
            Objects.requireNonNull(projection, "this one names where it is written");
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
            Objects.requireNonNull(size, "this one names the size it means");
        }
    }

    /** The operation computes a number, and this says which arithmetic and where it answers it. */
    record ComputesANumber(NumericResult<ArgumentRef> result) implements OperationFact {

        public ComputesANumber {
            Objects.requireNonNull(result, "this one says what it computes");
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
    record IsDefinedByCases(DefinitionCase<ArgumentRef> one) implements OperationFact {

        public IsDefinedByCases {
            Objects.requireNonNull(one, "this one states a case");
        }
    }

    /**
     * The operation answers a number taken of the one value it is given: how long a string is, how
     * many a container holds, which hour of its day a time falls in.
     *
     * <p>One list, because a reader that answers "does this rule bound a number" has to give the
     * same answer wherever it is asked. The discharge procedure keys an atom on one of these over
     * its argument's path and a partition draws a boundary on one — and where those two disagreed,
     * a rule discharged in one place was reported in the other as a rule the model does not state.
     *
     * <p><b>What it is taken as, and nothing else.</b> A size is never negative, a count is a whole
     * number, and a string of any length exists: three propositions about {@code String.length} that
     * are declared as themselves — {@link BoundsItsResult}, the operation's own result type, {@link
     * EveryAnswerItCanGiveHasASourceValue} — rather than read off the arm. Written into the arm,
     * each would be true of the operations that share it and of no others, which is what a term
     * standing for one operation and answering for a kind of operation already was (#1027).
     *
     * <p>One value is the whole of what such a term can be <em>about</em>. A number taken of two
     * locations is not one of these: what it would be read off is a pair, and a term names one
     * path. An operation over several whose result the model can state says so as the form it
     * answers ({@link AnswersAFormOfItsArguments}) and is read into that form instead, which is why
     * the two cannot both be declared of one operation.
     *
     * <p><b>Being about one value is not taking only one.</b> An operation may be given values
     * beside the one it measures, and those decide which number of it is taken: a divisor says
     * which quotient. Such an argument is read as the constant it stands for and carried as part of
     * which number this is ({@code semantics.TakenArguments}), so a rule about the quotient by two
     * and one about the quotient by three are rules about two numbers of one place. An argument
     * that reads as no constant leaves a taking nothing names — which number it would be is not
     * settled, and a term built without it would be the quotient by whatever a reader assumed.
     */
    record AnswersANumberTakenOfAValueItIsGiven(TakenAs how) implements OperationFact {

        public AnswersANumberTakenOfAValueItIsGiven {
            Objects.requireNonNull(how, "this one says what the number is taken as");
        }
    }

    /**
     * Every number this operation could answer is one some value it could be given answers.
     *
     * <p>Not a property of how the number is taken. A string of any length is written by repeating
     * a character and a character is always to be had; every hour of the day is an hour some time
     * falls in. Two different accounts of why, and one proposition — which is why it is asked of the
     * operation rather than derived from {@link TakenAs}, where the answer would have to be the same
     * for every operation sharing an arm: a {@code List.length} and a {@code String.length} share
     * one and only the second of them has it.
     *
     * <p>What is left out is what a count over an element the language may have none of leaves. A
     * {@code Set<Bool>} is capped at two by how many booleans there are; a {@code List<T>} of one
     * needs a {@code T}, and a {@code T} nothing inhabits has none. Whether such a value exists is
     * a question about the element and not about the number, so those operations declare nothing
     * here and an edge on one of them is settled by a row rather than by an argument.
     *
     * <p>Beside the building and not the same statement as it. That a value answering the number
     * exists is this; that the generator can write one down is what the generator answers, and an
     * operation may satisfy the first while the second is held back by how much it is worth
     * building.
     */
    record EveryAnswerItCanGiveHasASourceValue() implements OperationFact {}
}
