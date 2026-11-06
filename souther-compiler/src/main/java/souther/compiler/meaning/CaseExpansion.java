package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * What a reader that stopped taking a line's cases apart at their number is told of one of them
 * beside why it stopped: how many ways there were, and what in the model the parts it is taken
 * apart on came from.
 *
 * <p>About one case and not about the stop. Why the line was not worked out is a reason a report
 * gathers and puts together with others like it; this is a count of one case of one line, which
 * nothing puts together with another, so it is kept beside the reason and never in it. Which case
 * it is, is what the reading that asked it tells cases apart by: the line's relation, and the
 * condition the case was said as ({@link DecidingCase#eachByItsOwnCondition}).
 *
 * @param line       the quantity the line is on, named the way a report names a border on it
 * @param cutAt      where on the quantity the line is, written as a border's level is: what tells
 *                   a reader two lines on one quantity apart
 * @param relation   the relation the line came to, as the reading spelled it
 * @param ofTheCase  the condition the case was said as
 * @param counted    how many ways there were of choosing one of what the case stands for
 * @param attributed what the parts the case is taken apart on came from
 * @param diagnosed  how many ways some of those parts can come out together, where they compare
 *                   one number ({@link WhatTheNumbersOfACaseLeave}): what the numbers leave, and
 *                   no count of cases nor of what a rewrite would leave
 */
public record CaseExpansion(String line, String cutAt, Spelling relation, Proposition ofTheCase,
                            CaseCount counted, Attribution attributed,
                            List<Diagnosis> diagnosed) {

    public CaseExpansion {
        Objects.requireNonNull(line, "cases are a line's");
        Objects.requireNonNull(cutAt, "a line is somewhere on its quantity");
        Objects.requireNonNull(relation, "of some relation");
        Objects.requireNonNull(ofTheCase, "a case is said as some condition");
        Objects.requireNonNull(counted, "cases are some number of ways");
        Objects.requireNonNull(attributed, "what they came from, or why that was not said");
        diagnosed = List.copyOf(diagnosed);
    }

    /**
     * A case counted, before what its parts came from is read: that is read off how the statement
     * was derived, which the reading that counted it does not hold.
     *
     * @param line     the quantity the line is on
     * @param cutAt    where on it the line is
     * @param relation the relation the line came to
     * @param asked    the case
     * @param counted  how many ways there were of choosing one of what it stands for
     */
    public record Counted(String line, String cutAt, Spelling relation, DecidingCase asked,
                          CaseCount counted) {

        public Counted {
            Objects.requireNonNull(line, "cases are a line's");
            Objects.requireNonNull(cutAt, "a line is somewhere on its quantity");
            Objects.requireNonNull(relation, "of some relation");
            Objects.requireNonNull(asked, "a case asked");
            Objects.requireNonNull(counted, "cases are some number of ways");
        }

        /** This case, with what made its parts and what the numbers they compare leave. */
        CaseExpansion attributed(Attribution attributed) {
            return new CaseExpansion(line, cutAt, relation, asked.condition(), counted,
                    attributed, WhatTheNumbersOfACaseLeave.of(asked.standsFor()));
        }

        /**
         * Each of {@code counted}, in order, with what made its parts read off {@code derivedBy},
         * the derivations of the one statement they are all cases of on each application it was
         * read on.
         */
        public static List<CaseExpansion> attributedTo(List<Counted> counted,
                                                       List<Derivation> derivedBy) {
            List<Attribution> made = TheChoicesACaseIsMadeOf.of(
                    counted.stream().map(each -> each.asked().standsFor()).toList(), derivedBy);
            List<CaseExpansion> out = new ArrayList<>();
            for (int at = 0; at < counted.size(); at++) {
                out.add(counted.get(at).attributed(made.get(at)));
            }
            return List.copyOf(out);
        }
    }

    /** What the parts a case is taken apart on came from, or why that was not said. */
    public sealed interface Attribution {}

    /**
     * What the parts came from.
     *
     * <p><b>Not a factoring of the count.</b> The cases are alternatives and choices held
     * together, sharing what follows from a choice, so how many ways there are is no product of
     * these; and one may stand inside another, an {@code if} inside a closure on each of its
     * applications. What each says is what made some of the parts the case is taken apart on.
     *
     * @param factors      what made the parts, in the order the derivations meet them
     * @param partsSplitOn how many parts the case is taken apart on
     * @param unattributed how many of them nothing here was found to have made: a part a step
     *                     made out of others, where no step said which of the model's constructs
     *                     it is of
     */
    public record Attributed(List<Factor> factors, int partsSplitOn, int unattributed)
            implements Attribution {

        public Attributed {
            factors = List.copyOf(factors);
            if (partsSplitOn < 0 || unattributed < 0 || unattributed > partsSplitOn) {
                throw new IllegalArgumentException("parts are some of those split on: "
                        + unattributed + " of " + partsSplitOn);
            }
        }
    }

    /** Nothing is said of what the parts came from, for the reason {@code why}. */
    public record NotAttributed(WhyNotAttributed why) implements Attribution {

        public NotAttributed {
            Objects.requireNonNull(why, "a reading given up is given up for a reason");
        }
    }

    /** Why what the parts came from was not said: neither is anything the line stopped at. */
    public enum WhyNotAttributed {

        /** No derivation of the statement was held where the case was counted. */
        NOTHING_DERIVED,

        /** More steps were walked than {@link TheChoicesACaseIsMadeOf#STEPS_A_READING_TAKES}. */
        STEPS_A_READING_TAKES
    }

    /**
     * How many ways some parts a case is taken apart on can come out together, where they
     * compare one number. A count of what the numbers leave and of nothing a reading does.
     */
    public sealed interface Diagnosis {}

    /**
     * Comparisons of one affine form that each order it against a constant: their truths come
     * out by which side of each point the value is on, so no more ways than one past the points.
     *
     * @param quantity    the form, without its constant, as its quantities are spelled
     * @param comparisons how many of the parts compare it so
     * @param points      how many points they turn at, told apart by the value and by whether
     *                    the value itself is on the side above
     * @param waysAtMost  how many ways their truths can come out together at most: one past the
     *                    points, of the two to the power of {@code comparisons} they would if
     *                    nothing tied them
     */
    public record OrderedBoundaries(String quantity, int comparisons, int points, int waysAtMost)
            implements Diagnosis {

        public OrderedBoundaries {
            Objects.requireNonNull(quantity, "the boundaries are of some quantity");
            if (comparisons < 2 || points < 1 || points > comparisons
                    || waysAtMost != points + 1) {
                throw new IllegalArgumentException("comparisons at points, one way past them: "
                        + comparisons + ", " + points + ", " + waysAtMost);
            }
        }
    }

    /**
     * Comparisons of remainders of one dividend by one divisor: one remainder decides them all.
     *
     * @param dividend    the dividend, without its constant, as its quantities are spelled
     * @param divisor     what it is divided by
     * @param comparisons how many of the parts compare a remainder of it so
     * @param ways        how many ways their truths come out together, one remainder at a time
     */
    public record CorrelatedRemainders(String dividend, int divisor, int comparisons, int ways)
            implements Diagnosis {

        public CorrelatedRemainders {
            Objects.requireNonNull(dividend, "remainders are of some dividend");
            if (comparisons < 2 || ways < 1 || ways > divisor) {
                throw new IllegalArgumentException("comparisons coming out no more ways than"
                        + " there are remainders: " + comparisons + ", " + ways + " of "
                        + divisor);
            }
        }
    }

    /** One thing in the model that made some of the parts a case is taken apart on. */
    public sealed interface Factor {}

    /**
     * A choice the model writes: an {@code if}, a {@code match}, or an operation of the language
     * whose answer is one of several cases.
     *
     * @param construct    the construct, in the copy of the model it was read in
     * @param kind         which kind of choice
     * @param alternatives among how many one choice there chooses: two for an {@code if}, the
     *                     arms of a {@code match}, the cases of an operation
     * @param times        how many of its choosings the case is taken apart on: one on each
     *                     application of a closure it stands in, and one wherever else it is read
     * @param operation    the operation, for the cases of one
     */
    public record Choice(ModelOccurrence construct, ChoiceKind kind, int alternatives, int times,
                         Optional<ValueName.Stdlib> operation) implements Factor {

        public Choice {
            Objects.requireNonNull(construct, "a choice is made at some construct");
            Objects.requireNonNull(kind, "a choice is of some kind");
            Objects.requireNonNull(operation, "an operation makes it or none does");
            if (alternatives < 2 || times < 1) {
                throw new IllegalArgumentException("a choice among some, made some times: "
                        + alternatives + ", " + times);
            }
        }
    }

    /** Which kind of choice a construct of the model makes, as its author wrote it. */
    public enum ChoiceKind {

        /** An {@code if}, choosing a branch. */
        IF,

        /** A {@code match}, choosing an arm. */
        MATCH,

        /** An operation of the language whose answer is one of several cases of its arguments. */
        CASES
    }

    /**
     * A call of one of the language's operations that applies a closure, on as many of its
     * applications as the case is taken apart on parts of.
     *
     * @param call         the call, in the copy of the model it was read in
     * @param operation    the operation called
     * @param applications on how many of its applications some part the case is taken apart on
     *                     was read
     */
    public record Applications(ModelOccurrence call, ValueName.Stdlib operation,
                               int applications)
            implements Factor {

        public Applications {
            Objects.requireNonNull(call, "applications are made by some call");
            Objects.requireNonNull(operation, "of some operation");
            if (applications < 1) {
                throw new IllegalArgumentException("a closure applied is applied some times");
            }
        }
    }

    /**
     * The ways of keeping elements a statement over what was kept is written out over: one part
     * for each way the truths keeping them come out.
     *
     * @param keptBy the constructs of the model the truths keeping the elements are
     * @param ways   the most parts one writing out made that the case is taken apart on
     * @param times  how many writings out the case is taken apart on parts of: one on each
     *               application of a closure it stands in
     */
    public record KeptWays(List<ModelOccurrence> keptBy, int ways, int times) implements Factor {

        public KeptWays {
            keptBy = List.copyOf(keptBy);
            if (ways < 1 || times < 1) {
                throw new IllegalArgumentException("ways written out some times: " + ways
                        + ", " + times);
            }
        }
    }
}
