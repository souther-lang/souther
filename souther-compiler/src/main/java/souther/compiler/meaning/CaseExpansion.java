package souther.compiler.meaning;

import souther.compiler.types.ExpansionLineage;
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
 * nothing puts together with another, so it is kept beside the reason and never in it.
 *
 * <p>Three things of different owners, held apart: which case it is ({@link Which}), how a
 * reader names its line, and what the case came to ({@link CameTo}). Which case is the reading's
 * own identity of it and nothing else, so whatever gathers these tells two apart by it alone;
 * what a case came to is an answer about it, and two readings of one case are two answers, never
 * two cases.
 *
 * @param which  which case of which line it is
 * @param line   the quantity the line is on, named the way a report names a border on it
 * @param cutAt  where on the quantity the line is, written as a border's level is: what tells a
 *               reader two lines on one quantity apart
 * @param cameTo how many ways the case was, what made its parts, and what the numbers leave
 */
public record CaseExpansion(Which which, String line, String cutAt, CameTo cameTo) {

    public CaseExpansion {
        Objects.requireNonNull(which, "some case of some line");
        Objects.requireNonNull(line, "cases are a line's");
        Objects.requireNonNull(cutAt, "a line is somewhere on its quantity");
        Objects.requireNonNull(cameTo, "and came to something");
    }

    /**
     * One place an author's line was put: which of their lines, and the relation it came to
     * there — the place of a line as the reading that put it there tells places apart
     * ({@code PlaceOfALine}), both halves, since two lines an author wrote can come to one
     * relation and one line comes to a relation for each case of what a call hands it.
     *
     * @param written  which of the author's lines it is
     * @param relation the relation the line came to, as the reading spelled it
     */
    public record Line(WrittenLine written, Spelling relation) {

        public Line {
            Objects.requireNonNull(written, "one of the author's lines");
            Objects.requireNonNull(relation, "of some relation");
        }
    }

    /**
     * Which case of which line: the place of the line, and the condition the case was said as,
     * which is what a case is told apart by wherever it is read ({@link
     * DecidingCase#eachByItsOwnCondition}).
     *
     * @param line      the place of the line
     * @param condition the condition the case was said as
     */
    public record Which(Line line, Proposition condition) {

        public Which {
            Objects.requireNonNull(line, "a case is of some line");
            Objects.requireNonNull(condition, "a case is said as some condition");
        }
    }

    /**
     * What one reading of a case came to.
     *
     * @param counted    how many ways there were of choosing one of what the case stands for
     * @param attributed what the parts the case is taken apart on came from
     * @param diagnosed  how many ways some of those parts can come out together, where they compare
     *                   one number ({@link WhatTheNumbersOfACaseLeave}): what the numbers leave,
     *                   and no count of cases nor of what a rewrite would leave
     */
    public record CameTo(CaseCount counted, Attribution attributed, List<Diagnosis> diagnosed) {

        public CameTo {
            Objects.requireNonNull(counted, "cases are some number of ways");
            Objects.requireNonNull(attributed, "what they came from, or why that was not said");
            diagnosed = List.copyOf(diagnosed);
        }
    }

    /**
     * A case counted, before what its parts came from is read: that is read off how the statement
     * was derived, which the reading that counted it does not hold.
     *
     * @param of      the place of the line
     * @param line    the quantity the line is on
     * @param cutAt   where on it the line is
     * @param asked   the case
     * @param counted how many ways there were of choosing one of what it stands for
     */
    public record Counted(Line of, String line, String cutAt, DecidingCase asked,
                          CaseCount counted) {

        public Counted {
            Objects.requireNonNull(of, "cases are of some place of a line");
            Objects.requireNonNull(line, "cases are a line's");
            Objects.requireNonNull(cutAt, "a line is somewhere on its quantity");
            Objects.requireNonNull(asked, "a case asked");
            Objects.requireNonNull(counted, "cases are some number of ways");
        }

        /** This case, with what made its parts and what the numbers they compare leave. */
        CaseExpansion attributed(Attribution attributed) {
            return new CaseExpansion(new Which(of, asked.condition()), line, cutAt,
                    new CameTo(counted, attributed,
                            WhatTheNumbersOfACaseLeave.of(asked.standsFor())));
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
     * @param multiplied   the helpers whose copies made parts the case's choices held together
     *                     multiply, in the order the cases meet them
     */
    public record Attributed(List<Factor> factors, int partsSplitOn, int unattributed,
                             List<MultipliedHelper> multiplied)
            implements Attribution {

        public Attributed {
            factors = List.copyOf(factors);
            multiplied = List.copyOf(multiplied);
            if (partsSplitOn < 0 || unattributed < 0 || unattributed > partsSplitOn) {
                throw new IllegalArgumentException("parts are some of those split on: "
                        + unattributed + " of " + partsSplitOn);
            }
        }

        /** Every construct of the model this names: what each factor is, and where each helper
         *  multiplied made its parts. */
        public List<ModelOccurrence> constructsNamed() {
            List<ModelOccurrence> out = new ArrayList<>();
            factors.forEach(factor -> out.addAll(factor.constructs()));
            multiplied.forEach(helper -> out.addAll(helper.madeAt()));
            return out;
        }
    }

    /**
     * A helper read more than once — at more than one copy of its body, or on more than one
     * application of a closure its call stands in — whose readings the case chooses among one
     * beside another: two choices made together, each among more than one way, one among parts
     * one reading's comparisons made and the other among parts another reading made
     * ({@code ReadingsChosenOneBesideAnother}). Made together as two choices held together, or as
     * a choice made again past more than one alternative of the other, which is how a walk that
     * reaches a candidate only past every way the one before it fails is taken apart. Declared as
     * a behavior, the helper is not expanded, and each reading is its answer.
     *
     * <p>Not every helper whose comparisons made parts. Readings chosen among as alternatives to
     * each other add to the ways and multiply nothing, and so does a choice inside one alternative
     * alone; one reading whose choices multiply others' is the same reading however it is
     * declared. Neither is told here, and nothing here says what the case would come to: that is
     * another compilation.
     *
     * @param helper the helper
     * @param madeAt the comparisons and the conditions of choices it wrote that made those parts,
     *               each in the copy of the body it was read in, in the order the cases meet them
     */
    public record MultipliedHelper(ValueName.Helper helper, List<ModelOccurrence> madeAt) {

        public MultipliedHelper {
            Objects.requireNonNull(helper, "a helper multiplied");
            madeAt = List.copyOf(madeAt);
            if (madeAt.isEmpty()) {
                throw new IllegalArgumentException("a helper multiplies parts it made somewhere");
            }
        }

        /**
         * The helpers whose copies the copy {@code at} stands in, the one calling this helper
         * first: what its call is written inside on the way out to the behavior's own body. A
         * helper cannot call a behavior, so a call declared as one has to move out past them all.
         */
        public static List<ValueName.Helper> calledInside(ModelOccurrence at) {
            List<ValueName.Helper> out = new ArrayList<>();
            if (at.lineage() instanceof ExpansionLineage.Expansion copy) {
                for (ExpansionLineage each = copy.within();
                        each instanceof ExpansionLineage.Expansion step; each = step.within()) {
                    if (step.expanded() instanceof ValueName.Helper helper) {
                        out.add(helper);
                    }
                }
            }
            return List.copyOf(out);
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
    public sealed interface Factor {

        /** The constructs of the model it is, which is where an author goes about it. */
        default List<ModelOccurrence> constructs() {
            return switch (this) {
                case Choice choice -> List.of(choice.construct());
                case Applications applications -> List.of(applications.call());
                case KeptWays kept -> kept.keptBy();
            };
        }
    }

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
