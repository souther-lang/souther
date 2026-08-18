package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.Partitions;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's rows reach of the distinctions its model draws.
 *
 * <p>Values only — no classifier, no representative source. What decides a class is a function, and a
 * function held in a memoised answer never compares equal to the same function computed again, so
 * everything downstream would recompute on every ask. What a report needs is the names and the
 * numbers; the functions are used on the way here and left behind.
 *
 * @param axes         one entry per position the model divides
 * @param boundaries   one entry per rule that drew a line, per side of it
 * @param notDerivable positions no class came back for, each saying whether the model divides them
 *                     no way at all or this could not read what it divides them by. Both used to be
 *                     one list of paths, and the sentence written from it claimed the first about
 *                     both
 * @param omitted      positions dropped for being past the axis limit, with what dropping each
 *                     one cost — a position that was carrying a boundary leaves the rows there
 *                     unmeasured rather than covered
 * @param whyUnclassified why the rows counted in {@link AxisCoverage#unclassifiedRows} could not be
 *                     placed. The count is the measurement and this is what it came out of, which
 *                     is why they are two things and not one wider count. Not a report's list of
 *                     reasons: these are what classification observed, and joining them to
 *                     everything else a module could not read happens where that list is built
 */
public record PartitionEvidence(Partitioned partitioned, Bounded bounded,
                                PairSpace pairs,
                                List<souther.compiler.partition.UndividedPosition> notDerivable,
                                List<souther.compiler.inputs.UnreadRule> unread,
                                List<Partitions.OmittedAxis> omitted,
                                List<Incompleteness> whyUnclassified) {


    /**
     * No measure of this kind here at all, which is not a measure that came back empty.
     *
     * <p>What a {@code >->} composition gets. It has no positions of its own for either of these to
     * be about, the way it has no arms, and no row anybody writes would give it one — so the two
     * answer inapplicable, and a verdict that counted them would hold every model with a composition
     * in it open for a measurement that was never anybody's to make.
     */
    public static final PartitionEvidence NONE = new PartitionEvidence(Partitioned.absent(),
            Bounded.absent(), PairSpace.NONE, List.of(), List.of(), List.of(), List.of());

    public PartitionEvidence {
        notDerivable = List.copyOf(notDerivable);
        unread = List.copyOf(unread);
        omitted = List.copyOf(omitted);
        whyUnclassified = List.copyOf(whyUnclassified);
    }

    /**
     * A position something is written about that this reading did not turn into a line, and what
     * stopped it.
     *
     * <p>The reason in the vocabulary a document promises its reader, not the one this compiler
     * records for itself: which capability was missing is this compiler's own business, and which
     * kind of thing stopped the derivation is what a reader can act on.
     */
    public record UnreadPosition(String at,
                                 souther.compiler.partition.UndividedPosition.Reason reason) {}

    /**
     * Every position this reading carries an unread finding about: a rule it did not turn into a
     * line, and a position it divided no way and said why.
     *
     * <p>Not every position whose rules this reading is short of. How far the reading of a position
     * ran is what its axis carries ({@link AxisCoverage#read()}), and a position measured on a
     * reading that did not run to the end need have no entry here — these are findings about rules
     * and that is an account of a position. Read as the whole of what was left unread, this would
     * be the very thing it was written to stop: one question answered by a list that answers
     * another.
     *
     * <p>One reading, and the two surfaces write from it. It used to be assembled twice — a person
     * was shown the rules no line came from together with the positions divided no way, and the
     * document was written from the second alone — so a rule left unread at a position the axes
     * went on to measure reached one reader and stopped there. Nothing was wrong with either list;
     * what was wrong is that one question was answered by reading two of them in one place and one
     * of them in the other.
     *
     * <p>The rules come first and the undivided positions after, deduplicated: a position can be
     * in both, and it is one thing that was found about it either way.
     */
    public List<UnreadPosition> notRead() {
        List<UnreadPosition> out = new java.util.ArrayList<>();
        for (souther.compiler.inputs.UnreadRule each : unread) {
            add(out, new UnreadPosition(each.at().toString(),
                    souther.compiler.partition.ReportedReason.of(each.why())));
        }
        for (souther.compiler.partition.UndividedPosition position : notDerivable) {
            if (position.why() instanceof souther.compiler.partition.UndividedPosition.Why
                    .CannotDerive stopped) {
                add(out, new UnreadPosition(position.at().toString(), stopped.reason()));
            }
        }
        return List.copyOf(out);
    }

    private static void add(List<UnreadPosition> out, UnreadPosition said) {
        if (!out.contains(said)) {
            out.add(said);
        }
    }

    /** The positions, for a reader that wants them and not what the measure made of itself. */
    public List<AxisCoverage> axes() {
        return partitioned.at();
    }

    /** The lines, likewise. */
    public List<BoundaryAssessment> boundaries() {
        return bounded.at();
    }

    /**
     * The positions this behavior is measured at, and — where there are none — why not.
     *
     * <p>The list alone cannot say. An empty one is what a behavior whose model divides nothing has
     * and what a behavior whose positions could not be read has, and a reader counting entries calls
     * both of them measured and finds no gaps. So the measure answers for itself, and the entries are
     * what it answered with.
     */
    public record Partitioned(List<AxisCoverage> at, MeasurementStatus status, Reason reason) {

        /** Why no position was measured. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** Nothing came back divided. Whether the model draws no line anywhere or the reading
             *  stopped short of one is not something this can tell, and only a proof excludes: the
             *  positions it could not derive are named beside it and may be carrying rules. */
            NO_AXIS_DERIVED(MeasurementStatus.NOT_MEASURED),
            /** This behavior has no positions for the measure to be about — a {@code >->}
             *  composition, which is measured at its stages. */
            NO_SUBJECT(MeasurementStatus.NOT_APPLICABLE);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        public static Partitioned of(List<AxisCoverage> at) {
            return at.isEmpty()
                    ? new Partitioned(List.of(), Reason.NO_AXIS_DERIVED.status(),
                            Reason.NO_AXIS_DERIVED)
                    : new Partitioned(at, MeasurementStatus.COMPLETE, null);
        }

        static Partitioned absent() {
            return new Partitioned(List.of(), Reason.NO_SUBJECT.status(), Reason.NO_SUBJECT);
        }

        public Partitioned {
            at = List.copyOf(at);
            Unavailable.check(status, reason);
        }
    }

    /** The lines some rule drew that this behavior is measured at, and — where there are none — why
     * not. The same argument as {@link Partitioned}: an empty list of obligations reads exactly like
     * a measure that was made and found everything met. */
    public record Bounded(List<BoundaryAssessment> at, MeasurementStatus status, Reason reason) {

        /** Why no line was measured. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No obligation was derived. A model whose bounds sit one type away from the position
             *  the behavior takes has this, and so has one with no bound anywhere; nothing here can
             *  tell them apart, and calling it measured said the rows carrying a model's whole risk
             *  had earned nothing. */
            NO_LINES_DERIVED(MeasurementStatus.NOT_MEASURED),
            /** This behavior has no positions for a line to be drawn on — a {@code >->} composition,
             *  which is measured at its stages. */
            NO_SUBJECT(MeasurementStatus.NOT_APPLICABLE);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        public static Bounded of(List<BoundaryAssessment> at) {
            return at.isEmpty()
                    ? new Bounded(List.of(), Reason.NO_LINES_DERIVED.status(),
                            Reason.NO_LINES_DERIVED)
                    : new Bounded(at, MeasurementStatus.COMPLETE, null);
        }

        static Bounded absent() {
            return new Bounded(List.of(), Reason.NO_SUBJECT.status(), Reason.NO_SUBJECT);
        }

        public Bounded {
            at = List.copyOf(at);
            Unavailable.check(status, reason);
        }
    }

    /**
     * How many two-class combinations the rows reach, and how much is known about the rest.
     *
     * <p>Three numbers rather than a percentage, because the denominator is not known. A combination
     * a row reaches is proven reachable — the row is the proof. A combination no row reaches has not
     * been shown impossible; nothing has tried to build one. Calling those unreachable would flatter
     * the coverage, and calling them missing would send the author after rows that may not exist.
     *
     * <p>{@link #provenInfeasible} is what a search settled: a combination whose values were tried and
     * refused for a reason that is about the combination, or one ruled out by a constraint. Nothing
     * fills it until something builds candidates, and a candidate that failed to build is not it —
     * another value of the same two classes may well have built.
     *
     * @param truncated whether the space was too large to enumerate, so these numbers describe part
     *                  of it
     * @param status    {@code PARTIAL} where the rows these were counted from are not all the rows
     *                  there were, or not all of them could be placed. Reached is still reached; what
     *                  is not reached is then undecided rather than untried
     */
    public record PairSpace(int total, int covered, int witnessedFeasible, int provenInfeasible,
                            int unknown, boolean truncated, MeasurementStatus status, Reason reason) {

        /** Why the combinations have no numbers. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No row names this behavior, so nothing sits anywhere. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        public static final PairSpace NONE =
                new PairSpace(0, 0, 0, 0, 0, false, MeasurementStatus.COMPLETE, null);

        public static PairSpace unavailable(int total, Reason reason) {
            return new PairSpace(total, 0, 0, 0, total, false, reason.status(), reason);
        }

        public PairSpace {
            Unavailable.check(status, reason);
        }

        /** Whether a single ratio would say anything. With unknowns in the denominator it would not. */
        public boolean decided() {
            return unknown == 0 && !truncated;
        }
    }



    /**
     * How much of one position's partition the rows reach.
     *
     * @param classes          the classes a row can be written at, which is what the model divides
     *                         the position into: a case its rules refuse is not one of them. Nothing
     *                         a body declares narrows this — what it declared is said beside these
     *                         numbers ({@link ClaimAnnotations}) and never into them
     * @param excluded         the classes the rules rule out and a body's claim named, so that a report says what it took
     *                         out rather than showing a position with fewer classes than the type has
     * @param unclassifiedRows rows whose value at this position could not be read. Above zero, an
     *                         unreached class is undecided rather than unreached.
     */
    public record AxisCoverage(String axis, String path, List<String> classes, Set<String> covered,
                               int unclassifiedRows, MeasurementStatus status, Reason reason,
                               Reading read) {

        /**
         * Which of this position's rules nothing accounted for.
         *
         * <p>It qualifies the classes and nothing else says it. A rule nothing took in may yet
         * refuse a value one of the classes holds, so the classes are the denominator the model
         * states and not one every class of which is known to be inhabited.
         *
         * <p><b>The questions the model raises, not a reading's account of itself.</b> There are
         * several readings of a clause and they are short of different things: the one that turns
         * clauses into sets of values has no word for a range, so it is short at every numeric
         * position an invariant bounds while two others have those rules whole. Written off that
         * reading, this line said a model had gone unread on the strength of a fact about this
         * compiler, two rows above a boundary drawn from the very rule it was about (issue #842).
         *
         * <p>Each entry names the rule. A position was all a reader used to be given, which left
         * them looking for a rule the sentence never named.
         */
        public sealed interface Reading {

            /** Nothing the rules raise about this position is left standing. */
            record Answered() implements Reading {}

            /**
             * The walk never reached the rules written about this position, so what is written
             * there is not known.
             *
             * <p>Its own answer beside the one below, and not a list that came back empty. Nothing
             * was found here because nothing looked: a position whose rules were never enumerated
             * has no rule to name and is not a position whose rules were all accounted for, and
             * telling an author the second sends them away from the one thing worth knowing
             * (issue #791).
             */
            record NotReached() implements Reading {}

            /** Some of it is, and which rules raised it. */
            record Standing(List<Unanswered> questions) implements Reading {

                public Standing {
                    if (questions.isEmpty()) {
                        throw new IllegalArgumentException(
                                "nothing standing is a different answer");
                    }
                    questions = List.copyOf(questions);
                }
            }
        }

        /**
         * One question a rule raised that nothing answered.
         *
         * <p>The rule as words and not as whatever identifies it. Which rules there are is a
         * question with more than one answer in it — an invariant's clause, a comparison in a body —
         * and a reader downstream that took one of them apart would have to be taught the next; the
         * words come from the one place that names a rule, and everything here is a string by the
         * time it arrives.
         *
         * @param rule     the rule, as a report names it
         * @param question what about the position it raised, in the words a document promises
         * @param subject  what the question is about, spelled the way a report names it. Carried
         *                 rather than worked out downstream from the axis: the questions do not
         *                 share a subject — which values may stand somewhere is about a position,
         *                 and a line is about a number taken of one — and a renderer choosing
         *                 between the two is how a reading of a string's values came to be printed
         *                 against its length
         */
        public record Unanswered(String rule, souther.compiler.check.CoverageObligation question,
                                 String subject) {}

        /** Nothing standing, which is what a caller holding no account of its own says. */
        public static final Reading ANSWERED = new Reading.Answered();

        /** Why a position has no coverage numbers. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No row names this behavior. An absence of evidence is not a set of gaps, so the classes
             *  nothing sits in are not classes nothing reaches. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        /** Which classes there are is a fact about the model, and no row has to exist for it to be
         *  so — which is why a position nothing was measured at still names them. */
        public static AxisCoverage unavailable(String axis, String path, List<String> classes,
                                               Reason reason, Reading read) {
            return new AxisCoverage(axis, path, classes, Set.of(), 0, reason.status(), reason, read);
        }

        public AxisCoverage {
            classes = List.copyOf(classes);
            covered = Set.copyOf(covered);
            if (read == null) {
                throw new IllegalArgumentException(
                        "a position with no account of what was read about its values: " + path);
            }
            Unavailable.check(status, reason);
        }

        public List<String> uncovered() {
            return classes.stream().filter(c -> !covered.contains(c)).toList();
        }
    }

}
