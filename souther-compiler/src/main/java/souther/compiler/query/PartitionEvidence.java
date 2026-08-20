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
                                List<souther.compiler.inputs.PositionReadingBlocked> blocked,
                                List<Unanswered> unanswered,
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
            Bounded.absent(), PairSpace.NONE, List.of(), List.of(), List.of(), List.of(),
            List.of(), List.of());

    public PartitionEvidence {
        notDerivable = List.copyOf(notDerivable);
        unread = List.copyOf(unread);
        blocked = List.copyOf(blocked);
        unanswered = List.copyOf(unanswered);
        omitted = List.copyOf(omitted);
        whyUnclassified = List.copyOf(whyUnclassified);
    }

    /**
     * One question a rule of the model raised about a position that nothing answered.
     *
     * <p>Beside the measures rather than inside one of them. The questions are the model's and every
     * measure here is one reader of them, so a position an axis could not be derived at is not a
     * position whose rules went unwritten — read off the axes, {@code value <= 10 * 2} raised a
     * question about its line, left it standing, and was reported as a model with nothing to answer
     * for, because no axis survived to carry it.
     *
     * <p>The rule as words and not as whatever identifies it. Which rules there are is a question
     * with more than one answer in it — an invariant's clause, a comparison in a body — and a reader
     * downstream that took one of them apart would have to be taught the next; the words come from
     * the one place that names a rule, and everything here is a string by the time it arrives.
     *
     * @param asked   the question as the accounting that raised it holds it: which rule, how a
     *                reader finds that rule, and what is owed. Handed on whole rather than taken
     *                apart — every round of this lost a part at a seam, and what is not taken apart
     *                cannot lose one. Which rule it is tells one question from another; the handle
     *                beside it is what a document shows and is not in step with that wherever a rule
     *                has no name
     * @param at      the position it is about, spelled the way a report names it. The walk's and not
     *                the accounting's: which position of a behavior's inputs a rule was filed at is
     *                what the walk that found it says, and the subject is relative to it
     * @param measure the number the position is measured by, where a border falls on one. Beside the
     *                subject because it is the reading's spelling of it and this document promises
     *                both
     */
    public record Unanswered(souther.compiler.check.RuleAccounting.Unanswered asked, String at,
                             String measure) {

        /** Which rule of the model raised it, which is what tells one question from another. */
        public souther.compiler.check.RuleRef rule() {
            return asked.rule();
        }

        /** How a reader finds that rule, which is not what tells it from another. */
        public souther.compiler.check.RuleCitation cited() {
            return asked.cited();
        }

        /** What it asks. Which measure's section a reader meets it in follows from this. */
        public souther.compiler.check.CoverageObligation question() {
            return asked.owed().obligation();
        }

        /**
         * And what it asks it about.
         *
         * <p>As the reading that raised it named it, and not as words for it: a position, a number
         * taken of one, and the comparison that drew a border between two moving terms are three
         * things, and two of them cannot be told apart once they are one string.
         */
        public souther.compiler.check.Owed.Subject subject() {
            return asked.owed().subject();
        }
    }

    /**
     * One entry of what this reading could not read, as a document writes it.
     *
     * <p>Two shapes because two authorities answer. A rule was read and could not be used, and the
     * finding names which rule; or the reading never got to the rules of a position, and there is
     * no rule to name. Written as one shape with the rule left out where there is none, a consumer
     * would have to read an absent field to know which of the two it was holding â which is the
     * reconstruction this pair exists to stop.
     *
     * <p>The reason in the vocabulary a document promises its reader, not the one this compiler
     * records for itself: which capability was missing is this compiler's own business, and which
     * kind of thing stopped the derivation is what a reader can act on.
     */
    public sealed interface NotRead {

        /** The position it is about, spelled the way a report names it. */
        String at();

        /** What stopped it, in the words a document promises. */
        souther.compiler.partition.UndividedPosition.Reason reason();

        /** A rule of the model this read and could not turn into a line. */
        record ARule(souther.compiler.inputs.UnreadRule finding) implements NotRead {

            @Override
            public String at() {
                return finding.at().toString();
            }

            @Override
            public souther.compiler.partition.UndividedPosition.Reason reason() {
                return souther.compiler.partition.ReportedReason.of(finding.why());
            }

            /** Which rule, which is what tells this finding from the one beside it. */
            public souther.compiler.check.RuleRef rule() {
                return finding.rule();
            }

            /** And how a reader finds that rule, which is not what tells it from another. */
            public souther.compiler.check.RuleCitation cited() {
                return finding.cited();
            }
        }

        /** A position whose rules this reading never arrived at. */
        record APosition(souther.compiler.inputs.PositionReadingBlocked finding)
                implements NotRead {

            @Override
            public String at() {
                return finding.at().toString();
            }

            @Override
            public souther.compiler.partition.UndividedPosition.Reason reason() {
                return souther.compiler.partition.ReportedReason.of(finding.why());
            }
        }
    }

    /**
     * Everything this reading could not read: the rules it did not turn into lines, and the
     * positions it did not reach the rules of.
     *
     * <p>Not every position whose rules this reading is short of. How far the reading of a position
     * ran is what its axis carries ({@link AxisCoverage#read()}), and a position measured on a
     * reading that did not run to the end need have no entry here — these are findings about rules
     * and that is an account of a position. Read as the whole of what was left unread, this would
     * be the very thing it was written to stop: one question answered by a list that answers
     * another.
     *
     * <p><b>Both halves are canonical and neither is recovered from a verdict.</b> This used to add
     * the positions {@link #notDerivable} could not derive, which is an account of whether anything
     * divides a position and not of what was read — and a rule left unread reached that list only
     * after being projected onto the position it was about, losing the rule on the way. So a rule
     * and the position it is at came back as two entries of one list, one of which could name
     * nothing. What is joined here are the two findings themselves, each from the
     * reader that made it.
     *
     * <p>The rules come first and the positions after, in the order each was read.
     */
    public List<NotRead> notRead() {
        List<NotRead> out = new java.util.ArrayList<>();
        unread.forEach(each -> out.add(new NotRead.ARule(each)));
        blocked.forEach(each -> out.add(new NotRead.APosition(each)));
        return List.copyOf(out);
    }

    /** The positions, for a reader that wants them and not what the measure made of itself. */
    public List<AxisCoverage> axes() {
        return partitioned.at();
    }

    /** The lines, likewise. */
    public List<BorderAssessment> boundaries() {
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
    public record Bounded(List<BorderAssessment> at, MeasurementStatus status, Reason reason) {

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

        public static Bounded of(List<BorderAssessment> at) {
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
        public record Reading(Reach reach, boolean everyQuestionAboutItsValuesWasAnswered) {

            /**
             * Whether what this measure is short of is nothing.
             *
             * <p>Its own questions and not every question the position raises. Which values may
             * stand somewhere is what classes are made of and is this measure's to be short of;
             * where the line falls is the border measure's, and a position with a line nothing
             * answered has classes that are all the model divides it into. Counted here, the two
             * measures #869 told apart would go back to one number.
             */
            public boolean answered() {
                return reach == Reach.EVERY_RULE && everyQuestionAboutItsValuesWasAnswered;
            }
        }

        /**
         * Whether the walk reached the rules written about this position.
         *
         * <p>Its own axis beside the questions, and not another arm among them. Nothing was found
         * where nothing looked, and an empty list of questions says every rule was accounted for —
         * which is the opposite of the one thing worth knowing (issue #791). The two are not
         * exclusive either: a rule can have arrived and gone unaccounted for while a subtree beside
         * it was never entered, and a type that made them arms could not say so.
         */
        public enum Reach {

            /** Every rule written about the position reached a reading. */
            EVERY_RULE,

            /** Some of them did not, so what is written there is not known. */
            SOME_OUT_OF_SIGHT
        }

        /** Nothing standing, which is what a caller holding no account of its own says. */
        public static final Reading ANSWERED = new Reading(Reach.EVERY_RULE, true);

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

        /**
         * The classes of this position no row is in, each knowing which position it is a class of.
         *
         * <p>A bare name used to be enough because one axis was read at a time. It is not enough to
         * be told apart by: two positions of one behavior divide into classes named after the same
         * cases, and a class name alone is the same words about two of them. A reader given the
         * name and nothing else cannot say which position to write the row at, and neither can a
         * document trying to join the two back together.
         *
         * <p>Which of {@link #axis} and {@link #path} names the position to a reader is not settled
         * here. The two are for different readers and a value that chose one of them would be this
         * measure writing a report's sentence.
         */
        public List<AxisClass> uncovered() {
            return classes.stream().filter(c -> !covered.contains(c))
                    .map(c -> new AxisClass(this, c)).toList();
        }
    }

    /**
     * One class of one position.
     *
     * <p>A class is a class <em>of</em> something, and the two halves travel together for the same
     * reason {@link BorderAssessment.Point} exists: a count, a document and a finding are three
     * readings of one item, and each of them flattening it its own way is where a part goes missing.
     */
    public record AxisClass(AxisCoverage axis, String name) {

        public AxisClass {
            // A class with no position is the thing this exists to make unsayable. Held here and
            // not only where a finding takes one: the value is what says a class is a class of
            // something, and a reader that got one without a position would find out at whichever
            // sentence names the position first.
            java.util.Objects.requireNonNull(axis, "a class is a class of a position");
            java.util.Objects.requireNonNull(name, "a class of a position has a name");
        }
    }

}
