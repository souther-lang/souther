package souther.compiler.query;

import souther.compiler.observe.Incompleteness;

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
 * <p><b>Why these are still here, beside the measures that went without them.</b> #953 moved every
 * fact that costs a measure something into what weakened that measure, and the obvious next step is
 * to drop the lists and project them back out. Two of them cannot be: {@code unread} holds rules
 * that were set aside and left neither measure short — a comparison relating two positions is read,
 * says what it says, and divides nothing ({@code BlockReason.RuleWithoutLineReason.leavesShort}) — so the
 * weakening is a strictly smaller set than what a reader is owed, and a projection would drop
 * exactly those rules from the report.
 *
 * <p>The other, {@code unanswered}, looks as though it would project: every unanswered question
 * goes to the measure that answers it. It is kept anyway, because that is a reading of the code and
 * not a measurement of it, and the rule this normalization follows is to drop only what something
 * shows is covered.
 *
 * @param whyUnclassified why the rows counted in {@link AxisCoverage#unclassifiedRows} could not be
 *                     placed. The count is the measurement and this is what it came out of, which
 *                     is why they are two things and not one wider count. Not a report's list of
 *                     reasons: these are what classification observed, and joining them to
 *                     everything else a module could not read happens where that list is built
 */
public record PartitionEvidence(Measure<List<AxisCoverage>> partitioned,
                                Measure<List<BorderAssessment>> bounded,
                                PairSpace pairs,
                                List<souther.compiler.partition.UndividedPosition> notDerivable,
                                List<souther.compiler.inputs.RuleWithoutALine> unread,
                                List<souther.compiler.inputs.PositionReadingBlocked> blocked,
                                List<souther.compiler.inputs.PositionValuesNotSeparated> notSeparated,
                                List<Unanswered> unanswered,
                                List<Incompleteness> whyUnclassified) {


    /**
     * No measure of this kind here at all, which is not a measure that came back empty.
     *
     * <p>What a {@code >->} composition gets. It has no positions of its own for either of these to
     * be about, the way it has no arms, and no row anybody writes would give it one — so the two
     * answer inapplicable, and a verdict that counted them would hold every model with a composition
     * in it open for a measurement that was never anybody's to make.
     */
    public static final PartitionEvidence NONE = new PartitionEvidence(
            PartitionDerivation.noSubject(), BoundaryDerivation.noSubject(),
            PairSpace.NONE, List.of(), List.of(), List.of(), List.of(),
            List.of(), List.of());

    /**
     * What the model divides a behavior into, where its boundary could not be worked out.
     *
     * <p>Not {@link #NONE}. That says the model holds no subject for either measure and no row would
     * change it, which is a claim about the model; this is a measure that was asked for, started and
     * could not be finished, and what it went without is beside it. The two used to be one absent
     * key, which is how a behavior whose parameter named an unresolved type reached a reader with
     * nothing to read and nothing saying why.
     *
     * <p>Nothing here has a declaration to fall back on. The positions this measure is about are the
     * ones the model divides, worked out from the boundary and from the rules written about it —
     * unlike the positions of the signature measure, which a declared behavior writes down and which
     * are known there whatever the boundary did. So both measures come back short and only one of
     * them still knows how many places it was to have counted at.
     *
     * <p>The pair space is sized at nought for the same reason: a size is a product over those
     * positions. Nothing reads the number — the measurement beside it says none could be finished,
     * and a document leaves the whole section out rather than writing a size nobody worked out.
     */
    public static PartitionEvidence boundaryNotDerived(String behavior) {
        return new PartitionEvidence(
                BoundaryForMeasurement.failed(behavior), BoundaryForMeasurement.failed(behavior),
                PairSpace.boundaryNotDerived(behavior), List.of(), List.of(), List.of(), List.of(),
                List.of(), List.of());
    }

    /** Whether this is what a behavior whose boundary could not be worked out comes to. */
    public boolean boundaryNotDerived() {
        return BoundaryForMeasurement.wasNotDerived(partitioned);
    }

    public PartitionEvidence {
        notDerivable = List.copyOf(notDerivable);
        unread = List.copyOf(unread);
        notSeparated = List.copyOf(notSeparated);
        blocked = List.copyOf(blocked);
        unanswered = List.copyOf(unanswered);
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
     * One entry of the document's {@code notRead}, as a document writes it.
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
    /*
     * `NotRead` is the document's word, and it is wider than the word. A rule read from end to end
     * that draws no line arrives here, and the array it is written to is called `notRead` in every
     * document of schema 7. Renaming that is a version and a retired word, and the schema already
     * tells a consumer which entries are about a limit of this compiler and which are facts about
     * the rule — so the word stays, and the name here is the word, because this is where the
     * document's shape is written and a type named for one thing writing a field named for another
     * is a second place to be kept in step.
     *
     * Behind this projection it means what it says. Nothing in the compiler calls a rule it read to
     * the end one it could not read: what a reading fell short of is `BlockReason.ReadingStopReason`
     * and a rule that is no line at a position is `RuleWithoutALine`. The older word lives on this
     * side alone.
     */
    public sealed interface NotRead {

        /** The position it is about, spelled the way a report names it. */
        String at();

        /** What stopped it, in the words a document promises. */
        souther.compiler.partition.UndividedPosition.Reason reason();

        /**
         * Whether this is a reading that stopped, rather than one that ran to the end and left the
         * position divided no way.
         *
         * <p>Both are here because both leave the position with nothing from that rule, and they
         * are opposite sentences to whoever is told one: a form no reader takes apart is a limit of
         * this compiler, and a rule whose quantity is empty was read from end to end and says what
         * it says. Read off the reason word instead, a renderer would be deciding which half a word
         * belongs to — a second place for the split to be made, and the two would disagree the day
         * a word is added.
         */
        boolean readingStopped();

        /** A rule of the model this read and could not turn into a line. */
        record ARule(souther.compiler.inputs.RuleWithoutALine finding) implements NotRead {

            @Override
            public String at() {
                return finding.at().toString();
            }

            @Override
            public souther.compiler.partition.UndividedPosition.Reason reason() {
                return souther.compiler.partition.ReportedReason.of(finding.why());
            }

            @Override
            public boolean readingStopped() {
                return finding.why() instanceof souther.compiler.inputs.BlockReason.RuleReadingStopped;
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

            /** A walk that never arrived at the rules of a position is a reading that stopped,
             *  whatever stopped it. */
            @Override
            public boolean readingStopped() {
                return true;
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

    /**
     * What every measure of this behavior's positions went without, all of them.
     *
     * <p>Asked here rather than assembled by whoever wants it. There are six measures under this —
     * the two derivations, each position, each point of each border, and the combinations — and a
     * reader listing them is a reader who has to be told when a seventh arrives. The report listed
     * them, so a measure added here would have been a measure the report left out of every whole
     * above it, silently (issue #953).
     */
    public WeakeningSet weakening() {
        WeakeningSet out = partitioned.weakening()
                .union(bounded.weakening())
                .union(pairs.counted().weakening());
        for (AxisCoverage axis : axes()) {
            out = out.union(axis.reached().weakening());
        }
        for (BorderAssessment.Point point : BorderAssessment.pointsOf(boundaries())) {
            out = out.union(point.item().weakening());
        }
        return out;
    }

    /** The positions, for a reader that wants them and not what the measure made of itself. Empty
     *  where the measure has none to show, which its own answer says the reason for. */
    public List<AxisCoverage> axes() {
        return PartitionDerivation.at(partitioned);
    }

    /** The lines, likewise. */
    public List<BorderAssessment> boundaries() {
        return BoundaryDerivation.at(bounded);
    }

    /**
     * How many two-class combinations the rows reach, and how much is known about the rest.
     *
     * <p>Three numbers rather than a percentage, because the denominator is not known. A combination
     * a row reaches is proven reachable — the row is the proof. A combination no row reaches has not
     * been shown impossible; nothing has tried to build one. Calling those unreachable would flatter
     * the coverage, and calling them missing would send the author after rows that may not exist.
     *
     * <p>{@code total} is outside the measurement because it is a fact about the model: the product
     * of what a row can be written at is that whether or not anybody counted. What was counted is
     * inside, and a space nobody counted has no counts at all — it used to have four zeroes, which
     * read exactly like a space where nothing was reached.
     *
     * <p>The other thing that used to sit out here was {@code truncated}, a boolean that had to be
     * kept in step with a status beside it (#951 added the check that did it). A space too large to
     * walk is now said once, as what weakened the measurement.
     */
    public record PairSpace(int total, Measurement<PairCounts> counted) {

        /**
         * What the rows reached of the space, where anybody counted.
         *
         * <p>{@code provenInfeasible} is what a search settled: a combination whose values were
         * tried and refused for a reason that is about the combination, or one ruled out by a
         * constraint. Nothing fills it until something builds candidates, and a candidate that
         * failed to build is not it — another value of the same two classes may well have built.
         */
        public record PairCounts(int covered, int witnessedFeasible, int provenInfeasible,
                                 int unknown) {}

        /** Why the combinations have no numbers. */
        public enum NoRows implements souther.compiler.observe.NotMeasuredReason {
            /** No row names this behavior, so nothing sits anywhere. */
            NO_ROWS
        }

        public static final PairSpace NONE =
                new PairSpace(0, new Measurement.Complete<>(new PairCounts(0, 0, 0, 0)));

        /** A space nobody counted. It keeps its size, which the model settles, and has no counts. */
        public static PairSpace noRows(int total) {
            return new PairSpace(total, new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }

        /** The same, where nobody asked for a measurement at all. */
        public static PairSpace notAsked(int total) {
            return new PairSpace(total, new Measurement.NotMeasured<>(NothingWasAsked.NOT_ASKED));
        }

        /** A space whose size was never worked out, because the positions it is a product over
         *  were not. What it is short of is what every measure of that behavior is short of. */
        public static PairSpace boundaryNotDerived(String behavior) {
            return new PairSpace(0, BoundaryForMeasurement.failed(behavior));
        }

        /** A space too large to walk to the end of. What it is measured in part by is the fact that
         *  stopped it, said once. */
        public static PairSpace truncated(String behavior, long size, int limit) {
            int total = (int) Math.min(size, Integer.MAX_VALUE);
            return new PairSpace(total, new Measurement.Partial<>(
                    new PairCounts(0, 0, 0, total),
                    WeakeningSet.of(new Weakening.PairSpaceTruncated(behavior, size, limit))));
        }

        /**
         * The numbers, where a measurement was made.
         *
         * <p>Throws where none was. A measure with no number has none, and an accessor that answered
         * zero would be the thing this type was introduced to remove — a reader would get an answer
         * and no sign that nobody measured it.
         */
        public PairCounts counts() {
            return counted.made().orElseThrow(() -> new IllegalStateException(
                    "a pair space nobody counted was read for its counts"));
        }

        /** Whether a single ratio would say anything. With unknowns in the denominator it would not,
         *  and a measurement that is not complete has them whether or not they were counted. */
        public boolean decided() {
            return counted instanceof Measurement.Complete<PairCounts> whole
                    && whole.value().unknown() == 0;
        }
    }

    /**
     * How much of one position's partition the rows reach.
     *
     * @param classes the classes a row can be written at, which is what the model divides the
     *                position into: a case its rules refuse is not one of them. Outside the
     *                measurement, because it is what the model says and is so whether or not
     *                anybody counted. Nothing a body declares narrows it — what it declared is said
     *                beside these numbers ({@link ClaimAnnotations}) and never into them
     * @param reached what the rows reached of them, where anybody counted. A position nothing was
     *                measured at used to carry an empty {@code covered} and a zero count beside a
     *                status saying so, which reads exactly like a position every class of which
     *                went unreached
     */
    public record AxisCoverage(souther.compiler.partition.AxisId at, String path,
                               List<String> classes, Reading read,
                               Measurement<Reached> reached) {

        /**
         * What the rows reached at one position.
         *
         * @param unclassifiedRows rows whose value at this position could not be read. Above zero,
         *                         an unreached class is undecided rather than unreached — and what
         *                         made them unreadable is what the measurement is weakened by
         */
        public record Reached(Set<String> covered, int unclassifiedRows) {

            public Reached {
                covered = Set.copyOf(covered);
            }
        }

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
        public enum NoRows implements souther.compiler.observe.NotMeasuredReason {
            /** No row names this behavior. An absence of evidence is not a set of gaps, so the
             *  classes nothing sits in are not classes nothing reaches. */
            NO_ROWS
        }

        /** Which classes there are is a fact about the model, and no row has to exist for it to be
         *  so — which is why a position nothing was measured at still names them. */
        public static AxisCoverage noRows(souther.compiler.partition.AxisId at, String path,
                                          List<String> classes, Reading read) {
            return new AxisCoverage(at, path, classes, read,
                    new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }

        /** The same, where nobody asked for a measurement at all. */
        public static AxisCoverage notAsked(souther.compiler.partition.AxisId at, String path,
                                            List<String> classes, Reading read) {
            return new AxisCoverage(at, path, classes, read,
                    new Measurement.NotMeasured<>(NothingWasAsked.NOT_ASKED));
        }

        public AxisCoverage {
            classes = List.copyOf(classes);
            if (read == null) {
                throw new IllegalArgumentException(
                        "a position with no account of what was read about its values: " + path);
            }
        }

        /**
         * The numbers, where a measurement was made.
         *
         * <p>Throws where none was. A measure with no number has none, and an accessor that answered
         * zero would be the thing this type was introduced to remove — a reader would get an answer
         * and no sign that nobody measured it.
         */
        public Reached rows() {
            return reached.made().orElseThrow(() -> new IllegalStateException(
                    "a position nobody measured was read for what the rows reached: " + path));
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
            // Empty where nothing was measured here. An absence of evidence is not a set of gaps:
            // the classes nothing sits in are not classes nothing reaches, and the measurement
            // beside this says which of the two a reader is looking at.
            return reached.made()
                    .map(it -> classes.stream().filter(c -> !it.covered().contains(c))
                            .map(c -> new AxisClass(this, c)).toList())
                    .orElseGet(List::of);
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
