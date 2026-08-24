package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Place;
import souther.compiler.observe.Classification;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Rows for the classes and the arms a caller says are owed one.
 *
 * <p>The plan comes in and this composes for nothing of its own. Which class of which position no
 * row sits in, and which arm no row goes through, is what a measure reads off the rows and reports;
 * a search working either out again is a second reading of one fact, free to offer a row at a class
 * the report calls reached. A combination of the body's decisions is where a witness for an arm is
 * looked for and is not itself a thing anyone is owed a row at.
 *
 * <p>What comes out is inputs and nothing else. The expected answer is left for a person, because the
 * compiler does not know it: the whole point of a model with no {@code let} is that the answer lives in
 * a legacy system or in someone's head, and a generator that guessed would turn a question into an
 * assertion nobody made.
 *
 * <p>What it reports is not only the rows. Everything on the plan gets an entry saying what came of
 * it, with which of {@link UnresolvedCombination.Reason} it was — the list is that enum's to keep,
 * and naming it here would be a second copy going stale. A generator that returned only the rows it
 * managed would read as though the rest were covered, and one that gave the same answer to every kind
 * would send an author looking for a value that does not exist while a row they could write in a line
 * went unwritten.
 */
public final class Generator {

    /** How many assignments of values one parameter is tried at in one pass. The choices multiply, so
     * this is a bound on the search and not on any one position — and reaching it is reported as the
     * search having stopped, which is a different thing from every assignment having been refused. A
     * parameter with something held in reserve is walked twice, each pass under this bound. */
    private static final int MAX_TUPLES = 256;

    /**
     * How many rows one combination is composed for before the search gives up on it.
     *
     * <p>What a combination leaves open is often several assignments, and the first of them is
     * chosen for what else it covers rather than for reaching the meeting — so a second is worth
     * trying where the first went somewhere else. What this bounds is how much of the search one
     * combination may spend: a group whose reading is wrong misses at every assignment, and without
     * a bound it would work its way through the whole space while every other group waited.
     */
    private static final int MOST_CANDIDATES = 3;

    /** The behavior a row would be written for: what its inputs are called, what they are, and where
     * the model divides them. */
    public record Subject(BehaviorInputs inputs, List<Axis> axes, HeldCounts held) {

        public Subject {
            axes = List.copyOf(axes);
        }

        /**
         * What the reading of the input says about how many its containers hold.
         *
         * <p>Handed in rather than read here, and answered about the positions of the input alone.
         * A coordinate of a {@link ConstructionPlan} is spelled the same way and is not one of
         * these, and what a plan's node holds is read off that node's own type -- which is the
         * separation {@code AConstructionPositionIsNotAnInputPositionTest} keeps.
         */
        public HeldCounts held() {
            return held;
        }



        /**
         * The same three facts a row is read by, which is the point of holding one value.
         *
         * <p>Written out here as well, a row would be generated from one reading of what the
         * behavior takes and read back by another — and how a position is written is exactly what
         * the two came to disagree about.
         */
        public List<String> parameters() {
            return inputs.parameters();
        }

        public List<Type> types() {
            return inputs.types();
        }

        public Symbols symbols() {
            return inputs.symbols();
        }
    }

    /**
     * One row's worth of input, and what it was composed for.
     *
     * <p>The purpose and not the classes it turned out to sit in. Those are two questions — which
     * row this is, and what this run of the generator is handing it — and the second moves with
     * the rest of the model while the first does not. Held as the second, a row composed for one
     * class was named for every position it happened to hold, and an edit somewhere else in the
     * model renamed a row nothing about had changed (issue #967).
     *
     * <p>What a candidate turned out to sit in is not here at all, which is the point: a reader
     * that had it would be free to use it as evidence of coverage, and a row this run offers is a
     * question rather than evidence of anything.
     *
     * <p><b>As many purposes as it answers.</b> One candidate can be what two obligations were
     * waiting for — two arms of the body taken by the one path through it — and each of them is
     * answered by it. Held as one purpose, the two were written as a single composite thing with a
     * name made by joining theirs, which reads as an obligation that was never raised; held as
     * none but the first, the second went unanswered beside a row that answered it.
     *
     * @param purposes what the row was composed for, in the order the things were taken
     * @param inputs   one value per parameter, in the order the behavior takes them
     */
    public record GeneratedRow(List<Purpose> purposes, List<FixtureTemplate> inputs) {

        public GeneratedRow {
            purposes = List.copyOf(purposes);
            inputs = List.copyOf(inputs);
            if (purposes.isEmpty()) {
                throw new IllegalArgumentException("a row is composed for something");
            }
        }

        /** One row composed for one thing, which is what most of the searches here compose. */
        public GeneratedRow(Purpose purpose, List<FixtureTemplate> inputs) {
            this(List.of(purpose), inputs);
        }

        /** What the row is about, where this package has a name for it. An arm is named by the
         *  report and not here, so a row composed for one contributes nothing. */
        public List<String> labels() {
            return purposes.stream().flatMap(purpose -> purpose.labels().stream()).toList();
        }
    }

    /**
     * What a row was composed for.
     *
     * <p>In this package's own words and not the report's. A finding is what a report is written
     * from and lives a layer above; what a search here is asked for is a class of a position, a
     * combination the body decides together, or a point of a border — and a reader upstream joins
     * those to its findings by identity ({@link GenerationResult#attemptAt}).
     */
    public sealed interface Purpose {

        /** What a report writes this row as being about, one label per thing it was composed for. */
        List<String> labels();

        /** One class of one position: the row a class no row is in is owed. */
        record ForAClass(AxisId at, String classId, String label) implements Purpose {

            @Override
            public List<String> labels() {
                return List.of(label);
            }
        }

        /**
         * One arm of the body: the row an arm nothing reaches is owed.
         *
         * <p>The arm and not the combination a witness for it was found at. A combination is where
         * the search looked; what a reader is owed a row for is the arm, and the two came apart as
         * soon as one combination was allowed to answer two arms — written as the combination, that
         * row named a thing nobody asked about and hid the two things that were asked.
         *
         * <p>By the probe alone, which is the arm's identity everywhere. What an arm is called is
         * the report's word ({@code ArmVocabulary}) and is not something this package spells: a
         * name made here would be a second vocabulary for one thing, free to drift from the one the
         * finding is written in.
         */
        record ForAnArm(int probe) implements Purpose {

            @Override
            public List<String> labels() {
                return List.of();
            }
        }

        /**
         * One point of one border: the row an edge nothing sits on is owed.
         *
         * <p>What it was composed for, which is not the same as what a reader may be shown. A
         * border's points coincide — a row at the bottom of two ranges is at both — so what a block
         * offers such a row under is the renderer's to decide, and this says what the search was
         * asked for.
         */
        record ForAPoint(String label) implements Purpose {

            @Override
            public List<String> labels() {
                return List.of(label);
            }
        }

        /**
         * A row nothing here can name from one thing.
         *
         * <p>A border's points coincide — each probe fills the positions its own edge does not name
         * from the bottom of their domains, so two minimum edges compose one row — and which of
         * them is offered is what changes when something else is written. A row named for whichever
         * happened to be offered would be renamed by an edit that did not touch it, so it is
         * written without a name, which the language allows: an unnamed row cannot be addressed
         * from outside, and that is the state of a row nobody has named yet.
         */
        record Unstated() implements Purpose {

            @Override
            public List<String> labels() {
                return List.of();
            }
        }
    }

    /**
     * A row that is already written, as the two things this reads it for.
     *
     * <p>Where its values sit is what says which classes it fills; what its run did is what says
     * which arms of the body it goes through. The second is not derivable from the first, which is
     * the whole of what this issue is about — a row whose values sit in a combination's classes and
     * whose run went elsewhere took none of the arms it names, and looks from the values alone
     * exactly like one that took them.
     *
     * @param at      which class of each divided position the row's values fall in
     * @param watched what came of running it. A sum and not an account that may be empty: a run
     *                that recorded nothing and a row nothing recorded are the same empty account
     *                and are not the same fact, and which of them this is decides what may be
     *                concluded from the row
     */
    public record ObservedRow(Map<AxisId, Classification> at, Watched watched) {

        public ObservedRow {
            at = Map.copyOf(at);
            watched = watched == null ? new Watched.NoAccount() : watched;
        }

        /** A row nothing here can say anything about the run of, for a caller with none to read. */
        public static ObservedRow unseen(Map<AxisId, Classification> at) {
            return new ObservedRow(at, new Watched.NoAccount());
        }
    }

    /**
     * A combination no row could be written for, and why.
     *
     * <p>{@code ALL_CANDIDATES_REJECTED} is not a proof that the combination is impossible. It says
     * every value this tried was refused, which is a fact about the values tried; another value of the
     * same classes may well build. Nothing here writes into {@code provenInfeasible} for that reason.
     *
     * @param said what the class said about itself where it said anything, in its own words. Kept
     *             beside the reason rather than folded into it: the reason is the category a reader
     *             acts on, and this is the sentence that says which case of it this was. Folded into
     *             {@code detail} it would be printed where the subject goes.
     */
    public record UnresolvedCombination(List<String> classes, Reason reason, String detail,
                                        Optional<String> said) {

        public enum Reason {
            /**
             * Nothing here knows how to compose a value of the shape asked for.
             *
             * <p>A fact about this compiler rather than about the model — a collection of more
             * elements than a row is worth carrying is one case of it, and a position nothing built
             * a value at is another. Which is why no sentence read off it says a value cannot be
             * written: the row may be the easiest one in the file to write by hand.
             *
             * <p>And why nothing decides this from the shape of the question. A reason read off the
             * kind of term outlives whatever made it true, and says a value cannot be composed while
             * the same generation composes one in the row above.
             */
            NOTHING_COMPOSES_ONE,
            /** Every value tried was refused at construction. */
            ALL_CANDIDATES_REJECTED,
            /** The search stopped before it got here. */
            SEARCH_LIMIT,
            /**
             * The rules leave no value here, and the whole of what they leave was walked.
             *
             * <p>Apart from every other word here, and the difference is the whole point of having
             * it. The rest say what this compiler did not manage; this one says what the model
             * settles — every position of the point is bounded, every combination of those bounds
             * was tried, and none of them reaches it. A reader may act on this and may not act on
             * the others (ADR-0091).
             */
            THE_RULES_LEAVE_NOTHING_THERE,
            /**
             * One position of the row would have to be two things at once.
             *
             * <p>What the model settles, as {@link #THE_RULES_LEAVE_NOTHING_THERE} is, and not
             * something this compiler fell short of. A class under one case of a sum and a class
             * under another are classes of positions that are not in one value: no row is a
             * {@code FeedQuery} and has a {@code GlobalQuery}'s {@code tag}. Reported as a value
             * nothing composed, an author would go looking for a row that cannot exist.
             */
            ONE_POSITION_CANNOT_BE_BOTH,
            /** The module's classes were not there to build a candidate against. */
            NOTHING_TO_BUILD_AGAINST,
            /** The build asked for no values to be composed, so nothing was tried here. What such a
             *  point is owed is whatever it was owed; what is missing is a row to offer for it. */
            NO_VALUES_WERE_ASKED_FOR,
            /**
             * The position was held back, so no class of it was searched for.
             *
             * <p>Some row wrote a value here that could not be read, which leaves what the rows
             * cover at this position unknown — and so what they do not cover. A row offered for a
             * class here may be one already sitting in the file, which is a specific piece of work
             * handed to somebody who has done it.
             *
             * <p>Told apart from {@link #SEARCH_LIMIT} because they are different pieces of news
             * and only one of them is about this search: that one says the budget ran out with the
             * class still owed, this says the class was never a thing to look for.
             */
            THE_POSITION_WAS_WITHHELD,
            /**
             * The group of decisions this belongs to was wider than the walk offers, so no
             * combination of it was looked in.
             *
             * <p>Told apart from {@link #SEARCH_LIMIT} for the reason {@link
             * #THE_POSITION_WAS_WITHHELD} is: that one says the budget ran out while walking, and
             * this says the walk never started. Raising the row budget changes the first and not
             * the second.
             *
             * <p>Named at all because the alternative is silence. An arm claimed only by a group
             * held back leaves no entry, and an arm with no entry is one no combination claims —
             * so the report said the body never reaches it, which is a statement about the model
             * this compiler was not entitled to make.
             */
            THE_GROUP_WAS_NOT_OFFERED,
            /**
             * The rows were not read, so nothing was searched for at all.
             *
             * <p>What made them unreadable is said in its own words beside this, and is a fact
             * about the evaluation rather than about any class. Named here so that a class is not
             * told the search reached it and stopped.
             */
            THE_ROWS_WERE_NOT_READ,
            /** The generated classes would not link, so the decoders could not be reached. Told
             * apart from the one above it because they were there, which is not what that says. */
            LINKAGE_FAILED,
            /**
             * No row composed for the combination was seen reaching it.
             *
             * <p>Said that way round because it is what the search establishes. Some of the
             * assignments tried may have composed nothing at all, so a word about what every row
             * did would be a word about rows there were none of; what holds of all of them is that
             * none was a witness.
             *
             * <p>Not a proof that the combination is unreachable, and nothing reads it as one. It
             * is a fact about the candidates — and, where the reading that named the combination is
             * wrong, about that reading. Either way the combination stays untried rather than being
             * counted as offered (ADR-0091).
             */
            NO_CERTIFIED_WITNESS,
            /**
             * A strategy that takes this class produced neither a row nor a reason for it.
             *
             * <p>Which is this compiler failing to say, and not something established about the
             * class. Named rather than guessed at: the alternative is to write down whichever cause
             * seemed likely when the branch was added, and a reason read off an empty result outlives
             * whatever made it plausible.
             */
            NO_REASON_RECORDED;

            /**
             * Whether this reason proves there is nothing to find, which one of them does.
             *
             * <p>Asked rather than matched on. Every reader of one of these has the same question —
             * may I say the model settles this, or am I saying what this compiler did not manage —
             * and each that answered it by naming the one word carried a copy of the decision
             * ADR-0091 took. A reason added is then a case here rather than a word that quietly
             * joins whichever side a reader's condition happened to leave it on.
             *
             * <p>Named as {@link souther.compiler.query.PartitionEvidence.PairSpace#provenInfeasible}
             * names it, since it is the same question about the same thing.
             */
            public boolean provesInfeasible() {
                return switch (this) {
                    case THE_RULES_LEAVE_NOTHING_THERE, ONE_POSITION_CANNOT_BE_BOTH -> true;
                    // Every one of these is this compiler falling short, and none of them is the
                    // model saying anything: another value of the same classes may well build.
                    case NOTHING_COMPOSES_ONE, ALL_CANDIDATES_REJECTED, SEARCH_LIMIT,
                         NOTHING_TO_BUILD_AGAINST, NO_VALUES_WERE_ASKED_FOR, LINKAGE_FAILED,
                         NO_CERTIFIED_WITNESS, THE_GROUP_WAS_NOT_OFFERED,
                         THE_POSITION_WAS_WITHHELD, THE_ROWS_WERE_NOT_READ,
                         NO_REASON_RECORDED -> false;
                };
            }
        }

        public UnresolvedCombination {
            classes = List.copyOf(classes);
            said = said == null ? Optional.empty() : said;
        }

        public UnresolvedCombination(List<String> classes, Reason reason, String detail) {
            this(classes, reason, detail, Optional.empty());
        }

        public UnresolvedCombination(List<String> classes, Reason reason) {
            this(classes, reason, null, Optional.empty());
        }

        /**
         * What one of these is really about, where several say the same thing.
         *
         * <p>A position nothing can write a value for makes every combination it takes part in
         * unfillable, and saying so once per combination is one fact repeated a hundred times. The
         * position is the fact; the combinations are arithmetic on it.
         */
        public String subject() {
            return detail == null ? String.join(" x ", classes) : detail;
        }
    }

    public record GenerationResult(List<GeneratedRow> rows, List<UnresolvedCombination> unresolved,
                                   List<GenerationReason> reasons, List<ClassAttempt> classes,
                                   List<ArmAttempt> arms) {

        public static final GenerationResult NONE =
                new GenerationResult(List.of(), List.of(), List.of(), List.of(), List.of());

        public GenerationResult(List<GeneratedRow> rows, List<UnresolvedCombination> unresolved,
                                List<GenerationReason> reasons) {
            this(rows, unresolved, reasons, List.of(), List.of());
        }

        public GenerationResult {
            rows = List.copyOf(rows);
            unresolved = List.copyOf(unresolved);
            reasons = List.copyOf(reasons);
            classes = List.copyOf(classes);
            arms = List.copyOf(arms);
        }

        /**
         * What composing a row that takes {@code probe} came to, or null where no combination this
         * run took claims it.
         *
         * <p>One entry per arm the run was asked about, made where the search ends and read here.
         * A row through the arm is what it is owed and is the answer whatever the combinations
         * beside it came to; where there is none, what every one of them came to is carried, the
         * search's budget and the model's own refusal being different news.
         *
         * <p>Null is an answer and not a failure, and it is one thing: no combination of the body's
         * own decisions claims this arm, so nothing here composes an input for it. An arm the
         * search stopped short of says so in its own entry — read off an absent one, that arm was
         * reported as one the body cannot reach, which is a fact about the model told on the
         * strength of a limit (issue #967).
         */
        public ArmAttempt armAt(int probe) {
            for (ArmAttempt each : arms) {
                if (each.probe() == probe) {
                    return each;
                }
            }
            return null;
        }

        /**
         * What composing a row for one class came to, or null where this run was not asked about it.
         *
         * <p>Asked by identity — the position's own name and the class's own id — so that a finding
         * about a class and the attempt made for it are two readings of one thing. Matched on the
         * words a report writes instead, a class and the row offered for it were joined by a label
         * that two positions of one type spell the same way.
         */
        public ClassAttempt attemptAt(AxisId at, String classId) {
            for (ClassAttempt each : classes) {
                if (each.at().equals(at) && each.classId().equals(classId)) {
                    return each;
                }
            }
            return null;
        }

        /**
         * Whether this result has nothing to say — which a reason is not.
         *
         * <p>A result that is nothing but a reason used to answer yes, and the block it belongs to
         * was dropped whole. So an author who asked what to write got silence where the answer was
         * that the generator could not look, and silence is what having nothing left to write looks
         * like.
         */
        public boolean isEmpty() {
            return rows.isEmpty() && unresolved.isEmpty() && reasons.isEmpty();
        }
    }

    /**
     * What composing a row for one of the body's combinations came to, at one arm that row claims.
     *
     * <p>Per arm and keyed by the arm, because an arm is what a finding is about while a
     * combination is what a search is asked for. One row claims several arms — a combination is
     * what the body settles together, and taking it is taking a way through each of the forks it
     * reads — so the row that answers a finding about one of them is found by that arm's own
     * number and not by reading the combination's name.
     *
     * <p>The number the plan gave the arm ({@code ControlPointId.ArmOccurrence#probe}), which is
     * the number the site carries ({@code CoverageSites.Site#index}). One identity, so a finding
     * and the attempt made for it are two readings of one arm.
     */
    public sealed interface ArmAttempt {

        /** Which arm, by the number the plan gave it. */
        int probe();

        /** A row composed for a combination that takes this arm. */
        record Built(int probe, GeneratedRow row) implements ArmAttempt {}

        /**
         * No row came of the combinations that would have taken it, and what each came to.
         *
         * <p>All of them, because they are not one fact. One combination stopping at the search's
         * budget and another the model's own rules refuse are different news — the first says a row
         * may still be writable and the second says the model settles it — and the arm is answered
         * by the whole of what was tried rather than by whichever was walked first.
         */
        record Unresolved(int probe, List<UnresolvedCombination> why) implements ArmAttempt {

            public Unresolved {
                why = List.copyOf(why);
                if (why.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an arm nothing was tried at is one no combination claims");
                }
            }
        }
    }

    /**
     * A value the module already states that a row's positions can be composed against.
     *
     * <p>A name per position and nothing else. What each value <em>is</em> is the module's to say,
     * and a row naming it is a row an author writes today — the reading that builds a fixture
     * expands the name where the row is read, so nothing here has to hold the value or agree with
     * it.
     *
     * <p>Why a row wants one: where the gap is a class at one position, the row a reader of a table
     * recognises is that class against values the model already puts beside it. Composed from the
     * classes alone, every position of the row holds whatever the search happened to name there,
     * and a reader has to work out which of the differences the answer turned on (issue #967).
     *
     * <p><b>Only what the model states, which may be one position of several.</b> The map is
     * partial and a position it does not name is one this origin makes no claim about: the search
     * composes that position from its classes. A behavior of several parameters written against one
     * value apiece, chosen for each on its own, would be a row whose positions the model never says
     * anything about together — so a tuple is an origin only where an author wrote a row with one,
     * which is a set of values they reached for together, and never one assembled from values the
     * file declares one after the other.
     *
     * <p>Which positions an origin names is what makes it an origin for a class or not. A row for a
     * class of {@code to} written against a value of {@code from} has its own position composed
     * like any other, so it is not that value with one field moved — it is a row with a
     * recognisable value somewhere else. Still worth offering, and not ahead of one that grounds
     * the class it is for: see {@link #nearestFirst}.
     */
    public record Baseline(Map<String, Named> at) {

        public Baseline {
            at = Map.copyOf(at);
        }

        /** Whether this names a value at any position at all. */
        public boolean isEmpty() {
            return at.isEmpty();
        }

        /** A value the module states, by the name a row writes it under. */
        public record Named(String module, String name) {}
    }

    /**
     * What composing a row for one class of one position came to.
     *
     * <p>Held per class and keyed by the class, because a class is what a finding is about and the
     * row offered for it is what answers that finding. A search whose results were a list of rows
     * left the two joined by whatever a reader could match — the words in a row's name — and a row
     * is named for what it was composed for rather than for everything it turns out to settle.
     */
    public sealed interface ClassAttempt {

        /** The position, by the name every reading of it uses. */
        AxisId at();

        /** The class, by the id the partition gave it — never the label, which two positions of
         *  one type spell the same way. */
        String classId();

        /** A row composed for this class. */
        record Built(AxisId at, String classId, GeneratedRow row) implements ClassAttempt {}

        /** No row came of it, and why. Never a statement that none exists. */
        record Unresolved(AxisId at, String classId, UnresolvedCombination why)
                implements ClassAttempt {}
    }

    /**
     * Whether a value written this way can be built at all.
     *
     * <p>The one thing a generator cannot work out for itself. A record's fields can constrain each
     * other, and whether two values are allowed together is the derived decoder's answer, not a rule
     * that can be read off the types one at a time.
     */
    @FunctionalInterface
    public interface CandidateCheck {

        /**
         * What building the candidate at one parameter came to: what was built, or why nothing was.
         *
         * <p>What was built and not only whether it built. Where a candidate landed is the
         * decoder's answer — a newtype's construction may narrow it, and a rule relating two
         * fields decides whether it exists at all — and a caller that had only the refusal was
         * left reading its own request back as the answer.
         */
        Built build(int parameter, FixtureTemplate candidate);

        /** Whether the candidate was refused, for a caller that has nothing to do with what it is. */
        default Optional<String> refuse(int parameter, FixtureTemplate candidate) {
            return build(parameter, candidate) instanceof Built.Refused refused
                    ? Optional.of(refused.why()) : Optional.empty();
        }

        /**
         * Nothing is refused and nothing is built — what a caller with no runtime to build against
         * uses.
         *
         * <p>{@link Built.NothingBuiltIt} and not a value: there is no runtime here, so no
         * candidate went through one, and a reader that took silence for a value would be reading
         * what it asked for back as what it got.
         */
        CandidateCheck ANY = (_, _) -> new Built.NothingBuiltIt();

        /**
         * A check that says which candidates are refused and nothing about the rest.
         *
         * <p>For a caller with no runtime: what it accepts, nothing built, so there is nothing for
         * it to hand back. Written as a value that was built, a reader asking where a candidate
         * landed would be handed what it had asked for.
         */
        static CandidateCheck refusing(Refusal said) {
            return (parameter, candidate) -> said.at(parameter, candidate)
                    .<Built>map(Built.Refused::new).orElseGet(Built.NothingBuiltIt::new);
        }

        /** Which candidates are refused, and why. */
        @FunctionalInterface
        interface Refusal {

            /** Empty where the candidate is allowed; the reason it is not, otherwise. */
            Optional<String> at(int parameter, FixtureTemplate candidate);
        }

        /** What came of building one candidate. */
        sealed interface Built {

            /** It built, and this is what it came to. */
            record Value(souther.compiler.observe.ObservedValue observed) implements Built {}

            /** It did not, and why. Never a claim that no value of the shape can be built. */
            record Refused(String why) implements Built {}

            /**
             * Nothing built it, so nothing here can say what it is.
             *
             * <p>Told apart from a value because they are not the same news. A caller checking
             * where a candidate landed has an answer in one case and none in the other, and a
             * candidate nothing built is offered on the strength of the reading that composed it —
             * which is what the row says of itself either way.
             */
            record NothingBuiltIt() implements Built {}
        }
    }

    /**
     * A way to run a composed row and see what it did.
     *
     * <p>The other thing a generator cannot work out for itself, and the one this issue is about.
     * Which combination a row sits in is settled by running it: everything before that is a reading
     * of the body, and a reading is what may be wrong.
     *
     * <p>Separate from {@link CandidateCheck} because the questions are. That one is asked of one
     * value at one position while the row is being composed, and answers whether the value can be
     * built at all; this is asked of the whole row afterwards, and answers where it went.
     */
    @FunctionalInterface
    public interface Trial {

        /** What running {@code inputs} through the behavior came to. */
        Watched run(List<FixtureTemplate> inputs);

        /** Nothing runs here — what a caller with no runtime to run against uses. */
        Trial NOTHING_RUNS = _ -> new Watched.NoAccount();
    }

    /**
     * What came of running one composed row.
     *
     * <p>A sum, so that a caller has to say which of them it has. Having no account of a row and
     * having one that shows it reached nothing are the same emptiness read off a set of places and
     * are not the same fact: the first leaves every combination as untried as it was, and the second
     * is a row that missed.
     */
    public sealed interface Watched {

        /** It ran, something was recording, and this is what it was seen doing. Also what a row
         *  that aborted part way comes back as: it went where it went before it stopped, and that
         *  is recorded. */
        record Ran(souther.compiler.coverage.Observation seen) implements Watched {}

        /**
         * Nothing here can say what it did.
         *
         * <p>Three things come to this and they are one arm because nothing tells them apart by
         * acting differently: nothing ran the row, something ran it and nothing was recording, and
         * something ran it and the recording was never read. What none of them is, is a run that
         * reached nothing — that is {@link Ran} of an empty account, and it is the one difference
         * anything here turns on.
         */
        record NoAccount() implements Watched {}
    }

    // --- composing the rows ---------------------------------------------------------------------

    /**
     * Rows for every class of the behavior's positions no written row sits in.
     *
     * <p>Deterministic: the axes are ordered before anything starts, ties go to the lower index, and
     * nothing consults a clock or a hash order — the same model and the same rows produce the same
     * rows twice. Nothing is asked about the body here, so no arm is looked for.
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        AdequacyPolicy.OfTheGeneration budget) {
        return fill(subject, existing, check, List.of(), budget);
    }

    /**
     * The same, and a row through every arm the body's combinations take.
     *
     * <p>Two questions and one set of rows. A class is what the model divides a position into and is
     * answerable with no body to read; an arm is a way through the body, and where a row through it
     * is looked for is the combinations the decisions settle together. The classes go first: what
     * each is owed is one row, and a budget the arms spent first left a class the report names with
     * nothing offered for it.
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups,
                                        AdequacyPolicy.OfTheGeneration budget) {
        return fill(subject, existing, check, groups, Trial.NOTHING_RUNS, budget);
    }

    /**
     * The same, running each row composed at a combination to see whether it took the arm.
     *
     * <p>Which is the only thing that can say so. A row is composed by narrowing each position to
     * the classes the combination leaves it, and every step of that narrowing is a reading of the
     * body — so a row that misses is what a reading being wrong looks like, and a row that misses
     * looks like one that arrives until something watches it.
     *
     * <p>A row that missed is not offered and the arm stays unanswered. It is not evidence that the
     * arm is unreachable: what was shown is that these candidates were not witnesses (ADR-0091).
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups,
                                        Trial trial, AdequacyPolicy.OfTheGeneration budget) {
        return fill(subject, existing, check, groups, trial, List.of(),
                everyClassNoRowSitsIn(subject, existing),
                everyArmACombinationMayTake(subject, groups, budget), budget);
    }

    /**
     * Every arm a combination of the body may take, which is at least every arm one does take.
     *
     * <p><b>Not what a build asks for.</b> Which arms are owed a row is what measuring them
     * established, and a build hands that in. This is for a caller with no measurement beside it —
     * a test standing the search up on its own — and it says so by being a list the caller passes
     * rather than one the search makes for itself.
     *
     * <p><b>And <em>may</em> rather than <em>does</em>, which the name carries because the answer
     * cannot.</b> An offered group is walked, so what it contributes is exact: a choice whose
     * factors leave a position nothing is not a combination and is not counted. A group the budget
     * held back is not walked, and what it contributes is the union over the way in and every
     * outcome of every factor — which includes arms no single combination of it claims, since two
     * factors that disagree about a position have choices no row sits in.
     *
     * <p>That direction is the safe one and the other is not. An arm left out is an arm nothing
     * asks for, and an arm nothing asks for is reported as one no combination claims — which says
     * the body settles something it does not. An arm asked for and not found is answered
     * {@link UnresolvedCombination.Reason#THE_GROUP_WAS_NOT_OFFERED}, which is true of it however
     * many combinations of the held-back group would have claimed it.
     */
    public static Set<Integer> everyArmACombinationMayTake(
            Subject subject, List<souther.compiler.interaction.Interaction> groups,
            AdequacyPolicy.OfTheGeneration budget) {
        Set<Integer> out = new LinkedHashSet<>();
        InteractionCells.Offered offered = InteractionCells.of(groups, ordered(subject), budget);
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                if (selection != null) {
                    out.addAll(claimed(selection));
                }
            }
        }
        // And the arms behind a group the limit held back. They are arms the combinations take —
        // what the limit settled is that nothing walked them, which is the search's answer and not
        // a fact about which arms exist. Left out, a caller with no measurement beside it asks for
        // fewer arms because this compiler declined to look, and never learns that it did.
        for (InteractionCells.NotOffered held : offered.notOffered()) {
            out.addAll(armsIn(held.claims()));
        }
        return out;
    }

    /** One class of one position, which is what a row can be owed for. */
    public record ClassOwed(AxisId at, String classId) {}

    /**
     * Every class of every position no row the author wrote sits in.
     *
     * <p><b>Not what a build asks for.</b> Which classes are owed a row is what the partition
     * measure established, and a build hands that in. This is for a caller with no measurement
     * beside it — a test standing the search up on its own — and it says so by being a list the
     * caller passes rather than one the search makes for itself.
     *
     * <p>Read off the values the rows state, which needs nothing run: where a row stands is settled
     * by what is written at each position. So the answer is the same one the measure reaches, and a
     * build that ran nothing is not a build with nothing to generate for.
     *
     * <p>A row of the author's can sit in more than one class of a position at once — a list with
     * one element under a line and one over it — and each of them is covered. Read as one class,
     * the rest would be asked for again, which is work the author has already done.
     */
    public static Set<ClassOwed> everyClassNoRowSitsIn(Subject subject,
                                                       List<ObservedRow> existing) {
        Set<ClassOwed> out = new LinkedHashSet<>();
        for (Axis axis : ordered(subject)) {
            Set<String> covered = new LinkedHashSet<>();
            for (ObservedRow row : existing) {
                Classification here = row.at().get(axis.id());
                if (here != null) {
                    covered.addAll(here.classIds());
                }
            }
            for (PartitionClass cls : axis.classes()) {
                if (!covered.contains(cls.id())) {
                    out.add(new ClassOwed(axis.id(), cls.id()));
                }
            }
        }
        return out;
    }

    /**
     * The same, composing each row's positions against a value the module already states where
     * there is one for them.
     *
     * <p>Which changes what a row says rather than what it is for. A row is composed for one class
     * either way; what a baseline settles is where the positions the row is <em>not</em> about
     * stand, and a value the model already names is one a reader recognises — so the difference
     * between the row and what is already written is the class, and the class alone.
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups,
                                        Trial trial, List<Baseline> baselines,
                                        Set<ClassOwed> classesOwed,
                                        Set<Integer> armsOwed,
                                        AdequacyPolicy.OfTheGeneration budget) {
        List<Axis> ordered = ordered(subject);
        // A position where some row's value could not be read is a position nothing is known about.
        // A row generated for a class there may be a row that is already written, and telling an
        // author to write one is worse than saying nothing: it is a specific piece of work that is
        // already done.
        List<GenerationReason> undecided = new ArrayList<>();
        List<Axis> axes = new ArrayList<>();
        for (Axis axis : ordered) {
            // A position inside a collection the rules leave no room in. No value stands there in
            // any row, so no class of it is a cell to fill — and left in, every combination of the
            // row would be one no row can be written for, including the ones that name a position
            // beside it and have nothing to do with this one.
            if (holdsNothing(subject, axis)) {
                continue;
            }
            if (readEverywhere(axis, existing)) {
                axes.add(axis);
            } else {
                undecided.add(new GenerationReason.PositionWithheld(axis.id()));
            }
        }
        if (axes.isEmpty()) {
            return new GenerationResult(List.of(), List.of(), undecided);
        }
        // Which class of which position is owed a row, handed in by whoever read the rows. The
        // search keeps no list of its own: a class is owed one where nothing sits in it, and what
        // sits where is what the partition measure reads off the rows — so a search working it out
        // a second time is a second reading of one fact, free to disagree with the reported one.
        //
        // Walked in the search's own order over the positions it kept, so a plan naming a class of
        // a position nothing could be read at is dropped with that position: why it went is already
        // said, and it is not a class this run failed at.
        List<int[]> owed = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (classesOwed.contains(
                        new ClassOwed(axes.get(i).id(), axes.get(i).classes().get(c).id()))) {
                    owed.add(new int[] {i, c});
                }
            }
        }

        List<GeneratedRow> rows = new ArrayList<>();
        List<ClassAttempt> attempts = new ArrayList<>();
        List<ArmAttempt> arms = new ArrayList<>();
        List<UnresolvedCombination> unresolved = new ArrayList<>();
        List<GenerationReason> reasons = new ArrayList<>(undecided);
        // The classes first. What each is owed is one row, and the arms below are looked for among
        // combinations that would be composed either way — so a budget the combinations spent
        // first left a class the report names with nothing offered for it and a search limit
        // beside it, over rows nobody is owed.
        // Every class on the list gets an entry, including the ones the limit stopped the search
        // before. What was not tried is a fact of this run and is written down here — read off the
        // count of a reason at the end, it arrived at a reader as a fact about the model instead:
        // a class nothing looked at answered "no reason recorded", and an arm answered "nothing
        // reaches it" (issue #967).
        int classesLeft = 0;
        for (int i = 0; i < owed.size(); i++) {
            int[] at = owed.get(i);
            if (rows.size() >= budget.rows()) {
                classesLeft = owed.size() - i;
                for (int cut = i; cut < owed.size(); cut++) {
                    Axis axis = axes.get(owed.get(cut)[0]);
                    UnresolvedCombination why = new UnresolvedCombination(
                            List.of(label(axis, owed.get(cut)[1])),
                            UnresolvedCombination.Reason.SEARCH_LIMIT);
                    attempts.add(new ClassAttempt.Unresolved(axis.id(),
                            axis.classes().get(owed.get(cut)[1]).id(), why));
                    unresolved.add(why);
                }
                break;
            }
            ClassAttempt attempt = rowFor(subject, axes, at[0], at[1], baselines, check);
            attempts.add(attempt);
            switch (attempt) {
                case ClassAttempt.Built made -> rows.add(made.row());
                case ClassAttempt.Unresolved none -> unresolved.add(none.why());
            }
        }
        // And the arms this run was asked for, looked for among the combinations the body settles
        // together. A combination is where a witness is found and is not itself owed a row: nothing
        // reports one, so a search that composed for every combination was filling a space nobody
        // asked about — which is what the pair space was, arriving a second time under another
        // name. So a combination claiming no arm on the list is not searched, and one is dropped
        // from the list as soon as a row goes through it.
        Set<Integer> left = new LinkedHashSet<>(armsOwed);
        Map<Integer, GeneratedRow> built = new LinkedHashMap<>();
        Map<Integer, List<UnresolvedCombination>> failed = new LinkedHashMap<>();
        // Arms a combination was still to be searched at when the limit came. Collected by walking
        // the rest of the cells and composing nothing, which costs a claim lookup each and is the
        // only way to tell an arm the search ran out on from one no combination claims — the two
        // are one silence, and a reader told the second where the first happened is told the model
        // settles something it does not.
        Set<Integer> cutOff = new LinkedHashSet<>();
        // The arms this run ended up answering with a group nobody walked, collected as those
        // answers are made rather than worked out again afterwards. What decides one is the order
        // the three answers are asked in below; a set built here from `left`, `cutOff` and
        // `notOffered` would be that order written a second time, free to stop agreeing with it.
        Set<Integer> wentUnwalked = new LinkedHashSet<>();
        // And the arms behind a group nothing walked, which is a second silence with a different
        // cause. The one above is a budget that ran out with the arm still owed; this is a group
        // the offer never opened, and raising the budget does not reach it.
        InteractionCells.Offered offered = InteractionCells.of(groups, axes, budget);
        Set<Integer> notOffered = new LinkedHashSet<>();
        // Which arms each held-back group could have been searched at, kept per group so that the
        // summary at the end can be counted off the entries rather than worked out a second way.
        List<List<Integer>> behindEachHeldGroup = new ArrayList<>();
        for (InteractionCells.NotOffered held : offered.notOffered()) {
            List<Integer> behindIt = armsIn(held.claims());
            behindEachHeldGroup.add(behindIt);
            notOffered.addAll(behindIt);
        }
        boolean unconfirmed = false;
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size() && !left.isEmpty(); index++) {
                CellSelection selection = group.at(index);
                if (selection == null) {
                    // The factors this choice takes leave a position nothing, so it is not a
                    // combination the body has a path to and there is nothing to look in.
                    continue;
                }
                List<Integer> takes = new ArrayList<>(claimed(selection));
                takes.retainAll(left);
                if (takes.isEmpty()) {
                    continue;   // no arm on the list is looked for here
                }
                if (rows.size() >= budget.rows()) {
                    cutOff.addAll(takes);
                    continue;
                }
                switch (witnessFor(subject, axes, selection, check, trial, takes)) {
                    case Witness.None none -> {
                        UnresolvedCombination why = new UnresolvedCombination(
                                none.classes(), none.reason(), none.detail(), none.said());
                        unresolved.add(why);
                        takes.forEach(probe -> failed
                                .computeIfAbsent(probe, _ -> new ArrayList<>()).add(why));
                    }
                    case Witness.Certified found -> {
                        rows.add(found.row());
                        takes.forEach(probe -> built.put(probe, found.row()));
                        takes.forEach(left::remove);
                    }
                    case Witness.Unconfirmed offer -> {
                        rows.add(offer.row());
                        takes.forEach(probe -> built.put(probe, offer.row()));
                        takes.forEach(left::remove);
                        // Nothing watched it, so what it is offered for is what the reading says
                        // and not what anything saw. Said once for the behavior: it is one fact
                        // about this generation.
                        unconfirmed = true;
                    }
                }
            }
        }
        // One entry per arm the run was asked about, in the order it was asked. An arm the limit
        // cut off carries that beside whatever was tried before it: a combination the model refuses
        // says nothing about the ones nobody got to, and an arm answered by the first alone was
        // reported as settled by the model on the strength of a search that stopped.
        for (int probe : armsOwed) {
            GeneratedRow row = built.get(probe);
            List<UnresolvedCombination> why = new ArrayList<>(
                    failed.getOrDefault(probe, List.of()));
            if (row != null) {
                arms.add(new ArmAttempt.Built(probe, row));
            } else if (cutOff.contains(probe)) {
                why.add(new UnresolvedCombination(List.of(),
                        UnresolvedCombination.Reason.SEARCH_LIMIT));
                arms.add(new ArmAttempt.Unresolved(probe, why));
            } else if (notOffered.contains(probe)) {
                // Asked after the two above, so an arm some offered group reached or the budget
                // stopped at keeps that answer. What is left here is an arm whose only claim came
                // from a group nothing walked, and the union a held-back group is named by is a
                // superset — which is why this is the last of the three and not the first.
                why.add(new UnresolvedCombination(List.of(),
                        UnresolvedCombination.Reason.THE_GROUP_WAS_NOT_OFFERED));
                arms.add(new ArmAttempt.Unresolved(probe, why));
                wentUnwalked.add(probe);
            } else if (!why.isEmpty()) {
                arms.add(new ArmAttempt.Unresolved(probe, why));
            }
            // And an arm with none of them is one no combination claims, which is the one thing an
            // absent entry may mean.
        }
        // Said once, at the end, and about both searches. One that ran out on the classes stopped
        // whether or not the arms had anything left to do, and two limits reported apart would be
        // read as two searches.
        // Counted off what the limit actually stopped. An arm still on the list because every
        // combination claiming it was refused is not one the limit cut off, and counting it here
        // told a reader to raise a limit that would change nothing.
        if (classesLeft + cutOff.size() > 0) {
            reasons.add(new GenerationReason.SearchLimit(axes.get(0).id().behavior(),
                    classesLeft + cutOff.size()));
        }
        // And the groups the limit held back that an arm was left waiting on. Counted off the
        // entries just made and not off the obligation this run started with, because the two are
        // different sets: an arm owed at the start may have been built from another group that was
        // offered, or stopped at by the row budget, and either way the entry for it says so and the
        // group is not what it is waiting on. `NotOffered`'s own contract is that what it names is
        // read for "what is left owed after every offered group has been searched", which is
        // available here and nowhere earlier.
        //
        // Read off `wentUnwalked` rather than rebuilt from `left`, `cutOff` and `notOffered`. Those
        // three would be the order the answers are asked in, written a second time beside the one
        // that decides — and a summary that disagrees with the entries under it is worse than no
        // summary, since a reader checks the number against them.
        int heldBackAndWaitedOn = 0;
        for (List<Integer> behindIt : behindEachHeldGroup) {
            if (behindIt.stream().anyMatch(wentUnwalked::contains)) {
                heldBackAndWaitedOn++;
            }
        }
        if (heldBackAndWaitedOn > 0) {
            reasons.add(new GenerationReason.GroupsNotOffered(axes.get(0).id().behavior(),
                    heldBackAndWaitedOn));
        }
        if (unconfirmed) {
            reasons.add(new GenerationReason.RowsNotConfirmed(axes.get(0).id().behavior()));
        }
        return new GenerationResult(rows, unresolved, reasons, attempts, arms);
    }

    /**
     * Which arms a combination claims a run through, by the numbers the plan gave them.
     *
     * <p>Only the arms. A combination's claims are what a run through it would be recorded at, and
     * a comparison is one of those — it is a place a run passes and not a way through a fork, so
     * nothing about an arm is owed for it.
     */
    private static List<Integer> claimed(CellSelection selection) {
        return armsIn(selection.claims());
    }

    /** The arms a list of claims names, by the numbers the plan gave them. Shared with the groups
     *  the limit held back, which have claims and no cell to read them off. */
    private static List<Integer> armsIn(List<souther.compiler.coverage.ControlClaim> claims) {
        List<Integer> out = new ArrayList<>();
        for (souther.compiler.coverage.ControlClaim claim : claims) {
            if (claim.at() instanceof souther.compiler.coverage.ControlPointId.ArmOccurrence arm
                    && arm.probe().isPresent()) {
                out.add(arm.probe().getAsInt());
            }
        }
        return out;
    }

    /**
     * How many assignments the walk over the origins tries before it gives up on a class.
     *
     * <p>One budget for the whole walk, over every origin and every distance. Held per origin, a
     * model stating a hundred values had a hundred budgets and the number was no bound on anything;
     * and the walk is nearest-first, so a budget spent is a budget spent on the rows nearest what
     * the model already says.
     *
     * <p>Its own budget and never {@link #MAX_TUPLES}. That one bounds the walk over the values one
     * parameter's fields may take once the classes are settled; this bounds the walk over which
     * classes to settle them at, and the two multiply — shared, one of them would be spent by the
     * other and which of them ran out would depend on the model.
     *
     * <p><b>The only bound.</b> There was a second one — at most two positions moved beside the one
     * the row is about — which was a rule about what a row may say wearing the clothes of a search
     * limit: a witness three moves away was not tried however much budget was left, and what came
     * back said no row was composed rather than that this had stopped looking. If a row that moves
     * many positions is one this should not offer, that is a policy with a name and a sentence of
     * its own, not a constant inside a loop.
     */
    private static final int MOST_REPAIRS = 64;

    /**
     * A row for one class: composed against what the model already says where it can be, and moving
     * as little else as it takes.
     *
     * <p>Outward from what a reader would recognise: the target alone before the target and one
     * supporting position, before the target and two, and within one distance the values the model
     * states in the order they were gathered, the classes last. What that order is and why is
     * {@link #nearestFirst}'s to say; what this does is walk it and stop at the first row that
     * lands in the class.
     *
     * <p><b>Not the other way round.</b> The synthetic composition used to run first and its
     * failure ended the class: a row the baseline could have been written for came back as one
     * nothing composed, because a representative chosen from the classes alone broke a rule that
     * relates two positions while the model's own value does not. Composing is one of the origins,
     * not the gate in front of them.
     *
     * <p>And a refusal of the exact mutation is a reason to repair it, not to abandon the origin.
     * Where {@code f = C} needs {@code g = G2} beside it, what a reader wants is the baseline with
     * both moved — {@code Cond &#123;...none, f = C, g = G2&#125;} — and falling back to a
     * composition moves everything the classes happened to name. The supporting position is part of
     * the row and no part of what it is for: the row is still named for the class alone
     * ({@link Purpose.ForAClass}).
     */
    private static ClassAttempt rowFor(Subject subject, List<Axis> axes, int at, int cls,
                                       List<Baseline> baselines, CandidateCheck check) {
        Axis axis = axes.get(at);
        String classId = axis.classes().get(cls).id();
        String label = label(axis, cls);
        Attempt last = null;
        // Every baseline the module states rather than the one this compiler picked. Narrowed to
        // the only value of a type, a module that states a second one lost the spread from every
        // row of every behavior taking it — a change somewhere else in the file, answering a
        // question nobody asked it. What order they are walked in is
        // {@link #nearestFirst}'s to say.
        Perturbations walk = nearestFirst(subject, axes, at, cls, baselines, check);
        for (Candidate candidate : walk.candidates()) {
            Map<String, FixtureTemplate> given = candidate.from().isEmpty() ? Map.of()
                    : against(subject, axes, candidate.stands(), at, candidate.where(),
                            candidate.from());
            if (!candidate.from().isEmpty() && given.isEmpty()) {
                continue;   // nothing here can be written against the model's value
            }
            Attempt made = build(subject, axes, candidate.where(), check, given);
            if (made.row() == null) {
                last = made;
                continue;
            }
            if (!inTheClass(subject, axes, at, classId, made.row().inputs(), check)) {
                last = new Attempt(null, UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, label,
                        Optional.empty());
                continue;
            }
            return new ClassAttempt.Built(axis.id(), classId, new GeneratedRow(
                    new Purpose.ForAClass(axis.id(), classId, label), made.row().inputs()));
        }
        // What the walk came to, and the budget first. A search that stopped says so whatever the
        // last assignment it got to came to: the refusal of the sixty-fourth candidate is a fact
        // about that candidate, and offered as the class's answer it stands for a space the search
        // never entered — the value one place further on that builds, and the composition behind
        // the baselines that was never reached.
        UnresolvedCombination why = walk.cutShort() || last == null || last.row() != null
                ? new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.SEARCH_LIMIT)
                : new UnresolvedCombination(List.of(label), last.reason(), last.detail(),
                        last.said());
        return new ClassAttempt.Unresolved(axis.id(), classId, why);
    }

    /**
     * One assignment to try, and the origin it is a move away from.
     *
     * @param from   the value the model states that this row is written against, or a baseline
     *               naming nothing where the row is composed from the classes
     * @param stands where {@code from}'s own values already sit, which is what the move is measured
     *               against and what a spread writes over
     * @param where  the classes this assignment puts every position at
     */
    private record Candidate(Baseline from, int[] stands, int[] where) {}

    /**
     * The assignments a class was given to try, and whether they are all of them.
     *
     * <p><b>The budget is a fact about the search and travels with what the search returned.</b> A
     * list alone cannot say whether it ran out or was cut off, and a caller reading the end of it
     * as the end of the space answered a class with the last refusal it saw — "every value tried
     * was refused" over a search that stopped at the sixty-fourth of them, with a value that builds
     * one place further on. The same fault as an absent ledger entry: one silence standing for two
     * pieces of news, and the stronger one read off it.
     *
     * @param candidates the assignments to try, nearest what the model already says first
     * @param cutShort   whether the budget stopped this before the assignments ran out
     */
    private record Perturbations(List<Candidate> candidates, boolean cutShort) {}

    /**
     * The assignments to try for one class, nearest what the model already says first.
     *
     * <p>Built whole and then walked, rather than walked as four nested loops. The budget is the
     * length of this list, so it is a bound on the search rather than a test inside one — nested,
     * the check that stopped the innermost walk left the three around it turning, and the number
     * bounded nothing.
     *
     * <p><b>Whether the origin states the class's own position, before anything else.</b> A row for
     * a class of {@code to} written against a value of {@code from} has {@code to} composed from
     * its classes like any other position — so it is not that value with one field moved, which is
     * the thing this exists to offer. It is a row with a recognisable value somewhere else, worth
     * offering after every origin that grounds the position and not among them.
     *
     * <p>Not a tie-break inside a distance. An origin that does not name the position is measured
     * against a tuple partly of the search's own making — {@link #stands} fills what the origin
     * says nothing about from the classes, and what is filled that way sits at distance zero by
     * construction. So the ungrounded origin arrived as a nearest one and won, and the value the
     * model states of the position the row is about went untried.
     *
     * <p><b>Then distance, among the values the model states.</b> How far a row moves from the
     * value it is written against is what this is minimising, so every baseline is tried at the
     * target alone before any is tried with a supporting field moved. Within one distance the
     * origins keep the order they were gathered in, which puts a value the author's own rows name
     * before one the module merely states — the whole of one origin's moves at that distance
     * before the next origin's. Ordered with the supporting sets outside the origins, provenance
     * decided only which origin won a given set of supporting positions, and a later origin that
     * happened to repair on an earlier set beat an earlier origin that repaired on a later one.
     *
     * <p><b>And the classes last, whatever their distance.</b> A composed row is not a nearer
     * baseline: its distance is measured from values the search itself named, so it is zero by
     * construction and says nothing about how far the row is from what a reader recognises. Put in
     * the same order, a row composed from the classes won against every baseline that needed one
     * supporting field — which is the objective read backwards.
     */
    private static Perturbations nearestFirst(Subject subject, List<Axis> axes, int at, int cls,
                                              List<Baseline> baselines, CandidateCheck check) {
        List<Candidate> out = new ArrayList<>();
        List<Baseline> stated = new ArrayList<>(baselines);
        List<int[]> stand = new ArrayList<>();
        for (Baseline baseline : stated) {
            stand.add(stands(subject, axes, baseline, check));
        }
        // Set where an assignment was there to be taken and the budget was already full, which is
        // the one place the two can be told apart. Read off the length instead, a list that filled
        // the budget exactly and a space that had nothing more are the same list.
        boolean cutShort = false;
        // The position the row is about, which is what an origin either states a value of or does
        // not. Both kinds are walked and the grounding ones whole, at every distance, before any of
        // the others.
        String about = axes.get(at).path().head();
        walk:
        for (boolean grounding : new boolean[] {true, false}) {
            for (int moved = 0; moved < axes.size(); moved++) {
                for (int origin = 0; origin < stated.size(); origin++) {
                    if (stand.get(origin) == null) {
                        continue;   // nothing built this origin's values, so nothing measures it
                    }
                    if (stated.get(origin).at().containsKey(about) != grounding) {
                        continue;
                    }
                    for (int[] supporting : supportingSets(axes, at, moved)) {
                        for (int[] where
                                : assignmentsOver(axes, stand.get(origin), at, cls, supporting)) {
                            if (out.size() >= MOST_REPAIRS) {
                                cutShort = true;
                                break walk;
                            }
                            out.add(new Candidate(stated.get(origin), stand.get(origin), where));
                        }
                    }
                }
            }
        }
        Baseline classes = new Baseline(Map.of());
        int[] composed = composes(axes);
        // Reached only where the baselines left room. A composition that builds sits behind a
        // budget the baselines spent, and a caller told the baselines were all refused would go
        // looking for a value the model cannot hold — so the fact that this was never reached is
        // what {@code cutShort} carries.
        composing:
        for (int moved = 0; !cutShort && moved < axes.size(); moved++) {
            for (int[] supporting : supportingSets(axes, at, moved)) {
                for (int[] where : assignmentsOver(axes, composed, at, cls, supporting)) {
                    if (out.size() >= MOST_REPAIRS) {
                        cutShort = true;
                        break composing;
                    }
                    out.add(new Candidate(classes, composed, where));
                }
            }
        }
        return new Perturbations(out, cutShort);
    }

    /**
     * Which positions beside {@code at} a row may move, {@code moved} of them at a time.
     *
     * <p>In the axes' own order and combinations of it, so two runs of one model walk the same
     * assignments in the same order and offer the same rows.
     */
    private static List<int[]> supportingSets(List<Axis> axes, int at, int moved) {
        List<int[]> out = new ArrayList<>();
        chooseSupporting(axes, at, moved, 0, new int[moved], 0, out);
        return out;
    }

    private static void chooseSupporting(List<Axis> axes, int at, int moved, int from,
                                         int[] taken, int filled, List<int[]> out) {
        if (filled == moved) {
            out.add(taken.clone());
            return;
        }
        for (int i = from; i < axes.size(); i++) {
            if (i == at) {
                continue;
            }
            taken[filled] = i;
            chooseSupporting(axes, at, moved, i + 1, taken, filled + 1, out);
        }
    }

    /**
     * Every assignment that pins {@code at} to {@code cls} and moves the positions in
     * {@code supporting}, each of the rest standing where a position a row is not about stands.
     *
     * <p>The supporting positions take each of their classes in turn, the first of them being where
     * they would have stood anyway — so the first assignment of every set is the one that moves
     * nothing beside the target, and a set larger than it is only reached once the smaller ones are
     * spent.
     */
    private static List<int[]> assignmentsOver(List<Axis> axes, int[] from, int at, int cls,
                                               int[] supporting) {
        List<int[]> out = new ArrayList<>();
        // What the row is about first, and the origin's own classes kept wherever they can be kept
        // beside it. Cloned outright, a row about a class under one case of a sum would carry the
        // classes of the positions under another, which is a row that has to be two things at once.
        walkSupporting(axes, standing(axes, from, at, cls), supporting, 0, out);
        return out;
    }

    /**
     * Which class each position's value falls in for the value the model already states there, or
     * null where nothing built one to look at.
     *
     * <p>Read off what was built and never off what the baseline was asked to be. A position with
     * no baseline stands where a composition would put it — the row is not about it either way, and
     * what it holds is what the classes give it.
     *
     * <p>Nothing where no runtime built the values: a distance measured from a baseline nothing
     * looked at would be measured from a guess, and the composition is the origin this run has.
     */
    private static int[] stands(Subject subject, List<Axis> axes, Baseline baseline,
                                CandidateCheck check) {
        List<souther.compiler.observe.ObservedValue> observed = new ArrayList<>();
        for (String parameter : subject.parameters()) {
            Baseline.Named named = baseline.at().get(parameter);
            if (named == null) {
                // Not a value this origin names, and not one it needs: the axes under it are read
                // off the composition below.
                observed.add(new souther.compiler.observe.ObservedValue.Unknown("no baseline"));
                continue;
            }
            if (!(check.build(observed.size(),
                    FixtureTemplate.named(named.module(), named.name()))
                            instanceof CandidateCheck.Built.Value(var value))) {
                return null;
            }
            observed.add(value);
        }
        Map<AxisId, Classification> where =
                InputClassifications.of(observed, subject.inputs(), axes);
        int[] out = composes(axes);
        for (int i = 0; i < axes.size(); i++) {
            Classification here = where.get(axes.get(i).id());
            if (here == null) {
                continue;
            }
            for (String id : here.classIds()) {
                int found = classIn(axes.get(i), id);
                if (found >= 0) {
                    out[i] = found;
                    break;
                }
            }
        }
        return out;
    }

    /** Where every position stands when a row is composed from the classes alone. */
    private static int[] composes(List<Axis> axes) {
        return standing(axes, null, NOT_HERE, NOT_HERE);
    }

    private static void walkSupporting(List<Axis> axes, int[] where, int[] supporting, int filled,
                                       List<int[]> out) {
        if (filled == supporting.length) {
            out.add(where.clone());
            return;
        }
        int axis = supporting[filled];
        int stood = where[axis];
        // A position this row stands at no class of is not one to move it through. What it would
        // have taken is not a class of this row, so every assignment over it is the same row.
        if (stood == NOT_HERE) {
            walkSupporting(axes, where, supporting, filled + 1, out);
            return;
        }
        for (int c = 0; c < axes.get(axis).classes().size(); c++) {
            // Where it already stands is not a move, and the assignment that makes it is the one
            // the smaller set already produced.
            if (c == stood) {
                continue;
            }
            where[axis] = c;
            // And a class the rest of the assignment cannot be beside is not a move either: it is
            // a row that would have to be two things at once, which no value is.
            if (requiredBy(axes, where) instanceof Requirements.Merge.Merged) {
                walkSupporting(axes, where, supporting, filled + 1, out);
            }
        }
        where[axis] = stood;
    }

    /**
     * Whether the candidate's value at {@code at} really is in {@code classId}.
     *
     * <p>Asked of what was built and never of what was asked for. A class names the values it
     * stands for and a row writes one of them, and between the two are the decoders and the rules
     * the model states — a construction may narrow what it is given, and a value written under a
     * name is read back through it. So where the check built the candidate, where it landed is read
     * off the built value by the walk every written row's values go through
     * ({@link InputClassifications}).
     *
     * <p>True where nothing built it. There is no runtime to put a candidate through, so nothing
     * here can say where it went — and a row nothing could judge is offered as it was composed,
     * which is what {@code Trial.NOTHING_RUNS} leaves a row that nothing ran.
     */
    private static boolean inTheClass(Subject subject, List<Axis> axes, int at, String classId,
                                      List<FixtureTemplate> inputs, CandidateCheck check) {
        List<souther.compiler.observe.ObservedValue> observed = new ArrayList<>();
        for (int p = 0; p < inputs.size(); p++) {
            if (!(check.build(p, inputs.get(p)) instanceof CandidateCheck.Built.Value(var value))) {
                return true;   // nothing built it, so nothing says where it went
            }
            observed.add(value);
        }
        Classification where =
                InputClassifications.of(observed, subject.inputs(), axes).get(axes.get(at).id());
        return where != null && where.classIds().contains(classId);
    }

    /**
     * {@code composed} with every position a baseline names written against that baseline.
     *
     * <p>A parameter no moved position is under is written as the baseline itself: the value is
     * already in the model and this row is not about it, so naming it says so. A parameter some
     * moved position is under is written as the baseline with those fields moved, which is the row
     * — the difference between it and what the model already says is what the row is for, and
     * everything else standing where the model puts it is what makes that readable (issue #967).
     *
     * <p>What a baseline cannot be written for is kept as it was composed, and silently: this is
     * how a row is written and not whether one could be. A position the baseline reaches through
     * more than one field, a class with no value to put there, a value the model refuses beside the
     * rest of the row — each of them leaves that parameter composed from its classes, which is a
     * row that says the same thing in more words.
     */
    private static Map<String, FixtureTemplate> against(Subject subject, List<Axis> axes,
                                                        int[] from, int target, int[] where,
                                                        Baseline baseline) {
        Map<String, FixtureTemplate> out = new LinkedHashMap<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            String parameter = subject.parameters().get(p);
            Baseline.Named at = baseline.at().get(parameter);
            if (at == null) {
                continue;
            }
            FixtureTemplate named = FixtureTemplate.named(at.module(), at.name());
            FixtureTemplate written = movedUnder(axes, from, parameter, target, where).isEmpty()
                    ? named
                    : withFieldsMoved(subject, p, axes, from, parameter, target, where, named);
            // Left out where the baseline cannot be written for this assignment, which leaves that
            // parameter to be composed from its classes. How a row is written never decides
            // whether the model allows it — the check below asks that of every parameter alike.
            if (written != null) {
                out.put(parameter, written);
            }
        }
        return Map.copyOf(out);
    }

    /** Which axes this assignment moves under {@code parameter}: the one the row is about, and any
     *  the search moved beside it to make the row buildable. */
    private static List<Integer> movedUnder(List<Axis> axes, int[] from, String parameter,
                                            int target, int[] where) {
        List<Integer> moved = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            if (!axes.get(i).path().head().equals(parameter)) {
                continue;
            }
            // Moved against where the baseline's own value stands, which is what the spread writes
            // over. Measured against a composition, a field the baseline already holds the right
            // value in was written out again for no reason, and one it did not was left unwritten.
            if (i == target || where[i] != from[i]) {
                moved.add(i);
            }
        }
        return moved;
    }

    /**
     * The baseline with the fields this assignment moves under {@code parameter} set to values of
     * the classes it moves them to, or null where this cannot be written.
     *
     * <p>Each field reached in one step. A position further down is a record inside a record, and
     * writing it means spreading the value at every step on the way — which is a row that names
     * values this has not been asked whether it can name. Such a parameter keeps what the classes
     * composed for it, which says the same thing and says it in full.
     */
    private static FixtureTemplate withFieldsMoved(Subject subject, int p, List<Axis> axes,
                                                   int[] from, String parameter, int target,
                                                   int[] where, FixtureTemplate baseline) {
        if (!(subject.types().get(p) instanceof Type.Ref(TypeSymbol built))
                || !(subject.symbols().scope().reach(built) instanceof TypeReachName.Written type)) {
            return null;
        }
        Map<String, FixtureTemplate> moved = new LinkedHashMap<>();
        for (int i : movedUnder(axes, from, parameter, target, where)) {
            Axis axis = axes.get(i);
            if (axis.path().steps().size() != 1
                    || !(axis.path().steps().get(0) instanceof TermPath.Step.Field field)) {
                return null;
            }
            // The class's own values, and only those: a class composed through a constructor is a
            // walk this does not do, and one nothing can produce a value for has nothing to put
            // here.
            if (!(axis.classes().get(where[i]).representatives().evaluate()
                    instanceof RepresentativeSource.Evaluation.Values values)) {
                return null;
            }
            moved.put(field.name(), values.written().get(0));
        }
        return moved.isEmpty() ? null : FixtureTemplate.spreading(type, baseline, moved);
    }

    /**
     * The assignment a row about one class is written at: that class, and every other position at
     * the first of its own.
     *
     * <p>One position moved and no more, which is what makes the row readable as being about that
     * class. A row that also moved the positions beside it would be several answers a person has to
     * separate before any of them says anything, and which of the three the answer turned on would
     * be exactly what it does not say (issue #967).
     *
     * <p>The first class is where the others stand for now, and it is a stand-in for something
     * better: a value the model already states — a {@code let} in scope, or the value a row already
     * written puts there — is what a reader would recognise, and the first class of a position is
     * merely the first thing this can name. What the row is about does not change with it.
     */
    private static int[] movingOnly(List<Axis> axes, int at, int cls) {
        return standing(axes, null, at, cls);
    }

    /**
     * Where a position the row is not about stands: the first of its classes something can write a
     * value for, among the ones {@code admits} allows.
     *
     * <p>The first that <em>can</em>, and not the first. A class nothing composes a value for is
     * still a class of the position, and a row standing there is a row that cannot be built — so
     * taking the first outright made every row of every other position unbuildable whenever one
     * position happened to declare such a class first.
     *
     * <p>The first of the rest where none can, which is a row that will not build. Said that way
     * rather than by refusing here: what could not be composed and why is {@link #build}'s answer,
     * and a second place deciding it would be a second reason for the same row.
     */
    private static int standingAt(Axis axis, java.util.function.IntPredicate admits) {
        int first = -1;
        for (int c = 0; c < axis.classes().size(); c++) {
            if (!admits.test(c)) {
                continue;
            }
            if (first < 0) {
                first = c;
            }
            if (axis.classes().get(c).representatives().buildable()) {
                return c;
            }
        }
        return first;
    }

    /**
     * What building a row at one boundary came to: the row, or why there is none.
     *
     * <p>One or the other, and the type says so. A caller measuring the boundary reads whether a row
     * was built, which is a value that went through the decoder and so a witness that the edge can be
     * written; a caller offering work to a person reads the row itself. The attempt is made once and
     * both read it.
     */
    public sealed interface BoundaryAttempt {

        /** A value with the edge in it, built and accepted. */
        record Built(GeneratedRow row) implements BoundaryAttempt {}

        /** No row came of it, and why. Never a statement that none exists. */
        record Unresolved(UnresolvedCombination why) implements BoundaryAttempt {}
    }

    /**
     * A row at one coverage item of a border, built through the module's own decoders.
     *
     * <p>One entry, whatever the border was drawn on. What a search is handed is where each position
     * has to stand — one of them for a line at a position's own value, two for a line where two
     * positions stand apart, and as many as the rule named for a line over a form — and writing a row
     * with some positions fixed is one procedure. Written as a method per shape of line, the two that
     * existed offered different candidates for the same position and a third would have been a third
     * offer.
     *
     * <p><b>Every position of the item is fixed at once</b>, which is what makes the row one at the
     * item. A search that settled one and left the others to their own ranges would produce a row
     * beside the line as readily as one at it.
     *
     * <p>One row per boundary rather than one row covering several, because a row is a question put to
     * a person and a row sitting on three edges at once is three answers they have to separate.
     *
     * <p>Nothing here decides that a boundary cannot be written at. A refusal is a refusal of the
     * candidates that were tried, and another value of the same edge may build; what comes back says
     * which of the two happened and leaves the reading to the caller.
     */
    public static BoundaryAttempt probeFixing(Subject subject, String label,
                                              java.util.function.Function<NumericTerm, Carrier> on,
                                              Map<NumericTerm, Place> fixing, CandidateCheck check) {
        Map<TermPath, List<FixtureTemplate>> decided = new LinkedHashMap<>();
        // What the rest of the row has to sit beside. A field of a record is not chosen from its own
        // type once another field of that record is fixed: the rule relating them says what is left,
        // and taking the bottom of the type's range instead is how a boundary that can be written
        // came back as one every value tried was refused at.
        Map<TermPath, Place> settled = new LinkedHashMap<>();
        Map<TermPath, UnresolvedCombination.Reason> heldBack = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : fixing.entrySet()) {
            // The order this position is written back on, which is the position's own. Handed one
            // order for the whole fixing, a form over positions written back differently wrote each
            // of them as a value of whichever order the quantity happened to answer with.
            Carrier carrier = on.apply(each.getKey());
            if (carrier == null) {
                throw new IllegalStateException("a row is owed at " + each.getKey()
                        + " and the quantity it is owed for is over no such position");
            }
            Edge edge = edgeAt(subject, carrier, each.getKey(), each.getValue(), fixing.size() > 1);
            if (edge.values().isEmpty()) {
                return new BoundaryAttempt.Unresolved(
                        new UnresolvedCombination(List.of(label), edge.reason()));
            }
            TermPath at = each.getKey().path();
            // Two terms at one path is one location asked for two things at once — a string of a
            // length and the string itself — and what a row writes at a location is one value. The
            // fixing keeps them apart ({@link Realization.Found}) and this cannot, so it says so
            // rather than writing whichever came last and offering half the point as the whole.
            if (decided.containsKey(at)) {
                return new BoundaryAttempt.Unresolved(new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE));
            }
            decided.put(at, edge.values());
            if (edge.settledAt() != null) {
                settled.put(at, edge.settledAt());
            }
            heldBack.put(at, edge.refused());
        }
        List<FixtureTemplate> inputs = new ArrayList<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            String head = subject.parameters().get(p);
            Map<TermPath, List<FixtureTemplate>> here = new LinkedHashMap<>();
            for (NumericTerm term : fixing.keySet()) {
                if (term.path().head().equals(head)) {
                    here.put(term.path(), decided.get(term.path()));
                }
            }
            Outcome tried = valueAt(subject, p, here, settled, Requirements.NONE, check);
            if (tried.value() == null) {
                // Where the refusal is of the values one edge offered, what that edge held back
                // outranks it: values that were never built were not among the ones refused. Only
                // where one edge offered them, though — a point of a form fixes several positions
                // under one parameter, and which of their edges the refusal was about is not
                // something this knows. Taken from whichever came first, the reason named the wrong
                // position's search.
                UnresolvedCombination.Reason why = tried.reason();
                if (here.size() == 1
                        && why == UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
                    why = heldBack.getOrDefault(here.keySet().iterator().next(), why);
                }
                return new BoundaryAttempt.Unresolved(
                        new UnresolvedCombination(List.of(label), why, tried.detail()));
            }
            inputs.add(tried.value());
        }
        return new BoundaryAttempt.Built(
                new GeneratedRow(new Purpose.ForAPoint(label), inputs));
    }

    /**
     * The values that stand at one position's place of the item.
     *
     * <p>The axis's own edge where the subject has an axis at this position, which is where a count
     * taken of a location is met by whatever carries that count. Where it has none — a behavior whose
     * inputs nothing bounds has no axis and its body still draws lines between them — the value is
     * written from the declared type.
     *
     * @param besideAnother whether another position of the same item is fixed too. A count taken of a
     *                      location is met by several values and only one of them can be offered
     *                      beside a second position that is being fixed as well, which is a limit of
     *                      the reading this replaced rather than a rule: it is preserved here so that
     *                      collapsing the two searches into one changed nothing, and removing it is
     *                      its own answer to give
     */
    private static Edge edgeAt(Subject subject, Carrier carrier, NumericTerm term, Place at,
                               boolean besideAnother) {
        if (besideAnother && term instanceof NumericTerm.SizeOf) {
            return Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        for (Axis axis : subject.axes()) {
            if (axis.term().equals(term)) {
                return edgeOf(axis, carrier, at, subject.symbols(), subject.inputs().policy());
            }
        }
        // No axis at this position, which a behavior whose inputs nothing bounds has none of while
        // its body still draws lines between them. A count taken of a location is not writable this
        // way: four is not what goes at the position, it is four characters somebody has to choose.
        Type declared = term instanceof NumericTerm.SizeOf ? null : declaredAt(subject, term.path());
        if (declared == null) {
            return Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        FixtureTemplate standing = Witnesses.wrapped(declared,
                FixtureTemplate.on(carrier, at, subject.symbols().scope()::reach),
                subject.symbols());
        return standing == null ? Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : new Edge(List.of(standing), null, at, null);
    }

    /** The type declared at a position this subject has no axis for, which is a bare parameter and
     *  nothing else: a field of one is reached through a type this cannot name here. */
    private static Type declaredAt(Subject subject, TermPath path) {
        if (!path.steps().isEmpty()) {
            return null;
        }
        int at = subject.parameters().indexOf(path.head());
        return at < 0 || at >= subject.types().size() ? null : subject.types().get(at);
    }

    /**
     * The axes in the order the search fixes them.
     *
     * <p>Most classes first, and then parameter order and the path, so that two runs of one model
     * order them the same way and the rows come out in the same order twice.
     */
    private static List<Axis> ordered(Subject subject) {
        List<Axis> divided = new ArrayList<>(subject.axes().stream().filter(Axis::derivable).toList());
        divided.sort(Comparator.comparingInt((Axis a) -> -a.classes().size())
                .thenComparingInt(a -> {
                    int at = subject.parameters().indexOf(a.path().head());
                    return at < 0 ? Integer.MAX_VALUE : at;
                })
                .thenComparing(a -> a.path().toString()));
        return List.copyOf(divided);
    }

    /** Whether every existing row said where it sat at this position. One that did not leaves the
     * position undecided: what the rows cover there is unknown, so what they do not cover is unknown
     * too. */
    private static boolean readEverywhere(Axis axis, List<ObservedRow> existing) {
        for (ObservedRow row : existing) {
            Classification where = row.at().get(axis.id());
            // Whether the reading stopped, and not whether it placed anything. A row whose list
            // holds one value in a class and one nothing could read placed something and is short
            // of the rest, so what it does not cover here is as unknown as if it had placed nothing.
            if (where != null && where.stopped() != null) {
                return false;
            }
        }
        return true;
    }

    /**
     * Which one class each ordered axis fell in for one row, or -1 where the row named no single
     * one — because it could not be read there, or because its values fell in more than one.
     *
     * <p>Where a row sits, which is what a cell to be filled beside it is worked out from. A row
     * whose list holds elements either side of a line sits in no one cell at that position, and
     * choosing one of them would place the next row against an element this picked.
     */
    private static int[] whereIn(Map<AxisId, Classification> row, List<Axis> axes) {
        List<int[]> reached = reachedIn(row, axes);
        int[] at = new int[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            at[i] = reached.get(i).length == 1 ? reached.get(i)[0] : -1;
        }
        return at;
    }

    /**
     * Which classes each ordered axis fell in for one row, empty where the row did not say.
     *
     * <p>More than one where the position is inside a sequence: a row whose list holds elements
     * either side of a line stands in both classes there, and picking one of them would report what
     * the row covers off an element this chose.
     */
    private static List<int[]> reachedIn(Map<AxisId, Classification> row, List<Axis> axes) {
        List<int[]> at = new ArrayList<>();
        for (Axis axis : axes) {
            List<Integer> here = new ArrayList<>();
            if (row.get(axis.id()) instanceof Classification.Classified in) {
                for (int c = 0; c < axis.classes().size(); c++) {
                    if (in.classIds().contains(axis.classes().get(c).id())) {
                        here.add(c);
                    }
                }
            }
            int[] found = new int[here.size()];
            for (int k = 0; k < here.size(); k++) {
                found[k] = here.get(k);
            }
            at.add(found);
        }
        return at;
    }

    /** Where {@code id} sits among {@code axis}'s classes, or -1 where it is none of them. */
    private static int classIn(Axis axis, String id) {
        for (int c = 0; c < axis.classes().size(); c++) {
            if (axis.classes().get(c).id().equals(id)) {
                return c;
            }
        }
        return -1;
    }

    /**
    /**
     * Every position at the first class {@code cell} admits it, which is the assignment a row for
     * that cell is first tried at.
     *
     * <p>The positions the cell settles hold what it settles them at; the rest hold the first of
     * what they may, because the row is not about them. A row that also moved the positions beside
     * the combination would be several answers a person has to separate.
     */
    private static int[] firstAdmitted(List<Axis> axes, InteractionCells.Cell cell) {
        return standing(axes, null, NOT_HERE, NOT_HERE, cell::admits);
    }

    /** What a row is about, in the words the model uses. The class's label rather than its id: an id
     * is scoped by carrying its own path, and a description that carries the path already would say
     * it twice. */
    private static String label(Axis axis, int cls) {
        return axis.path() + "=" + axis.classes().get(cls).label();
    }

    /**
     * The positions the cell is about, at the classes the row came to hold.
     *
     * <p>The cell says which classes a position may hold and the row holds one of them, so the name
     * is read off the row: a name carrying the set would say what the cell allows rather than what
     * this row is. Positions the cell says nothing about stay out — the assignment chose them and
     * the combination says nothing about where they stand.
     *
     * <p>For saying which combination a search went to and came back from, and not for naming a
     * row: a row is composed for the arms it was looked for.
     */
    private static List<String> labels(List<Axis> axes, InteractionCells.Cell cell, int[] where) {
        List<String> out = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            if (cell.narrows(i) && where[i] >= 0) {
                out.add(label(axes.get(i), where[i]));
            }
        }
        return out;
    }

    // --- looking for a row that fills a combination ----------------------------------------------

    /**
     * What the search for a row filling one combination came to.
     *
     * <p>Three answers and not two, because a row seen filling the combination and a row offered
     * because nothing could watch it are not the same thing to have found. They differ in what may
     * afterwards be concluded from the row and in whether this generation may say its rows were
     * confirmed, so which of them it is, is the answer — rather than something read back off an
     * empty account of the run.
     */
    private sealed interface Witness {

        /** A row seen filling the combination, carrying the witness — that being the only value
         *  which says so. */
        record Certified(GeneratedRow row, CellSelection.CertifiedWitness by) implements Witness {}

        /** A row nothing could watch, offered on the strength of the reading alone. */
        record Unconfirmed(GeneratedRow row, int[] where) implements Witness {}

        /** No row to offer, and why. Never a statement that none exists. */
        record None(List<String> classes, UnresolvedCombination.Reason reason, String detail,
                    Optional<String> said) implements Witness {}
    }

    /**
     * A row that fills {@code selection}, looked for among the assignments it leaves open.
     *
     * <p>Composing and confirming are one act here and are two questions. A candidate is composed by
     * fixing every position, which the combination settles for some of them and the assignment
     * settles for the rest; then it is run, and what it did is held against what the combination
     * says a row filling it does. A candidate that went elsewhere is dropped and another assignment
     * is tried, because which assignment was chosen is a choice this made rather than something the
     * combination said.
     *
     * <p>What a run of candidates that all missed establishes is that they were not witnesses. It is
     * not that the combination is unreachable, and it is not by itself that the reading naming the
     * combination is wrong — the assignments were this search's, and so was the number of them.
     */
    private static Witness witnessFor(Subject subject, List<Axis> axes,
                                      CellSelection selection, CandidateCheck check, Trial trial,
                                      List<Integer> takes) {
        InteractionCells.Cell cell = selection.cell();
        List<int[]> tried = new ArrayList<>();
        Attempt last = null;
        int[] where = null;
        boolean missed = false;
        for (int candidate = 0; candidate < MOST_CANDIDATES; candidate++) {
            int[] at = assignment(axes, cell, candidate, tried);
            if (at == null) {
                break;   // the combination leaves nothing this has not already tried
            }
            tried.add(at);
            where = at;
            last = build(subject, axes, at, check);
            if (last.row() == null) {
                continue;   // nothing composed here; another assignment may compose
            }
            // Composed for the arms it was looked for, and not for the combination it was found
            // at. The combination is where the search went; the arms are what somebody is owed a
            // row at. One row answering two of them is two answers and not one composite thing.
            GeneratedRow named = new GeneratedRow(
                    takes.stream().map(Purpose.ForAnArm::new).map(Purpose.class::cast).toList(),
                    last.row().inputs());
            switch (trial.run(named.inputs())) {
                // Nothing can say where it went, so nothing certifies it and nothing refutes it.
                // Offered as it was before anything ran, and said to be. Both of the ways that
                // happens come here: nothing applied the row, or nothing was recording while it
                // was applied.
                case Watched.NoAccount _ -> {
                    return new Witness.Unconfirmed(named, at);
                }
                case Watched.Ran ran -> {
                    // Through the one thing that can say a row filled a combination, which is the
                    // same thing a row already in the file is put through.
                    Optional<CellSelection.CertifiedWitness> found =
                            selection.certifying(at, ran.seen());
                    if (found.isPresent()) {
                        return new Witness.Certified(named, found.get());
                    }
                    missed = true;
                }
            }
        }
        List<String> named = where == null ? List.of() : labels(axes, cell, where);
        if (missed) {
            return new Witness.None(named, UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, null,
                    Optional.empty());
        }
        if (last != null && last.row() == null) {
            return new Witness.None(named, last.reason(), last.detail(), last.said());
        }
        // Nothing was composed and nothing was refused, which takes the combination leaving no
        // assignment at all. Named rather than guessed at, the same way every other empty result
        // here is.
        return new Witness.None(named, UnresolvedCombination.Reason.NO_REASON_RECORDED, null,
                Optional.empty());
    }

    /**
     * The {@code candidate}th assignment to try for {@code cell}, or null where it leaves none this
     * has not tried.
     *
     * <p>The first leaves every position the combination does not settle at the first class the
     * cell admits there, which is as much of the row as this is about. The rest are the assignments
     * the combination admits, counted off in order — a fixed order, so the same model offers the
     * same rows twice.
     *
     * <p>Bounded by how many have been tried rather than by a walk over the space: at most
     * {@link #MOST_CANDIDATES} assignments are ever tried, so one of the first that many is one
     * that has not been.
     */
    private static int[] assignment(List<Axis> axes,
                                    InteractionCells.Cell cell, int candidate, List<int[]> tried) {
        if (candidate == 0) {
            return firstAdmitted(axes, cell);
        }
        List<List<Integer>> admitted = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            List<Integer> here = new ArrayList<>();
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (cell.admits(i, c)) {
                    here.add(c);
                }
            }
            if (here.isEmpty()) {
                return null;   // a position with nothing in it is not a combination
            }
            admitted.add(here);
        }
        for (int index = 0; index < MOST_CANDIDATES; index++) {
            int[] where = new int[axes.size()];
            int left = index;
            for (int i = 0; i < axes.size(); i++) {
                List<Integer> here = admitted.get(i);
                where[i] = here.get(left % here.size());
                left /= here.size();
            }
            if (!alreadyTried(tried, where)) {
                return where;
            }
        }
        return null;
    }

    private static boolean alreadyTried(List<int[]> tried, int[] where) {
        for (int[] each : tried) {
            if (java.util.Arrays.equals(each, where)) {
                return true;
            }
        }
        return false;
    }

    // --- turning classes into a row -------------------------------------------------------------

    private record Attempt(GeneratedRow row, UnresolvedCombination.Reason reason, String detail,
                           Optional<String> said) {

        static Attempt of(GeneratedRow row) {
            return new Attempt(row, null, null, Optional.empty());
        }

        static Attempt no(UnresolvedCombination.Reason reason, String detail) {
            return new Attempt(null, reason, detail, Optional.empty());
        }
    }

    /**
     * One assignment of classes, built into the values a row would carry.
     *
     * <p>What a position offers is values, and what has to build is all of them together: the check is
     * the model's own constructor over the whole input, so a field's value can be refused for what
     * another field was given. The unit being tried is the tuple, not the value — walking one index
     * across every position at once tries the diagonal of the choices and misses the rest, and two
     * fields whose rules are the same but written in a different order then land on different indices
     * and never meet.
     *
     * <p>So the assignments are walked outward from the one where every position takes its first
     * value: then the ones a single position has moved one step from, then two, and so on. Nearest
     * first, because a position's first value is the one that stands for it, and a row that took a
     * later one at every position is a row further from what the model says it is about. The walk
     * stops at {@link #MAX_TUPLES}, and stopping is reported as having stopped rather than as
     * everything having been refused.
     */
    private static Attempt build(Subject subject, List<Axis> axes, int[] where,
                                 CandidateCheck check) {
        return build(subject, axes, where, check, Map.of());
    }

    /**
     * The same, with the parameters {@code given} names written as it says instead of composed.
     *
     * <p>Which is what makes a value the model already states an origin of the search rather than a
     * rewrite of its answer. Composed first and rewritten after, a row the baseline could have been
     * written for came back as one nothing composed — a representative chosen from the classes
     * alone breaks a rule relating two positions while the model's own value does not — and a row
     * the baseline needed nothing beside came back carrying whatever the composition had needed.
     */
    private static Attempt build(Subject subject, List<Axis> axes, int[] where,
                                 CandidateCheck check, Map<String, FixtureTemplate> given) {
        Map<TermPath, List<FixtureTemplate>> decided = new LinkedHashMap<>();
        // What every position of this row has to be for the classes it sits in to exist. Read off
        // the paths and off the classes together, because both state one: a position under a
        // refinement requires it by being there at all, and a class of the position above states
        // the same requirement by being the class it is.
        Requirements required = Requirements.NONE;
        for (int i = 0; i < axes.size(); i++) {
            // A position this row stands at no class of. What it would have required is not
            // something the row has to meet, and there is nothing to compose for it.
            if (where[i] == NOT_HERE) {
                continue;
            }
            TermPath path = axes.get(i).path();
            String at = label(axes.get(i), where[i]);
            Requirements.Merge both =
                    required.merge(axes.get(i).requiring(axes.get(i).classes().get(where[i])));
            // A row that would have to be two things at one position. Which is not a combination
            // the model has at all — said here, and said as that: reported as a value nothing
            // composed, an author would go looking for a row that cannot exist.
            if (!(both instanceof Requirements.Merge.Merged merged)) {
                return new Attempt(null, UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                        at, Optional.empty());
            }
            required = merged.requirements();
            switch (axes.get(i).classes().get(where[i]).representatives().evaluate()) {
                case RepresentativeSource.Evaluation.Values values ->
                        decided.put(path, values.written());
                // Not a value but how one is arrived at: the walk below builds one at this position,
                // field by field, the way it builds every other record. What it is built through is
                // already in the requirements, which is where the plan reads it.
                case RepresentativeSource.Evaluation.Compose _ -> { }
                // What the class said about itself. A class that recorded why nothing was produced
                // for it knows something this does not, and the two answers are not the same claim:
                // one is that nothing was arrived at, and the other is that nothing can be. Read as
                // the first, a case somebody can write in one line is reported as a row that does
                // not exist.
                case RepresentativeSource.Evaluation.NothingProducible cannot -> {
                    return new Attempt(null, UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, at,
                            Optional.of(cannot.why()));
                }
            }
        }
        List<FixtureTemplate> inputs = new ArrayList<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            FixtureTemplate written = given.get(subject.parameters().get(p));
            if (written != null) {
                // Written as the caller says, and put through the same check a composed value goes
                // through: how a row is written never decides whether the model allows it.
                Optional<String> refused = check.refuse(p, written);
                if (refused.isPresent()) {
                    return new Attempt(null, UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                            subject.parameters().get(p), refused);
                }
                inputs.add(written);
                continue;
            }
            Outcome tried = valueFor(subject, p, axes, decided, required, check);
            if (tried.value() == null) {
                return Attempt.no(tried.reason(), tried.detail());
            }
            inputs.add(tried.value());
        }
        // The values, and no name. What a row is about is what it was composed for, which is the
        // caller's question and not this one's: this is handed an assignment and does not know
        // whether it is a class, a combination the body decides together, or an edge. Named here
        // from the assignment, every row said every position it happened to hold — which is what
        // put three classes in the name of a row composed for one (issue #967).
        return Attempt.of(new GeneratedRow(new Purpose.Unstated(), inputs));
    }

    /**
     * One parameter's value, searched for on its own.
     *
     * <p>Each parameter is built and refused on its own — the check is the model's constructor for that
     * one type, and a rule relating two of them is not something a model can write. So the choices
     * under one parameter and the choices under another do not multiply, and searching them together
     * would spend the bound on assignments that differ only in a parameter already settled. Two
     * parameters of eight either-or fields are two searches of 256, not one of 65,536.
     */
    private static Outcome valueFor(Subject subject, int p, List<Axis> axes,
                                    Map<TermPath, List<FixtureTemplate>> decided,
                                    Requirements required, CandidateCheck check) {
        TermPath at = TermPath.of(subject.parameters().get(p));
        Map<TermPath, List<FixtureTemplate>> here = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.path().head().equals(at.head())
                    && decided.containsKey(axis.path())) {
                here.put(axis.path(), decided.get(axis.path()));
            }
        }
        return valueAt(subject, p, here, settledIn(here), required, check);
    }

    /**
     * The positions a caller fixed at one number.
     *
     * <p>Only where the position has a single value to take. A class offers one value to stand for
     * it, and that is the one the row will carry, so the rest of the record can be chosen beside it;
     * a position still holding several is not settled at all and nothing is claimed of it.
     */
    private static Map<TermPath, Place> settledIn(Map<TermPath, List<FixtureTemplate>> decided) {
        Map<TermPath, Place> out = new LinkedHashMap<>();
        decided.forEach((path, candidates) -> {
            if (candidates.size() == 1) {
                Place number = Counts.writtenIn(candidates.get(0).value());
                if (number != null) {
                    out.put(path, number);
                }
            }
        });
        return out;
    }

    /** One parameter's value, with the positions the caller fixed already decided. */
    private static Outcome valueAt(Subject subject, int p,
                                   Map<TermPath, List<FixtureTemplate>> decided,
                                   Map<TermPath, Place> settled,
                                   Requirements required, CandidateCheck check) {
        // Where a value has to be built under this parameter, worked out once. What each position
        // may take, the search that chooses them one at a time, and the composing of what was chosen
        // all read this, so there is no second reading of the declarations for one of them to
        // disagree with.
        TermPath root = TermPath.of(subject.parameters().get(p));
        // How many the rules say a list at a position holds at the fewest, read from the same
        // reading of the parameter the values are chosen against. A list built around an element
        // has to meet that too: a row holding an element in the class and breaking the rule about
        // how many the list holds is not a row.
        FieldDomains under = rulesOf(subject.types().get(p), subject.symbols(),
                subject.inputs().policy(), under(root, settled));
        ConstructionPlan plan = ConstructionPlan.of(subject.types().get(p), root, subject.symbols(),
                decided.keySet(), required, (at, building) -> leastHeld(under, at, building,
                        subject.symbols()));
        Choices choices = choicesOf(subject, p, plan, decided, settled);
        if (choices.missingAt() != null) {
            return new Outcome(null, UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    choices.missingAt());
        }
        Outcome product = walk(subject, p, choices, check);
        if (product.value() != null) {
            return product;
        }
        // Every position took its value knowing only what the caller had settled, so a rule relating
        // two of them was satisfied only where the lists happened to already hold a pair that does.
        // Asked again choosing one position at a time, each from what is left once the ones before it
        // are asserted, which is the only way `a < b` is met in general.
        Outcome conditioned = conditioned(subject, p, plan, decided, settled, check);
        if (conditioned.value() != null) {
            return conditioned;
        }
        // A pass that stopped at its bound has not tried everything it had, and neither pass may be
        // reported as though it had: `ALL_CANDIDATES_REJECTED` is what a reader is told nothing else
        // can be written at, and a search still holding assignments it never composed has not
        // established that.
        if (product.reason() == UnresolvedCombination.Reason.SEARCH_LIMIT
                || conditioned.reason() == UnresolvedCombination.Reason.SEARCH_LIMIT) {
            return new Outcome(null, UnresolvedCombination.Reason.SEARCH_LIMIT, null);
        }
        // Every value that was offered was refused, which is only the whole story where every value
        // the rules allow was offered. A position that read a count past what a row is built to carry,
        // or that has more pairings than are built at once, held something back, and saying so is the
        // difference between a fact about the model and a fact about this.
        UnresolvedCombination.Reason held = heldBack(subject, p, plan, settled);
        return held == null ? product : new Outcome(null, held, null);
    }

    /**
     * Whether {@code axis} stands inside a collection the rules leave no room in.
     *
     * <p>Asked of the collections the position is inside and not of the position itself: what a rule
     * capping a collection at none says is that nothing stands at any position under it, whatever
     * the values there could otherwise be. Asked of every one of them, because a position two
     * sequences deep needs each of them to hold something — read off the outermost alone, a list of
     * lists whose inner lists hold nothing was offered rows for what the inner lists hold.
     */
    private static boolean holdsNothing(Subject subject, Axis axis) {
        for (TermPath inside : axis.path().sequencesContainingIt()) {
            if (subject.held().most(inside) < 1) {
                return true;
            }
        }
        return false;
    }

    /**
     * How many the rules say the list at {@code path} holds at the most, or every number where they
     * say nothing about how many.
     *
     * <p>Beside the floor and asked separately, because a collection built around an element has to
     * meet both: the floor says how many it needs beside the one being placed, and this says whether
     * there is room for that one at all. Read only for the floor, a rule capping a collection at
     * none was met with a collection of one and every combination of the row came back as one every
     * value was refused at — over a position the rules leave no room in, and over the positions
     * beside it that have nothing to do with it.
     */
    private static int mostHeld(FieldDomains rules, TermPath path, Type building, Symbols symbols) {
        String field = fieldUnder(path);
        return Partitions.mostHeld(building, symbols, field == null ? null : rules.heldAt(field));
    }

    /** How many the rules say the value built at {@code path} holds at the fewest, or zero where
     *  they say nothing about how many. Read the same two ways as the cap beside it. */
    private static int leastHeld(FieldDomains rules, TermPath path, Type building, Symbols symbols) {
        String field = fieldUnder(path);
        return Partitions.leastHeld(building, symbols, field == null ? null : rules.heldAt(field));
    }

    /**
     * Why a position of this parameter offered less than its rules allow, or null where none did.
     *
     * <p>Under the same settled positions the values were chosen against. A rule counting one field
     * against another asks for nothing in particular until the row fixes the other, so a reading
     * without them answers about a rule this row is no longer under — and would say "every value
     * tried was refused" of a position whose values were never built.
     */
    private static UnresolvedCombination.Reason heldBack(Subject subject, int p,
                                                         ConstructionPlan plan,
                                                         Map<TermPath, Place> settled) {
        TermPath root = TermPath.of(subject.parameters().get(p));
        Type declared = subject.types().get(p);
        FieldDomains rules = rulesOf(declared, subject.symbols(), subject.inputs().policy(),
                under(root, settled));
        UnresolvedCombination.Reason held = null;
        // A collection asked to hold a value in a class, whose rules say it holds fewer than that.
        // Nothing composes one: what the search would offer is a collection the rules refuse, and
        // saying every candidate was refused sends an author looking for a value where the rule
        // says there is no room for one.
        for (ConstructionPlan.Held each : plan.held()) {
            if (mostHeld(rules, each.at(), each.type(), subject.symbols()) < each.least()) {
                return UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE;
            }
        }
        for (ConstructionPlan.Slot each : plan.slots()) {
            String field = fieldUnder(each.at());
            UnresolvedCombination.Reason here = Partitions.notBuilt(each.type(), subject.symbols(),
                    subject.inputs().policy(), field == null ? null : rules.heldAt(field));
            // Nothing of the shape having been built outranks some of it having been: the first says
            // the search never had what the rule asks for, and a reader owed one sentence is owed that.
            if (here == UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE) {
                return here;
            }
            if (here != null) {
                held = here;
            }
        }
        return held;
    }

    /**
     * One parameter's value, chosen a position at a time.
     *
     * <p>Depth first, so that a position is chosen against a projection that already has the ones
     * before it in it. The projection is the same one the whole search started from — what the
     * record's rules leave each of its fields — asked again with the assignment so far settled into
     * it, which is what {@link FieldDomains#of(TypeSymbol, Hir.Data, Symbols, Map)} is for.
     *
     * <p>Second, and not instead. What it costs is a reading of the record's rules per position per
     * branch, and the search in front of it answers most rows without any of that; running this one
     * first would spend it on every row to change none of them.
     */
    private static Outcome conditioned(Subject subject, int p, ConstructionPlan plan,
                                       Map<TermPath, List<FixtureTemplate>> decided,
                                       Map<TermPath, Place> settled,
                                       CandidateCheck check) {
        List<ConstructionPlan.Slot> found = plan.slots();
        // What the caller fixed goes first, so that everything chosen after it is chosen beside it.
        // A class stands for one value and a boundary is one value, and neither is worth deciding
        // after the positions whose range it settles.
        List<ConstructionPlan.Slot> positions = new ArrayList<>(
                found.stream().filter(each -> decided.containsKey(each.at())).toList());
        positions.addAll(
                found.stream().filter(each -> !decided.containsKey(each.at())).toList());
        Budget budget = new Budget();
        FixtureTemplate built = descend(subject, p, plan, positions, 0, new LinkedHashMap<>(),
                new LinkedHashMap<>(settled), decided, check, budget);
        if (built != null) {
            return new Outcome(built, null, null);
        }
        return new Outcome(null, budget.cutShort
                ? UnresolvedCombination.Reason.SEARCH_LIMIT
                : UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED, null);
    }

    /**
     * What is left of the bound on one search, and whether it ran out.
     *
     * <p>The two are one fact and are held together. Nothing left is not the same as everything
     * tried, and a search that stopped at the bound reporting that every value was refused would put
     * a combination nobody looked at beside the ones that were.
     */
    private static final class Budget {

        private int left = MAX_TUPLES;
        private boolean cutShort;

        /**
         * Whether there is room to compose one more assignment.
         *
         * <p>The only place the bound is called reached. Spending the last of it is not the same as
         * being short of it: a search whose last assignment was composed and refused has tried
         * everything it had, and marking it where the count reaches zero would report the one search
         * that finished as the one that stopped.
         */
        boolean spend() {
            if (left <= 0) {
                cutShort = true;
                return false;
            }
            left--;
            return true;
        }
    }

    /**
     * The assignment this branch leads to, or null where none of them builds.
     *
     * @param chosen  what the positions before this one took
     * @param settled the numbers among them, which is what a projection can be asked about
     * @param budget  assignments left to compose, shared down the whole search
     */
    private static FixtureTemplate descend(Subject subject, int p, ConstructionPlan plan,
                                           List<ConstructionPlan.Slot> positions, int index,
                                           Map<TermPath, FixtureTemplate> chosen,
                                           Map<TermPath, Place> settled,
                                           Map<TermPath, List<FixtureTemplate>> decided,
                                           CandidateCheck check, Budget budget) {
        if (index == positions.size()) {
            if (!budget.spend()) {
                return null;
            }
            FixtureTemplate whole = compose(plan.root(), chosen, subject.symbols(), subject.inputs().policy());
            return whole != null && check.refuse(p, whole).isEmpty() ? whole : null;
        }
        ConstructionPlan.Slot position = positions.get(index);
        TermPath where = position.at();
        for (FixtureTemplate candidate : candidatesAt(subject, p, position, settled, decided)) {
            chosen.put(where, candidate);
            Place number = Counts.writtenIn(candidate.value());
            if (number != null) {
                settled.put(where, number);
            }
            FixtureTemplate found = descend(subject, p, plan, positions, index + 1, chosen, settled,
                    decided, check, budget);
            if (found != null) {
                return found;
            }
            chosen.remove(where);
            settled.remove(where);
            if (budget.cutShort) {
                return null;
            }
        }
        return null;
    }

    /** What one position can take, given what the positions before it took. */
    private static List<FixtureTemplate> candidatesAt(Subject subject, int p,
                                                      ConstructionPlan.Slot position,
                                                      Map<TermPath, Place> settled,
                                                      Map<TermPath, List<FixtureTemplate>> decided) {
        List<FixtureTemplate> fixed = decided.get(position.at());
        if (fixed != null) {
            return fixed;
        }
        TermPath at = TermPath.of(subject.parameters().get(p));
        FieldDomains left = rulesOf(subject.types().get(p), subject.symbols(),
                subject.inputs().policy(), under(at, settled));
        String field = fieldUnder(position.at());
        return Partitions.displacedRepresentativesOf(position.type(), subject.symbols(),
                subject.inputs().policy(), field == null ? null : left.at(field),
                field == null ? null : left.heldAt(field));
    }

    /**
     * Every position a row chooses a value at, in the order they are decided.
     *
     * @param at        the paths, so that an assignment can be read back as which value went where
     * @param values    what each of those positions can take, never empty
     * @param reserves  what each holds back for the case where everything above was refused, which is
     *                  usually nothing. Kept apart rather than appended: the search is over the
     *                  product of {@code values} and is bounded, so a value added to one position
     *                  moves the assignments past it further back — and a row that was being reached
     *                  would stop being reached over a widening at a position it does not involve
     * @param missingAt the position nothing at all can be written at, where there is one — which is
     *                  not a choice to make but a reason there is no row
     * @param plan      what these positions are positions of, carried so that an assignment is
     *                  composed back into the shape the positions were taken from rather than into
     *                  one worked out a second time
     */
    private record Choices(ConstructionPlan plan, List<TermPath> at,
                           List<List<FixtureTemplate>> values,
                           List<List<FixtureTemplate>> reserves, String missingAt) {

        static Choices missing(ConstructionPlan plan, String at) {
            return new Choices(plan, List.of(), List.of(), List.of(), at);
        }

        boolean anythingHeldBack() {
            return reserves.stream().anyMatch(each -> !each.isEmpty());
        }

        /** The same positions, each offering what it held back as well. */
        List<List<FixtureTemplate>> widened() {
            List<List<FixtureTemplate>> out = new ArrayList<>();
            for (int i = 0; i < values.size(); i++) {
                List<FixtureTemplate> here = new ArrayList<>(values.get(i));
                here.addAll(reserves.get(i));
                out.add(List.copyOf(here));
            }
            return List.copyOf(out);
        }
    }

    /**
     * What the positions of one row can take: the axes at the classes this assignment fixes, and every
     * other position at whatever stands for its type.
     *
     * <p>The plan's positions and not a walk of its own, which is what leaves nothing for these and
     * the composing to disagree about. A record is not a position but the fields under it are, and a
     * position the caller has already decided keeps what it was given.
     *
     * @param decided what the caller fixed: the classes of an axis, or the single value a boundary is
     *                to be reached at
     */
    private static Choices choicesOf(Subject subject, int p, ConstructionPlan plan,
                                     Map<TermPath, List<FixtureTemplate>> decided,
                                     Map<TermPath, Place> settled) {
        Symbols symbols = subject.symbols();
        ReadingPolicy policy = subject.inputs().policy();
        TermPath at = TermPath.of(subject.parameters().get(p));
        List<TermPath> paths = new ArrayList<>(decided.keySet());
        List<List<FixtureTemplate>> values = new ArrayList<>(decided.values());
        // A position the caller fixed holds nothing back: it was given the value it is to take.
        List<List<FixtureTemplate>> reserves = new ArrayList<>(
                java.util.Collections.nCopies(paths.size(), List.<FixtureTemplate>of()));
        FieldDomains left = rulesOf(subject.types().get(p), symbols, policy, under(at, settled));
        for (ConstructionPlan.Slot slot : plan.slots()) {
            if (paths.contains(slot.at())) {
                continue;   // an axis decides here
            }
            String field = fieldUnder(slot.at());
            souther.compiler.numeric.NumericDomain.Bounds here = field == null ? null : left.at(field);
            List<FixtureTemplate> stands = Partitions.representativesHolding(slot.type(), symbols,
                    policy, here, field == null ? null : left.heldAt(field));
            if (stands.isEmpty()) {
                // Nothing could be written at all: a position of a type nothing stands for. Which is
                // not the same as a value that was written and refused, and reporting it as one sends
                // the author looking for a rule relating two inputs that has nothing to do with it.
                return Choices.missing(plan, slot.at() + ": " + Type.show(slot.type()));
            }
            paths.add(slot.at());
            values.add(stands);
            reserves.add(Partitions.inReserve(slot.type(), symbols, policy, here));
        }
        return new Choices(plan, paths, values, reserves, null);
    }

    /**
     * A row stands at no class of this axis.
     *
     * <p>Not a class this could not choose. A position under a narrowing the row does not meet is
     * one the row is not at — the reading of a written row says the same of it, standing nowhere
     * below a case it is not — so the assignment has nothing to say there and says that.
     */
    private static final int NOT_HERE = -1;

    /**
     * What an assignment requires of the row, or the position two of its classes disagree about.
     *
     * <p>One merge and no second account. An axis the assignment is not at requires nothing: it is
     * not part of this row, so what it would have needed is not something the row has to meet.
     */
    private static Requirements.Merge requiredBy(List<Axis> axes, int[] where) {
        Requirements required = Requirements.NONE;
        for (int i = 0; i < axes.size() && i < where.length; i++) {
            if (where[i] == NOT_HERE) {
                continue;
            }
            Requirements.Merge both =
                    required.merge(axes.get(i).requiring(axes.get(i).classes().get(where[i])));
            if (!(both instanceof Requirements.Merge.Merged merged)) {
                return both;
            }
            required = merged.requirements();
        }
        return new Requirements.Merge.Merged(required);
    }

    /**
     * Where every position stands for a row about the class at {@code at}, keeping what
     * {@code from} put at the positions that can keep it.
     *
     * <p>The row is about one class, so what it requires is settled first and everything else is
     * chosen beside it. A position whose own narrowing the row does not meet stands at no class of
     * it — offered its first class regardless, every row about a class under one case of a sum
     * would ask to be another case as well, and none of them would be composed.
     *
     * @param at  which axis the row is about, or {@link #NOT_HERE} where it is about none
     */
    private static int[] standing(List<Axis> axes, int[] from, int at, int cls) {
        return standing(axes, from, at, cls, (_, _) -> true);
    }

    /** Which classes of a position something outside the requirements will have. */
    private interface Admits {

        boolean at(int axis, int cls);
    }

    /** The same, among the classes {@code admits} allows — which is what a cell of the body's own
     *  combinations leaves at each position. */
    private static int[] standing(List<Axis> axes, int[] from, int at, int cls, Admits admits) {
        int[] where = new int[axes.size()];
        java.util.Arrays.fill(where, NOT_HERE);
        // What the row is about, settled before anything is chosen beside it. A class never
        // contradicts its own position: what a path requires is required at the positions above it,
        // and what a class selects is selected at the position itself.
        Requirements required = at < 0 ? Requirements.NONE
                : axes.get(at).requiring(axes.get(at).classes().get(cls));
        if (at >= 0) {
            where[at] = cls;
        }
        for (int i = 0; i < axes.size(); i++) {
            if (i == at) {
                continue;
            }
            Axis axis = axes.get(i);
            Requirements soFar = required;
            // What the position itself requires, before any class of it is chosen. A position the
            // row cannot be at takes no class, whichever class would otherwise have stood here.
            if (!soFar.compatibleWith(axis.requirements())) {
                continue;
            }
            int here = i;
            int kept = from != null && i < from.length && from[i] != NOT_HERE
                    && admits.at(here, from[i])
                    && soFar.compatibleWith(axis.requiring(axis.classes().get(from[i])))
                    ? from[i]
                    : standingAt(axis, c -> admits.at(here, c) && soFar.compatibleWith(
                            axis.requiring(axis.classes().get(c))));
            where[i] = kept;
            if (kept != NOT_HERE
                    && soFar.merge(axis.requiring(axis.classes().get(kept)))
                            instanceof Requirements.Merge.Merged merged) {
                required = merged.requirements();
            }
        }
        return where;
    }

    /**
     * The rules of the record a parameter is, or nothing where it is not one.
     *
     * <p>One reading of the parameter, not one per record inside it. A clause on the outer record
     * says what is left for a position two levels down, and a reading rebuilt at the inner record
     * has never seen it.
     *
     * <p>Written once because two readers want it: what a position is offered, and why a position
     * offered less than its rules allow. Those are the two halves of one floor and they were the two
     * halves this was already asymmetric about.
     */
    private static FieldDomains rulesOf(Type type, Symbols symbols, ReadingPolicy policy,
                                        Map<String, Count> settled) {
        return type instanceof Type.Ref ref
                && symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data && !data.newtype()
                ? FieldDomains.of(ref.name(), data, symbols, policy, settled) : FieldDomains.NONE;
    }

    /** What a position under a parameter is called where the parameter's own rules name it, or null
     * where the position is the parameter itself and where no rule of the parameter can name it
     * ({@link TermPath#fieldKey}). */
    private static String fieldUnder(TermPath path) {
        String where = path.fieldKey();
        return where == null || where.isEmpty() ? null : where;
    }

    /** The settled positions of one parameter, named the way the reading of that parameter names
     * them: from the value itself, with the parameter dropped. */
    private static Map<String, Count> under(TermPath root, Map<TermPath, Place> settled) {
        if (settled.isEmpty()) {
            return Map.of();
        }
        Map<String, Count> out = new LinkedHashMap<>();
        // The numbers among them, at the positions of this parameter. Asked of the paths and not
        // of how they are written: a rendering runs the steps together with whatever each wears, so
        // a test on the text has to name every separator a step can have.
        settled.forEach((path, at) -> {
            if (!path.isAtOrUnder(root) || !(at instanceof Count number)) {
                return;
            }
            String field = path.relativeTo(root).fieldKey();
            // Where no clause of the parameter can name the position, nothing of this parameter's
            // rules is about it and there is nothing to settle. A position inside a sequence is one,
            // and so is one under a narrowing: the rules that name it are the narrowed value's.
            if (field != null && !field.isEmpty()) {
                out.put(field, number);
            }
        });
        return out;
    }

    /** What came of trying the assignments for one parameter: its value, or why there is none. */
    private record Outcome(FixtureTemplate value, UnresolvedCombination.Reason reason,
                           String detail) {}

    /**
     * The assignments, nearest first, until one builds.
     *
     * <p>Breadth-first over the choices: the assignment where every position takes its first value,
     * then every assignment one step from one already tried. Deterministic, because the order the
     * positions were collected in is the order their steps are taken in, and a row is compared against
     * the last run's to see what changed.
     *
     * <p>Twice where a position held something back, and the second pass runs only after the first ran
     * out. What the positions offer ordinarily is searched whole before anything held in reserve is
     * offered at all, so a row the first pass reaches is reached at the assignment it always was: a
     * wider set of choices is a longer walk to every assignment in it, and a widening meant for one
     * position would otherwise take rows away from the rest.
     */
    private static Outcome walk(Subject subject, int p, Choices choices, CandidateCheck check) {
        Outcome tried = over(subject, p, choices.plan(), choices.at(), choices.values(), check);
        // Only where the ordinary assignments ran out. A search that stopped at the bound has not
        // tried them all, and starting a wider one in front of the ones it never reached would spend
        // what is left on assignments further from what the model says the row is about, while the
        // nearer ones stay untried.
        if (tried.value() != null || !choices.anythingHeldBack()
                || tried.reason() != UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return tried;
        }
        return over(subject, p, choices.plan(), choices.at(), choices.widened(), check);
    }

    /** One pass over one set of choices, from the assignment where every position takes its first
     * value outward. */
    private static Outcome over(Subject subject, int p, ConstructionPlan plan, List<TermPath> at,
                                List<List<FixtureTemplate>> values, CandidateCheck check) {
        int positions = at.size();
        ArrayDeque<int[]> next = new ArrayDeque<>();
        Set<String> seen = new LinkedHashSet<>();
        int[] first = new int[positions];
        next.add(first);
        seen.add(Arrays.toString(first));

        int tried = 0;
        while (!next.isEmpty() && tried < MAX_TUPLES) {
            int[] assignment = next.poll();
            tried++;
            Map<TermPath, FixtureTemplate> chosen = new LinkedHashMap<>();
            for (int i = 0; i < positions; i++) {
                chosen.put(at.get(i), values.get(i).get(assignment[i]));
            }
            FixtureTemplate built = compose(plan.root(), chosen, subject.symbols(), subject.inputs().policy());
            if (built != null && check.refuse(p, built).isEmpty()) {
                return new Outcome(built, null, null);
            }
            for (int i = 0; i < positions; i++) {
                if (assignment[i] + 1 >= values.get(i).size()) {
                    continue;
                }
                int[] stepped = assignment.clone();
                stepped[i]++;
                if (seen.add(Arrays.toString(stepped))) {
                    next.add(stepped);
                }
            }
        }
        // Nothing left to try is every assignment refused; something left is the search having stopped,
        // and the difference is what the reader is owed. Neither carries a detail: what these are
        // about is the combination, and a detail is read as the position that is the fact behind
        // several of them.
        return next.isEmpty()
                ? new Outcome(null, UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED, null)
                : new Outcome(null, UnresolvedCombination.Reason.SEARCH_LIMIT, null);
    }

    /**
     * The value at one position of the plan: what the assignment chose there, or a record built out
     * of the positions under it.
     *
     * <p>Null where the assignment put nothing at a position the plan asks for one at, and where a
     * name this module cannot write leaves no value to write. It used to be null for a third reason
     * — the walk that collected the choices and this one disagreeing about where the positions
     * were — and that reason has nowhere left to come from: both are this plan's positions, so a
     * disagreement between them is not something the two can be in.
     *
     * <p>What was built is handed back to the recipe that said how to build it, which puts on the
     * names the position writes its values under. The composing and the writing are one recipe
     * because they are one fact about the position: a class of {@code data DecisionN = Decision}
     * composes an {@code Approved} and the row carries {@code DecisionN(Approved { id = 1 })}.
     * Composed without that, the row carries a value of a type the parameter does not declare.
     */
    private static FixtureTemplate compose(ConstructionPlan.Node node,
                                           Map<TermPath, FixtureTemplate> chosen, Symbols symbols,
                                           ReadingPolicy policy) {
        return switch (node) {
            case ConstructionPlan.Slot slot -> chosen.get(slot.at());
            case ConstructionPlan.Built built -> composed(built, chosen, symbols, policy);
            case ConstructionPlan.Held held -> held(held, chosen, symbols, policy);
        };
    }

    /**
     * The list of one this plan builds around what stands at its element.
     *
     * <p>Under the names the position is written with, as a record is: a row at a
     * {@code data Basket = List<Item>} carries {@code Basket([...])}, and a list composed without
     * them is of a type the parameter does not declare.
     */
    private static FixtureTemplate held(ConstructionPlan.Held plan,
                                        Map<TermPath, FixtureTemplate> chosen, Symbols symbols,
                                        ReadingPolicy policy) {
        FixtureTemplate element = compose(plan.under(), chosen, symbols, policy);
        if (element == null) {
            return null;
        }
        // The one placed in the class, and enough beside it for the collection to be one the rules
        // admit. What may stand beside it is the carrier's business — a list may hold the same
        // value again and a set may not — so the collection is asked for whole rather than padded
        // here.
        if (!(souther.compiler.check.TypeView.of(plan.type(), symbols).shape()
                instanceof souther.compiler.check.Shape.Sequence carrier)) {
            return null;
        }
        FixtureTemplate collection =
                Witnesses.holdingAlso(carrier, element, plan.least(), symbols, policy);
        if (collection == null) {
            return null;
        }
        List<TypeReachName.Written> worn = new ArrayList<>();
        for (TypeOps.Layer layer : plan.worn()) {
            if (!(symbols.scope().reach(layer.named()) instanceof TypeReachName.Written written)) {
                return null;   // a name this module cannot write leaves no value to write
            }
            worn.add(written);
        }
        return RepresentativeSource.under(worn, collection);
    }

    /** One record of the plan, out of what the assignment put at the positions under it. */
    private static FixtureTemplate composed(ConstructionPlan.Built built,
                                            Map<TermPath, FixtureTemplate> chosen, Symbols symbols,
                                            ReadingPolicy policy) {
        Map<String, FixtureTemplate> fields = new LinkedHashMap<>();
        for (Map.Entry<String, ConstructionPlan.Node> under : built.under().entrySet()) {
            FixtureTemplate value = compose(under.getValue(), chosen, symbols, policy);
            if (value == null) {
                return null;
            }
            fields.put(under.getKey(), value);
        }
        // Under the names the position is written with, which the descent that found the fields took
        // off to find them. A row at a `data SlotN = Slot` carries `SlotN(Slot { ... })`, and a value
        // composed without them is of a type the parameter does not declare.
        List<TypeReachName.Written> worn = new ArrayList<>();
        for (TypeOps.Layer layer : built.worn()) {
            if (!(symbols.scope().reach(layer.named()) instanceof TypeReachName.Written written)) {
                return null;   // a name this module cannot write leaves no value to write
            }
            worn.add(written);
        }
        if (!(symbols.scope().reach(built.of()) instanceof TypeReachName.Written written)) {
            return null;
        }
        // Under every name the position wears, which where a refinement narrowed it are the names
        // it wore before the narrowing and the ones the narrowed value wears after it. One list and
        // one putting-back-on: read as two, the outer names had to be recovered from the class that
        // asked for the narrowing rather than from the position they belong to.
        return RepresentativeSource.under(worn, FixtureTemplate.record(written, fields));
    }

    /**
     * What a row is to carry where a boundary is drawn: the values to try there, why there are none
     * where there are none, and the number the position itself is thereby settled at.
     *
     * <p>The last is a number only sometimes. A line on the content of a location settles that
     * location at it, and what the rest of the record may hold is read from the rules relating them;
     * a line on a count taken of a location settles no number inside it, and saying it did would tell
     * the rest of the row that a string's length is the number the string holds.
     */
    private record Edge(List<FixtureTemplate> values, UnresolvedCombination.Reason reason,
                        Place settledAt, UnresolvedCombination.Reason heldBack) {

        Edge {
            values = List.copyOf(values);
        }

        static Edge none(UnresolvedCombination.Reason why) {
            return new Edge(List.of(), why, null, null);
        }

        /**
         * What to report where every value offered here was refused.
         *
         * <p>Not always that they were refused. Where the values are some of the values and the rest
         * were never built, the search stopping is the more of the two facts, and the one a reader
         * would act on: another value of this edge may be the one that builds.
         */
        UnresolvedCombination.Reason refused() {
            return heldBack == null ? UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED : heldBack;
        }
    }

    /**
     * The values that stand on {@code value}'s edge of {@code axis}.
     *
     * <p>Which values those are is the term's question. The content of a location is the number
     * written at it; a count taken of a location is met by whatever carries that count, and what
     * carries a count is {@link Witnesses}'s to answer — asked rather than decided here, so that a
     * value it learns to build is a boundary this reaches without being told again.
     */
    private static Edge edgeOf(Axis axis, Carrier carrier, Place at, Symbols symbols,
                               ReadingPolicy policy) {
        if (!(axis.term() instanceof NumericTerm.SizeOf)) {
            // Written by the carrier the line was drawn on, and wearing every name the position
            // declares. Read off the boundary's own shape instead, a count on one carrier could be
            // written as a literal of another — which is how a date-time's second count reached a
            // row as an `Int`, and the decoder refused it with the report saying only that every
            // value tried had been refused.
            FixtureTemplate standing = Witnesses.wrapped(axis.type(),
                    FixtureTemplate.on(carrier, at, symbols.scope()::reach), symbols);
            return standing == null
                    ? Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Edge(List.of(standing), null, at, null);
        }
        int size = CountDomain.asCount(at);
        if (size < 0) {
            return Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Type holder = TypeOps.base(axis.type(), symbols);
        Witnesses.Sized built = Witnesses.ofSize(holder, size, symbols, policy, Set.of());
        if (built.values().isEmpty()) {
            return Edge.none(Witnesses.reasonForSize(holder, size, policy, symbols));
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : built.values()) {
            out.add(Witnesses.wrapped(axis.type(), each, symbols));
        }
        return new Edge(out, null, null, built.heldBack());
    }

    private Generator() {}
}
