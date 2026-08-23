package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.inputs.NumericTerm;
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
 * Rows that would fill the combinations nothing has written yet.
 *
 * <p>What comes out is inputs and nothing else. The expected answer is left for a person, because the
 * compiler does not know it: the whole point of a model with no {@code let} is that the answer lives in
 * a legacy system or in someone's head, and a generator that guessed would turn a question into an
 * assertion nobody made.
 *
 * <p>What it reports is not only the rows. A combination it could produce nothing for is said out
 * loud, with which of {@link UnresolvedCombination.Reason} it was — the list is that enum's to keep,
 * and naming it here would be a second copy going stale. A generator that returned only the rows it
 * managed would read as though the rest were covered, and one that gave the same answer to every kind
 * would send an author looking for a value that does not exist while a row they could write in a line
 * went unwritten.
 */
public final class Generator {

    /** How many rows one call will write. Past this the output stops being something a person reads
     * and pastes, and a model that wants more than this has axes it should be measured at fewer of. */
    static final int MAX_ROWS = 200;

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
     * @param purpose what the row was composed for
     * @param inputs  one value per parameter, in the order the behavior takes them
     */
    public record GeneratedRow(Purpose purpose, List<FixtureTemplate> inputs) {

        public GeneratedRow {
            inputs = List.copyOf(inputs);
        }

        /** What the row is about, in the form a row's description is written in. */
        public String description() {
            return String.join(" x ", purpose.labels());
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

        /** A combination the body settles together, which is as many positions as it reads. */
        record ForACombination(List<String> labels) implements Purpose {

            public ForACombination {
                labels = List.copyOf(labels);
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
     * <p>Where its values sit is what says which classes and which pairs it fills; what its run did
     * is what says which combinations of the body's decisions it fills. The second is not derivable
     * from the first, which is the whole of what this issue is about — a row whose values sit in a
     * combination's classes and whose run went elsewhere fills nothing, and looks from the values
     * alone exactly like one that fills it.
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
            /** The module's classes were not there to build a candidate against. */
            NOTHING_TO_BUILD_AGAINST,
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
                    case THE_RULES_LEAVE_NOTHING_THERE -> true;
                    // Every one of these is this compiler falling short, and none of them is the
                    // model saying anything: another value of the same classes may well build.
                    case NOTHING_COMPOSES_ONE, ALL_CANDIDATES_REJECTED, SEARCH_LIMIT,
                         NOTHING_TO_BUILD_AGAINST, LINKAGE_FAILED, NO_CERTIFIED_WITNESS,
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
         * <p>Null is an answer and not a failure: an arm no combination of the body's own decisions
         * reaches is an arm nothing here composes an input for, which is a different piece of news
         * from one a search tried and could not reach.
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

        /** No row came of the combination that would have taken it, and why. */
        record Unresolved(int probe, UnresolvedCombination why) implements ArmAttempt {}
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
     * <p><b>All the positions at once.</b> A behavior of several parameters written against one
     * value apiece, chosen for each on its own, is a row whose positions the model never says
     * anything about together — while a row the author already wrote names a set of values that go
     * together. So an origin is the whole tuple, and the search walks the tuples.
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

    // --- filling the pairs ----------------------------------------------------------------------

    /**
     * Rows for the two-class combinations the existing rows do not sit in.
     *
     * <p>Greedy and deterministic, in the shape IPO has: take the first combination nothing covers, fix
     * those two positions, and choose every other position for how many further uncovered combinations
     * it brings in. Ties go to the lower index, the axes are ordered before anything starts, and nothing
     * consults a clock or a hash order — the same model and the same rows produce the same rows twice.
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check) {
        return fill(subject, existing, check, List.of());
    }

    /**
     * The same, offering a row for each combination of the decisions that settle one value together
     * before it fills what is left of the pairs.
     *
     * <p>Two questions and one set of rows. A cell is what the body says has to be varied together;
     * a pair is what the types divide, which is what can still be asked of a behavior with no body
     * to read. The cells go first because they fix the most and leave the least to choose, and what
     * they leave free is what the pairs are spent on — so the rows a cell needs are rows the pair
     * space was going to want anyway, rather than rows added beside them.
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups) {
        return fill(subject, existing, check, groups, Trial.NOTHING_RUNS);
    }

    /**
     * The same, running each row composed for a combination to see whether it got there.
     *
     * <p>Which is the only thing that can say so. A row is composed by narrowing each position to
     * the classes the combination leaves it, and every step of that narrowing is a reading of the
     * body — so a row that misses is what a reading being wrong looks like, and a row that misses
     * looks like one that arrives until something watches it.
     *
     * <p>A row that missed is not offered and the combination stays untried. It is not evidence
     * that the combination is unreachable: what was shown is that these candidates were not
     * witnesses (ADR-0091).
     */
    public static GenerationResult fill(Subject subject, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups,
                                        Trial trial) {
        return fill(subject, existing, check, groups, trial, List.of());
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
                                        Trial trial, List<Baseline> baselines) {
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
        // Which class of which position no row the author wrote is in. Settled here, from what is
        // written, and not touched again: a row this run offers is a question and not evidence, and
        // letting one take a class out of the list would leave that class with nothing named for it
        // while the row that displaced it was named for something else.
        List<int[]> owed = owedClasses(axes, existing);

        List<GeneratedRow> rows = new ArrayList<>();
        List<ClassAttempt> attempts = new ArrayList<>();
        List<ArmAttempt> arms = new ArrayList<>();
        List<UnresolvedCombination> unresolved = new ArrayList<>();
        List<GenerationReason> reasons = new ArrayList<>(undecided);
        // What the author wrote, and only that. Settled here for the same reason the classes
        // above are: a row this run offers is a question, and a combination it happens to reach is
        // not evidence that the combination is covered. Added to as candidates arrived, the answer
        // for one combination depended on which of the others had been reached first — so a
        // combination went unoffered because an earlier candidate had been seen in it, and the
        // author was handed a row named for something else and told nothing about this one.
        List<Placement> written = new ArrayList<>();
        for (ObservedRow row : existing) {
            written.add(new Placement(whereIn(row.at(), axes), row.watched()));
        }
        // Built here and not handed in: a cell is one class per position of the axes this
        // generation kept, and the caller's list is neither ordered the same nor filtered the same.
        // No more of any one group than could be offered, since the rest would be built to be
        // thrown away.
        List<InteractionCells.Group> byGroup = InteractionCells.of(groups, axes);
        int[] taken = new int[byGroup.size()];
        // One from each group in turn, while there is budget for a row. A group met first would
        // otherwise spend the whole budget and leave the rest of them nothing; and taken this way
        // there is no count of how many of a group to prepare, so a combination a written row
        // already sits in costs no row and does not stand in for one that would have.
        boolean anyLeft = true;
        boolean unconfirmed = false;
        int withheld = 0;
        while (anyLeft && rows.size() < MAX_ROWS) {
            anyLeft = false;
            for (int g = 0; g < byGroup.size() && rows.size() < MAX_ROWS; g++) {
                InteractionCells.Group group = byGroup.get(g);
                if (taken[g] >= group.size()) {
                    continue;
                }
                CellSelection selection = group.at(taken[g]++);
                anyLeft = true;
                if (selection == null) {
                    // The factors this choice takes leave a position nothing, so it is not a
                    // combination the body has a path to and there is nothing to ask for.
                    continue;
                }
                CombinationStanding standing = standingOf(written, selection);
                if (standing instanceof CombinationStanding.Filled) {
                    continue;   // a row was seen filling it, so nothing is owed
                }
                if (standing instanceof CombinationStanding.MayBeWritten) {
                    // Not filled and not offered: a row in the file sits where one filling this
                    // would, and nothing could say whether it does. Counted so that it is said —
                    // an author told nothing here would read it as a combination covered.
                    withheld++;
                    continue;
                }
                switch (witnessFor(subject, axes, selection, check, trial)) {
                    case Witness.None none -> {
                        UnresolvedCombination why = new UnresolvedCombination(
                                none.classes(), none.reason(), none.detail(), none.said());
                        unresolved.add(why);
                        claimed(selection).forEach(
                                probe -> arms.add(new ArmAttempt.Unresolved(probe, why)));
                    }
                    case Witness.Certified found -> {
                        rows.add(found.row());
                        claimed(selection).forEach(
                                probe -> arms.add(new ArmAttempt.Built(probe, found.row())));
                    }
                    case Witness.Unconfirmed offer -> {
                        rows.add(offer.row());
                        claimed(selection).forEach(
                                probe -> arms.add(new ArmAttempt.Built(probe, offer.row())));
                        // Nothing watched it, so what it is offered for is what the reading says
                        // and not what anything saw. Said once for the behavior: it is one fact
                        // about this generation.
                        unconfirmed = true;
                    }
                }
            }
        }
        int cellsLeft = 0;
        for (int g = 0; g < byGroup.size(); g++) {
            cellsLeft += byGroup.get(g).left(taken[g]);
        }
        int classesLeft = 0;
        for (int i = 0; i < owed.size(); i++) {
            int[] at = owed.get(i);
            if (rows.size() >= MAX_ROWS) {
                classesLeft = owed.size() - i;
                for (int left = i; left < owed.size(); left++) {
                    unresolved.add(new UnresolvedCombination(
                            List.of(label(axes.get(owed.get(left)[0]), owed.get(left)[1])),
                            UnresolvedCombination.Reason.SEARCH_LIMIT));
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
        // Said once, at the end, and about both searches. One that ran out on the cells stopped
        // whether or not the classes had anything left to do, and two limits reported apart would
        // be read as two searches.
        if (cellsLeft + classesLeft > 0) {
            reasons.add(new GenerationReason.SearchLimit(axes.get(0).id().behavior(),
                    cellsLeft + classesLeft));
        }
        if (unconfirmed) {
            reasons.add(new GenerationReason.RowsNotConfirmed(axes.get(0).id().behavior()));
        }
        if (withheld > 0) {
            reasons.add(new GenerationReason.CombinationsWithheld(axes.get(0).id().behavior(),
                    withheld));
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
        List<Integer> out = new ArrayList<>();
        for (souther.compiler.coverage.ControlClaim claim : selection.claims()) {
            if (claim.at() instanceof souther.compiler.coverage.ControlPointId.ArmOccurrence arm
                    && arm.probe().isPresent()) {
                out.add(arm.probe().getAsInt());
            }
        }
        return out;
    }

    /**
     * How many positions beside the one a row is about it may move to be buildable.
     *
     * <p>A bound on what a row may say, before it is one on the search. A row that moved eight
     * positions to reach one class is a row whose reader cannot tell which of the eight the answer
     * turned on, which is what a row about one class exists not to be (issue #967). Past this the
     * class is reported as one no row was composed for, which leaves it writable by hand.
     */
    private static final int MOST_SUPPORTING = 2;

    /**
     * How many assignments the walk over the origins tries before it gives up on a class.
     *
     * <p>Its own budget and never {@link #MAX_TUPLES}. That one bounds the walk over the values one
     * parameter's fields may take once the classes are settled; this bounds the walk over which
     * classes to settle them at, and the two multiply — shared, one of them would be spent by the
     * other and which of them ran out would depend on the model.
     */
    private static final int MOST_REPAIRS = 64;

    /**
     * A row for one class: composed against what the model already says where it can be, and moving
     * as little else as it takes.
     *
     * <p>The origins are walked before the repairs, and both outward from what a reader would
     * recognise. A value the model states is what a row is written against where there is one, and
     * the classes are what is left when there is not — so the order is {@code baseline} then
     * {@code composed}, and within each, the target alone before the target and one supporting
     * position, before the target and two.
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
        // The values the model states first, in the order they were gathered, and the classes after
        // — each walked outward from the target alone. A row composed from the classes moves every
        // position away from what the model says, so it is further from what a reader recognises
        // than a baseline row with a supporting move; and one baseline is nearer than another only
        // in how far the row has to move from it, which is what the distance below measures. So the
        // origins are the outer loop and the distance the inner.
        //
        // Every baseline the module states rather than the one this compiler picked. Narrowed to
        // the only value of a type, a module that states a second one lost the spread from every
        // row of every behavior taking it — a change somewhere else in the file, answering a
        // question nobody asked it.
        List<Baseline> origins = new ArrayList<>(baselines);
        origins.add(new Baseline(Map.of()));   // the classes, which name nothing
        for (Baseline baseline : origins) {
            // Where the origin's own values already stand, which is what a move is measured from.
            // Measured from the composition either way, a class the baseline is already in looked
            // like no move at all and was never tried as one — so a row the baseline needed one
            // supporting field for fell through to being composed from the classes.
            int[] from = baseline.isEmpty() ? composes(axes) : stands(subject, axes, baseline, check);
            if (from == null) {
                continue;
            }
            int tried = 0;
            for (int moved = 0; moved <= MOST_SUPPORTING && tried < MOST_REPAIRS; moved++) {
                for (int[] supporting : supportingSets(axes, at, moved)) {
                    for (int[] where : assignmentsOver(axes, from, at, cls, supporting)) {
                        if (++tried > MOST_REPAIRS) {
                            break;
                        }
                        Map<String, FixtureTemplate> given = baseline.isEmpty() ? Map.of()
                                : against(subject, axes, from, at, where, baseline);
                        if (!baseline.isEmpty() && given.isEmpty()) {
                            continue;   // nothing here can be written against the model's value
                        }
                        Attempt made = build(subject, axes, where, check, given);
                        if (made.row() == null) {
                            last = made;
                            continue;
                        }
                        if (!inTheClass(subject, axes, at, classId, made.row().inputs(), check)) {
                            last = new Attempt(null,
                                    UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, label,
                                    Optional.empty());
                            continue;
                        }
                        return new ClassAttempt.Built(axis.id(), classId, new GeneratedRow(
                                new Purpose.ForAClass(axis.id(), classId, label),
                                made.row().inputs()));
                    }
                }
            }
        }
        UnresolvedCombination why = last == null || last.row() != null
                ? new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.SEARCH_LIMIT)
                : new UnresolvedCombination(List.of(label), last.reason(), last.detail(),
                        last.said());
        return new ClassAttempt.Unresolved(axis.id(), classId, why);
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
        int[] where = from.clone();
        where[at] = cls;
        walkSupporting(axes, where, supporting, 0, out);
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
        int[] where = new int[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            where[i] = standingAt(axes.get(i), _ -> true);
        }
        return where;
    }

    private static void walkSupporting(List<Axis> axes, int[] where, int[] supporting, int filled,
                                       List<int[]> out) {
        if (filled == supporting.length) {
            out.add(where.clone());
            return;
        }
        int axis = supporting[filled];
        int stood = where[axis];
        for (int c = 0; c < axes.get(axis).classes().size(); c++) {
            // Where it already stands is not a move, and the assignment that makes it is the one
            // the smaller set already produced.
            if (c == stood) {
                continue;
            }
            where[axis] = c;
            walkSupporting(axes, where, supporting, filled + 1, out);
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
     * Which class of which position no row the author wrote is in, as {@code [axis, class]}.
     *
     * <p>Off the written rows and nothing else. What this run composes is what the list is answered
     * with, so a row it offers must not shorten it — a class taken out by a row composed for
     * something else is a class an author is told nothing about, and the row that took it out is
     * named for its own reason and says nothing about this one.
     *
     * <p>A row of the author's can sit in more than one class of a position at once — a list with
     * one element under a line and one over it — and each of them is covered. Read as one class,
     * the rest would be asked for again, which is work the author has already done.
     */
    private static List<int[]> owedClasses(List<Axis> axes, List<ObservedRow> existing) {
        List<int[]> owed = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            Set<String> covered = new LinkedHashSet<>();
            for (ObservedRow row : existing) {
                Classification here = row.at().get(axes.get(i).id());
                if (here != null) {
                    covered.addAll(here.classIds());
                }
            }
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (!covered.contains(axes.get(i).classes().get(c).id())) {
                    owed.add(new int[] {i, c});
                }
            }
        }
        return owed;
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
        int[] where = new int[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            where[i] = i == at ? cls : standingAt(axes.get(i), _ -> true);
        }
        return where;
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
    public static BoundaryAttempt probeFixing(Subject subject, String label, Carrier carrier,
                                              Map<NumericTerm, Place> fixing, CandidateCheck check) {
        Map<String, List<FixtureTemplate>> decided = new LinkedHashMap<>();
        // What the rest of the row has to sit beside. A field of a record is not chosen from its own
        // type once another field of that record is fixed: the rule relating them says what is left,
        // and taking the bottom of the type's range instead is how a boundary that can be written
        // came back as one every value tried was refused at.
        Map<String, Place> settled = new LinkedHashMap<>();
        Map<String, UnresolvedCombination.Reason> heldBack = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : fixing.entrySet()) {
            Edge edge = edgeAt(subject, carrier, each.getKey(), each.getValue(), fixing.size() > 1);
            if (edge.values().isEmpty()) {
                return new BoundaryAttempt.Unresolved(
                        new UnresolvedCombination(List.of(label), edge.reason()));
            }
            String at = each.getKey().path().toString();
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
            Map<String, List<FixtureTemplate>> here = new LinkedHashMap<>();
            for (NumericTerm term : fixing.keySet()) {
                if (term.path().head().equals(head)) {
                    here.put(term.path().toString(), decided.get(term.path().toString()));
                }
            }
            Outcome tried = valueAt(subject, p, here, settled, Map.of(), check);
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
     * A row this generation counts the combinations against: where it sits, and what came of
     * running it.
     *
     * <p>A row the author wrote, and nothing else. This used to hold rows this search composed as
     * well, and the answer for one combination then depended on which of the others had been
     * reached first — a combination went unoffered because a candidate composed for something else
     * had been seen in it, which is a reading read back as evidence for itself.
     *
     * <p>What a candidate reaches is worth knowing and is not this. It is what the row would show
     * once somebody answers it and it is in the file; until then the row is a question, and a
     * question does not cover anything.
     */
    private record Placement(int[] where, Watched watched) {}

    /**
     * Where one combination stands before anything is composed for it.
     *
     * <p>Named at length because {@link Standing} beside it is where a value stands against a line,
     * and a nested type sharing that word would answer to it inside this file and to the other one
     * everywhere else.
     *
     * <p>Three answers because two questions are being asked of the rows, and folding them into one
     * is what this issue is about. Whether a combination is filled is a question about evidence, and
     * only a run answers it. Whether a row for it is worth putting in front of an author is a
     * question about what is already in their file, and a row they have written answers that
     * whatever anything can establish about it — re-offering a combination over such a row hands
     * back work already done.
     *
     * <p>Kept apart because the second is not the first. A combination withheld is not one anything
     * showed to be filled, so it is not counted as such and it is not passed over in silence: it is
     * said, and what it says is that a row in the file may fill it and nothing here could tell.
     */
    private sealed interface CombinationStanding {

        /** A row was seen filling it. The witness is what says so and the only thing that can. */
        record Filled(CellSelection.CertifiedWitness by) implements CombinationStanding {}

        /** A row already in the author's file sits where one filling this would, and nothing could
         *  say whether it does. Not evidence, and not silence either. */
        record MayBeWritten() implements CombinationStanding {}

        /** Nothing here says anything about it. */
        record Owed() implements CombinationStanding {}
    }

    /**
     * Where {@code selection} stands against the rows counted so far.
     *
     * <p>Evidence first and on its own terms: a row of either kind, seen doing what the combination
     * names and sitting where it leaves room, fills it — one question put to one thing that can
     * answer it. Only where nothing was established does whose row it is come into it, and then it
     * decides what to offer rather than what is true.
     */
    private static CombinationStanding standingOf(List<Placement> written, CellSelection selection) {
        boolean maybe = false;
        for (Placement row : written) {
            if (row.watched() instanceof Watched.Ran ran) {
                Optional<CellSelection.CertifiedWitness> found =
                        selection.certifying(row.where(), ran.seen());
                if (found.isPresent()) {
                    return new CombinationStanding.Filled(found.get());
                }
            } else if (selection.cell().holds(row.where())) {
                // A row in the file sits where one filling this would, and nothing could say
                // whether it does. Not evidence, and not silence either: offering a row here risks
                // handing an author work they have already done.
                maybe = true;
            }
        }
        return maybe ? new CombinationStanding.MayBeWritten() : new CombinationStanding.Owed();
    }

    /**
     * Every position at the first class {@code cell} admits it, which is the assignment a row for
     * that cell is first tried at.
     *
     * <p>The positions the cell settles hold what it settles them at; the rest hold the first of
     * what they may, because the row is not about them. A row that also moved the positions beside
     * the combination would be several answers a person has to separate.
     */
    private static int[] firstAdmitted(List<Axis> axes, InteractionCells.Cell cell) {
        int[] where = new int[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            int at = i;
            where[i] = standingAt(axes.get(i), c -> cell.admits(at, c));
        }
        return where;
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
     * this row is. Positions the cell says nothing about stay out — they are what the pass filling
     * the rest of the row spent on the pairs, and this row is not for them.
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
     * fixing every position, which the combination settles for some of them and the pair search
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
                                      CellSelection selection, CandidateCheck check, Trial trial) {
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
            // Named for the combination it was composed for, which is the positions the decisions
            // read. What the pair search filled the rest of the row with is what this row turns out
            // to settle beside that, and a name carrying it would move when nothing about the row
            // had.
            GeneratedRow named = new GeneratedRow(
                    new Purpose.ForACombination(labels(axes, cell, at)), last.row().inputs());
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
        Map<String, List<FixtureTemplate>> decided = new LinkedHashMap<>();
        Map<String, RepresentativeSource.Evaluation.Compose> recipes = new LinkedHashMap<>();
        for (int i = 0; i < axes.size(); i++) {
            String path = axes.get(i).path().toString();
            String at = label(axes.get(i), where[i]);
            switch (axes.get(i).classes().get(where[i]).representatives().evaluate()) {
                case RepresentativeSource.Evaluation.Values values ->
                        decided.put(path, values.written());
                // Not a value but how one is arrived at: the walk below builds one at this position,
                // field by field, the way it builds every other record, and this writes what was
                // built under the names the position wears.
                case RepresentativeSource.Evaluation.Compose compose -> recipes.put(path, compose);
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
            Outcome tried = valueFor(subject, p, axes, decided, recipes, check);
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
                                    Map<String, List<FixtureTemplate>> decided,
                                    Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                    CandidateCheck check) {
        TermPath at = TermPath.of(subject.parameters().get(p));
        Map<String, List<FixtureTemplate>> here = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.path().head().equals(at.head())
                    && decided.containsKey(axis.path().toString())) {
                here.put(axis.path().toString(), decided.get(axis.path().toString()));
            }
        }
        return valueAt(subject, p, here, settledIn(here), recipes, check);
    }

    /**
     * The positions a caller fixed at one number.
     *
     * <p>Only where the position has a single value to take. A class offers one value to stand for
     * it, and that is the one the row will carry, so the rest of the record can be chosen beside it;
     * a position still holding several is not settled at all and nothing is claimed of it.
     */
    private static Map<String, Place> settledIn(Map<String, List<FixtureTemplate>> decided) {
        Map<String, Place> out = new LinkedHashMap<>();
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
                                   Map<String, List<FixtureTemplate>> decided,
                                   Map<String, Place> settled,
                                   Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                   CandidateCheck check) {
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
                decided.keySet(), recipes, (at, building) -> leastHeld(under, at, building,
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
                                                         Map<String, Place> settled) {
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
                                       Map<String, List<FixtureTemplate>> decided,
                                       Map<String, Place> settled,
                                       CandidateCheck check) {
        List<ConstructionPlan.Slot> found = plan.slots();
        // What the caller fixed goes first, so that everything chosen after it is chosen beside it.
        // A class stands for one value and a boundary is one value, and neither is worth deciding
        // after the positions whose range it settles.
        List<ConstructionPlan.Slot> positions = new ArrayList<>(
                found.stream().filter(each -> decided.containsKey(each.at().toString())).toList());
        positions.addAll(
                found.stream().filter(each -> !decided.containsKey(each.at().toString())).toList());
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
                                           Map<String, FixtureTemplate> chosen,
                                           Map<String, Place> settled,
                                           Map<String, List<FixtureTemplate>> decided,
                                           CandidateCheck check, Budget budget) {
        if (index == positions.size()) {
            if (!budget.spend()) {
                return null;
            }
            FixtureTemplate whole = compose(plan.root(), chosen, subject.symbols(), subject.inputs().policy());
            return whole != null && check.refuse(p, whole).isEmpty() ? whole : null;
        }
        ConstructionPlan.Slot position = positions.get(index);
        String where = position.at().toString();
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
                                                      Map<String, Place> settled,
                                                      Map<String, List<FixtureTemplate>> decided) {
        List<FixtureTemplate> fixed = decided.get(position.at().toString());
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
    private record Choices(ConstructionPlan plan, List<String> at,
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
                                     Map<String, List<FixtureTemplate>> decided,
                                     Map<String, Place> settled) {
        Symbols symbols = subject.symbols();
        ReadingPolicy policy = subject.inputs().policy();
        TermPath at = TermPath.of(subject.parameters().get(p));
        List<String> paths = new ArrayList<>(decided.keySet());
        List<List<FixtureTemplate>> values = new ArrayList<>(decided.values());
        // A position the caller fixed holds nothing back: it was given the value it is to take.
        List<List<FixtureTemplate>> reserves = new ArrayList<>(
                java.util.Collections.nCopies(paths.size(), List.<FixtureTemplate>of()));
        FieldDomains left = rulesOf(subject.types().get(p), symbols, policy, under(at, settled));
        for (ConstructionPlan.Slot slot : plan.slots()) {
            if (paths.contains(slot.at().toString())) {
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
            paths.add(slot.at().toString());
            values.add(stands);
            reserves.add(Partitions.inReserve(slot.type(), symbols, policy, here));
        }
        return new Choices(plan, paths, values, reserves, null);
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
    private static Map<String, Count> under(TermPath root, Map<String, Place> settled) {
        if (settled.isEmpty()) {
            return Map.of();
        }
        Map<String, Count> out = new LinkedHashMap<>();
        String prefix = root + ".";
        // The numbers among them. A projection relates positions arithmetically, so a position whose
        // places are not numbers settles nothing there.
        settled.forEach((path, at) -> {
            if (path.startsWith(prefix) && at instanceof Count number) {
                out.put(path.substring(prefix.length()), number);
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
    private static Outcome over(Subject subject, int p, ConstructionPlan plan, List<String> at,
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
            Map<String, FixtureTemplate> chosen = new LinkedHashMap<>();
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
                                           Map<String, FixtureTemplate> chosen, Symbols symbols,
                                           ReadingPolicy policy) {
        return switch (node) {
            case ConstructionPlan.Slot slot -> chosen.get(slot.at().toString());
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
                                        Map<String, FixtureTemplate> chosen, Symbols symbols,
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
                                            Map<String, FixtureTemplate> chosen, Symbols symbols,
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
        FixtureTemplate record = RepresentativeSource.under(worn,
                FixtureTemplate.record(written, fields));
        return built.recipe() == null ? record : built.recipe().written(record);
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
