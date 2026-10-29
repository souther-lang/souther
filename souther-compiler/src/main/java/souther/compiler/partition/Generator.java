package souther.compiler.partition;

import souther.compiler.carrier.Lookup;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.Rewriting;
import souther.compiler.coverage.RunRewrite;
import souther.compiler.coverage.WalkRewrites;
import souther.compiler.flow.Ways;
import souther.compiler.meaning.PieceDemand;
import souther.compiler.meaning.Quantity;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.ast.Hir;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.PathAccess;
import souther.compiler.reading.TheRestOfTheBlock;
import souther.compiler.reading.WayIn;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.WorkFigure;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.SequencedMap;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.function.Supplier;

/**
 * Rows for the classes and the arms a caller says are owed one.
 *
 * <p>The plan comes in and this composes for nothing of its own. Which class of which position no
 * row sits in, and which arm no row goes through, is what a measure reads off the rows and reports;
 * a search working either out again is a second reading of one fact, free to offer a row at a class
 * the report calls reached. A combination of the body's decisions is where a witness for an arm is
 * looked for and is not itself a thing anyone is owed a row at.
 *
 * <p>What comes out is everything it takes to run the row and nothing that says what should come of
 * it. The inputs, and what each dependency the behavior requires is stood in with; the expected
 * answer is left for a person, because the compiler does not know it — the whole point of a model
 * with no {@code let} is that the answer lives in a legacy system or in someone's head, and a
 * generator that guessed would turn a question into an assertion nobody made.
 *
 * <p>The stand-ins are on a candidate from the moment it is composed. What a row does is what it
 * does in some environment, so a candidate run in one environment and published in another is a row
 * certified for a line nobody is offered — and completing a row downstream is how the two came
 * apart.
 *
 * <p>What it reports is not only the rows. Everything on the plan gets an entry saying what came of
 * it, with which of {@link UnresolvedCombination.Reason} it was — the list is that enum's to keep,
 * and naming it here would be a second copy going stale. A generator that returned only the rows it
 * managed would read as though the rest were covered, and one that gave the same answer to every kind
 * would send an author looking for a value that does not exist while a row they could write in a line
 * went unwritten.
 */
public final class Generator {

    /** How many assignments of values one parameter is tried at in one pass. A parameter with
     *  something held in reserve is walked twice, each pass under this bound. The figure is
     *  {@link CompositionBudget}'s, where every budget of this compiler's is named. */
    private static final int MAX_TUPLES =
            CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES.maximum();

    /**
     * How many things one combination may be asking before the search gives up on it.
     *
     * <p>A combination is a class apiece at the positions it is about, and where it leaves a
     * position more than one class it is asking more than one thing. What this bounds is how many of
     * those a search may try: a group whose reading is wrong misses at every one of them, and
     * without a bound it would work its way through the whole space while every other group waited.
     *
     * <p><b>Readings and not assignments.</b> Counted over whole assignments, most of what the bound
     * was spent on differed only at positions the combination says nothing about — so three tries
     * were three rows asking the same thing, and a combination's second meaning went untried however
     * much of the bound was left ({@link Interpretation}).
     */
    private static final int MOST_INTERPRETATIONS = 3;

    /**
     * How many rows one reading of a combination is run for before the search moves on.
     *
     * <p>Counted in runs, because a run is what this is protecting. Reaching the arm is what a row
     * for a combination has to do and only the behavior can say whether it did, so every candidate
     * that composes costs a run — while a candidate the model refuses costs nothing but the
     * composing, and counting those would let a model whose rules refuse a few compositions spend a
     * reading's whole share without ever asking the behavior anything.
     *
     * <p>Its own bound and not the class walk's. {@link #MOST_REPAIRS} bounds a walk whose every
     * candidate is built and no more; this bounds one whose every candidate is run. The two are the
     * same shape of search and are not the same cost, and one number over both would be set by
     * whichever of them it hurt more.
     */
    private static final int MOST_RUNS_PER_INTERPRETATION = 3;

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
     * <p><b>And what it stands the behavior's dependencies in with.</b> A row is offered to be
     * completed and run, and a row with nothing standing in for a dependency its target requires is
     * one nothing can run — which is true of every dependency the target has, not only of the ones
     * the body decides on. Which dependency each answer is about is {@link StoodInAnswer}'s, and
     * the {@code with} a block writes is a projection of these rather than a second account of
     * them.
     *
     * @param purposes what the row was composed for, in the order the things were taken
     * @param inputs   one value per parameter, in the order the behavior takes them
     * @param answers  what it stands each dependency its target requires in with
     */
    public record GeneratedRow(List<Purpose> purposes, List<FixtureTemplate> inputs,
                               List<StoodInAnswer> answers) {

        public GeneratedRow {
            purposes = List.copyOf(purposes);
            inputs = List.copyOf(inputs);
            answers = List.copyOf(answers);
            if (purposes.isEmpty()) {
                throw new IllegalArgumentException("a row is composed for something");
            }
        }

        /** One row composed for one thing, of a behavior that requires nothing to be stood in. */
        public GeneratedRow(Purpose purpose, List<FixtureTemplate> inputs) {
            this(List.of(purpose), inputs, List.of());
        }

        /** The row as everything it takes to run one. */
        public RowToRun toRun() {
            return new RowToRun(inputs, answers);
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
     * those to its findings by identity ({@link GenerationResult}).
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
         * One combination of two classes: the row a behavior held to the pair space is owed there.
         *
         * <p>The two classes the requirement is of and nothing else. A row that reaches them may
         * have had to move a third position to be a value at all — where two classes require a
         * third thing the baseline does not have — and that position is part of the row and no part
         * of what it is for. Written in, the row would be named for a combination nobody asked
         * about, which is what a row composed for a pair used to do (issue #967).
         *
         * <p>A set, because a combination is a pair rather than an order of them. Which order a
         * search settles them in is {@link Pins}'s and is not something a row is named by.
         */
        record ForAFallbackPairCell(java.util.Set<ClassOfAPosition> classes, List<String> labels)
                implements Purpose {

            public ForAFallbackPairCell {
                classes = java.util.Set.copyOf(classes);
                labels = List.copyOf(labels);
            }

            @Override
            public List<String> labels() {
                return labels;
            }
        }

        /**
         * One combination of the body's decisions: the row a meeting nothing makes is owed.
         *
         * <p>The decisions the meeting settles a value by, which is the requirement's identity
         * everywhere. Where a search found a row for it is a cell of a group, and two cells of two
         * groups can settle the same decisions — so a row named by where it was found would be
         * named for one of the places rather than for the thing that was asked.
         *
         * <p>No label, for the reason an arm has none: what a combination of decisions is called is
         * the report's word, written from the conditions and the places they are read at. A name
         * made here would be a second vocabulary for one thing.
         */
        record ForACombinationOfDecisions(java.util.Set<souther.compiler.reading.Condition> settled)
                implements Purpose {

            public ForACombinationOfDecisions {
                settled = java.util.Set.copyOf(settled);
            }

            @Override
            public List<String> labels() {
                return List.of();
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
        record ForAnArm(ArmProbe probe) implements Purpose {

            @Override
            public List<String> labels() {
                return List.of();
            }
        }

        /**
         * A rewrite of the body no row told from it: the row it answers differently on.
         *
         * <p>No words, for the reason an arm has none: what a rewrite is called is the report's
         * word, and the report writes it from the finding it reports the rewrite in.
         */
        record ForAReplacement(ReplacementOwed replacement) implements Purpose {

            @Override
            public List<String> labels() {
                return List.of();
            }
        }

        /**
         * One rule of the decision a body states: the row a way nothing takes is owed.
         *
         * <p>The rule and not where it was found. What a reader is owed a row for is the way
         * through the body, and a search that stood a value in it stood it somewhere the rule
         * admits — which is one of the values the rule takes and not the rule.
         *
         * <p>No words. What a rule is called is a report's question and is answered by sending a
         * reader to each condition the way turns on; a name made here would be a second vocabulary
         * for one thing, free to drift from the one the finding is written in.
         */
        record ForADecisionRule(DecisionRule rule) implements Purpose {

            public ForADecisionRule {
                if (rule == null) {
                    throw new IllegalArgumentException("a row for a rule is for some rule");
                }
            }

            @Override
            public List<String> labels() {
                return List.of();
            }
        }

        /**
         * One case a statement of the decision draws inside itself: the row a step of a search, or
         * a way round the order of a repeated key, no row was seen in is owed.
         *
         * <p>The case and not the rule the row was placed at. A rule every row takes may still
         * have a case none of them is in, and what the row is for is the case. No words, for the
         * reason a rule has none: what a case is called is the report's question.
         */
        record ForACaseOfAStatement(CaseOfAStatement which) implements Purpose {

            public ForACaseOfAStatement {
                if (which == null) {
                    throw new IllegalArgumentException("a row for a case is for some case");
                }
            }

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
    public record ObservedRow(Lookup<AxisId, Classification> at, Watched watched) {

        public ObservedRow {
            Objects.requireNonNull(at, "where the row's values sit");
            watched = watched == null ? new Watched.NoAccount() : watched;
        }

        /** A row nothing here can say anything about the run of, for a caller with none to read. */
        public static ObservedRow unseen(Lookup<AxisId, Classification> at) {
            return new ObservedRow(at, new Watched.NoAccount());
        }
    }

    /**
     * A combination no row could be written for, and why.
     *
     * <p>{@code ALL_CANDIDATES_REJECTED} is not a proof that the combination is impossible. It says
     * every value this tried was refused, which is a fact about the values tried; another value of the
     * same classes may well build. So nothing anywhere records the combination as impossible: what
     * a pair space holds is what the rows reach and what is unknown, and this compiler assesses
     * reachability nowhere.
     *
     * @param classes what the row was composed for: the classes of a combination, or the one label
     *             of a point
     * @param detail the position the combination came to nothing at, where several combinations
     *             came to nothing at the same one, or null. A name and never a sentence: it is
     *             printed where the subject goes ({@link #subject()}), and a sentence there reads as
     *             the thing no row was found for. What a walk found out is {@code said}
     * @param said what the class said about itself where it said anything, in its own words. Kept
     *             beside the reason rather than folded into it: the reason is the category a reader
     *             acts on, and this is the sentence that says which case of it this was. Folded into
     *             {@code detail} it would be printed where the subject goes.
     * @param alsoShort what else was true of the search, under the position it is about: the rules
     *             about a position's strings that gave the offer no value. <b>Beside the reason and
     *             never instead of it</b>, which is what tells it from {@code said}. That one is
     *             this category in this case and a reader is shown it in place of the category's
     *             own words; these are a second thing that happened, and a reader shown them
     *             instead would be told the rule and never told that a figure stopped the search.
     *             So a reader of one of these writes both, and neither is dropped for the other
     */
    public record UnresolvedCombination(List<String> classes, Reason reason, String detail,
                                        Optional<String> said,
                                        SequencedMap<TermPath, StringOfferShortfall> alsoShort) {

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
            /**
             * Nothing was composed for what a dependency the target requires answers.
             *
             * <p>A row of a behavior that requires one cannot be run until something answers for
             * it, whether or not the body decides on what it says. So this stops a row going out
             * rather than leaving one that reports a stand-in missing the moment it is pasted.
             *
             * <p>A fact about this compiler and not about the model: what a dependency answers may
             * be a shape nothing here writes a value of, and an author writes one by hand.
             */
            NOTHING_STANDS_IN_FOR_A_DEPENDENCY,
            /**
             * The row needs a dependency to answer by what it was applied to, and nothing here
             * writes a table.
             *
             * <p>A row answers a dependency for itself with a {@code with}, which is row-local and
             * answers every call that row makes. A way that needs two answers at two calls needs a
             * table, and a table is written once for a module — it is part of the environment
             * several rows share rather than part of a row, and what a module already states about
             * that environment is not read here.
             *
             * <p>A fact about this compiler and not about the model. The way may well be reachable,
             * and an author who writes the table by hand reaches it.
             */
            A_TABLE_IS_WHAT_THIS_NEEDS,
            /**
             * The search left something untried.
             *
             * <p>Not that it stopped. A figure with no room for the candidate in front of it leaves
             * something untried, and so does a walk that ran to the end of a population this
             * compiler writes some of, and a walk that met a number it could not hold — the last two
             * stopped nothing and there is no figure in them, and a word saying a search halted
             * would send a reader looking for one. What was left, and whether raising anything or a
             * host with more room reaches it, is what travels beside this
             * ({@link CompositionBudget}, {@link CompositionRepertoire},
             * {@link CompositionCapacity}).
             *
             * <p>What it licenses is one thing either way, which is why it is one word: nothing here
             * was shown about the model, so a reader may not act on it as they may act on
             * {@link #NO_VALUE_CAN_STAND_THERE}.
             */
            THE_SEARCH_LEFT_SOMETHING_UNTRIED,
            /**
             * No value can stand here.
             *
             * <p>Apart from every other word here, and the difference is the whole point of having
             * it. The rest say what this compiler did not manage; this one says what the model
             * settles, and a reader may act on this and on none of the others (ADR-0091).
             *
             * <p><b>The word is the theorem and not the way it was come by.</b> Two routes reach it
             * and ADR-0091 admits both: a walk of the whole of what the rules leave that reached
             * nothing, and the model shown to leave nothing before anything was walked. And what
             * shows it may be a rule or no rule at all — a {@code Set<Bool>} asked for three
             * elements is refused by its element having two values. What a reader does about it is
             * the same whichever, and a word that also said which would be false on the others.
             */
            NO_VALUE_CAN_STAND_THERE,
            /**
             * One position of the row would have to be two things at once.
             *
             * <p>What the model settles, as {@link #NO_VALUE_CAN_STAND_THERE} is, and not
             * something this compiler fell short of. A class under one case of a sum and a class
             * under another are classes of positions that are not in one value: no row is a
             * {@code FeedQuery} and has a {@code GlobalQuery}'s {@code tag}. Reported as a value
             * nothing composed, an author would go looking for a row that cannot exist.
             */
            ONE_POSITION_CANNOT_BE_BOTH,
            /**
             * A condition on the way comes out the other way for every row.
             *
             * <p>What the model settles, as the one above is: a predicate that always holds, or two
             * sides whose difference is the same on every row, leaves a way past it that no input
             * takes. Reported as a value nothing composed, an author would go looking for a row
             * that cannot exist.
             */
            A_CONDITION_NEVER_COMES_OUT_THAT_WAY,
            /** The module's classes were not there to build a candidate against. */
            NOTHING_TO_BUILD_AGAINST,
            /**
             * A way into the arm was read, and one of the decisions on it places at no class.
             *
             * <p>So there is nothing to steer a row by along that way: a row put at the classes the
             * rest of it leaves may go the other way round that fork, and would be offered for an
             * arm it never takes. A fact about what the partition divides this body's positions
             * into, and not about whether a run reaches the arm.
             */
            THE_WAY_IN_PLACES_AT_NO_CLASS,
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
             * <p>Told apart from {@link #THE_SEARCH_LEFT_SOMETHING_UNTRIED} because they are different pieces of news
             * and only one of them is about this search: that one says the budget ran out with the
             * class still owed, this says the class was never a thing to look for.
             */
            THE_POSITION_WAS_WITHHELD,
            /**
             * The group of decisions this belongs to was wider than the walk offers, so no
             * combination of it was looked in.
             *
             * <p>Told apart from {@link #THE_SEARCH_LEFT_SOMETHING_UNTRIED} for the reason {@link
             * #THE_POSITION_WAS_WITHHELD} is: that one says the budget ran out while walking, and
             * this says the walk never started. Raising the row budget changes the first and not
             * the second.
             *
             * <p>Named at all because the alternative is silence about the one thing raising a
             * budget does not fix. What the arm itself came to is its own entry's to say — a row
             * through it comes from the way into it whether or not anything above it was walked —
             * and this is the second half of that entry where there is one.
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
            /**
             * A value was found for it and the block a person is handed has no room left.
             *
             * <p>The one word here that says nothing was tried and nothing is missing. What stood
             * in this was already found — the search that settled the obligation ran a value and
             * saw it take the way — and what stopped is the number of rows one block offers.
             *
             * <p>Its own word beside {@link #THE_SEARCH_LEFT_SOMETHING_UNTRIED}, which is the
             * nearest thing and is not this: that one says a search stopped before it had an
             * answer, and a reader acts on it by raising what the search may walk. This says the
             * answer is in hand and the list was cut, which is a different limit and a different
             * thing to raise.
             */
            THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE,
            /** The generated classes would not link, so the decoders could not be reached. Told
             * apart from the one above it because they were there, which is not what that says. */
            LINKAGE_FAILED,
            /**
             * No row composed for it was seen reaching it.
             *
             * <p>Said that way round because it is what the search establishes. Some of the
             * assignments tried may have composed nothing at all, so a word about what every row
             * did would be a word about rows there were none of; what holds of all of them is that
             * none was a witness.
             *
             * <p><b>Of a combination and of a point of a line alike.</b> Both are things a row is
             * composed for and both are answered by watching what the row turned out to do — a
             * combination by the arms the run took, a point by the walk that reads a row at one. A
             * second word for the second of them would be the same sentence said twice.
             *
             * <p>Not a proof that either is unreachable, and nothing reads it as one. It is a fact
             * about the candidates — and, where the reading that named the thing is wrong, about
             * that reading. Either way it stays untried rather than being counted as offered
             * (ADR-0091).
             */
            NO_CERTIFIED_WITNESS,
            /**
             * The walk ran to the end of what it had and put no candidate forward at all.
             *
             * <p>Nothing was built, so nothing was refused, and nothing stopped it: what it had to
             * offer was nothing. A fact about what this compiler can compose here, like
             * {@link #NOTHING_COMPOSES_ONE} and unlike the two words about the model — another
             * reading of the same position may well offer one.
             *
             * <p>It used to be spelled as no reason having been recorded, which was a confession
             * this compiler had failed to say why. The confession was real and belonged somewhere
             * else: a class or an arm the run never answered for. That absence cannot be built now,
             * and what is left here is a walk that ran and came back empty — which is a thing that
             * happened rather than a thing nobody wrote down.
             */
            NO_CANDIDATE_WAS_OFFERED,
            /**
             * Candidates were put forward and every one of them was refused, and they were not all
             * the candidates there were to put forward.
             *
             * <p>Apart from {@link #ALL_CANDIDATES_REJECTED}, and the difference is the whole of
             * what this word is for. That one says the values the rules leave were tried and every
             * one was refused, which is a reader's licence to go looking for the rule that refuses
             * them. Here a rule about the position composed nothing — this compiler could not read
             * it, or could not afford the machine for it — so the values tried came from the rules
             * beside it, and the refusal that followed says nothing about the rule missing from
             * them.
             *
             * <p>Apart from {@link #THE_SEARCH_LEFT_SOMETHING_UNTRIED} as well, and this one is the
             * easier to mistake. That one is a search that stopped holding candidates it never
             * tried, and raising the figure tries them. This search ran to the end of everything it
             * was given; what was short was the giving, and no figure over the search reaches it.
             *
             * <p>Which rule it was, and what stopped it, is said beside this rather than in it. An
             * author rewriting a rule and an author allowing more are doing different work, and
             * what they act on together is this: what was offered was not everything, so nothing
             * about the model follows from its having been refused.
             */
            NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
            /**
             * No reading of the line was searched, so nothing was looked for at the point.
             *
             * <p>A line an {@code invariant} drew is owed once over every behavior carrying the
             * type, and a row at it is composed by walking one of those behaviors' inputs. Where
             * the search of every one this request was about had no answer to give, the walk came
             * back having looked at nothing — which is a fact about this run and says nothing
             * whatever about the line.
             *
             * <p>Apart from {@link #NO_CANDIDATE_WAS_OFFERED}, which is a walk that ran. Read as
             * that, a request that could not look at the one reading it was about would have
             * reported the line as refusing a row.
             */
            NO_READING_OF_THE_LINE_COULD_BE_SEARCHED,
            /**
             * Every row that was composed sits where the body answers nothing, so each would reach
             * an {@code unreachable} and be refused.
             *
             * <p>Not one of the words about the model. Nothing proves the inputs there do not
             * arise — the body states it — so this says no row can be offered there, and not that
             * none exists.
             */
            EVERY_ROW_THERE_REACHES_AN_UNREACHABLE;

            /**
             * Whether this reason proves there is nothing to find, which one of them does.
             *
             * <p>Asked rather than matched on. Every reader of one of these has the same question —
             * may I say the model settles this, or am I saying what this compiler did not manage —
             * and each that answered it by naming the one word carried a copy of the decision
             * ADR-0091 took. A reason added is then a case here rather than a word that quietly
             * joins whichever side a reader's condition happened to leave it on.
             *
             * <p>Named as {@link souther.compiler.query.PartitionEvidence.PairSpace} names it, since
             * it is the same question about the same thing.
             */
            public boolean provesInfeasible() {
                return switch (this) {
                    case NO_VALUE_CAN_STAND_THERE, ONE_POSITION_CANNOT_BE_BOTH,
                         A_CONDITION_NEVER_COMES_OUT_THAT_WAY -> true;
                    // Every one of these is this compiler falling short, and none of them is the
                    // model saying anything: another value of the same classes may well build.
                    case NOTHING_COMPOSES_ONE, ALL_CANDIDATES_REJECTED,
                         NOT_ALL_CANDIDATES_COULD_BE_OFFERED, THE_SEARCH_LEFT_SOMETHING_UNTRIED,
                         NOTHING_STANDS_IN_FOR_A_DEPENDENCY, A_TABLE_IS_WHAT_THIS_NEEDS,
                         NOTHING_TO_BUILD_AGAINST, NO_VALUES_WERE_ASKED_FOR, LINKAGE_FAILED,
                         NO_CERTIFIED_WITNESS, THE_GROUP_WAS_NOT_OFFERED,
                         THE_POSITION_WAS_WITHHELD, THE_ROWS_WERE_NOT_READ,
                         THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE,
                         THE_WAY_IN_PLACES_AT_NO_CLASS, NO_CANDIDATE_WAS_OFFERED,
                         NO_READING_OF_THE_LINE_COULD_BE_SEARCHED -> false;
                    // What the body states and nothing proves: a statement, so not a proof.
                    case EVERY_ROW_THERE_REACHES_AN_UNREACHABLE -> false;
                };
            }

            /**
             * Whether a search that came back with this word did not look at every candidate there
             * was, which a row built beside it must not be held over.
             *
             * <p>Asked of the word and answered for each, with no default: a reason added is a
             * case here, decided when it is added, and not a word that joins whichever side a
             * reader's condition leaves it on. The searches that looked at everything are the ones
             * that proved nothing could stand there, the one whose candidates were all refused, and
             * the one whose rows all reach an {@code unreachable}; each of the others is this
             * compiler falling short of the candidates, or of reading them.
             */
            public boolean leavesSomethingUntried() {
                return switch (this) {
                    case NO_VALUE_CAN_STAND_THERE, ONE_POSITION_CANNOT_BE_BOTH,
                         A_CONDITION_NEVER_COMES_OUT_THAT_WAY, ALL_CANDIDATES_REJECTED,
                         EVERY_ROW_THERE_REACHES_AN_UNREACHABLE -> false;
                    case NOTHING_COMPOSES_ONE, NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                         THE_SEARCH_LEFT_SOMETHING_UNTRIED, NOTHING_STANDS_IN_FOR_A_DEPENDENCY,
                         A_TABLE_IS_WHAT_THIS_NEEDS, NOTHING_TO_BUILD_AGAINST,
                         NO_VALUES_WERE_ASKED_FOR, LINKAGE_FAILED, NO_CERTIFIED_WITNESS,
                         THE_GROUP_WAS_NOT_OFFERED, THE_POSITION_WAS_WITHHELD,
                         THE_ROWS_WERE_NOT_READ, THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE,
                         THE_WAY_IN_PLACES_AT_NO_CLASS, NO_CANDIDATE_WAS_OFFERED,
                         NO_READING_OF_THE_LINE_COULD_BE_SEARCHED -> true;
                };
            }

            /**
             * The word a search these budgets stopped comes back with.
             *
             * <p>One way only. Which budget stopped a search is what the search hands over, and this
             * is the word readers of the word have always had — read the other way round, a reader
             * would be recovering a budget from something that never held one: two of these come
             * back with the same word and one of them comes back with it without any budget having
             * been reached at all.
             *
             * <p>The words are what each of these has always said, kept rather than tidied. A budget
             * carries what stopped a search; what a report and a document say of it is a separate
             * decision from this one, and moving a word here would move it for them.
             *
             * <p>Budgets that come back with different words are the stops of more than one walk:
             * a walk over the numbers of a set stopped at its figure after the attempt at each
             * number met one of its own, or two searches whose findings were joined
             * ({@link CompositionShortfall#and}). What such a search comes to is then what its
             * walks came to together, which is not a choice between causes: the words say how far a
             * walk got — to the end of what it was handed and composing nothing there, or stopped in
             * front of something it did not try — and a search any walk of which stopped in front of
             * something left that untried, whatever the others came to. So the word for a walk cut
             * short takes in the word for one that ran to its end. Every budget still travels beside
             * the word, so what somebody would raise is the same either way.
             */
            public static Reason wordFor(java.util.Collection<CompositionBudget> budgets) {
                HowFar farthest = null;
                for (CompositionBudget each : budgets) {
                    HowFar here = switch (each) {
                        case ELEMENTS_A_PROPOSAL_HOLDS, CHARACTERS_A_PROPOSAL_HOLDS,
                             PLACES_A_PAIR_IS_TRIED_AT,
                             // Beside the figure it was split off, because the word is the walk's
                             // answer and the figures are what stopped it. Given a word of its own,
                             // one walk would say two things depending on which of its own numbers
                             // ran out first — and an answer carrying the word and the budget could
                             // not be assembled at all ({@link CompositionBudget#splitFrom}).
                             PLACES_A_PAIR_IS_LOOKED_AT -> HowFar.TO_THE_END;
                        case PAIRINGS_BUILT_AT_ONCE, ELEMENTS_A_TOTAL_IS_SPREAD_OVER,
                             // The pairs past it were never composed for, so what the search came
                             // to is about the pairs it tried.
                             PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED,
                             CHOICES_OF_INPUT_NUMBERS_LOOKED_AT,
                             SHAPES_OF_A_TOTAL_OFFERED, ELEMENTS_A_COUNT_IS_COMPOSED_WITH,
                             CONTAINERS_A_COUNT_IS_OFFERED, SHARES_A_COUNT_IS_TRIED_AT,
                             TOTALS_A_COUNT_IS_TRIED_AT, COUNTS_OF_KEYS_TRIED,
                             VALUES_AN_ELEMENT_IS_CHOSEN_AMONG,
                             WAYS_DOWN_TO_A_TOTAL_TRIED,
                             WAYS_UNDER_THE_CASES_TRIED,
                             // The cases past it were never planned under, so what the search came
                             // to is about the cases it tried.
                             CASES_A_RULE_ABOVE_IS_PLANNED_UNDER,
                             STEPS_A_SEARCH_MAY_TAKE, ASSIGNMENTS_A_SEARCH_COMPOSES,
                             ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW,
                             // The strings past this many pieces were never offered, so what the
                             // search came to is about the strings it tried.
                             PIECES_A_STRING_IS_PUT_TOGETHER_OF,
                             STRINGS_OF_THE_ROW_A_PIECE_IS_TAKEN_FROM,
                             // The sides past it were made of a number repeated, so what the
                             // search came to is about the lists it tried.
                             ELEMENTS_A_SIDE_IS_SEARCHED_OVER, NUMBERS_A_SIDE_IS_BALANCED_FROM,
                             VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED,
                             LEVELS_A_SIDE_IS_ASKED_AT,
                             // The divisors past this one were never asked for, so what the search
                             // came to is about the pairs of the ones it tried.
                             DIVISORS_OF_A_PRODUCT_TRIED,
                             // Likewise the divisors of a remainder past the ones it tried.
                             DIVISORS_OF_A_REMAINDER_TRIED,
                             // And the remainders of a sum past the ones it tried.
                             REMAINDERS_A_SUM_IS_TRIED_AT,
                             // The numbers past this one were never asked for, so what the search
                             // came to is about the numbers it tried and about nothing else. The
                             // word says that, where the word for a set walked to its end says the
                             // set has no value in it.
                             NUMBERS_OF_A_SET_TRIED,
                             // Likewise the choices of a number for each of several totals past
                             // this one: the search came to is about the choices it tried.
                             COMBINATIONS_OF_TOTALS_TRIED,
                             // The counts a string is written for past this one, and the lengths
                             // past the ones looked at, were never asked for either.
                             CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL,
                             CODE_POINTS_BEYOND_A_COUNT_A_STRING_IS_LOOKED_FOR -> HowFar.CUT_SHORT;
                        // Reaching these stops no composing, so no search comes back from one of
                        // them and there is no word to give. Asked for one all the same, this says
                        // so rather than lending a word from a budget that does stop something.
                        // The last stops a reading of a body rather than a search for a value, and
                        // what it stopped is carried where that reading is
                        // ({@link DecisionReading.Enumeration}).
                        case TIMES_THE_RULES_ARE_ASKED_AGAIN,
                             VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT,
                             // Beside it for the same reason: what either of them stopped is the
                             // getting past a condition on the way, and the row is composed either
                             // way.
                             PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT,
                             ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR,
                             VALUES_A_POINT_IS_TRIED_WITH,
                             DEPTH_A_CONSTRUCTION_PLAN_DESCENDS,
                             PATHS_OF_A_DECISION_READ,
                             // It stops the asking whether an input takes a way, which keeps the
                             // way and composes nothing.
                             CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE,
                             // It stops a reading of what a condition means, and what it stopped
                             // is carried as a part nothing read, naming it.
                             READINGS_OF_ONE_CONDITION, TOTAL_READINGS_OF_ONE_CONDITION,
                             PARTS_A_DERIVATION_CONCLUDES,
                             // It stops the writing out of the cases of a statement over the ways
                             // of keeping elements, which is taken as a part nothing read, naming
                             // it.
                             WAYS_A_STATEMENT_IS_WRITTEN_OUT_OVER,
                             // It stops a reader taking a count of statements apart into its
                             // choices, which takes the count as a part it could not see into,
                             // naming it.
                             PARTS_THE_CHOICES_OF_A_COUNT_COME_TO,
                             // It stops what a path takes in of a condition, and what it stopped
                             // is carried as a condition the path did not take in, naming it.
                             ALTERNATIVES_A_PATH_TRIES,
                             // They stop the working out of where a line decides, and what they
                             // stopped is carried as a line nobody worked out, naming them.
                             STEPS_A_STATEMENT_IS_READ_IN, CASES_A_LINE_IS_TAKEN_APART_INTO,
                             CASES_A_LINE_IS_ASKED_IN,
                             // Past either the way is looked along whole, the row is composed
                             // either way, and what was not looked along is carried with the row's
                             // account.
                             WAYS_A_WAY_IS_LOOKED_ALONG, CHOICES_ON_A_WAY_LOOKED_AT,
                             // It stops a reading of a way for one relation, which composes
                             // nothing, and what it stopped is carried as what the relation says
                             // it stopped at.
                             WALKS_A_WAY_IS_READ_AGAIN_WITH,
                             PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH,
                             // What it stops is the looking for a way past a guard, beside a row
                             // already found, and what it stopped is carried beside that row.
                             RUNS_REPAIRING_A_ROW -> throw new IllegalArgumentException(
                                "no search comes back from this budget, so it has no word: " + each);
                    };
                    farthest = farthest == null || here.compareTo(farthest) > 0 ? here : farthest;
                }
                if (farthest == null) {
                    throw new IllegalArgumentException(
                            "a search nothing stopped has no word to read off what stopped it");
                }
                return farthest.word;
            }

            /**
             * How far a walk a budget stopped got, which is what its word says; in the order the
             * walks of one search are put together in, a later one taking in an earlier.
             */
            private enum HowFar {

                /** To the end of what it was handed, with nothing composed there. */
                TO_THE_END(NOTHING_COMPOSES_ONE),

                /** Stopped in front of something it did not try, which a search any walk of which
                 *  stopped has left untried whatever the others came to. */
                CUT_SHORT(THE_SEARCH_LEFT_SOMETHING_UNTRIED);

                private final Reason word;

                HowFar(Reason word) {
                    this.word = word;
                }
            }

            /**
             * The same answer in the words a walk of a coverage item comes back with.
             *
             * <p>Two vocabularies for one distinction, and this is the whole of what relates them.
             * A walk says one of two things and a search says one of nineteen, so the projection
             * runs this way and never the other — read back, seventeen words would have to name a
             * walk's answer and none of them does.
             *
             * <p>Exhaustive, with the seventeen named. A word added is a word somebody has to
             * decide about here, and deciding is what a {@code default} would do on their behalf:
             * it would put the new word among the ones no walk says, which is the answer for
             * seventeen of them and is nobody's to assume for the eighteenth.
             */
            public Realization.Unknown.Reason asAWalksAnswer() {
                return switch (this) {
                    case NOTHING_COMPOSES_ONE -> Realization.Unknown.Reason.NOTHING_COMPOSED_ONE;
                    case THE_SEARCH_LEFT_SOMETHING_UNTRIED -> Realization.Unknown.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;
                    // What a walk of a coverage item comes back with is what it did, and these are
                    // what somebody else did: the model settling the point, a candidate refused, a
                    // module with no classes, a position held back, a group never offered.
                    case ALL_CANDIDATES_REJECTED, NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                         NO_VALUE_CAN_STAND_THERE,
                         NOTHING_STANDS_IN_FOR_A_DEPENDENCY, A_TABLE_IS_WHAT_THIS_NEEDS,
                         ONE_POSITION_CANNOT_BE_BOTH, A_CONDITION_NEVER_COMES_OUT_THAT_WAY,
                         NOTHING_TO_BUILD_AGAINST,
                         NO_VALUES_WERE_ASKED_FOR, LINKAGE_FAILED, NO_CERTIFIED_WITNESS,
                         THE_GROUP_WAS_NOT_OFFERED, THE_POSITION_WAS_WITHHELD,
                         THE_ROWS_WERE_NOT_READ, THE_WAY_IN_PLACES_AT_NO_CLASS,
                         THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE,
                         NO_CANDIDATE_WAS_OFFERED, NO_READING_OF_THE_LINE_COULD_BE_SEARCHED,
                         EVERY_ROW_THERE_REACHES_AN_UNREACHABLE ->
                            throw new IllegalStateException(
                                    "no walk of a coverage item comes back with this: " + this);
                };
            }
        }

        public UnresolvedCombination {
            classes = List.copyOf(classes);
            // Copied like the classes beside it, and for the reason a record copies anything: two
            // of these are equal by what they hold, so a caller keeping the map it handed in is a
            // caller who can change what one of them is after it was made.
            alsoShort = java.util.Collections.unmodifiableSequencedMap(
                    new LinkedHashMap<>(alsoShort));
            said = said == null ? Optional.empty() : said;
        }

        public UnresolvedCombination(List<String> classes, Reason reason, String detail,
                                     Optional<String> said) {
            this(classes, reason, detail, said, new LinkedHashMap<>());
        }

        public UnresolvedCombination(List<String> classes, Reason reason) {
            this(classes, reason, null, Optional.empty());
        }

        /**
         * One at a point, with what the walk for it found out said beside the word.
         *
         * <p>A point is its own subject: one label, and no position several of these share. So
         * what the walk found goes where a reader is told which case of the word this was, and
         * never where the point is named.
         */
        static UnresolvedCombination atAPoint(
                String label, Reason reason, String said,
                SequencedMap<TermPath, StringOfferShortfall> alsoShort) {
            return new UnresolvedCombination(List.of(label), reason, null,
                    Optional.ofNullable(said), alsoShort);
        }

        /** The same, of a walk whose offer was short of nothing the rules leave. */
        static UnresolvedCombination atAPoint(String label, Reason reason, String said) {
            return atAPoint(label, reason, said, new LinkedHashMap<>());
        }

        /**
         * What one of these is really about, where several say the same thing.
         *
         * <p>A position nothing can write a value for makes every combination it takes part in
         * unfillable, and saying so once per combination is one fact repeated a hundred times. The
         * position is the fact; the combinations are arithmetic on it.
         *
         * <p>Where there is no such position, the classes themselves: a combination's, or a
         * point's one label.
         */
        public String subject() {
            return detail == null ? String.join(" x ", classes) : detail;
        }
    }

    /**
     * What a generation with nothing owed came to.
     *
     * <p>The rows offered at a behavior's boundaries are this: composed for points, which nobody is
     * asked about and nothing keeps a list of. What a run against a plan comes to is
     * {@link FillResult}, and holding both in one shape meant a result that had dropped its
     * obligations and one that never had any were the same value.
     */
    public record GenerationResult(List<GeneratedRow> rows, List<UnresolvedCombination> unresolved,
                                   List<GenerationReason> reasons) {

        public static final GenerationResult NONE =
                new GenerationResult(List.of(), List.of(), List.of());

        public GenerationResult {
            rows = List.copyOf(rows);
            unresolved = List.copyOf(unresolved);
            reasons = List.copyOf(reasons);
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
    public record Baseline(Lookup<String, Named> at) {

        public Baseline {
            Objects.requireNonNull(at, "the values a module states, by the parameter each is of");
        }

        /** The baseline that states one value, at one parameter. */
        public static Baseline stating(String parameter, Named value) {
            return new Baseline(Lookup.built(put -> put.put(parameter, value)));
        }

        /**
         * A value the module states, held as the reference it is reached by rather than as a name
         * rebuilt from parts.
         *
         * <p>{@code reachedAs} carries both what this denotes ({@link ReachName#denotes()}, the
         * identity a fixture entry is keyed by) and how it is written ({@link ReachName#rendered()},
         * what a generated row prints). The two are not one string for an imported value — its
         * rendered form is qualified while its declaration's own name is not — so building one from
         * the other reconstructs a name from parts this already has whole, and had it wrong: a value
         * imported bare and one written qualified denote the one declaration and render two ways.
         */
        public record Named(ReachName.Declaration reachedAs) {

            public Named {
                Objects.requireNonNull(reachedAs, "a baseline is the reference a value is reached by");
            }
        }
    }

    /**
     * What composing a row for one class of one position came to.
     *
     * <p>Held per class and keyed by the class, because a class is what a finding is about and the
     * row offered for it is what answers that finding. A search whose results were a list of rows
     * left the two joined by whatever a reader could match — the words in a row's name — and a row
     * is named for what it was composed for rather than for everything it turns out to settle.
     */
    private sealed interface ClassAttempt {

        /** The position, by the name every reading of it uses. */
        AxisId at();

        /** The class, by the id the partition gave it — never the label, which two positions of
         *  one type spell the same way. */
        String classId();

        /** A row composed for this class, and what looking for one that goes further came to where
         *  it stops at a guard — or null where there is nothing to say about one. */
        record Built(AxisId at, String classId, GeneratedRow row, RepairShortfall repair)
                implements ClassAttempt {}

        /** No row came of it, and what the search came to. Never a statement that none exists. */
        record Unresolved(AxisId at, String classId, CameToNothing came)
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
         * What the decoder of {@code type} says of {@code candidate} on its own, before it is put
         * beside anything.
         *
         * <p>A proof a search can use, and only in one direction. A value put inside a parameter is
         * read there by its own type's decoder, so a value that decoder refuses on its own is refused
         * in every value it could be put in, and no assignment holding it needs composing. The
         * converse does not follow: a value admitted on its own can still be refused beside the
         * others, by a rule relating two fields, and that stays {@link #build}'s to say.
         *
         * <p>{@link Admissibility#UNKNOWN} unless a runtime answers, and never read as either of the
         * other two. A search that took it for a refusal would drop values nothing refused; one that
         * took it for an admission would have nothing to drop, which is all it is.
         */
        default Admissibility admissibility(Type type, FixtureTemplate candidate) {
            return Admissibility.UNKNOWN;
        }

        /**
         * The value the decoder of {@code type} makes of {@code candidate} on its own, read the way
         * a built row's input is: empty where it refuses it, where the type has no decoder of its
         * own, or where nothing here can build.
         *
         * <p>The one way a value written as a fixture becomes a value a search walks. A reader of
         * the fixture's text or tree would be a second reading of what the decoder already says.
         */
        default Optional<ObservedValue> builtAlone(Type type, FixtureTemplate candidate) {
            return Optional.empty();
        }

        /** What a type's own decoder said of a value, or that nothing asked it. */
        enum Admissibility {
            ADMITTED,
            REFUSED,
            UNKNOWN
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

        /** What running {@code row} through the behavior came to. */
        ObservedRun run(RowToRun row);

        /**
         * What running {@code row} answered under {@code asked}, or empty where nothing can run
         * it. Nothing runs here unless a way to run rows says otherwise.
         */
        default Optional<AnswerObservation> runReplacing(RowToRun row, Rewriting asked) {
            return Optional.empty();
        }

        /**
         * Whether the behavior answering {@code now} answered differently from {@code was}. Nothing
         * here can say unless a way to run rows has the declarations to read the two with.
         */
        default AnswerChange change(AnswerObservation was, AnswerObservation now) {
            return AnswerChange.COULD_NOT_TELL;
        }

        /**
         * Every rewrite a row whose run went where {@code ran} did is asked, and that
         * {@link #runReplacing} can be asked for: the questions the measure of the rows written
         * puts to such a row ({@link ArmReplacements#askedOfARun}, {@link
         * WalkRewrites#askedOfARun}). None unless a way to run rows has the classes and the plan
         * to say which.
         */
        default List<RunRewrite> rewritesThrough(AlignedObservation ran) {
            return List.of();
        }

        /**
         * Whether a row handed here can be run at all. False only where nothing runs rows, which
         * a search says as nothing having run — and not as a run that came back with nothing,
         * which is a row run and seen to stop.
         *
         * <p>Asked of the way to run rows and not of which object it is, so a way wrapped in
         * another still says it.
         */
        default boolean runsRows() {
            return true;
        }

        /** Nothing runs here — what a caller with no runtime to run against uses. */
        Trial NOTHING_RUNS = new Trial() {

            @Override
            public ObservedRun run(RowToRun row) {
                return ObservedRun.nothingRan();
            }

            @Override
            public boolean runsRows() {
                return false;
            }
        };
    }

    /**
     * {@code trial}, running each row once, and each row under each rewrite once, whoever asks.
     *
     * <p>A search runs a row to see where it goes, another composes the same values, a row is run
     * to choose it among others and its reader runs it again to see where it stands: each is one
     * row in one environment, and a run of it answers the same every time. So what a row came to
     * is kept in one place for as long as {@code trial} is the way rows are run, and every search
     * holding it reads it there.
     */
    public static Trial once(Trial trial) {
        return runningOnce(trial);
    }

    static RunOnce runningOnce(Trial trial) {
        return trial instanceof RunOnce already ? already : new RunOnce(trial);
    }

    /**
     * What {@link #once} is.
     *
     * <p>Keyed by what a row is written as, which is its values and what it stands the dependencies
     * in with. A template is the text and the expression it stands for, and the second is a tree
     * whose equality is its own — so a pair of them makes no key, while the text is the whole of
     * what a row applied twice would be. The stand-ins are part of the key because they are part of
     * the run: a row applied in one environment is not the row applied in another.
     *
     * <p>What a search may spend is counted in the runs it makes, and a row run already costs
     * nothing. So a search with a figure of its own runs through {@link #run(RowToRun, Spend)}
     * and {@link #runReplacing(RowToRun, Map, Spend)}, which ask it to spend only for a run not
     * made before: the figure stays the search's, and what is free is decided here, once, for the
     * row and for the row under a rewrite alike.
     */
    static final class RunOnce implements Trial {

        private final Trial trial;
        private final Map<List<String>, ObservedRun> ran = new ConcurrentHashMap<>();
        private final Map<Replaced, Optional<AnswerObservation>> replaced =
                new ConcurrentHashMap<>();

        /** One row as it is written, and what a run of it asks the classes to rewrite. */
        private record Replaced(List<String> written, Rewriting asked) {}

        private RunOnce(Trial trial) {
            this.trial = trial;
        }

        /**
         * What running {@code row} came to, where it was run already or {@code spend} allows a
         * run; null where it needed a run and {@code spend} had none.
         */
        ObservedRun run(RowToRun row, Spend spend) {
            ObservedRun already = ran.get(writtenAs(row));
            if (already != null) {
                return already;
            }
            return spend.aRun() ? run(row) : null;
        }

        /**
         * What running {@code row} under {@code asked} answered, where it was run so already or
         * {@code spend} allows a run; null where it needed a run and {@code spend} had none.
         */
        Optional<AnswerObservation> runReplacing(RowToRun row, Rewriting asked, Spend spend) {
            Optional<AnswerObservation> already = replaced.get(new Replaced(writtenAs(row), asked));
            if (already != null) {
                return already;
            }
            return spend.aRun() ? runReplacing(row, asked) : null;
        }

        @Override
        public boolean runsRows() {
            return trial.runsRows();
        }

        @Override
        public ObservedRun run(RowToRun row) {
            List<String> written = writtenAs(row);
            ObservedRun already = ran.get(written);
            if (already != null) {
                return already;
            }
            ObservedRun now = trial.run(row);
            ran.put(written, now);
            return now;
        }

        @Override
        public Optional<AnswerObservation> runReplacing(RowToRun row, Rewriting asked) {
            Replaced key = new Replaced(writtenAs(row), asked);
            Optional<AnswerObservation> already = replaced.get(key);
            if (already != null) {
                return already;
            }
            Optional<AnswerObservation> now = trial.runReplacing(row, asked);
            replaced.put(key, now);
            return now;
        }

        @Override
        public AnswerChange change(AnswerObservation was, AnswerObservation now) {
            return trial.change(was, now);
        }

        @Override
        public List<RunRewrite> rewritesThrough(AlignedObservation ran) {
            return trial.rewritesThrough(ran);
        }

        static List<String> writtenAs(RowToRun row) {
            return new ComposedRow(row.inputs(), row.answers()).writtenAs();
        }
    }

    /**
     * A search's own figure for the runs it may make, asked only for a run nobody made before
     * ({@link RunOnce}).
     */
    @FunctionalInterface
    interface Spend {

        /** Whether one more run may be made, counting it where it may. */
        boolean aRun();
    }

    /**
     * What one composed row's run came to: where it went, and what it answered.
     *
     * <p>Two things and not one, because they are not found out together. Where a run went is what
     * the classes recorded, and a run nothing recorded still answered; a run that aborted part way
     * went where it went and answered nothing.
     *
     * @param watched where it went, or that nothing can say
     * @param answer  what it answered, or that it answered nothing
     */
    public record ObservedRun(Watched watched, AnswerObservation answer) {

        public ObservedRun {
            Objects.requireNonNull(watched, "a run says where it went, or that nothing can say");
            Objects.requireNonNull(answer, "a run says what it answered, or that it answered nothing");
        }

        /** A row nothing ran: nothing can say where it went, and it answered nothing. */
        public static ObservedRun nothingRan() {
            return new ObservedRun(new Watched.NotRun(), new AnswerObservation.NotAnswered());
        }
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
        record Ran(AlignedObservation seen) implements Watched {}

        /**
         * Something ran the row and nothing here can say what it did: nothing was recording, or the
         * recording was never read. What it answered is the run's, and a run that aborted is as
         * much one that did not answer here as it is in {@link Ran}. What this is not is a run that
         * reached nothing — that is {@link Ran} of an empty account — or a row nothing ran
         * ({@link NotRun}).
         */
        record NoAccount() implements Watched {}

        /**
         * Nothing ran the row: no way to run it, or a row short of what the behavior is stood in
         * with. It answered nothing because nothing was asked, which is not a run that stopped
         * without an answer, and a search that needs a run to say anything has nothing to go on.
         */
        record NotRun() implements Watched {}
    }

    // --- composing the rows ---------------------------------------------------------------------
    //
    // fill's convenience overloads, planOver, everyArmACombinationMayTake and
    // everyClassNoRowSitsIn moved to GenerationFixtures (test source, same package): every one of
    // them was reachable only from tests, and everyClassNoRowSitsIn was a second derivation of what
    // Adequacy.RowsOwed already computes (issue #1905) — read the rows a build already has rather
    // than the measure. Main calls only the plan-taking form directly below.

    /**
     * What became of one arm, over every place a run through it is recorded at.
     *
     * <p>One of the two folds an arm's answer is made by, and the one over the places. The other is
     * over the runs a behavior whose dependencies a way leaves open is searched by, and it combines
     * what this returns — so the two are named apart, and what a payload means over the places is
     * not what it means over the runs.
     *
     * <p>Built wins over everything, because a row through any splice goes through the arm the
     * author wrote. Where none built, the reasons of every place are kept together: they are not
     * one fact and they do not order against each other — one splice the model refuses says the arm
     * may be unreachable there, one nothing can steer a row to says this compiler fell short, and a
     * reader handed whichever came first was handed the order the walk took.
     *
     * <p>And where nothing was tried anywhere, what the reading made of every place — which is what
     * an arm with nowhere to be looked for has, and is not one answer. One splice of a helper may
     * be somewhere the model proves no run reaches while another is somewhere this compiler cannot
     * state the way to, and those are a fact about the model and a shortfall of ours. Read off
     * whichever place came first, the same body with its two call sites swapped answered one and
     * then the other.
     */
    private static ArmDisposition acrossOccurrences(
            ArmOwed asked, Map<ArmProbe, RowId> built,
            Map<ArmProbe, List<CameToNothing>> failed, Set<ArmProbe> cutOff,
            souther.compiler.reading.CoverageRead.Read read) {
        List<CameToNothing> why = new ArrayList<>();
        boolean anyCutOff = false;
        for (ArmProbe probe : asked.occurrences()) {
            RowId row = built.get(probe);
            if (row != null) {
                return new ArmDisposition.Built(row, probe);
            }
            why.addAll(failed.getOrDefault(probe, List.of()));
            anyCutOff |= cutOff.contains(probe);
        }
        if (anyCutOff) {
            // What ran out is how many rows this call writes, which the compilation set and says
            // for itself. Nothing of this compiler's own was met, so there is no figure here.
            why.add(CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                    UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED)));
        }
        if (!why.isEmpty()) {
            return new ArmDisposition.Unresolved(why);
        }
        List<PathAccess> nowhere = new ArrayList<>();
        for (ArmProbe probe : asked.occurrences()) {
            PathAccess access = read.armAt(probe);
            if (!nowhere.contains(access)) {
                nowhere.add(access);
            }
        }
        return new ArmDisposition.NoWayIn(nowhere);
    }

    /**
     * Which arm of the body a search steers a row towards, and every place it may steer to.
     *
     * <p>A handle and not an identity. What a row is owed for is one arm the author wrote, however
     * many times a helper carrying it is spliced in; a probe is one of those occurrences, and it is
     * what a search has to name because a run is recorded at an occurrence. So a proposal says
     * which obligation it targets and carries one of these to reach it, and the two are not the
     * same value.
     *
     * <p><b>All of the occurrences, and not one chosen for the arm.</b> What steers a row into a
     * splice is what stands on the way to <em>that</em> splice, and two splices of one arm are
     * reached by different ways: a helper called under a decision this compiler can state and again
     * under one it cannot has one arm nothing can steer a row to and one it can. Asked at a single
     * occurrence, the answer was whichever the walk wrote first — the same body with its two call
     * sites swapped offered a row for the arm in one order and said nothing could steer one in the
     * other, and no measure was in a position to notice.
     *
     * <p>Named rather than carried as the number the plan gave it. Spelled as a bare {@code int} it
     * put the things a run is asked about into two vocabularies, and anything holding both had to
     * say which kind of thing a number was every time it read one.
     */
    public record ArmOwed(List<ArmProbe> occurrences) {

        public ArmOwed {
            occurrences = List.copyOf(occurrences);
            if (occurrences.isEmpty()) {
                throw new IllegalArgumentException(
                        "an arm a row can be steered to is recorded somewhere");
            }
            // One place is one occurrence, and a walk over the occurrences would visit a place
            // listed twice twice.
            if (Set.copyOf(occurrences).size() != occurrences.size()) {
                throw new IllegalArgumentException(
                        "one place is named twice among an arm's occurrences: " + occurrences);
            }
        }

        /** An arm the caller has one place for, which is what a search stood up on its own has. */
        public ArmOwed(ArmProbe probe) {
            this(List.of(probe));
        }
    }

    /**
     * The same, composing each row's positions against a value the module already states where
     * there is one for them.
     *
     * <p>Which changes what a row says rather than what it is for. A row is composed for one class
     * either way; what a baseline settles is where the positions the row is <em>not</em> about
     * stand, and a value the model already names is one a reader recognises — so the difference
     * between the row and what is already written is the class, and the class alone.
     *
     * <p><b>And every row it composes stands the behavior's dependencies in with {@code stood}.</b>
     * What a class or an arm asks about is the positions, so nothing on this route asks a
     * dependency for one answer over another and the environment is the behavior's rather than the
     * row's. It arrives here because a candidate is run in it: composed without it and completed
     * afterwards, the row the search certified and the row a person is offered were two rows, and
     * the arm was settled by running the one nobody sees.
     *
     * <p>A behavior whose stand-ins nothing composed has no rows at all, which is what comes back.
     * Every obligation on the plan is answered with what the composition came to, because none of
     * them can be answered with a row that cannot be applied.
     */
    public static FillResult fill(GenerationPlan plan, List<ObservedRow> existing,
                                        CandidateCheck check,
                                        souther.compiler.reading.CoverageRead.Read read,
                                        Trial trial, List<Baseline> baselines,
                                        AnswersStoodIn stood, HeldOutcome.Of holding,
                                        WhereNothingIsAnswered unanswered,
                                        AdequacyPolicy.OfTheGeneration budget) {
        return switch (stood) {
            case AnswersStoodIn.NothingComposed(var why) ->
                    FillResult.nothingWasLookedFor(plan, why, List.of());
            case AnswersStoodIn.Stood(var answers) ->
                    filling(plan, existing, check, read, runningOnce(trial), baselines, answers,
                            holding, unanswered, budget);
        };
    }

    /** The search itself, once the environment its rows go out in is in hand. */
    private static FillResult filling(GenerationPlan plan, List<ObservedRow> existing,
                                      CandidateCheck check,
                                      souther.compiler.reading.CoverageRead.Read read,
                                      RunOnce trial, List<Baseline> baselines,
                                      List<StoodInAnswer> answers, HeldOutcome.Of holding,
                                      WhereNothingIsAnswered unanswered,
                                      AdequacyPolicy.OfTheGeneration budget) {
        MeasuredInput subject = plan.subject();
        List<ClassOfAPosition> classesOwed = plan.classesOwed();
        // Every place a run through an owed arm is recorded at, which is where a row may be
        // steered. Flattened here because the search looks in one place at a time; what each of
        // them came to is folded back onto the arm below, so a row through any occurrence fills
        // the arm the author wrote.
        List<ArmProbe> armsOwed = plan.armsOwed().stream()
                .flatMap(each -> each.occurrences().stream()).distinct().toList();
        MeasuredInput.MeasuredAxes ordered = ordered(subject);
        // A position where some row's value could not be read is a position nothing is known about.
        // A row generated for a class there may be a row that is already written, and telling an
        // author to write one is worse than saying nothing: it is a specific piece of work that is
        // already done.
        List<GenerationReason> undecided = new ArrayList<>();
        // The positions that were held back, kept so that the classes of one are answered for by
        // name. A reason about the position says what happened to it; a class of it is a thing this
        // run was asked for, and is owed an entry of its own saying it was never looked for.
        Set<AxisId> withheld = new LinkedHashSet<>();
        // And the positions the rules leave no room for anything at, kept for the same reason: a
        // class of one is a thing this run was asked for, and what the rules leave there is an
        // answer about the model rather than an absence.
        Set<AxisId> leftNoRoom = new LinkedHashSet<>();
        // Which of them the search keeps, decided here and narrowed from the same projection: the
        // ones kept are these axes and not a list assembled beside them, so the walk they are read
        // by is still the one they were measured at.
        Set<AxisId> keptAxes = new LinkedHashSet<>();
        for (Axis axis : ordered.axes()) {
            // A position inside a collection the rules leave no room in. No value stands there in
            // any row, so no class of it is a cell to fill — and left in, every combination of the
            // row would be one no row can be written for, including the ones that name a position
            // beside it and have nothing to do with this one.
            if (holdsNothing(subject, axis)) {
                leftNoRoom.add(axis.id());
                continue;
            }
            if (readEverywhere(axis, existing)) {
                keptAxes.add(axis.id());
            } else {
                undecided.add(new GenerationReason.PositionWithheld(axis.id()));
                withheld.add(axis.id());
            }
        }
        MeasuredInput.MeasuredAxes axes = ordered.where(axis -> keptAxes.contains(axis.id()));
        // No return where nothing was kept. Nothing being divided is a fact about the classes, and
        // the arms below do not read the classes for their answer: what it takes to arrive at an arm
        // is what the reading of the body says, and that reading was made before this was called.
        // Stopped here, an arm that reading had an answer for was left with no entry at all, and
        // whoever read the result for one had nothing to go on but the absence.
        //
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
                        new ClassOfAPosition(axes.get(i).id(), axes.get(i).classes().get(c).id()))) {
                    owed.add(new int[] {i, c});
                }
            }
        }

        // The values a row can be written against, resolved once for the behavior. Read per class,
        // this was the same walk through the decoders for every class owed, for an answer that is a
        // fact about the module rather than about the class asking.
        // The references this run composes, numbered by the run that composes them. A name a row
        // writes for a value the module states reaches a declaration and is some reference of it,
        // and no source wrote that one: the occurrence begins here, so this is what says which it
        // is. One minter for the run, so that two of them are two.
        FixtureReferences references =
                new FixtureReferences(subject.symbols().module(), subject.behavior());

        List<ResolvedOrigin> origins = resolve(axes, baselines, check, references);

        // Every search here runs its rows through {@code trial}, so a row two searches both
        // composed the same values for is applied once — a class's row run to see how far it got
        // among them, the candidates an arm is looked for with, and the rows a requirement's row
        // is chosen among.
        GoingOn goingOn = new GoingOn(read, trial, holding, unanswered);

        // The rows this run composes, each numbered where it is composed. The number is an
        // identity and nothing reads it as a place: what says two obligations were answered by one
        // line is that both entries name the same one.
        SequencedMap<RowId, FilledRow> composed = new LinkedHashMap<>();
        List<ClassAttempt> attempts = new ArrayList<>();
        // Which row answered which class. A row is a line in the file and the same line can answer
        // several things, so what says a class was answered is the entry naming the row rather than
        // anything written on the row itself.
        Map<ClassOfAPosition, RowId> answeredAt = new LinkedHashMap<>();
        List<CameToNothing> unresolved = new ArrayList<>();
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
            if (composed.size() >= budget.rowLimit()) {
                classesLeft = owed.size() - i;
                for (int cut = i; cut < owed.size(); cut++) {
                    Axis axis = axes.get(owed.get(cut)[0]);
                    UnresolvedCombination why = new UnresolvedCombination(
                            List.of(label(axis, owed.get(cut)[1])),
                            UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED);
                    // Nothing of this compiler's own was met: what ran out is how many rows this
                    // call writes, which the compilation set and a reader is told about where the
                    // search says how many classes it left ({@link GenerationReason.SearchLimit}).
                    // Named here as a figure, an author would go looking for one of this
                    // compiler's to raise and find the number was theirs all along.
                    attempts.add(new ClassAttempt.Unresolved(axis.id(),
                            axis.classes().get(owed.get(cut)[1]).id(),
                            CameToNothing.metNothing(why)));
                    unresolved.add(CameToNothing.metNothing(why));
                }
                break;
            }
            ClassAttempt attempt = rowFor(axes, at[0], at[1], origins, check, references, answers,
                    goingOn);
            attempts.add(attempt);
            switch (attempt) {
                case ClassAttempt.Built made -> {
                    // Its own row, whatever the ones beside it are written as. Two classes can be
                    // answered by rows written the same way and are still two rows the search
                    // composed one apiece — each is offered for its own class, and merging them
                    // would take one of the two classes its answer.
                    answeredAt.put(new ClassOfAPosition(attempt.at(), attempt.classId()),
                            compose(composed, made.row(), made.repair()));
                }
                case ClassAttempt.Unresolved none -> unresolved.add(none.came());
            }
        }
        // And the arms this run was asked for, one at a time and each from its own places to look.
        // What it takes to arrive at an arm is what the reading of the body says, and that is where
        // a row for one comes from. A combination the body settles together is a second place: a
        // row found there arrives at the arm and exercises the combination at once, so it is looked
        // in first — which is a preference between two answers and not one of them standing in for
        // the other. An arm no combination is over is answered from its way in all the same.
        Set<ArmProbe> left = new LinkedHashSet<>(armsOwed);
        // The other places each owed arm stands in, so that one row down one splice ends the
        // search for that arm rather than starting it again at the next.
        Map<ArmProbe, List<ArmProbe>> siblings = new LinkedHashMap<>();
        for (ArmOwed asked : plan.armsOwed()) {
            for (ArmProbe probe : asked.occurrences()) {
                siblings.put(probe, asked.occurrences().stream()
                        .filter(each -> !each.equals(probe)).toList());
            }
        }
        Map<ArmProbe, RowId> built = new LinkedHashMap<>();
        Map<ArmProbe, List<CameToNothing>> failed = new LinkedHashMap<>();
        // Arms the row budget ran out before, which is what the search stopping looks like from an
        // arm. Told apart from an arm with nowhere to look, because raising the budget changes one
        // of them and nothing about the other.
        Set<ArmProbe> cutOff = new LinkedHashSet<>();
        // And the arms behind a group nothing walked, which is a second silence with a different
        // cause. The one above is a budget that ran out with the arm still owed; this is a group
        // the offer never opened, and raising the budget does not reach it.
        InteractionCells.Offered offered =
                InteractionCells.of(read.interactions(), axes, budget.cellsPerGroup());
        // The combinations worth looking in, built once. A group builds a cell where it is asked
        // for one, so a walk per arm builds every cell of it again for an answer that does not
        // depend on which arm is asking.
        List<WhereToLook>cells = placesFor(new LinkedHashSet<>(armsOwed), offered);
        // And the ways into the arms inside closures, read off the ways once for every arm asked.
        Map<ArmProbe, List<WayIn>> namedWays =
                waysNamedInto(read, axes.subject().partitioning().operationsStanding().armsNamed());
        Set<ArmProbe> notOffered = new LinkedHashSet<>();
        // Which arms each held-back group could have been searched at, kept per group so that the
        // summary at the end can be counted off the entries rather than worked out a second way.
        List<List<ArmProbe>> behindEachHeldGroup = new ArrayList<>();
        for (InteractionCells.NotOffered held : offered.notOffered()) {
            List<ArmProbe> behindIt = armsIn(held.claims());
            behindEachHeldGroup.add(behindIt);
            notOffered.addAll(behindIt);
        }
        boolean unconfirmed = false;
        // And what each row this run kept was watched doing, by the number it goes by. A meeting is
        // settled by a run, so the question "does a row in hand already make this one" is a
        // question about what was observed — asked of the values, it would be asked of a reading.
        Map<RowId, AlignedObservation> seenOf = new LinkedHashMap<>();
        for (ArmProbe probe : armsOwed) {
            if (!left.contains(probe)) {
                // A row already composed was watched going through it, which is the one thing that
                // says so. Nothing is composed a second time for what a run was seen doing.
                continue;
            }
            for (WhereToLook place : whereToLookFor(probe, read, cells, namedWays, axes)) {
                if (composed.size() >= budget.rowLimit()) {
                    cutOff.add(probe);
                    break;
                }
                if (place.tried == null) {
                    place.tried = witnessFor(axes, place.at, check, trial,
                            List.of(probe), origins, references, answers);
                }
                // Each of the three, one at a time, so that a fourth added later has to be decided
                // about here rather than fall in with whichever of these a cast happened to take.
                // What else this row goes through is what watching it says, and nothing else: a
                // cell claims the arms a reading believes a row filling it takes, and discharging
                // them on that belief is the reading certifying itself (issue #1009).
                GeneratedRow row;
                List<ArmProbe> also;
                // What watched it, where anything did. Kept beside the row so that a meeting asked
                // about below is answered by a row already seen making it.
                AlignedObservation seen;
                switch (place.tried) {
                    case Witness.NoCombination none -> {
                        noRow(unresolved, failed, probe, CameToNothing.metNothing(
                                new UnresolvedCombination(List.of(),
                                        UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                                        null, Optional.of(none.said()))));
                        continue;
                    }
                    // The word, and with it what the search met. An arm nothing reached is told
                    // apart from an arm this compiler stopped short of by what travels beside the
                    // word, and there is nothing else in the answer that tells them apart.
                    case Witness.Exhausted none -> {
                        noRow(unresolved, failed, probe, none.cameToNothing());
                        continue;
                    }
                    // What ran out is how many readings and runs one arm is given, which is a walk
                    // of this compiler's rather than a figure the composing of a row is held to —
                    // and beside it whatever those candidates ran into, which is.
                    case Witness.Limited none -> {
                        noRow(unresolved, failed, probe, none.cameToNothing());
                        continue;
                    }
                    case Witness.Certified made -> {
                        row = made.row();
                        seen = made.by().seen();
                        also = alsoThrough(seen, left, probe);
                    }
                    case Witness.Unconfirmed offer -> {
                        row = offer.row();
                        // Nothing watched it, so what it is offered for is what the reading says
                        // and not what anything saw, and no other arm comes off the list for it.
                        // Said once for the behavior: it is one fact about this generation.
                        also = List.of();
                        seen = null;
                        unconfirmed = true;
                    }
                }
                // The row already offering these values where there is one, so that a class's row
                // an arm also goes through is one line and not two. What each of them is offered for
                // is the entries naming it, so nothing is written on the row here.
                RowId kept = keep(composed, row);
                if (seen != null) {
                    seenOf.putIfAbsent(kept, seen);
                }
                built.put(probe, kept);
                left.remove(probe);
                also.forEach(each -> {
                    built.put(each, kept);
                    left.remove(each);
                });
                // And the other places this same arm stands in. What is owed is the arm the author
                // wrote, and a row down one splice of it goes through the arm — so looking in the
                // rest composes a second row for work that has one, and the run would hold rows
                // nothing points at.
                siblings.getOrDefault(probe, List.of()).forEach(left::remove);
                break;
            }
            if (built.containsKey(probe) || cutOff.contains(probe) || failed.containsKey(probe)
                    || !(read.armAt(probe) instanceof PathAccess.Ways)) {
                continue;
            }
            // A way in was read and nothing was tried along it, which is two things and not one:
            // every way this reading has places at no class of any position, and — where the arm is
            // behind one — a group the limit held back was never walked either. Both are said. They
            // do not order against each other: one is what the partition divides this body into and
            // the other is what this run declined to do, and a reader handed whichever a condition
            // reached first was handed the order the branches were written in.
            List<CameToNothing> nowhere = new ArrayList<>();
            nowhere.add(CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                    UnresolvedCombination.Reason.THE_WAY_IN_PLACES_AT_NO_CLASS)));
            if (notOffered.contains(probe)) {
                nowhere.add(CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                        UnresolvedCombination.Reason.THE_GROUP_WAS_NOT_OFFERED)));
            }
            // The arm's own account and no cell's. Nothing was composed, so there is no cell this
            // is a fact about, and a line said for one would name nothing.
            failed.computeIfAbsent(probe, _ -> new ArrayList<>()).addAll(nowhere);
        }
        // One entry per arm the run was asked about, in the order it was asked. An arm the limit
        // cut off carries that beside whatever was tried before it: a place the model refuses says
        // nothing about the ones nobody got to, and an arm answered by the first alone was reported
        // as settled by the model on the strength of a search that stopped.
        // One entry per arm the plan named, folded over every place a run through it is recorded
        // at. A row through any of them goes through the arm the author wrote, so one built answer
        // settles it however many splices came to nothing; where none built, what a reader is owed
        // is what every place came to, since a splice nothing can steer a row to says nothing
        // about the one beside it.
        Map<ArmOwed, ArmDisposition> armAnswers = new LinkedHashMap<>();
        for (ArmOwed asked : plan.armsOwed()) {
            armAnswers.put(asked, acrossOccurrences(asked, built, failed, cutOff, read));
        }
        // Said once, at the end, and about both searches. One that ran out on the classes stopped
        // whether or not the arms had anything left to do, and two limits reported apart would be
        // read as two searches.
        // Counted off what the limit actually stopped. An arm still on the list because every
        // combination claiming it was refused is not one the limit cut off, and counting it here
        // told a reader to raise a limit that would change nothing.
        if (classesLeft + cutOff.size() > 0) {
            reasons.add(new GenerationReason.SearchLimit(subject.behavior(),
                    classesLeft + cutOff.size()));
        }
        // And the groups the limit held back that this run was asked about an arm behind. What it
        // says is what the search did not do: none of that group's combinations was looked in, so
        // nothing here exercises the decisions in it together. Whether the arms behind it got rows
        // is a different question and their own entries answer it — a row through an arm comes from
        // the way into it whether or not anything above it was walked.
        //
        // Against what was asked for, and not against what was left owed at the end. Read off what
        // was left, the line would come and go with whether the ways in happened to compose, which
        // is not what the limit did; asked about nothing behind it, the group costs this run
        // nothing and is not named (issue #967).
        int heldBackAndAskedAbout = 0;
        for (List<ArmProbe> behindIt : behindEachHeldGroup) {
            if (behindIt.stream().anyMatch(armsOwed::contains)) {
                heldBackAndAskedAbout++;
            }
        }
        if (heldBackAndAskedAbout > 0) {
            reasons.add(new GenerationReason.GroupsNotOffered(subject.behavior(),
                    heldBackAndAskedAbout));
        }
        if (unconfirmed) {
            reasons.add(new GenerationReason.RowsNotConfirmed(subject.behavior()));
        }
        // One entry per class the plan named, which the walk above wrote for the ones it kept a
        // position for. A class of a position that was held back was never a thing to look for, and
        // it says that here rather than being left out — a class the plan named and nothing
        // answered for is what a reader downstream had to invent a sentence about.
        Map<ClassOfAPosition, ClassDisposition> classAnswers = new LinkedHashMap<>();
        for (ClassAttempt attempt : attempts) {
            ClassOfAPosition key = new ClassOfAPosition(attempt.at(), attempt.classId());
            classAnswers.put(key, switch (attempt) {
                case ClassAttempt.Built _ -> new ClassDisposition.Built(answeredAt.get(key));
                case ClassAttempt.Unresolved none -> new ClassDisposition.Unresolved(none.came());
            });
        }
        for (ClassOfAPosition asked : classesOwed) {
            if (classAnswers.containsKey(asked)) {
                continue;
            }
            if (withheld.contains(asked.at())) {
                classAnswers.put(asked, new ClassDisposition.Unresolved(
                        CameToNothing.metNothing(new UnresolvedCombination(
                                List.of(labelOf(subject, asked)),
                                UnresolvedCombination.Reason.THE_POSITION_WAS_WITHHELD))));
            } else if (leftNoRoom.contains(asked.at())) {
                // The position is inside a collection the rules cap at none, so no value stands
                // there in any row this model admits. Which is what the model says rather than what
                // this search fell short of, and a reader may act on it.
                classAnswers.put(asked, new ClassDisposition.Unresolved(
                        CameToNothing.metNothing(new UnresolvedCombination(
                                List.of(labelOf(subject, asked)),
                                UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE))));
            }
        }
        // And the combinations the body settles a value by, where those are what this behavior is
        // held to. Rows through every arm can leave one of them unmade, which is the whole reason
        // it is asked about — so a row for one is looked for at a cell of the group that states it,
        // which is where the search for an arm already looks.
        //
        // <p>Certified by the run and by nothing else. A row sitting where the cell leaves room is
        // a reading of the body, and a reading is what may be wrong; what says the decisions were
        // settled together is a run watched doing all of what the cell names, which is what a
        // certified witness is.
        Map<ObligationIdentity.OfACombinationOfDecisions, ClassDisposition> meetingAnswers =
                new LinkedHashMap<>();
        Map<ObligationIdentity.OfACombinationOfDecisions, List<CellSelection>> waysTo =
                waysTo(subject.behavior(), offered);
        for (ObligationIdentity.OfACombinationOfDecisions asked : plan.meetingsOwed()) {
            List<CellSelection> ways = waysTo.getOrDefault(asked, List.of());
            if (ways.isEmpty()) {
                // A meeting no group this run walked states. What is owed was read under the
                // measure's limit and this search is held to its own, so a group held back here is
                // a meeting with nowhere to be looked for — which is this run's news and not the
                // model's.
                CameToNothing came = CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                        offered.notOffered().isEmpty()
                                ? UnresolvedCombination.Reason.NOTHING_TO_BUILD_AGAINST
                                : UnresolvedCombination.Reason.THE_GROUP_WAS_NOT_OFFERED));
                meetingAnswers.put(asked, new ClassDisposition.Unresolved(came));
                unresolved.add(came);
                continue;
            }
            // A row this run already composed that something watched making it. One row makes as
            // many meetings as it makes, and the arms above compose rows that go through them.
            RowId already = null;
            for (Map.Entry<RowId, AlignedObservation> each : seenOf.entrySet()) {
                if (ways.stream().anyMatch(way -> way.certifiedBy(each.getValue()))) {
                    already = each.getKey();
                    break;
                }
            }
            if (already != null) {
                meetingAnswers.put(asked, new ClassDisposition.Built(already));
                continue;
            }
            if (composed.size() >= budget.rowLimit()) {
                CameToNothing came = CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                        UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED));
                meetingAnswers.put(asked, new ClassDisposition.Unresolved(came));
                unresolved.add(came);
                continue;
            }
            RowId made = null;
            CameToNothing came = null;
            for (CellSelection at : ways) {
                Witness tried = witnessFor(axes, at, check, trial, claimed(at),
                        List.of(new Purpose.ForACombinationOfDecisions(asked.settled())),
                        origins, references, answers);
                switch (tried) {
                    case Witness.NoCombination none -> came = CameToNothing.metNothing(
                            new UnresolvedCombination(List.of(),
                                    UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH, null,
                                    Optional.of(none.said())));
                    // The word the search came to, and with it what the search met on the way.
                    // What a reader does about a meeting nothing answered turns on whether a
                    // number of this compiler's would have reached one.
                    case Witness.Exhausted none -> came = none.cameToNothing();
                    // What ran out here is how many readings and runs one combination is given,
                    // which is a walk of this compiler's over the readings rather than a figure
                    // the composing of a row is held to — and whatever the candidates it did try
                    // ran into, which is.
                    case Witness.Limited none -> came = none.cameToNothing();
                    case Witness.Certified it -> {
                        made = keep(composed, it.row());
                        seenOf.putIfAbsent(made, it.by().seen());
                    }
                    // Composed and watched by nothing. A meeting is settled by the run, so a row
                    // nothing saw make it is not an answer here, and what holds of the candidates
                    // is what that word says: none of them was a witness. A build that watches no
                    // run asks for none of these in the first place, so this is the shape being
                    // right rather than a state a report is written from.
                    case Witness.Unconfirmed _ -> {
                        unconfirmed = true;
                        came = CameToNothing.metNothing(new UnresolvedCombination(List.of(),
                                UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS));
                    }
                }
                if (made != null) {
                    break;
                }
            }
            if (made != null) {
                meetingAnswers.put(asked, new ClassDisposition.Built(made));
            } else {
                meetingAnswers.put(asked, new ClassDisposition.Unresolved(came));
                unresolved.add(came);
            }
        }
        // And the combinations of two classes, where the pair space is what this behavior is held
        // to. The same search as a class, with both positions held instead of one: what the
        // requirement names is a hard pin at each, and everything else is chosen beside them — so a
        // combination the baseline cannot be moved to directly is repaired at the positions the
        // requirement says nothing about, and is not answered by giving one of the two up.
        Map<ObligationIdentity.OfAFallbackPairCell, ClassDisposition> pairAnswers =
                new LinkedHashMap<>();
        for (ObligationIdentity.OfAFallbackPairCell asked : plan.pairsOwed()) {
            if (composed.size() >= budget.rowLimit()) {
                CameToNothing came = CameToNothing.metNothing(
                        new UnresolvedCombination(labelsOf(axes, asked),
                                UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED));
                pairAnswers.put(asked, new ClassDisposition.Unresolved(came));
                unresolved.add(came);
                continue;
            }
            Map<Integer, Integer> wanted = pinned(axes, asked);
            if (wanted == null) {
                // A class of a position this run has no axis for. Nothing here can be steered to
                // it, which is this compiler's shortfall and not something the model states.
                CameToNothing came = CameToNothing.metNothing(
                        new UnresolvedCombination(labelsOf(axes, asked),
                                UnresolvedCombination.Reason.NOTHING_TO_BUILD_AGAINST));
                pairAnswers.put(asked, new ClassDisposition.Unresolved(came));
                unresolved.add(came);
                continue;
            }
            Pins pins = Pins.of(axes, wanted);
            // A row this run has already composed that sits in both classes. One row settles as
            // many requirements as it settles, so a search here would compose a second row with
            // the same values and hand a person the same work twice — which is what the offering
            // would then have to take back out.
            RowId already = null;
            for (Map.Entry<RowId, FilledRow> each : composed.entrySet()) {
                if (pins.holds(axes, each.getValue().line().inputs(), check)) {
                    already = each.getKey();
                    break;
                }
            }
            if (already != null) {
                pairAnswers.put(asked, new ClassDisposition.Built(already));
                continue;
            }
            Composed made = rowFor(axes, pins,
                    List.of(new Purpose.ForAFallbackPairCell(asked.classes(), pins.labels())),
                    origins, check, references, answers, goingOn);
            if (made.row() == null) {
                pairAnswers.put(asked, new ClassDisposition.Unresolved(made.came()));
                unresolved.add(made.came());
            } else {
                pairAnswers.put(asked, new ClassDisposition.Built(
                        compose(composed, made.row(), made.repair())));
            }
        }
        // And the rewrites of the body no row was seen to tell from it, each looked for as a row the
        // rewrite answers differently on. Last, because what each asks is a row the others would
        // have composed anyway only by chance, and a row a rewrite is told by is one more line.
        Map<ReplacementOwed, ReplacementDisposition> replacementAnswers = new LinkedHashMap<>();
        for (ReplacementOwed asked : plan.replacementsOwed()) {
            // Held to the block only where the row is for one: a row that settles a measure is
            // not one of the rows a person is handed, and how many of those there may be is no
            // part of what the rows establish.
            if (plan.rewrites().use() == RewriteSearch.For.THE_BLOCK
                    && composed.size() >= budget.rowLimit()) {
                replacementAnswers.put(asked, new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.ROWS_A_BLOCK_MAY_HOLD));
                continue;
            }
            if (!trial.runsRows()) {
                replacementAnswers.put(asked, new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.NOTHING_RAN));
                continue;
            }
            ReplacementWitness looking =
                    new ReplacementWitness(trial, asked, plan.rewrites().runs());
            GeneratedRow found = switch (asked) {
                case ReplacementOwed.OfAnArm arm -> {
                    List<Purpose> purposes = List.of(new Purpose.ForAReplacement(asked));
                    List<WhereToLook> here =
                            placesFor(new LinkedHashSet<>(arm.occurrences()), offered);
                    GeneratedRow seen = null;
                    // Where the classes place a row down a way into the arm. A row nothing
                    // watched is not one a rewrite can be told on, and the search asks for none.
                    for (ArmProbe probe : arm.occurrences()) {
                        for (WhereToLook place : whereToLookFor(probe, read, here, namedWays,
                                axes)) {
                            seen = looking.tookFrom(() -> witnessFor(axes, place.at, check, trial,
                                    purposes, looking::of, origins, references, answers));
                            if (seen != null) {
                                break;
                            }
                        }
                        if (seen != null) {
                            break;
                        }
                    }
                    // And at the pieces of the strings the rows seen going through it held, where
                    // the bodies part a string and go on to attempt a construction of each piece.
                    // Before the rows below are moved, because the runs are one budget and these
                    // are read off the body: a few strings, each one change from a row seen,
                    // where moving a row asks for as many as composing a value takes. And a list
                    // of those rows with one more element, a value the rows of the module ran
                    // with, where the classes divide no element and the rows held none. And from
                    // the rows seen going through it, which is where a run through the arm is
                    // known to start whatever a reading of the way in could state — an arm
                    // decided by a relation between inputs, which no class of either holds a side
                    // of, among them. A candidate of each in turn, as for a body answering one
                    // value: the runs are one budget, and none of the three is asked ahead of
                    // another.
                    int through = arm.seenThrough().size();
                    Examining pieces = new Examining(looking);
                    Examining lists = new Examining(looking);
                    Beside growing = aListGrown(arm.ranWith(), axes.subject(), check, looking);
                    yield seen != null ? seen : taking(looking, List.of(
                            inOrder(through, at -> piecesDemanded(arm.seenThrough().get(at),
                                    axes, purposes, looking, check, answers,
                                    read.piecesAttempted(), pieces)),
                            inOrder(through, at -> candidatesBeside(arm.seenThrough().get(at),
                                    axes, purposes, check, answers, growing, lists)),
                            inOrder(through, at -> movedFrom(arm.seenThrough().get(at), axes,
                                    purposes, looking, check, answers))));
                }
                // From the rows seen entering the walk, which is where a run of it is known to start
                // whatever a reading of the way in could state. A rewrite of a walk parts from it
                // only from a second step on, so a list those rows held grown by one element and
                // then by two is asked first. Then a row in each class of each position, as for a
                // body answering one value: a walk over a list the rows hold fixed parts from its
                // rewrite where the value its step reads lies, which is what the classes divide.
                // And last a row with one position moved.
                case ReplacementOwed.OfAWalk walk -> {
                    List<Purpose> purposes = List.of(new Purpose.ForAReplacement(asked));
                    // A candidate grown from each row in turn, the rows holding the most elements
                    // first: one already of one element is a step from a row of two, where both
                    // rewrites can part from the walk, and a row grown from nothing reaches two only
                    // with both elements chosen here. In turn and not one row after another, since
                    // what a row holds may be what keeps every list grown from it answering alike.
                    List<List<ObservedValue>> from = walk.seenThrough().stream()
                            .sorted(Comparator.comparingInt(Generator::elementsHeld).reversed())
                            .toList();
                    int through = from.size();
                    Examining lists = new Examining(looking);
                    Beside growing = grownTwice(
                            aListGrown(walk.ranWith(), axes.subject(), check, looking));
                    // And beside each, a string the body parts with a piece more, and one put as
                    // pieces the body demands: a walk over the pieces is a walk over a list no
                    // input holds, and a string of more pieces is how it is handed more elements.
                    // And a list as long as the row's with one element changed for one the rows
                    // hold elsewhere: what the step does with one element and with another is what
                    // a rewrite is seen by.
                    Examining pieces = new Examining(looking);
                    Examining parted = new Examining(looking);
                    Examining changed = new Examining(looking);
                    Beside aPieceMore = (value, type, reading, parameter) ->
                            NearbyValues.withAPieceMore(value, type, reading, parameter,
                                    walk.separators());
                    Beside anElementChanged = (value, type, reading, _) ->
                            NearbyValues.withAnElementChanged(value, type, reading,
                                    walk.ranWith());
                    List<Iterator<GeneratedRow>> grownFromEach = new ArrayList<>();
                    for (List<ObservedValue> each : from) {
                        grownFromEach.add(candidatesBeside(each, axes, purposes, check, answers,
                                growing, lists));
                        grownFromEach.add(candidatesBeside(each, axes, purposes, check, answers,
                                anElementChanged, changed));
                        if (!walk.separators().isEmpty()) {
                            grownFromEach.add(candidatesBeside(each, axes, purposes, check,
                                    answers, aPieceMore, parted));
                        }
                        grownFromEach.add(piecesDemanded(each, axes, purposes, looking, check,
                                answers, read.piecesAttempted(), pieces));
                    }
                    GeneratedRow seen = taking(looking, grownFromEach);
                    for (int at = 0; at < axes.size() && seen == null; at++) {
                        for (int cls = 0; cls < axes.get(at).classes().size(); cls++) {
                            Pins pins = Pins.of(axes, Map.of(at, cls));
                            seen = looking.tookFromSearching(() -> search(axes, pins, purposes,
                                    origins, (_, _) -> true, check, references, answers,
                                    HeldTogether.Asked.NOTHING, row -> looking.of(row, null), true,
                                    goingOn.answersNothing()));
                            if (seen != null) {
                                break;
                            }
                        }
                    }
                    yield seen != null ? seen : taking(looking, List.of(
                            inOrder(through, at -> movedFrom(from.get(at), axes, purposes,
                                    looking, check, answers))));
                }
                case ReplacementOwed.ByOneAnswer one -> {
                    // Where the composition stands before anything is asked of it first: a body
                    // answering one value is told apart by any row it answers differently, and a
                    // behavior whose positions nothing divides has no class to look in.
                    List<Purpose> purposes = List.of(new Purpose.ForAReplacement(asked));
                    List<FixtureTemplate> composedFirst = looking.tookFromComposing(() -> composed(
                            axes, composes(axes.axes()), HeldTogether.Asked.NOTHING, check,
                            Map.of(), witnessedBy(looking, purposes, answers)));
                    GeneratedRow seen = composedFirst == null ? null
                            : new GeneratedRow(purposes, composedFirst, answers);
                    for (int at = 0; at < axes.size() && seen == null; at++) {
                        for (int cls = 0; cls < axes.get(at).classes().size(); cls++) {
                            Pins pins = Pins.of(axes, Map.of(at, cls));
                            seen = looking.tookFromSearching(() -> search(axes, pins, purposes,
                                    origins, (_, _) -> true, check, references, answers,
                                    HeldTogether.Asked.NOTHING, row -> looking.of(row, null), true,
                                    goingOn.answersNothing()));
                            if (seen != null) {
                                break;
                            }
                        }
                    }
                    // And beside the rows it answered, which is where a run is known to come back
                    // where the values the classes offer are ones the body gives no answer on. Last,
                    // because the runs are one budget: asked first, these could spend what a row the
                    // classes reach is found with, and a rewrite the classes tell apart would be
                    // left undecided. Three ways to look, a candidate of each in turn: a number
                    // moved by one, a string put as one a body parts, and a list with one more
                    // element — a value the rows of the module ran with, where the classes divide
                    // no element and the rows written hold only the lists they ran with. None is
                    // asked ahead of another, so one with many candidates leaves the others the
                    // runs it would have spent.
                    int rows = one.answeredOn().size();
                    Examining numbers = new Examining(looking);
                    Examining pieces = new Examining(looking);
                    Examining lists = new Examining(looking);
                    Beside growing = aListGrown(one.ranWith(), axes.subject(), check, looking);
                    yield seen != null ? seen : taking(looking, List.of(
                            inOrder(rows, at -> candidatesBeside(one.answeredOn().get(at), axes,
                                    purposes, check, answers, A_WHOLE_NUMBER_MOVED, numbers)),
                            inOrder(rows, at -> piecesDemanded(one.answeredOn().get(at), axes,
                                    purposes, looking, check, answers, read.piecesAttempted(),
                                    pieces)),
                            inOrder(rows, at -> candidatesBeside(one.answeredOn().get(at), axes,
                                    purposes, check, answers, growing, lists))));
                }
            };
            replacementAnswers.put(asked, found != null
                    ? new ReplacementDisposition.Witnessed(compose(composed, found, null))
                    : new ReplacementDisposition.NoneFound(looking.ended()));
        }
        // The searches' own maps, closed back into one answer per obligation in the plan's order. A
        // kind added to {@link GenerationObligation} without a case here does not compile, which is
        // the one place a search's algorithm-local maps become the pipeline's value.
        List<GenerationAnswer> discharged = new ArrayList<>();
        for (GenerationObligation obligation : plan.obligations()) {
            switch (obligation) {
                case GenerationObligation.Replacement q -> discharged.add(
                        new GenerationAnswer.Replacement(q, replacementAnswers.get(q.target())));
                case GenerationObligation.Class q -> discharged.add(
                        new GenerationAnswer.Class(q, classAnswers.get(q.target())));
                case GenerationObligation.Arm q -> discharged.add(
                        new GenerationAnswer.Arm(q, armAnswers.get(q.target())));
                case GenerationObligation.Pair q -> discharged.add(
                        new GenerationAnswer.Pair(q, pairAnswers.get(q.target())));
                case GenerationObligation.Meeting q -> discharged.add(
                        new GenerationAnswer.Meeting(q, meetingAnswers.get(q.target())));
            }
        }
        return new FillResult(composed, unresolved, reasons, Discharge.of(plan, discharged));
    }

    /**
     * A row the rewrite {@code looking} asks about answers differently on, composed from
     * {@code seen}, the inputs of a row a run was seen taking through the arm — or null where none
     * was.
     *
     * <p>The one place to look that rests on no reading of the way in: the run went through the
     * arm, so its inputs are somewhere a run through it starts, whatever a reading of the
     * conditions could state. What a row stating its answer would notice the rewrite by is a
     * different answer, so one position is moved at a time and the rest kept where the run had
     * them — each parameter in turn composed as a row with nothing pinned composes it, values
     * passed over moving it to the next its rules leave, beside the others written as they were
     * read. Written through the same check a composed value goes through, so what the run had is
     * never a value the model refuses on this row's behalf; and where the row went is what running
     * it says, as it is for every candidate the rewrite is asked about.
     *
     * <p>A value read off the run that this cannot write as a fixture leaves nothing to compose
     * from, and nothing is said of it here: the inputs are the run's and the gap is this
     * compiler's, which what the search came to already says ({@link ReplacementWitness#ended}).
     * A parameter moved is the whole of it, so a position inside a record is moved with the rest
     * of its record.
     */
    private static Iterator<GeneratedRow> movedFrom(List<ObservedValue> seen,
                                                    MeasuredInput.MeasuredAxes axes,
                                                    List<Purpose> purposes,
                                                    ReplacementWitness looking,
                                                    CandidateCheck check,
                                                    List<StoodInAnswer> answers) {
        MeasuredInput subject = axes.subject();
        List<FixtureTemplate> written = new ArrayList<>();
        for (int p = 0; p < seen.size(); p++) {
            if (!(ObservedFixtures.of(seen.get(p), subject.types().get(p), subject.ruleReading())
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate value))) {
                return Collections.emptyIterator();
            }
            written.add(value);
        }
        // A position at a time, composed when it is reached: the rows composed for it are
        // handed over as candidates, so the runs that put them to the rewrite are counted and
        // shared with the other ways of looking as theirs are.
        return new Iterator<>() {

            private int moved;

            private Iterator<GeneratedRow> composedForIt = Collections.emptyIterator();

            @Override
            public boolean hasNext() {
                while (!composedForIt.hasNext() && moved < written.size()) {
                    composedForIt = composedWith(moved++);
                }
                return composedForIt.hasNext();
            }

            @Override
            public GeneratedRow next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return composedForIt.next();
            }

            private Iterator<GeneratedRow> composedWith(int position) {
                Map<String, Written> kept = new LinkedHashMap<>();
                for (int p = 0; p < written.size(); p++) {
                    if (p != position) {
                        String parameter = subject.parameters().get(p);
                        kept.put(parameter, new Written(List.of(new WrittenWay(written.get(p),
                                Map.of(TermPath.of(parameter), written.get(p)))), false));
                    }
                }
                List<GeneratedRow> rows = new ArrayList<>();
                looking.tookFromComposing(() -> composed(axes, composes(axes.axes()),
                        HeldTogether.Asked.NOTHING, check, kept,
                        atMost(MOST_REPAIRS, () -> looking.composingStopped(
                                        List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS
                                                .at(MOST_REPAIRS))),
                                inputs -> {
                                    rows.add(new GeneratedRow(purposes, inputs, answers));
                                    return Acceptance.PASSED;
                                })));
                return rows.iterator();
            }
        };
    }

    /**
     * One step from the inputs of a row a run was seen coming back on.
     *
     * <p>Where the classes offer values the body does not answer on, they leave nothing to compare
     * the rewrite against; the run that came back is the one place known to. One whole number in the
     * inputs is moved by one at a time and the rest is kept as it was, each candidate written
     * through the same check a composed value goes through. Which candidate answers, and whether it
     * answers differently, is what running it says, as it is for every candidate the rewrite is
     * asked about.
     */
    private static final Beside A_WHOLE_NUMBER_MOVED =
            (value, type, reading, _) -> NearbyValues.of(value, type, reading);

    /**
     * The inputs of a row a run came back on with one more element in a list they hold — one of
     * {@code ranWith}, the values the rows of the module ran a position of the element's type with
     * ({@link NearbyValues#grown}). Which candidate answers, and whether it answers differently,
     * is what running it says.
     */
    private static Beside aListGrown(InputsRowsRanWith ranWith, MeasuredInput subject,
                                     CandidateCheck check, ReplacementWitness looking) {
        // What stands for a type is the same for every row and list the search grows, so it is one
        // for the search and made as far as the search asks, its stops said as they are met. A
        // type's values are bounded as a composing's candidates are, and the bound is said as that
        // figure.
        ElementsOfAType elements = new ElementsOfAType(
                standingFor -> subject.representativesHolding(standingFor,
                        FieldDomains.ConstructionLimits.NONE),
                ofOne -> ElementsOfAType.withOneElement(ofOne, subject.ruleReading()),
                subject.ruleReading(), check, MOST_REPAIRS, new ElementsOfAType.Stops() {

                    @Override
                    public void met(CompositionShortfall shortfall) {
                        looking.composingMet(shortfall);
                    }

                    @Override
                    public void limitedAt(int most) {
                        looking.composingStopped(List.of(
                                WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(most)));
                    }
                });
        return (value, type, reading, _) -> NearbyValues.grown(value, type, reading, ranWith,
                elements::of);
    }

    /** How many elements the lists in {@code row} hold between them, at every depth. */
    private static int elementsHeld(List<ObservedValue> row) {
        int n = 0;
        for (ObservedValue each : row) {
            n += elementsIn(each);
        }
        return n;
    }

    private static int elementsIn(ObservedValue value) {
        return switch (value) {
            case ObservedValue.Sequence sequence ->
                    sequence.elements().size() + elementsHeld(sequence.elements());
            case ObservedValue.Constructed constructed ->
                    elementsHeld(List.copyOf(constructed.fields().values()));
            case ObservedValue.Mapping mapping -> mapping.entries().stream()
                    .mapToInt(each -> elementsIn(each.key()) + elementsIn(each.value())).sum();
            case ObservedValue.Bool _, ObservedValue.Integer _, ObservedValue.Decimal _,
                 ObservedValue.Text _, ObservedValue.Temporal _, ObservedValue.Unit _,
                 ObservedValue.Absent _, ObservedValue.Unknown _, ObservedValue.Truncated _ -> 0;
        };
    }

    /**
     * {@code once}'s values, and after them each of those grown by {@code once} again: a list one
     * element longer, then two. Each with the element it was given last put first as well, where
     * the list is the value itself.
     *
     * <p>For a rewrite of a walk, which parts from the walk only from a second step on. A row a run
     * entered the walk with may hold no element, and that list one element longer is still a list no
     * rewrite of the walk answers differently on. Those grown by one are asked first, so a row
     * holding one element is grown to two before anything is grown from nothing. And a walk
     * stopping after its first element parts from one that goes on only where what the elements
     * after the first do differs from what the first does: the element a row held is put after the
     * new one as well as before it.
     */
    private static Beside grownTwice(Beside once) {
        Beside grown = (value, type, reading, parameter) -> new Iterator<>() {

            private final Iterator<ObservedValue> first = once.of(value, type, reading, parameter);

            /** The values grown once, kept as they are handed over, to be grown again after. */
            private final List<ObservedValue> grownOnce = new ArrayList<>();

            private int again;

            private Iterator<ObservedValue> second = Collections.emptyIterator();

            @Override
            public boolean hasNext() {
                if (first.hasNext()) {
                    return true;
                }
                while (!second.hasNext() && again < grownOnce.size()) {
                    second = once.of(grownOnce.get(again++), type, reading, parameter);
                }
                return second.hasNext();
            }

            @Override
            public ObservedValue next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                if (first.hasNext()) {
                    ObservedValue taken = first.next();
                    grownOnce.add(taken);
                    return taken;
                }
                return second.next();
            }
        };
        return (value, type, reading, parameter) -> new Iterator<>() {

            private final Iterator<ObservedValue> each = grown.of(value, type, reading, parameter);

            private final Deque<ObservedValue> ready = new ArrayDeque<>();

            @Override
            public boolean hasNext() {
                while (ready.isEmpty() && each.hasNext()) {
                    ObservedValue taken = each.next();
                    if (!(taken instanceof ObservedValue.Sequence list)) {
                        ready.add(taken);
                        continue;
                    }
                    // A list of one element is walked no further than its first, and no rewrite of
                    // a walk over it answers differently: it is grown again, and not asked.
                    if (list.elements().size() < 2) {
                        continue;
                    }
                    ready.add(taken);
                    List<ObservedValue> moved = new ArrayList<>();
                    moved.add(list.elements().getLast());
                    moved.addAll(list.elements().subList(0, list.elements().size() - 1));
                    ready.add(new ObservedValue.Sequence(moved));
                }
                return !ready.isEmpty();
            }

            @Override
            public ObservedValue next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return ready.poll();
            }
        };
    }

    /** The values a candidate puts at the position of one parameter, given the value the run had
     *  there. */
    @FunctionalInterface
    private interface Beside {

        Iterator<ObservedValue> of(ObservedValue seen, Type type, RuleReadingContext reading,
                                   String parameter);
    }

    /**
     * A row the rewrite {@code looking} asks about answers differently on, found beside the inputs
     * of a row a run was seen going through, at the strings it held where a body parts one and
     * builds a newtype of its pieces ({@link PieceDemand}).
     *
     * <p>Each such string is put as one whose pieces are all ones the newtype is written to
     * admit, which the position's own rules are met with: a rewrite of which pieces are kept
     * answers differently only where a piece it keeps and the body does not, or the other way, is
     * one the construction goes on with. No class of the input holds that, since what the
     * construction admits is stated of a value made from the string. Which candidate answers, and
     * whether it answers differently, is what running it says. None where no string is parted.
     */
    private static Iterator<GeneratedRow> piecesDemanded(List<ObservedValue> seen,
                                                         MeasuredInput.MeasuredAxes axes,
                                                         List<Purpose> purposes,
                                                         ReplacementWitness looking,
                                                         CandidateCheck check,
                                                         List<StoodInAnswer> answers,
                                                         List<PieceDemand> demands,
                                                         Examining examining) {
        if (demands.isEmpty()) {
            return Collections.emptyIterator();
        }
        return candidatesBeside(seen, axes, purposes, check, answers,
                (value, type, reading, parameter) ->
                        NearbyValues.demanded(value, type, reading, parameter, demands, seen,
                                looking::composingStoppedAt),
                examining);
    }

    /**
     * How many candidates one way of looking may make and check, whether it goes on to run them or
     * refuses them first.
     *
     * <p>The runs are counted where a candidate is put to the rewrite, and a candidate refused
     * before that costs none. A way of looking whose candidates are mostly refused would otherwise
     * be bounded by nothing but how many there are to make. The bound is the one a composing holds
     * the rows it hands over to, and reaching it is said as that figure: what was not made is not
     * found absent.
     */
    private static final class Examining {

        private final ReplacementWitness looking;

        private int left = MOST_REPAIRS;

        private boolean said;

        private Examining(ReplacementWitness looking) {
            this.looking = looking;
        }

        /** Whether one more candidate may be made, the first one past the bound said as stopped. */
        boolean oneMore() {
            if (left > 0) {
                left--;
                return true;
            }
            if (!said) {
                said = true;
                looking.composingStopped(List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS
                        .at(MOST_REPAIRS)));
            }
            return false;
        }
    }

    /**
     * The rows that put one position of {@code seen} where {@code how} says and leave the others
     * as the run had them, one at a time and in the order the positions and their candidates come.
     *
     * <p>Handed over lazily: a candidate is made when it is asked for, so the work of making them
     * follows the runs the search makes and not the number a value could have. Nothing where a
     * position of the run cannot be written as a fixture, since there is no row to move from.
     */
    private static Iterator<GeneratedRow> candidatesBeside(List<ObservedValue> seen,
                                                           MeasuredInput.MeasuredAxes axes,
                                                           List<Purpose> purposes,
                                                           CandidateCheck check,
                                                           List<StoodInAnswer> answers,
                                                           Beside how, Examining examining) {
        MeasuredInput subject = axes.subject();
        // As the run had them, written once: a candidate moves one position and leaves the others
        // as they were.
        List<FixtureTemplate> kept = new ArrayList<>();
        for (int p = 0; p < seen.size(); p++) {
            if (!(ObservedFixtures.of(seen.get(p), subject.types().get(p), subject.ruleReading())
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate value))) {
                return Collections.emptyIterator();
            }
            kept.add(value);
        }
        return new Iterator<>() {

            private int moved;

            private Iterator<ObservedValue> nearer;

            private GeneratedRow next;

            @Override
            public boolean hasNext() {
                while (next == null && moved < seen.size()) {
                    if (nearer == null) {
                        nearer = how.of(seen.get(moved), subject.types().get(moved),
                                subject.ruleReading(), subject.parameters().get(moved));
                    }
                    if (!nearer.hasNext()) {
                        nearer = null;
                        moved++;
                        continue;
                    }
                    if (!examining.oneMore()) {
                        moved = seen.size();
                        break;
                    }
                    ObservedValue near = nearer.next();
                    if (ObservedFixtures.of(near, subject.types().get(moved),
                            subject.ruleReading())
                            instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                    FixtureTemplate value)
                            && check.refuse(moved, value).isEmpty()) {
                        List<FixtureTemplate> inputs = new ArrayList<>(kept);
                        inputs.set(moved, value);
                        next = new GeneratedRow(purposes, inputs, answers);
                    }
                }
                return next != null;
            }

            @Override
            public GeneratedRow next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                GeneratedRow out = next;
                next = null;
                return out;
            }
        };
    }

    /** The candidates of {@code count} rows one after the other, each made when it is reached. */
    private static Iterator<GeneratedRow> inOrder(int count,
                                                  IntFunction<Iterator<GeneratedRow>> each) {
        return new Iterator<>() {

            private int at;

            private Iterator<GeneratedRow> current = Collections.emptyIterator();

            @Override
            public boolean hasNext() {
                while (!current.hasNext() && at < count) {
                    current = each.apply(at++);
                }
                return current.hasNext();
            }

            @Override
            public GeneratedRow next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return current.next();
            }
        };
    }

    /**
     * The first candidate of {@code strategies} the rewrite answers differently on, or null where
     * none does or the runs are spent.
     *
     * <p>One candidate of each in turn, so no strategy spends the runs another is found with: the
     * runs are one budget, and a strategy with many candidates asked first would leave the ones
     * after it with none. What a strategy has not yet asked when the runs are spent is said as
     * the runs being spent ({@link ReplacementWitness#of}), since the next candidate is put to it
     * all the same.
     */
    private static GeneratedRow taking(ReplacementWitness looking,
                                       List<Iterator<GeneratedRow>> strategies) {
        List<Iterator<GeneratedRow>> live = new ArrayList<>(strategies);
        while (!live.isEmpty()) {
            for (int at = 0; at < live.size(); ) {
                Iterator<GeneratedRow> each = live.get(at);
                if (!each.hasNext()) {
                    live.remove(at);
                    continue;
                }
                GeneratedRow row = each.next();
                switch (looking.of(row, null)) {
                    case TAKEN -> {
                        return row;
                    }
                    case STOPPED -> {
                        return null;
                    }
                    case PASSED -> at++;
                }
            }
        }
        return null;
    }

    /** Every row a composing hands over, put to {@code looking} until it takes one — at most as
     *  many as a search may compose for one requirement, the one past them said as the figure. */
    private static RowTaking witnessedBy(ReplacementWitness looking, List<Purpose> purposes,
                                         List<StoodInAnswer> answers) {
        return atMost(MOST_REPAIRS, () -> looking.composingStopped(
                        List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(MOST_REPAIRS))),
                inputs -> looking.of(new GeneratedRow(purposes, inputs, answers), null));
    }

    /**
     * Where each meeting of the body's decisions can be looked for, by the requirement it states.
     *
     * <p>Several cells to one requirement, because a body may record the same decisions in more
     * than one place. A run down any one of them settles the value by those decisions, which is
     * what the requirement asks — so they are ways to it rather than several requirements, and the
     * search takes the first that composes a row.
     *
     * <p>Read off the groups this run was offered, which is the same walk the measure reads its
     * requirements from. A cell whose factors leave a position nothing is no combination the body
     * has a path to, and there is nothing to look in.
     */
    private static Map<ObligationIdentity.OfACombinationOfDecisions, List<CellSelection>> waysTo(
            String behavior, InteractionCells.Offered offered) {
        Map<ObligationIdentity.OfACombinationOfDecisions, List<CellSelection>> out =
                new LinkedHashMap<>();
        // What each decision hashes to, once: the choices of a group are taken from the same few
        // outcomes, and a decision is a deep value that costs as much to hash each time.
        Map<souther.compiler.reading.Condition, Integer> hashes = new IdentityHashMap<>();
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                if (selection == null) {
                    continue;
                }
                out.computeIfAbsent(new ObligationIdentity.OfACombinationOfDecisions(
                        behavior, DecisionSet.of(group.settlesAt(index), hashes)),
                        _ -> new ArrayList<>()).add(selection);
            }
        }
        return out;
    }

    /**
     * Where each class of a combination of two stands among this run's positions, or null where
     * one of them is at a position this run has no axis for.
     *
     * <p>By the axis the class names, which is the identity both sides join on. Looked up by the
     * position's words instead, this would be a second answer to which axis a class is of.
     */
    private static Map<Integer, Integer> pinned(MeasuredInput.MeasuredAxes axes,
                                                ObligationIdentity.OfAFallbackPairCell asked) {
        Map<Integer, Integer> out = new LinkedHashMap<>();
        for (ClassOfAPosition each : asked.classes()) {
            int at = -1;
            for (int i = 0; i < axes.axes().size(); i++) {
                if (axes.get(i).id().equals(each.at())) {
                    at = i;
                    break;
                }
            }
            if (at < 0) {
                return null;
            }
            int cls = -1;
            for (int c = 0; c < axes.get(at).classes().size(); c++) {
                if (axes.get(at).classes().get(c).id().equals(each.classId())) {
                    cls = c;
                    break;
                }
            }
            if (cls < 0) {
                return null;
            }
            out.put(at, cls);
        }
        return out;
    }

    /** What a report writes the two classes of a combination as, in a steady order. */
    private static List<String> labelsOf(MeasuredInput.MeasuredAxes axes,
                                         ObligationIdentity.OfAFallbackPairCell asked) {
        Map<Integer, Integer> wanted = pinned(axes, asked);
        return wanted == null
                ? asked.classIdsInOrder()
                : Pins.of(axes, wanted).labels();
    }

    /**
     * Which arms a combination claims a run through, by the numbers the plan gave them.
     *
     * <p>Only the arms. A combination's claims are what a run through it would be recorded at, and
     * a comparison is one of those — it is a place a run passes and not a way through a fork, so
     * nothing about an arm is owed for it.
     */
    static List<ArmProbe> claimed(CellSelection selection) {
        return armsIn(selection.claims());
    }

    /**
     * A combination this run may look in, with the arms it claims read off it once.
     *
     * <p>A group builds a cell when it is asked for one, so asking again is building it again —
     * and what a cell is does not depend on which arm is being looked for in it. The arms it claims
     * are read here for the same reason.
     *
     * <p>What came of searching it is held here too, and is null where nothing has yet. One cell is
     * searched once however many arms are looked for in it: the candidates it admits and what they
     * did are facts about the cell, and composing them again per arm is the same work done twice for
     * the same answer.
     */
    private static final class WhereToLook {

        private final CellSelection at;

        private final List<ArmProbe> claims;

        private Witness tried;

        private WhereToLook(CellSelection at, List<ArmProbe> claims) {
            this.at = at;
            this.claims = claims;
        }
    }

    /**
     * The combinations worth looking in, walked once.
     *
     * <p>Only the ones claiming an arm this run was asked about. A group's cells are as many as the
     * budget allows and most of them claim nothing on the list, so keeping all of them would hold a
     * search space nobody asked about — which is what the cells were before a finding decided what
     * to look for.
     */
    private static List<WhereToLook>placesFor(Set<ArmProbe> armsOwed,
                                              InteractionCells.Offered offered) {
        List<WhereToLook>out = new ArrayList<>();
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                // A choice whose factors leave a position nothing is no combination the body has a
                // path to, and there is nothing to look in.
                if (selection == null) {
                    continue;
                }
                List<ArmProbe> claims = claimed(selection);
                if (claims.stream().anyMatch(armsOwed::contains)) {
                    out.add(new WhereToLook(selection, claims));
                }
            }
        }
        return out;
    }

    /**
     * Where a row through {@code probe} is looked for, in the order they are looked in.
     *
     * <p>Two sources and neither is the other's fallback. A combination the body settles together
     * claiming this arm comes first, because a row found there answers the arm and exercises the
     * combination at once; the ways into the arm come after, and answer it whether or not anything
     * meets above it. Reversed, the same row would be composed twice over; left with only the
     * first, an arm under a body whose decisions meet nowhere had nowhere to be looked for at all
     * (issue #1009).
     *
     * <p>A way that places at no class is not somewhere to look. What comes back is where a row can
     * be steered, and how many that is is what the caller reads to tell an arm nothing was tried
     * for from one every attempt failed at.
     */
    private static List<WhereToLook>whereToLookFor(
            ArmProbe probe, souther.compiler.reading.CoverageRead.Read read,
            List<WhereToLook>cells,
            Map<ArmProbe, List<WayIn>> namedWays,
            MeasuredInput.MeasuredAxes axes) {
        List<WhereToLook>out = new ArrayList<>();
        for (WhereToLook place : cells) {
            if (place.claims.contains(probe)) {
                out.add(place);
            }
        }
        for (WayIn way : namedWays.getOrDefault(probe, List.of())) {
            CellSelection at =
                    InteractionCells.at(way, way.decisions().getLast().claims(), axes);
            if (at != null && out.stream().noneMatch(already -> already.at.sameAs(at))) {
                out.add(new WhereToLook(at, List.of(probe)));
            }
        }
        if (read.armAt(probe) instanceof PathAccess.Ways ways) {
            for (souther.compiler.reading.WayIn way : ways.ways()) {
                CellSelection at = InteractionCells.at(way, ways.arrivesAt(), axes);
                // The same place twice is one place. A combination of the body's decisions and a
                // way into one of its arms can name the same classes held to the same run — a
                // combination of one factor is exactly the way into the arm it settles — and the
                // two are independent readings that neither know nor need to know that. Looked in
                // twice, the second composes the same candidates against the same rules for an
                // answer the first already has, and says what it came to a second time.
                if (at != null && out.stream().noneMatch(already -> already.at.sameAs(at))) {
                    // The way into one arm, which is nowhere else's to look in and so is not kept
                    // beyond this arm's search.
                    out.add(new WhereToLook(at, List.of(probe)));
                }
            }
        }
        return out;
    }

    /**
     * The ways into each arm of a {@code match} on what a closure was handed, which the reading of
     * the runs names no way into and the tree the operations stand in names the case of
     * ({@link ArmsNamed}): each way a run was read taking to the arm, with every such arm on it
     * read as the case it is. Read off the ways once, by the arm each ends at.
     *
     * <p>A run down the arm is one application, handed one element of that case, so a row holding
     * such an element is where to look. Only where to look: what a run through the row does is
     * what watching it says, and the operation may stop before the element. Two applications on
     * the way about one position are looked for in one element, which a row of one element of
     * the case both ask meets, and which two cases leave no cell for — nowhere to look, and
     * nothing said about the arm.
     */
    private static Map<ArmProbe, List<WayIn>> waysNamedInto(CoverageRead.Read read,
                                                            ArmsNamed named) {
        Map<ArmProbe, List<WayIn>> out = new HashMap<>();
        for (WayIn way : read.taken()) {
            if (way.decisions().isEmpty()
                    || !(way.decisions().getLast().claims().at() instanceof ControlPlace.Arm arm)
                    || arm.probe().isEmpty()
                    || !(read.arms().get(arm.probe().get())
                            instanceof PathAccess.Unsupported(var why))
                    || why != PathAccess.Unsupported.Why.RUNS_WHERE_SOMETHING_CALLS_IT) {
                continue;
            }
            List<Decision> asCases = new ArrayList<>();
            for (Decision decision : way.decisions()) {
                asCases.add(decision.constrains()
                        instanceof souther.compiler.reading.Condition.Arm at
                        && named.of(at).orElse(null)
                                instanceof souther.compiler.reading.Condition.Case taken
                        ? new Decision(taken, decision.claims())
                        : decision);
            }
            out.computeIfAbsent(arm.probe().get(), _ -> new ArrayList<>()).add(new WayIn(asCases));
        }
        return out;
    }

    /**
     * What one combination came to with no row, written down once for the cell and once per arm.
     *
     * <p>Said once for the cell, because what a cell came to is one fact about it and a block
     * printing it once per arm looked for there says the same thing as many times as the body has
     * arms. Kept per arm as well, because what an arm was owed and what it got is the arm's own
     * account.
     *
     * <p>Both hold the whole answer. What a reader meets in either place is what this came to, and
     * one of them holding the word alone would print the same thing twice in two vocabularies —
     * one of them saying a search stopped and naming nothing to raise.
     *
     * <p>Said once is what the carriers say, and not what this decides. The same word from two
     * places is one answer with what both met under it ({@link CameToNothing#joined}), which is
     * settled where the list becomes the value that travels; dropped here as a repeat instead, the
     * second place's figures would go with it.
     */
    private static void noRow(List<CameToNothing> unresolved,
                              Map<ArmProbe, List<CameToNothing>> failed, ArmProbe probe,
                              CameToNothing came) {
        unresolved.add(came);
        failed.computeIfAbsent(probe, _ -> new ArrayList<>()).add(came);
    }

    /**
     * Which other arms still owed a row this run was seen going through.
     *
     * <p>What a run did and not what a reading expects of it. One row can be a row through several
     * arms — every arm on the way to the one it was composed for is one it takes — and the arm it
     * was composed for is left out here because it is already answered.
     */
    private static List<ArmProbe> alsoThrough(AlignedObservation seen,
                                              Set<ArmProbe> left, ArmProbe probe) {
        List<ArmProbe> out = new ArrayList<>();
        for (ArmProbe each : left) {
            if (!each.equals(probe) && seen.lit(each)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * The row as this generation offers it, which is the one already offering the same values where
     * there is one.
     *
     * <p>Two arms searched for on their own can come to one row: what steers a row into an arm is a
     * conjunction of decisions, and two arms of one body ask for values that agree everywhere the
     * ways in agree. Written down twice, an author is handed the same line twice and told it
     * answers two different things.
     */
    private static RowId keep(SequencedMap<RowId, FilledRow> composed, GeneratedRow row) {
        List<String> written = new ComposedRow(row.inputs(), row.answers()).writtenAs();
        for (Map.Entry<RowId, FilledRow> already : composed.entrySet()) {
            // Whatever the row beside it was composed for, and not the arms alone. One set of
            // values is one line in the file: a class's row and an arm's row of the same values are
            // one row that fills the class and goes through the arm, and written down twice the
            // second was printed over the first and took its name away with it.
            //
            // By what the rows are written as, which is what "the same line" means and is a string
            // to compare. A template also carries the expression it stands for, and holding two
            // rows to that walks two trees for an answer the text already gave.
            // The line already here keeps what came of looking past it. The rows kept this way
            // are an arm's and a meeting's, taken where the run went and never exchanged for one
            // that goes further, so they bring nothing of the kind.
            if (already.getValue().line().writtenAs().equals(written)) {
                return already.getKey();
            }
        }
        return compose(composed, row, null);
    }

    /**
     * A row of these values, numbered where it is composed.
     *
     * <p>The number is minted here and read nowhere as a place. What the identity is for is saying
     * that two entries name one line, and an identity that meant "the nth row offered" would move
     * with whatever the offer was ordered by — which is the arrangement a row's own account of what
     * it was composed for came apart under.
     *
     * <p>With what looking for a row that goes further came to, under the same number, or null
     * where there is nothing to say ({@link FilledRow}).
     */
    private static RowId compose(SequencedMap<RowId, FilledRow> composed, GeneratedRow row,
                                 RepairShortfall repair) {
        RowId id = new RowId(composed.size());
        composed.put(id, new FilledRow(new ComposedRow(row.inputs(), row.answers()), repair));
        return id;
    }

    /** The arms a list of claims names, by the numbers the plan gave them. Shared with the groups
     *  the limit held back, which have claims and no cell to read them off. */
    static List<ArmProbe> armsIn(
            List<ControlClaim> claims) {
        List<ArmProbe> out = new ArrayList<>();
        for (ControlClaim claim : claims) {
            if (claim.at() instanceof ControlPlace.Arm arm
                    && arm.probe().isPresent()) {
                out.add(arm.probe().get());
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
     * The classes a row is composed for, in the order a search settles them.
     *
     * <p>What a requirement is and how a search is told about it are two things. A class of a
     * position is one of these and a combination of two classes is one of these; what tells the
     * second from every other is a set, because a combination is a pair rather than an order of
     * them — and a search walks positions in an order. Made here and nowhere else, so the order is
     * this type's answer rather than whatever order a caller's collection happened to iterate in:
     * one requirement would otherwise be searched two ways and offer two rows depending on how its
     * classes were stored.
     *
     * <p>By the position's number, ascending. Which order it is does not matter and that there is
     * one does: the walk below spends a budget in order, so two runs asked for one thing have to
     * ask it the same way round.
     */
    record Pins(List<Pin> at) {

        /** One class of one position, with the words a report writes for it. */
        record Pin(int axis, int cls, String classId, String label) {}

        Pins {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                throw new IllegalArgumentException("a row is composed for something");
            }
        }

        /** The pins of {@code wanted}, which is a class apiece at the positions it names. */
        static Pins of(MeasuredInput.MeasuredAxes axes, Map<Integer, Integer> wanted) {
            List<Pin> out = new ArrayList<>();
            wanted.keySet().stream().sorted().forEach(at -> {
                Axis axis = axes.get(at);
                int cls = wanted.get(at);
                out.add(new Pin(at, cls, axis.classes().get(cls).id(), label(axis, cls)));
            });
            return new Pins(out);
        }

        /** The demand these make over the positions, which is what the walk is asked for. */
        Interpretation reading() {
            return new Interpretation(Lookup.built(put -> at.forEach(each ->
                    put.put(each.axis(), each.cls()))));
        }

        /** What a report writes this row as being about. */
        List<String> labels() {
            return at.stream().map(Pin::label).toList();
        }

        /** Whether a row's values are in every one of them, which is what certifies it. */
        boolean holds(MeasuredInput.MeasuredAxes axes, List<FixtureTemplate> inputs,
                      CandidateCheck check) {
            return at.stream()
                    .allMatch(each -> inTheClass(axes, each.axis(), each.classId(), inputs, check));
        }
    }

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
     * both moved — {@code Cond {...none, f = C, g = G2}} — and falling back to a
     * composition moves everything the classes happened to name. The supporting position is part of
     * the row and no part of what it is for: the row is still named for the class alone
     * ({@link Purpose.ForAClass}).
     */
    private static ClassAttempt rowFor(MeasuredInput.MeasuredAxes axes, int at, int cls,
                                       List<ResolvedOrigin> origins, CandidateCheck check,
                                       FixtureReferences references,
                                       List<StoodInAnswer> answers, GoingOn goingOn) {
        Axis axis = axes.get(at);
        String classId = axis.classes().get(cls).id();
        Pins pins = Pins.of(axes, Map.of(at, cls));
        Composed made = rowFor(axes, pins,
                List.of(new Purpose.ForAClass(axis.id(), classId, pins.labels().getFirst())),
                origins, check, references, answers, goingOn);
        return made.row() == null
                ? new ClassAttempt.Unresolved(axis.id(), classId, made.came())
                : new ClassAttempt.Built(axis.id(), classId, made.row(), made.repair());
    }

    /**
     * What a search for one requirement came back with: the row, or what the search came to.
     *
     * @param row    the row, or null where the search took none
     * @param repair what looking for a row that goes further than {@code row} came to, or null
     *               where there is nothing to say about one: no row, a row not stopped at a guard,
     *               or a row nothing says how far it got
     * @param came   what the search came to, or null where it took a row
     */
    private record Composed(GeneratedRow row, RepairShortfall repair, CameToNothing came) {

        /** A row, and nothing to say about a guard. */
        static Composed going(GeneratedRow row) {
            return new Composed(row, null, null);
        }

        /** A row stopped at a guard, and what looking past it came to. */
        static Composed stopping(GeneratedRow row, RepairShortfall repair) {
            return new Composed(row, repair, null);
        }
    }

    /**
     * A row a search found, run, and exchanged for one that gets further into the body where a
     * position the row is not about is what stopped it.
     *
     * <p>A preference between rows that answer the same requirement, and nothing more. The row the
     * search found already holds every pin, so it is the answer whatever comes of this: nothing
     * that runs here can take it away, and where nothing runs, or nothing better is found, it is
     * the row that goes out. What a search came to, what it spent and what it left untried are the
     * search's and this does not touch them.
     *
     * <p>What it holds the row to is what gets it past the guard the run stopped at: a way the
     * guard's condition lets a run go on ({@link TheRestOfTheBlock#ways}), each comparison of it the
     * run did not come out the way it asks held the way a point of its border on that side is
     * ({@link HeldOutcome}). Held beside the pins and not in place of them, and the search is
     * the class's own search again with those demands besides — so what is chosen again is a value
     * inside the classes the row already stands in, or a class of a position the row is not about,
     * and never the class the row is for. Where a pinned class is what fails the guard, no row
     * holds both and nothing is found: the row stopping there is the row about that class.
     *
     * <p>Against the origin the row was found from and no other, and with every position of a
     * parameter the row writes as the value the model states held at the class the row stands at
     * there. That value is one the author chose, and what it does to the body is what the row says
     * about it; so the search walks only rows that keep it, rather than building others and turning
     * them away.
     *
     * <p>Kept only where the new row was seen in the rest of the block. Each guard is looked past
     * once, and what deciding between rows costs is runs, so that is what is counted
     * ({@link CompositionBudget#RUNS_REPAIRING_A_ROW}), and counted where a row not run before is
     * run: looking at a row run already costs nothing, so running out ends nothing by itself, and
     * a way is given up only where its own search wanted a run and had none. What was held before
     * is held after, so a row past the second guard is still past the first.
     *
     * <p><b>And where the row goes out stopped at a guard, what the looking came to goes with
     * it</b> ({@link RepairShortfall}): which guard, for which requirement, and what the guard came
     * to — no way past it at all, ways this reading could not write down, or every way written,
     * each searched and composing nothing, searched until a run was refused, or one nothing here
     * can hold a row to. Each in its own words, so a way the model lets no row down and a way this
     * compiler could not compose a row for are not read as one answer. A row not stopped at a
     * guard, or one nothing says how far it got, carries nothing: there is no guard to say it
     * stopped at.
     *
     * @param read    the reading of the body, which says where a guard's rest of the block is and
     *                what holds on the way there
     * @param trial   what runs a row, once for every search of this run
     * @param holding what holds each comparison of the body
     * @param answersNothing where the body read as {@code read} answers nothing, placed on this
     *                run's axes, which no row this run composes may sit
     */
    private record GoingOn(CoverageRead.Read read, RunOnce trial, HeldOutcome.Of holding,
                           WhereNothingIsAnswered answersNothing) {

        /** The row {@code found} took, or a row for the same requirement that got further in —
         *  with what looking further came to, where the row goes out stopped at a guard. */
        Composed past(MeasuredInput.MeasuredAxes axes, Pins pins, List<Purpose> purposes,
                      Searched found, CandidateCheck check,
                      FixtureReferences references, List<StoodInAnswer> answers) {
            // Not run at all where the body has no guard for a run to stop at. Nothing could be
            // exchanged, and a run is what every other search of this run is bounded in.
            Runs runs = new Runs();
            if (read.restOfTheBlock().isEmpty()
                    || !(watched(found.row(), runs).orElse(null)
                            instanceof ObservedRun(Watched.Ran(AlignedObservation seen), var _))) {
                // Nothing says how far it got, so nothing is further and no guard is one it
                // stopped at.
                return Composed.going(found.row());
            }
            Candidate from = found.from();
            Set<String> against = found.against();
            // The classes the row stands at, at every position of a parameter it writes as the
            // value the model states.
            Admits keeping = (axis, cls) ->
                    !against.contains(axes.axes().get(axis).path().head())
                            || cls == from.where()[axis];
            GeneratedRow best = found.row();
            List<HeldOutcome> held = List.of();
            Set<ArmProbe> tried = new LinkedHashSet<>();
            while (true) {
                Optional<TheRestOfTheBlock> rest = restOfTheBlockShortOf(seen);
                if (rest.isEmpty()) {
                    return Composed.going(best);   // not stopped at a guard
                }
                // Each guard once: looking past one a second time is where going round starts.
                if (!tried.add(rest.get().arm())) {
                    return Composed.stopping(best, new RepairShortfall(purposes,
                            rest.get().refused(),
                            new RepairShortfall.AtTheGuard.BackAtAGuardLookedPast()));
                }
                // What the reading said of the ways past, which is three answers: none of them is
                // a list's emptiness standing for the other two.
                List<List<ControlClaim>> written = switch (rest.get().ways()) {
                    case Ways.Unknown<List<ControlClaim>> _ -> null;
                    // Any way past is what the search is after, whichever of them a run is seen
                    // taking.
                    case Ways.Known<List<ControlClaim>>(List<List<ControlClaim>> paths, var _) ->
                            paths;
                };
                if (written == null || written.isEmpty()) {
                    return Composed.stopping(best, new RepairShortfall(purposes,
                            rest.get().refused(), written == null
                                    ? new RepairShortfall.AtTheGuard.WaysNotRead()
                                    : new RepairShortfall.AtTheGuard.NoWayGoesPast()));
                }
                ArmProbe goneOn = rest.get().arm();
                List<WayPastTheGuard> ways = waysOn(seen, written, against);
                RepairShortfall.WayPast[] came = new RepairShortfall.WayPast[ways.size()];
                // Two choices that ask the row for the same things are one search, whichever ways
                // they are choices of, and what it came to is what both of them came to.
                Map<AChoice, ChoiceCame> asked = new HashMap<>();
                GeneratedRow further = null;
                // The first choice of each way is looked for as a way with one choice is; the
                // rest share one figure over the guard, so that the searches made past it are as
                // many as its ways and that figure, and never their product.
                int more = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
                // Every way is looked for, runs left or not. Looking at a row run already costs
                // nothing, so a search with none left can still be answered by rows run before;
                // what says a way was given up is a run refused inside its own search.
                for (int at : fewestFirst(ways)) {
                    WayPastTheGuard.Holding way = (WayPastTheGuard.Holding) ways.get(at);
                    // One search for each choice the way can be held along, and what the way came
                    // to is what every one of them came to.
                    List<CameToNothing> each = new ArrayList<>();
                    Set<CompositionBudget> cutShort = EnumSet.noneOf(CompositionBudget.class);
                    cutShort.addAll(way.cutShort());
                    for (int choosing = 0; choosing < way.choices().size(); choosing++) {
                        List<HeldOutcome> choice = way.choices().get(choosing);
                        List<HeldOutcome> both = new ArrayList<>(held);
                        both.addAll(choice);
                        ChoiceCame already = asked.get(new AChoice(choice));
                        if (already != null) {
                            each.add(already.came());
                            if (already.stopped()) {
                                cutShort.add(CompositionBudget.RUNS_REPAIRING_A_ROW);
                            }
                            continue;
                        }
                        // What the choice asks beside what the row was held to above, put together
                        // once. A later choice no row is — one that takes a value two cases at
                        // once along the ways held above, or a number to two places — is no way
                        // for this row, and is not looked for nor counted. The first choice is
                        // looked for whatever it is, so that what the way came to says why.
                        HeldTogether together = heldTogether(axes.subject(), both, check);
                        if (choosing > 0 && together instanceof HeldTogether.Refused) {
                            continue;
                        }
                        if (choosing > 0 && more == 0) {
                            cutShort.add(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                            break;
                        }
                        if (choosing > 0) {
                            more--;
                        }
                        runs.stopped = false;
                        Searched searched = search(axes, pins, purposes, List.of(from.from()),
                                keeping, check, references, answers, together,
                                row -> switch (watched(row, runs).orElse(null)) {
                                    case null -> {
                                        runs.stopped = true;
                                        yield Acceptance.STOPPED;
                                    }
                                    // Past the guard and to an answer. A run that went on and
                                    // then stopped without one, or went past what a run may
                                    // spend, is not a row that answers, wherever it got to first.
                                    case ObservedRun(Watched.Ran(AlignedObservation run),
                                                     AnswerObservation answer)
                                            when run.lit(goneOn)
                                            && answer instanceof AnswerObservation.Answered ->
                                            Acceptance.TAKEN;
                                    default -> Acceptance.PASSED;
                                }, answersNothing);
                        if (searched.row() != null) {
                            further = searched.row();
                            held = List.copyOf(both);
                            break;
                        }
                        asked.put(new AChoice(choice),
                                new ChoiceCame(searched.came(), runs.stopped));
                        each.add(searched.came());
                        if (runs.stopped) {
                            cutShort.add(CompositionBudget.RUNS_REPAIRING_A_ROW);
                        }
                    }
                    if (further != null) {
                        break;
                    }
                    // A way some of whose choices a figure left unlooked at is cut short as much
                    // as one whose runs ran out: a row past none of those looked along may still
                    // be past it. Every figure that did, since each is a number to raise.
                    List<CameToNothing> joined = CameToNothing.joined(each);
                    came[at] = cutShort.isEmpty() ? new RepairShortfall.WayPast.Searched(joined)
                            : new RepairShortfall.WayPast.CutShort(joined, cutShort);
                }
                if (further == null) {
                    List<RepairShortfall.WayPast> each = new ArrayList<>();
                    for (int at = 0; at < ways.size(); at++) {
                        each.add(switch (ways.get(at)) {
                            case WayPastTheGuard.Unheld(var why, var figures) -> why.isEmpty()
                                    ? new RepairShortfall.WayPast.CutShort(List.of(), figures)
                                    : new RepairShortfall.WayPast.NotSearchable(why, figures);
                            case WayPastTheGuard.Holding _ -> came[at];
                        });
                    }
                    return Composed.stopping(best, new RepairShortfall(purposes,
                            rest.get().refused(), new RepairShortfall.AtTheGuard.NoWayPast(each)));
                }
                // Taken only where it was seen going on, and a row run once is not run again.
                if (!(watched(further, runs).orElse(null)
                        instanceof ObservedRun(Watched.Ran(AlignedObservation now), var _))) {
                    throw new IllegalStateException("a row taken for going past a guard is one"
                            + " that was seen doing so: " + further);
                }
                best = further;
                seen = now;
            }
        }

        /** The runs one row's repair may still make. */
        private static final class Runs {

            private int left = CompositionBudget.RUNS_REPAIRING_A_ROW.maximum();

            /**
             * Whether the search under way was refused a run for a row it had not seen run, which
             * is the one thing that says a way was given up — and never read off {@link #left},
             * which says what is left and not that anything was wanted.
             */
            private boolean stopped;
        }

        /**
         * One way past a guard, as what holding a row to it asks or why nothing can.
         *
         * <p>Every way the reading wrote down is one of these, so none of them leaves the account
         * of what looking past the guard came to by being left out of the list.
         */
        private sealed interface WayPastTheGuard {

            /**
             * What holds every part of the way the row did not do, one of {@code choices} at a
             * time.
             *
             * <p>Several where a part of the way is one of several things a row can be held to
             * ({@link HeldOutcome.Bringing.Found}): each choice is one of those for each part, so
             * a row held to any one of them is held to the whole way, and none of them is all a
             * row past the way could be.
             *
             * @param choices  one or more, each holding every part the row did not do, in the order
             *                 they are looked for in
             * @param cutShort the figures that left some choice out, none where none did
             */
            record Holding(List<List<HeldOutcome>> choices, Set<CompositionBudget> cutShort)
                    implements WayPastTheGuard {

                public Holding {
                    choices = choices.stream().map(List::copyOf).toList();
                    if (choices.isEmpty() || choices.getFirst().isEmpty()) {
                        throw new IllegalArgumentException(
                                "a way a row is held to holds it to something");
                    }
                    cutShort = InDeclaredOrder.of(cutShort);
                }
            }

            /**
             * Nothing here can hold a row to it: every reason a part of it gave, and every figure
             * that left a part unlooked at.
             *
             * <p>All of them, since the way is all of its parts at once and each part that cannot
             * be held is a thing somebody would have to do — told the first, a reader who does it
             * meets the next.
             *
             * @param why     the reasons; none where only figures stand in the way
             * @param figures the figures; none where none left a part unlooked at
             */
            record Unheld(Set<RepairShortfall.Barrier> why, Set<CompositionBudget> figures)
                    implements WayPastTheGuard {

                public Unheld {
                    why = InDeclaredOrder.of(why);
                    figures = InDeclaredOrder.of(figures);
                    if (why.isEmpty() && figures.isEmpty()) {
                        throw new IllegalArgumentException("a way nothing holds is held by nothing"
                                + " for some reason");
                    }
                }

                /** For one reason alone. */
                static Unheld because(RepairShortfall.Barrier why) {
                    return new Unheld(Set.of(why), Set.of());
                }
            }
        }

        /** What looking for one choice of a way came to, and whether a run was refused in it. */
        private record ChoiceCame(CameToNothing came, boolean stopped) {}

        /**
         * One choice of a way past a guard, as a key: the same choice where it holds the same ways
         * of holding each part, which are the same objects wherever they were met — what holds a
         * condition is worked out once per place ({@link HeldOutcome.Of}) — so they are compared
         * as objects, and a way's account of every condition on it is not walked to file one.
         */
        private record AChoice(List<HeldOutcome> held) {

            @Override
            public boolean equals(Object other) {
                if (!(other instanceof AChoice that) || that.held.size() != held.size()) {
                    return false;
                }
                for (int at = 0; at < held.size(); at++) {
                    if (held.get(at) != that.held.get(at)) {
                        return false;
                    }
                }
                return true;
            }

            @Override
            public int hashCode() {
                int out = 1;
                for (HeldOutcome each : held) {
                    out = 31 * out + System.identityHashCode(each);
                }
                return out;
            }
        }

        /**
         * The ways a row can be held to, by where they stand among {@code ways}, the ways that ask
         * least of the row first.
         *
         * <p>Fewest first, because what the row did is the best guess at what a row like it does:
         * the way the row went through the guard's condition with one comparison turned round
         * changes the row least. Which is the order they are looked for in and nothing more; what
         * each came to is said in the order the reading wrote them.
         */
        private static List<Integer> fewestFirst(List<WayPastTheGuard> ways) {
            List<Integer> out = new ArrayList<>();
            for (int at = 0; at < ways.size(); at++) {
                if (ways.get(at) instanceof WayPastTheGuard.Holding) {
                    out.add(at);
                }
            }
            out.sort(Comparator.comparingInt(
                    at -> ((WayPastTheGuard.Holding) ways.get(at)).choices().getFirst().size()));
            return out;
        }

        /**
         * Each of {@code written}, the ways past a guard the reading wrote down, as what holds every
         * part of it {@code seen} did not do, or why nothing here can.
         *
         * <p>A way whole and not a comparison at a time. A way is what the guard's condition takes
         * all at once — both sides of an {@code &&}, the second of an {@code ||} with the first
         * failing — and held a comparison at a time, the row was sent past one part of a way into
         * a guard that refused it on the next.
         *
         * <p>What the run already did is no demand: it was seen doing it, and the row it is
         * composed again holds it as the row did, or holds it by the classes. A part of a way
         * nothing here can state a demand for is one nothing here can hold a row to. Nor is one
         * whose demand stands a term at a parameter the row writes as the value the model states
         * ({@code against}): holding it would compose that parameter afresh, and the value the
         * author chose is the row's. Asked of each way a part can be held along, since another
         * way of holding the same part may leave the parameter as it is.
         *
         * <p>In the order the reading wrote them, one apiece.
         */
        private List<WayPastTheGuard> waysOn(AlignedObservation seen,
                                             List<List<ControlClaim>> written,
                                             Set<String> against) {
            List<WayPastTheGuard> out = new ArrayList<>();
            for (List<ControlClaim> way : written) {
                out.add(wayOn(seen, way, against));
            }
            return out;
        }

        /**
         * One of them.
         *
         * <p>A part no value can take bars the way whatever the other parts say, since
         * the way is all of them at once. It is said in place of a part nothing here could hold a
         * row to, which would send an author looking for a row nobody can write.
         */
        private WayPastTheGuard wayOn(AlignedObservation seen, List<ControlClaim> way,
                                      Set<String> against) {
            List<HeldOutcome.Bringing> each = new ArrayList<>();
            for (ControlClaim part : way) {
                if (!part.satisfiedBy(seen)) {
                    each.add(holding.at(part.at()));
                }
            }
            if (each.isEmpty()) {
                return WayPastTheGuard.Unheld.because(
                        RepairShortfall.Barrier.THE_ROW_ALREADY_DOES_ALL_OF_IT);
            }
            // A way that would write a stated value afresh is left, and the rest are what holds
            // the part.
            PartsHeld together = partsHeld(each, one -> !writesAnyOf(one, against));
            if (together.noRowGoes()) {
                return WayPastTheGuard.Unheld.because(
                        RepairShortfall.Barrier.NO_VALUE_CAN_GO_THAT_WAY);
            }
            if (!together.why().isEmpty() || !together.unlooked().isEmpty()) {
                return new WayPastTheGuard.Unheld(together.why(), together.unlooked());
            }
            Set<CompositionBudget> cutShort = EnumSet.noneOf(CompositionBudget.class);
            cutShort.addAll(together.cutShort());
            OneOfEach.Taken<HeldOutcome> choices = OneOfEach.ofEachPart(together.parts(),
                    CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum());
            if (!choices.everyWay()) {
                cutShort.add(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
            }
            return new WayPastTheGuard.Holding(choices.ways(), cutShort);
        }

        /**
         * Whether holding the row to {@code held} composes a parameter in {@code against}: in
         * every vocabulary it asks in, a case written at a position as much as a number, and of
         * every alternative it takes on the way as much as the condition ({@link HeldOutcome#asks}).
         */
        private static boolean writesAnyOf(HeldOutcome held, Set<String> against) {
            if (held.demands().stream().anyMatch(demand -> writesAnyOf(demand, against))) {
                return true;
            }
            for (OnTheWay asked : held.asks()) {
                boolean writes = switch (asked) {
                    case OnTheWay.TakenIn in -> writesAnyOf(in.demand(), against);
                    case OnTheWay.Narrowed narrowed -> WayToTheBorder.positionsOf(narrowed)
                            .stream().anyMatch(position -> against.contains(position.head()));
                    case OnTheWay.Counted counted -> WayToTheBorder.positionsOf(counted)
                            .stream().anyMatch(position -> against.contains(position.head()));
                    case OnTheWay.Settled _, OnTheWay.Declined _, OnTheWay.OneOf _ -> false;
                };
                if (writes) {
                    return true;
                }
            }
            return false;
        }

        /** Whether holding the row to {@code demand} composes a parameter in {@code against}. */
        private static boolean writesAnyOf(RowDemand demand, Set<String> against) {
            return switch (demand) {
                case RowDemand.AtAPoint point -> point.fixing().keySet().stream()
                        .anyMatch(target -> against.contains(target.writeRoot().head()));
                // What holding the row to it composes, and not what it only reads: a set holding
                // the value a stated value writes at a position is composed, and the stated value
                // is the row's as the author chose it.
                case RowDemand.OfACondition condition -> condition.positions().stream()
                        .filter(position -> !condition.valuesRead().contains(position))
                        .anyMatch(position -> against.contains(position.head()));
            };
        }

        /**
         * What running {@code row} came to, run once whoever asks; or empty where it has not been
         * run and {@code runs} has none left. A row run already costs nothing.
         */
        private Optional<ObservedRun> watched(GeneratedRow row, Runs runs) {
            return Optional.ofNullable(trial.run(row.toRun(), () -> {
                if (runs.left == 0) {
                    return false;
                }
                runs.left--;
                return true;
            }));
        }

        /**
         * Where the rest of the block is, for the guard {@code seen} left by its refusal, or empty
         * where it left none that way. A refusal ends the run, so there is at most one.
         */
        private Optional<TheRestOfTheBlock> restOfTheBlockShortOf(AlignedObservation seen) {
            for (Map.Entry<ArmProbe, TheRestOfTheBlock> refused
                    : read.restOfTheBlock().entrySet()) {
                if (seen.lit(refused.getKey()) && !seen.lit(refused.getValue().arm())) {
                    return Optional.of(refused.getValue());
                }
            }
            return Optional.empty();
        }

    }

    /**
     * The same, for any requirement the pins say: every one of them is held and everything else is
     * chosen beside them.
     *
     * <p>One search for a class and for a combination of two classes. What differs between them is
     * what is pinned and what the row is named for, and neither of those is a way of searching —
     * so a second walk written for the second would be the same order of origins, the same repairs
     * and the same certification, free to answer differently.
     */
    private static Composed rowFor(MeasuredInput.MeasuredAxes axes, Pins pins,
                                   List<Purpose> purposes,
                                   List<ResolvedOrigin> origins, CandidateCheck check,
                                   FixtureReferences references,
                                   List<StoodInAnswer> answers, GoingOn goingOn) {
        Searched searched = search(axes, pins, purposes, origins, (_, _) -> true, check,
                references, answers, HeldTogether.Asked.NOTHING, _ -> Acceptance.TAKEN,
                goingOn.answersNothing());
        if (searched.row() == null) {
            return new Composed(null, null, searched.came());
        }
        Composed made = goingOn.past(axes, pins, purposes, searched, check, references, answers);
        // The row that goes out is the one holding every pin, the way it went, that tells the
        // most of its arms' rewrites apart. Past the guards first, since that is a way the row
        // goes and what is chosen here keeps it.
        Candidate from = searched.from();
        List<FixtureTemplate> told = tellingArmsApart(axes, from.where(), check,
                from.from().writtenAgainst(axes, from.delta(), from.where(), references),
                goingOn.trial(), answers, made.row().inputs(),
                inputs -> pins.holds(axes, inputs, check) ? Acceptance.TAKEN
                        : Acceptance.PASSED);
        return told.equals(made.row().inputs()) ? made : new Composed(
                new GeneratedRow(made.row().purposes(), told, made.row().answers()),
                made.repair(), made.came());
    }

    /**
     * What one search for a requirement came to: the row it took and the candidate it was built
     * from, or what its walks came to where it took none.
     *
     * @param row     the row, or null where none was taken
     * @param from    the origin the row was written against and the classes it was built at, or
     *                null where no row was taken
     * @param against the parameters the row writes as the value the origin states. Not every
     *                parameter the origin states: one whose classes cannot be written against that
     *                value is composed instead, and the row says nothing about the stated value there
     * @param came    what the walks came to, or null where a row was taken
     * @param stoppedShort whether a walk stopped in front of a candidate it had not built, or met
     *                a figure of this compiler's on the way — which the word in {@code came} does
     *                not tell from a walk that ran to the end of what this compiler writes. Never
     *                where a row was taken
     * @param boundsReached the bounds of this class's own a walk was compared against and stopped
     *                at, each as it stood there; none where none stopped one
     */
    private record Searched(GeneratedRow row, Candidate from, Set<String> against,
                            CameToNothing came, boolean stoppedShort, List<Figure> boundsReached) {

        Searched {
            boundsReached = Figure.inOrder(boundsReached);
        }
    }

    /** What a search makes of a row that holds every pin. */
    enum Acceptance {

        /** The row this search is for. */
        TAKEN,

        /** Not this one, and the walk goes on. */
        PASSED,

        /** Not this one, and nothing more is asked: what deciding a row costs has run out. */
        STOPPED
    }

    /**
     * The search for a requirement, and the only one: every row taken for a class, and every row a
     * class's row is exchanged for, is found by this.
     *
     * <p>The values the module states first and then the composition, each with a budget of its
     * own, and what the two came to added up where neither took a row. What differs between the
     * callers is what they hand in — the origins walked, the classes a position may stand at, the
     * comparisons a row is held to beside the pins, and what a row has to be to be taken — and none
     * of those is a way of searching.
     *
     * @param origins what a row may be written against
     * @param admits  the classes each position may stand at beside the pins
     * @param held    the conditions every candidate is held to beside the pins, put together
     *                ({@link #heldTogether}) by whoever holds the row to them: what they ask is
     *                the same of every candidate, and whether it is anything a row can be is what
     *                a caller holding a choice of several asks before it searches
     * @param accepts what a row that holds every pin has to be besides
     * @param answersNothing where the body answers nothing, which no row taken may sit
     */
    private static Searched search(MeasuredInput.MeasuredAxes axes, Pins pins,
                                   List<Purpose> purposes, List<ResolvedOrigin> origins,
                                   Admits admits, CandidateCheck check,
                                   FixtureReferences references, List<StoodInAnswer> answers,
                                   HeldTogether held,
                                   Function<GeneratedRow, Acceptance> accepts,
                                   WhereNothingIsAnswered answersNothing) {
        return search(axes, pins, purposes, origins, admits, check, references, answers, held,
                accepts, false, answersNothing);
    }

    /**
     * The same, and where {@code rechoosing}, a candidate whose row {@code accepts} passes over has
     * its values chosen again before the next candidate is built: what it asks of a row is then
     * not something which classes the row stands at decides.
     */
    private static Searched search(MeasuredInput.MeasuredAxes axes, Pins pins,
                                   List<Purpose> purposes, List<ResolvedOrigin> origins,
                                   Admits admits, CandidateCheck check,
                                   FixtureReferences references, List<StoodInAnswer> answers,
                                   HeldTogether held,
                                   Function<GeneratedRow, Acceptance> accepts,
                                   boolean rechoosing, WhereNothingIsAnswered answersNothing) {
        String label = String.join(" with ", pins.labels());
        // What the pins ask for and nothing else, which is what every other position being free
        // means. Written as a reading, it goes through the same walk a combination's readings do.
        Interpretation reading = pins.reading();
        // Every baseline the module states rather than the one this compiler picked. Narrowed to
        // the only value of a type, a module that states a second one lost the spread from every
        // row of every behavior taking it — a change somewhere else in the file, answering a
        // question nobody asked it. What order they are walked in is {@link #nearestFirst}'s to
        // say; how many of them may be built is this class's own budget.
        Building building = new Building(axes, pins, purposes, label, check, MOST_REPAIRS,
                references, answers, held, accepts, rechoosing, answersNothing);
        WhatEachClassRequires requires = new WhatEachClassRequires(axes.axes());
        Traversal stated = nearestFirst(requires, reading, origins, admits, building);
        if (stated == Traversal.SATISFIED) {
            return new Searched(building.found, building.foundAt, building.foundAgainst, null,
                    false, List.of());
        }
        // The composition, whatever the stated values spent, and with a budget of its own.
        Building composing = new Building(axes, pins, purposes, label, check, MOST_REPAIRS,
                references, answers, held, accepts, rechoosing, answersNothing);
        Traversal composed = composing(requires, reading, origins, admits, composing);
        if (composed == Traversal.SATISFIED) {
            return new Searched(composing.found, composing.foundAt, composing.foundAgainst, null,
                    false, List.of());
        }
        // What the walks came to, added up the way a combination's readings are. What is pinned
        // is one reading — a class apiece at the positions the requirement names — so what is left
        // to say is whether either walk was stopped in front of work nobody did.
        Completeness looked = building.tried() == 0 && composing.tried() == 0
                ? Completeness.NOTHING_YET : Completeness.NOTHING_YET.searched();
        if (stated == Traversal.STOPPED || composed == Traversal.STOPPED) {
            looked = looked.cutShort();
        }
        Attempt last = composing.last == null ? building.last : composing.last;
        // What both walks found out over every candidate, and not what the candidate whose word
        // was taken found out. Which walk the word came from is settled by which ran last and which
        // candidate by which got furthest; a figure is something a walk ran into, and it is a
        // number somebody can raise whichever candidate was in front of it — and an offer short of
        // a rule is a rule somebody can rewrite, whichever candidate it was offered to.
        SearchShortfall found = building.foundOut.and(composing.foundOut);
        // Handed on in the word for what was found out, with it beside the word
        // ({@link SearchShortfall#published}): a candidate turned away under one origin is the
        // class's to say whichever candidate the word came from.
        CameToNothing came = switch (looked.found()) {
            // Nothing to try: the class cannot stand at its own position beside what the position
            // itself requires, under any origin. Which is the model not having this row rather than
            // a search that failed to find it.
            case Completeness.Nothing.NO_READING -> found.published(pins.labels(),
                    UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH, null,
                    Optional.of("nothing these classes can stand beside was left to try"));
            // The search stopped in front of a candidate it did not build. Said so whatever the ones
            // it did build came to: the refusal of the sixty-fourth is a fact about that candidate,
            // and offered as the class's answer it stands for a space the search never entered.
            case Completeness.Nothing.SEARCH_STOPPED -> found.published(pins.labels(),
                    UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED, null,
                    Optional.empty());
            // What one combination came to, which is what this says and all it says. A search for
            // a requirement runs at a combination of classes and the word below is that
            // combination's — so what a reader may take from it is that this compiler composed
            // nothing, and never that the rules leave nothing: another combination of the same
            // requirement goes on admitting values, and which one ran last is the order the walk
            // happened to take.
            case Completeness.Nothing.LOOKED_EVERYWHERE -> last == null
                    ? found.published(pins.labels(),
                            UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED, null,
                            Optional.empty())
                    : found.published(pins.labels(), last.reason(), last.detail(), last.said());
        };
        Set<Figure> boundsReached = new HashSet<>(building.boundsReached);
        boundsReached.addAll(composing.boundsReached);
        return new Searched(null, null, Set.of(), came,
                looked.found() == Completeness.Nothing.SEARCH_STOPPED
                        || !found.met().figures().isEmpty(), Figure.inOrder(boundsReached));
    }

    /**
     * Building the candidates offered for one class, up to what this class may spend.
     *
     * <p>What it costs to try a candidate here is one build, so that is what is counted. A candidate
     * no baseline can be written for costs nothing and is not counted: it is a way of writing a row
     * that this origin does not have, and the budget is over the rows built rather than over the
     * walk.
     *
     * <p>The bound is refused in front of the candidate rather than taken after it. A consumer that
     * did exactly as many as it was allowed and then reported having stopped said a candidate was
     * left where none was ({@link Traversal}).
     */
    private static final class Building implements TakingCandidates {

        // The row this walk was for, once one lands in the class. Read where the walk says it was
        // satisfied and nowhere else: a walk that stopped and a walk that finished are two answers
        // now, and reading a field to tell them apart is what having three of them is for.

        private final MeasuredInput.MeasuredAxes axes;

        private final Pins pins;

        private final List<Purpose> purposes;

        private final String label;

        private final CandidateCheck check;

        private final int most;

        /** What the last candidate that composed nothing came to. */
        private Attempt last;

        /**
         * What every candidate found out, and not what the last of them found out.
         *
         * <p>Beside {@code last} rather than read off it. The word a search comes back with is one
         * candidate's — the one that got furthest, which is the last that was tried — while a
         * figure, or an offer short of a rule, is something this walk ran into, and it went on being
         * true of the walk after the candidate that met it was replaced. Read off the last
         * candidate, a figure the first one reached is a number that would have let the walk go on
         * and that nobody is told about, and an offer it was short of is a search said to have had
         * everything.
         */
        private SearchShortfall foundOut = SearchShortfall.NONE;

        /** How many were built, which is what this is allowed so many of. */
        private int builds;

        /** How many were turned away before being built, for the classes leaving no room. */
        private int turnedAway;

        /** How many candidates were tried at all, built or turned away. */
        int tried() {
            return builds + turnedAway;
        }

        /** The figure this walk stopped at where it ran out of builds, as it stood there. */
        private final Set<Figure> boundsReached = new HashSet<>();

        /** What this has seen come of one parameter's value, which the walk leaves out. */
        private final ParameterProjections known;

        /** The row, once one lands in the class. */
        private GeneratedRow found;

        /** The candidate the row was built from, once there is one. */
        private Candidate foundAt;

        /** The parameters the row writes as the value the origin states, once there is one. */
        private Set<String> foundAgainst;

        /** The run's minter for the references what this composes will hold. */
        private final FixtureReferences references;

        /** What every row of this behavior stands its dependencies in with. */
        private final List<StoodInAnswer> answers;

        /**
         * The comparisons every candidate is held to beside the pins, put together once. What they
         * ask is the same of every candidate, and putting them together places the positions the
         * way to them bounds, which is a search of its own.
         */
        private final HeldTogether held;

        /** What a row that holds every pin has to be besides, to be the one this takes. */
        private final Function<GeneratedRow, Acceptance> accepts;

        /** Whether a candidate whose row is passed over has its values chosen again before the
         *  next candidate is built. */
        private final boolean rechoosing;

        /** Where the body answers nothing, which no row this takes may sit. */
        private final WhereNothingIsAnswered answersNothing;

        private Building(MeasuredInput.MeasuredAxes axes, Pins pins, List<Purpose> purposes,
                         String label, CandidateCheck check, int most,
                         FixtureReferences references, List<StoodInAnswer> answers,
                         HeldTogether held, Function<GeneratedRow, Acceptance> accepts,
                         boolean rechoosing, WhereNothingIsAnswered answersNothing) {
            this.rechoosing = rechoosing;
            this.answersNothing = answersNothing;
            this.axes = axes;
            this.pins = pins;
            this.purposes = purposes;
            this.label = label;
            this.check = check;
            this.most = most;
            this.references = references;
            this.answers = answers;
            this.held = held;
            this.accepts = accepts;
            this.known = new ParameterProjections(axes);
        }

        @Override
        public ParameterProjections known() {
            return known;
        }

        @Override
        public void reached(Figure figure) {
            boundsReached.add(figure);
        }

        @Override
        public Taken take(Candidate candidate) {
            Map<String, Written> given = candidate.from().writtenAgainst(axes,
                    candidate.delta(), candidate.where(), references);
            known.written(candidate, given);
            if (!candidate.from().composes() && given.isEmpty()) {
                return Taken.AND_MORE;   // nothing here can be written against the model's value
            }
            // What composing it would find out first, found out without building it. A candidate
            // whose classes leave what the row is held to no room is one nothing can be built
            // from, and what a search is allowed to build is not spent on it.
            Attempt noRoom = classesLeaveNoRoom(axes, candidate.where(), held);
            if (noRoom != null) {
                turnedAway++;
                foundOut = foundOut.and(noRoom.found());
                last = noRoom;
                return Taken.AND_MORE;
            }
            if (builds >= most) {
                boundsReached.add(buildsReached());
                return Taken.NOT_TAKEN;   // this candidate is the work nobody did
            }
            builds++;
            if (rechoosing) {
                return rechoosing(candidate, given);
            }
            Attempt made = build(axes, candidate.where(), held, check, given, answers);
            known.built(candidate, made);
            foundOut = foundOut.and(made.found());
            if (made.row() == null) {
                last = made;
                return Taken.AND_MORE;
            }
            // Every pin, and the values are what says so. What a row was steered towards is the
            // reading that produced the candidate; where it landed is what the classifier answers,
            // and a row certified on the first of two pins is a row that fills half a requirement.
            if (!pins.holds(axes, made.row().inputs(), check)) {
                last = new Attempt(null, UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, label,
                        Optional.empty());
                return Taken.AND_MORE;
            }
            // And nowhere the body answers nothing, whatever the pins are: a row there reaches an
            // `unreachable` and the compiler refuses it, so it is no row to hand anybody. Another
            // candidate may hold the pins somewhere else.
            if (answersNothingAt(answersNothing, axes, candidate.where(), made.row().inputs(),
                    check)) {
                last = new Attempt(null,
                        UnresolvedCombination.Reason.EVERY_ROW_THERE_REACHES_AN_UNREACHABLE, label,
                        Optional.empty());
                return Taken.AND_MORE;
            }
            GeneratedRow row = new GeneratedRow(purposes, made.row().inputs(), made.row().answers());
            return switch (accepts.apply(row)) {
                case TAKEN -> {
                    found = row;
                    foundAt = candidate;
                    foundAgainst = Set.copyOf(given.keySet());
                    yield Taken.AND_DONE;
                }
                case PASSED -> Taken.AND_MORE;
                // What deciding cost ran out in front of this row, which is the work nobody did.
                case STOPPED -> Taken.NOT_TAKEN;
            };
        }

        /** How many candidates this walk may build, as it stood where the walk ran out of them. */
        private Figure buildsReached() {
            return WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(most);
        }

        /**
         * One candidate, its values chosen again until a row holding every pin is one
         * {@link #accepts} takes. A row outside a pin is passed over the way one the caller passes
         * over is, since another choice of values may land inside it.
         *
         * <p>Every row composed after the candidate's first is a build of its own, counted against
         * the same figure the candidates are. Choosing again walks every assignment of every
         * parameter against every one of the others, which multiplies; uncounted, one candidate
         * could cost more than every other candidate of the search together.
         */
        private Taken rechoosing(Candidate candidate, Map<String, Written> given) {
            boolean[] first = {true};
            RowComposed came = composed(axes, candidate.where(), held, check, given, inputs -> {
                if (!first[0]) {
                    if (builds >= most) {
                        boundsReached.add(buildsReached());
                        return Acceptance.STOPPED;   // the rows past here are the work nobody did
                    }
                    builds++;
                }
                first[0] = false;
                if (!pins.holds(axes, inputs, check)) {
                    return Acceptance.PASSED;
                }
                if (answersNothingAt(answersNothing, axes, candidate.where(), inputs, check)) {
                    return Acceptance.PASSED;
                }
                GeneratedRow row = new GeneratedRow(purposes, inputs, answers);
                Acceptance asked = accepts.apply(row);
                if (asked == Acceptance.TAKEN) {
                    found = row;
                    foundAt = candidate;
                    foundAgainst = Set.copyOf(given.keySet());
                }
                return asked;
            });
            return switch (came) {
                case RowComposed.Taken _ -> Taken.AND_DONE;
                // Not a refusal, and what the walk found out on the way to the rows passed over is
                // found out all the same: a figure it stopped at, or an offer a way beside them was
                // short of, is a row the search may yet have.
                case RowComposed.PassedOver(SearchShortfall its) -> {
                    foundOut = foundOut.and(its);
                    yield Taken.AND_MORE;
                }
                case RowComposed.Halted _ -> Taken.NOT_TAKEN;
                case RowComposed.Failed(Attempt why, var _) -> {
                    known.built(candidate, why);
                    foundOut = foundOut.and(why.found());
                    last = why;
                    yield Taken.AND_MORE;
                }
            };
        }
    }

    /**
     * A value the module states, with where its own values already sit read off once.
     *
     * <p>Read once for the generation and never once per class. Where a baseline's values fall is a
     * fact about the module, and asking it again for every class owed is the same walk through the
     * decoders for the same answer.
     *
     * <p><b>Two origins standing alike are still two origins.</b> Where a row's values sit is what
     * orders this search; what those values are is what the model builds and what a rule relating
     * two of them accepts. So the same classes reached from two values of the module are two
     * candidates and not one, and a search that dropped the second answered a class it could have
     * written a row for.
     *
     * @param origin  what the module states, or the composition where the row is composed from the
     *                classes
     * @param stands  where the origin's own values already sit, which is what a move is measured
     *                against and what a spread writes over
     * @param index   where this came in the order the origins were gathered, which is what orders
     *                two origins one distance away
     */
    private record ResolvedOrigin(Origin origin, int[] stands, int index) {

        /** What a row is written against: values the module states, or nothing at all. */
        private sealed interface Origin {

            /** Values the module states, by the parameter each is of. */
            record Stated(Baseline baseline) implements Origin {}

            /** No value: the row is composed from the classes alone. */
            record Composition() implements Origin {}
        }

        /** Whether this is the composition rather than a value the module states. */
        boolean composes() {
            return origin instanceof Origin.Composition;
        }

        /** Whether this states a value for {@code parameter}, which it then writes where it can. */
        boolean states(String parameter) {
            return origin instanceof Origin.Stated stated
                    && stated.baseline().at().get(parameter) != null;
        }

        /**
         * The parameters of a row this writes as the value the module states, each as the name it
         * is written under, for the assignment {@code where} reached from {@code delta}. Nothing for
         * the composition, which writes no parameter that way.
         */
        Map<String, Written> writtenAgainst(MeasuredInput.MeasuredAxes axes, Delta delta,
                                            int[] where, FixtureReferences references) {
            return switch (origin) {
                case Origin.Stated stated ->
                        against(axes, delta, where, stated.baseline(), references);
                case Origin.Composition _ -> Map.of();
            };
        }

        /**
         * How much of what a demand is about this states a value of.
         *
         * <p>By the parameters and not by the positions. Two positions under one parameter are two
         * things a demand may be about and one value an origin can state, and an origin counted
         * once per position would be twice as grounded for a demand over two fields of one record
         * as for one over two records.
         */
        int grounding(Set<String> asked) {
            if (!(origin instanceof Origin.Stated stated)) {
                return 0;
            }
            int out = 0;
            for (String head : asked) {
                if (stated.baseline().at().containsKey(head)) {
                    out++;
                }
            }
            return out;
        }
    }

    /**
     * One assignment to try, and the origin it is a move away from.
     *
     * <p>The distance is a fact about the pair and travels with it. Worked out again where the row
     * is written, the order the search went in and the row that came out of it were two readings of
     * one thing.
     *
     * @param from  the origin this row is written against
     * @param where the classes this assignment puts every position at
     * @param delta where {@code where} does not stand where {@code from} does
     */
    private record Candidate(ResolvedOrigin from, int[] where, Delta delta) {}

    /**
     * A consumer of candidates, and what it has seen come of one parameter's value.
     *
     * <p>The walk reads the second, and only to leave out what the consumer would pass over again:
     * a candidate it would build and see come to nothing again, or one against an origin it could
     * not write again. What a candidate costs stays the consumer's to say: one left out was not
     * built, so neither a class nor an arm paid anything for it.
     */
    private interface TakingCandidates extends Taking<Candidate> {

        ParameterProjections known();

        /** Takes in that the walk stopped at {@code figure}, in front of work nobody did. */
        void reached(Figure figure);
    }

    /**
     * What came of one parameter's value, by the classes standing under that parameter, for one
     * consumer's walk: where building it came to nothing, and where an origin could not write it.
     *
     * <p>Came to nothing and not refused. What building one parameter's value comes to is the
     * model refusing it, or this compiler's search for it stopping short or finding nothing to
     * offer — and those are different news to a reader. What is kept here is what they share:
     * building the same value again would come to the same thing.
     *
     * <p>A parameter's value is built from what stands under it and from nothing else: the classes
     * of its own positions, and what an origin writes for it, which is the origin's value with the
     * fields under it moved ({@link #valueFor}, {@link #against}). So what became of it is what
     * becomes of it in every assignment that leaves those the same, whatever the other parameters'
     * positions do. Asked again for each of their moves, one answer is worked out once per
     * assignment of theirs — a number that doubles with every field beside it, while what is asked
     * stays the same.
     *
     * <p>Kept per origin, because what an origin writes for a parameter is its own value.
     *
     * <p>Not a claim that those classes hold no value together. Another value of the same classes
     * may be built where this one was not; what is known is only that this walk would build this
     * one again and have it come to nothing again.
     *
     * <p>Which axes are under a parameter is read off the head of the axis's path, and that is the
     * whole of what reaches the parameter's value: what a position requires is on its own path, and
     * every class of an axis is of the axis's own number ({@link Axis}). A language that let a
     * position under one parameter decide another's value would leave this keyed by too little.
     */
    private static final class ParameterProjections {

        private final List<String> parameters;

        /** The axes under each parameter. */
        private final int[][] under;

        private final Set<Projection> cameToNothing = new HashSet<>();

        /** The parameters something came to nothing at, under any origin. */
        private final Set<Integer> cameToNothingOf = new LinkedHashSet<>();

        /** Where an origin that states a parameter could not write it. */
        private final Set<Projection> unwritten = new HashSet<>();

        /** One parameter's classes, against one origin. */
        private record Projection(int origin, int parameter, List<Integer> classes) {}

        ParameterProjections(MeasuredInput.MeasuredAxes axes) {
            parameters = axes.subject().parameters();
            List<List<Integer>> found = new ArrayList<>();
            for (int p = 0; p < parameters.size(); p++) {
                found.add(new ArrayList<>());
            }
            for (int i = 0; i < axes.size(); i++) {
                int own = parameters.indexOf(axes.get(i).path().head());
                if (own < 0) {
                    throw new IllegalStateException("`" + axes.get(i).id() + "` is under no"
                            + " parameter of the behavior it divides");
                }
                found.get(own).add(i);
            }
            under = new int[parameters.size()][];
            for (int p = 0; p < parameters.size(); p++) {
                under[p] = found.get(p).stream().mapToInt(Integer::intValue).toArray();
            }
        }

        /** Takes in which of the parameters it states the candidate's origin could not write. */
        void written(Candidate candidate, Map<String, Written> given) {
            ResolvedOrigin origin = candidate.from();
            for (int p = 0; p < parameters.size(); p++) {
                if (origin.states(parameters.get(p)) && !given.containsKey(parameters.get(p))) {
                    unwritten.add(projection(origin.index(), p, candidate.where()));
                }
            }
        }

        /** Takes in what building the candidate came to, where it is one parameter's alone. */
        void built(Candidate candidate, Attempt made) {
            if (made.row() != null || made.localTo().isEmpty()) {
                return;
            }
            int p = made.localTo().getAsInt();
            cameToNothing.add(projection(candidate.from().index(), p, candidate.where()));
            cameToNothingOf.add(p);
        }

        /** Whether the consumer would pass over {@code where} against this origin again. */
        boolean leavesOut(ResolvedOrigin origin, int[] where) {
            for (int p : cameToNothingOf) {
                if (cameToNothingAt(origin, p, where)) {
                    return true;
                }
            }
            return writesNothing(origin, where);
        }

        /**
         * Where one walk that decides {@code steps} in turn against {@code origin} settles each
         * parameter, so that it can stop under a step past which everything it would produce is
         * left out.
         */
        Settling settling(ResolvedOrigin origin, int[] steps) {
            int[] last = new int[parameters.size()];
            int stated = -1;
            for (int p = 0; p < parameters.size(); p++) {
                last[p] = -1;
                for (int j = 0; j < steps.length; j++) {
                    for (int axis : under[p]) {
                        if (steps[j] == axis) {
                            last[p] = j;
                        }
                    }
                }
                if (origin.states(parameters.get(p))) {
                    stated = Math.max(stated, last[p]);
                }
            }
            return new Settling(origin, last, stated);
        }

        /**
         * One walk's steps, by the parameter each settles.
         *
         * <p>Asked at the step a parameter settles and not below it. What was asked further up
         * does not change further down, because nothing is learned while a walk is producing
         * what it hands over.
         *
         * @param last   the last step that decides a position under each parameter, or -1 where
         *               none does
         * @param stated the last step that decides a position under a parameter the origin states
         */
        record Settling(ResolvedOrigin origin, int[] last, int stated) {}

        /** Whether nothing under the step {@code filled} of a walk is anything but left out. */
        boolean leavesOut(Settling settling, int[] where, int filled) {
            for (int p : cameToNothingOf) {
                if (settling.last()[p] == filled - 1
                        && cameToNothingAt(settling.origin(), p, where)) {
                    return true;
                }
            }
            return settling.stated() == filled - 1 && writesNothing(settling.origin(), where);
        }

        private boolean cameToNothingAt(ResolvedOrigin origin, int p, int[] where) {
            return cameToNothing.contains(projection(origin.index(), p, where));
        }

        /** Whether {@code origin} is one that writes a value and can write none of them here. */
        private boolean writesNothing(ResolvedOrigin origin, int[] where) {
            if (origin.composes()) {
                return false;
            }
            for (int p = 0; p < parameters.size(); p++) {
                if (origin.states(parameters.get(p))
                        && !unwritten.contains(projection(origin.index(), p, where))) {
                    return false;
                }
            }
            return true;
        }

        private Projection projection(int origin, int p, int[] where) {
            return new Projection(origin, p, classes(p, where));
        }

        private List<Integer> classes(int parameter, int[] where) {
            List<Integer> out = new ArrayList<>(under[parameter].length);
            for (int axis : under[parameter]) {
                out.add(where[axis]);
            }
            return out;
        }
    }

    /**
     * Whether the classes of one assignment can stand together, kept as the assignment moves one
     * position at a time.
     *
     * <p>Two classes cannot stand together exactly where they leave one position no case in common,
     * which is what merging their requirements asks ({@link Requirements#merge}). Kept by position
     * instead of merged again from nothing, so moving one position costs that position's
     * requirements and not every position's: a position is asked again only where what is asked
     * of it changed.
     */
    private static final class StandingTogether implements NearestAssignments.Together {

        private final WhatEachClassRequires requires;

        /** What each position is asked to be, by how many of the classes standing ask it. */
        private final Map<TermPath, Map<CasesLeft, Integer>> asked = new HashMap<>();

        /** The positions the classes standing leave no case in common. */
        private final Set<TermPath> disagreeing = new HashSet<>();

        /** The positions the walk may move, which are the only ones it stands again with a case. */
        private final boolean[] movable;

        StandingTogether(WhatEachClassRequires requires, int[] where, int[] steps) {
            this.requires = requires;
            this.movable = new boolean[requires.axes.size()];
            for (int step : steps) {
                movable[step] = true;
            }
            for (int i = 0; i < requires.axes.size() && i < where.length; i++) {
                if (where[i] != NOT_HERE) {
                    add(i, where[i]);
                }
            }
        }

        /**
         * Moving a case of a sum is the row being another case: the positions under the case it
         * left stand at no class, and the ones under the case it enters stand at the first class
         * that can be beside the rest, as {@link #standing} stands them.
         */
        @Override
        public List<int[]> carry(int[] where, int axis, int from, int to) {
            if (requires.of(axis, from).equals(requires.of(axis, to))) {
                return List.of();
            }
            List<Axis> axes = requires.axes;
            Requirements leaving = axes.get(axis).requiring(axes.get(axis).classes().get(from));
            Requirements entering = axes.get(axis).requiring(axes.get(axis).classes().get(to));
            List<int[]> changed = new ArrayList<>();
            // Out from under the case left first, so that what is put under the one entered is
            // asked beside the row as it now is.
            for (int j = axis + 1; j < where.length; j++) {
                if (movable[j] && where[j] != NOT_HERE
                        && !axes.get(j).requirements().compatibleWith(entering)) {
                    changed.add(new int[] {j, where[j]});
                    remove(j, where[j]);
                    where[j] = NOT_HERE;
                }
            }
            for (int j = axis + 1; j < where.length; j++) {
                Requirements own = axes.get(j).requirements();
                if (!movable[j] || where[j] != NOT_HERE || own.compatibleWith(leaving)
                        || !own.compatibleWith(entering)) {
                    continue;
                }
                int here = j;
                int cls = standingAt(axes.get(j), c -> admits(here, c)
                        && !leavesNoRoomBeside(requires, where, here, c));
                if (cls != NOT_HERE) {
                    changed.add(new int[] {j, NOT_HERE});
                    add(j, cls);
                    where[j] = cls;
                }
            }
            return changed;
        }

        @Override
        public void restore(int[] where, List<int[]> changed) {
            for (int i = changed.size() - 1; i >= 0; i--) {
                int[] one = changed.get(i);
                if (where[one[0]] != NOT_HERE) {
                    remove(one[0], where[one[0]]);
                }
                if (one[1] != NOT_HERE) {
                    add(one[0], one[1]);
                }
                where[one[0]] = one[1];
            }
        }

        /** Moves {@code axis} from the class {@code from} to the class {@code to}. */
        @Override
        public void move(int axis, int from, int to) {
            remove(axis, from);
            add(axis, to);
        }

        @Override
        public boolean holds() {
            return disagreeing.isEmpty();
        }

        /** Whether {@code axis}, at no class now, can stand at {@code cls} beside the rest. */
        boolean admits(int axis, int cls) {
            add(axis, cls);
            boolean holds = holds();
            remove(axis, cls);
            return holds;
        }

        private void add(int axis, int cls) {
            for (Map.Entry<TermPath, CasesLeft> each : requires.of(axis, cls).entrySet()) {
                Map<CasesLeft, Integer> here =
                        asked.computeIfAbsent(each.getKey(), _ -> new HashMap<>());
                if (here.merge(each.getValue(), 1, Integer::sum) == 1) {
                    reask(each.getKey(), here);
                }
            }
        }

        private void remove(int axis, int cls) {
            for (Map.Entry<TermPath, CasesLeft> each : requires.of(axis, cls).entrySet()) {
                Map<CasesLeft, Integer> here = asked.get(each.getKey());
                if (here.merge(each.getValue(), -1, Integer::sum) == 0) {
                    here.remove(each.getValue());
                    reask(each.getKey(), here);
                }
                if (here.isEmpty()) {
                    asked.remove(each.getKey());
                }
            }
        }

        /** Whether what is asked of {@code at} still leaves it a case, after it changed. */
        private void reask(TermPath at, Map<CasesLeft, Integer> here) {
            Iterator<CasesLeft> each = here.keySet().iterator();
            CasesLeft common = each.hasNext() ? each.next() : null;
            while (common != null && each.hasNext()) {
                common = common.meet(each.next());
            }
            if (!here.isEmpty() && common == null) {
                disagreeing.add(at);
            } else {
                disagreeing.remove(at);
            }
        }
    }

    /**
     * What each class of each position requires of the row, read once for a walk.
     *
     * <p>A walk moves the same few positions through the same classes over and over. What a class
     * requires does not change with where the rest of the row stands, and reading it is most of
     * what a move costs.
     */
    private static final class WhatEachClassRequires {

        private final List<Axis> axes;

        private final List<List<Map<TermPath, CasesLeft>>> read = new ArrayList<>();

        /** What the pair space says of two classes beside their requirements. */
        private final ClassCoexistence coexistence;

        WhatEachClassRequires(List<Axis> axes) {
            this.axes = axes;
            for (Axis axis : axes) {
                read.add(new ArrayList<>(Collections.nCopies(axis.classes().size(), null)));
            }
            this.coexistence = ClassCoexistence.among(axes);
        }

        /** What standing {@code axis} at its class {@code cls} requires. */
        Map<TermPath, CasesLeft> of(int axis, int cls) {
            Map<TermPath, CasesLeft> known = read.get(axis).get(cls);
            if (known == null) {
                known = axes.get(axis).requiring(axes.get(axis).classes().get(cls)).refinements();
                read.get(axis).set(cls, known);
            }
            return known;
        }

        /**
         * Whether a row at the {@code one}th position's class {@code here} and the {@code other}th
         * position's class {@code there} is no row, because one of the two leaves the container
         * the other stands inside nothing to hold. The rest of what {@link ClassCoexistence} says
         * beside the requirements {@link #of} reads.
         */
        boolean leaveNoRoom(int one, int here, int other, int there) {
            return coexistence.leavesNoRoom(one, here, other, there);
        }
    }

    /**
     * The assignments written against a value the module states, nearest first, one at a time.
     *
     * <p>Handed over rather than handed back. What a walk may cost is a fact about whoever is paying
     * — a class counts what it builds, an arm counts what it runs, and a candidate the model refuses
     * costs neither of them anything — so the bound belongs to the consumer and the order belongs
     * here. Bounded here instead, one number stood for two kinds of work, and the arm was held to
     * the class's.
     *
     * <p><b>How much of what the demand is about the origin states, before anything else.</b> A row
     * for a class of {@code to} written against a value of {@code from} has {@code to} composed from
     * its classes like any other position — so it is not that value with one field moved, which is
     * the thing this exists to offer. It is a row with a recognisable value somewhere else, worth
     * offering after every origin that grounds what the row is about and not among them. A demand
     * over several positions is grounded by degrees, and the origins that state more of them come
     * first.
     *
     * <p>Not a tie-break inside a distance. An origin that does not name the position is measured
     * against a tuple partly of the search's own making — {@link #stands} fills what the origin
     * says nothing about from the classes, and what is filled that way sits at distance zero by
     * construction. So the ungrounded origin arrived as a nearest one and won, and the value the
     * model states of the position the row is about went untried.
     *
     * <p><b>Then distance, among the values the model states.</b> How far a row moves from the
     * value it is written against is what this is minimising, so every baseline is tried at what
     * the demand asks for alone before any is tried with a supporting field moved. Within one
     * distance the origins keep the order they were gathered in, which puts a value the author's
     * own rows name before one the module merely states — the whole of one origin's moves at that
     * distance before the next origin's. Ordered with the supporting sets outside the origins,
     * provenance decided only which origin won a given set of supporting positions, and a later
     * origin that happened to repair on an earlier set beat an earlier origin that repaired on a
     * later one.
     */
    private static Traversal nearestFirst(WhatEachClassRequires requires, Interpretation reading,
                                          List<ResolvedOrigin> origins, Admits admits,
                                          TakingCandidates taking) {
        List<Axis> axes = requires.axes;
        int[] about = about(axes, reading);
        Set<String> asked = reading.heads(axes);
        // One count of looks for every group of origins: a walk that was divided between them
        // would be allowed what each is, and not what all of them are.
        NearestAssignments.Looks looks = new NearestAssignments.Looks(MOST_LOOKS);
        // The origins that state most of what the demand is about, whole and at every distance,
        // before any that state less of it.
        for (int grounds = asked.size(); grounds >= 0; grounds--) {
            List<ResolvedOrigin> here = new ArrayList<>();
            for (ResolvedOrigin origin : origins) {
                if (!origin.composes() && origin.grounding(asked) == grounds) {
                    here.add(origin);
                }
            }
            if (here.isEmpty()) {
                continue;
            }
            Traversal walked = gather(requires, reading, about, here, admits, looks, taking);
            if (walked != Traversal.EXHAUSTED) {
                return walked;
            }
        }
        return Traversal.EXHAUSTED;
    }

    /**
     * The assignments composed from the classes, for a consumer none of the stated ones answered.
     *
     * <p><b>Its own walk and not the tail of the other one.</b> A composed row is not a nearer
     * baseline: its distance is measured from values the search itself named, so it is zero by
     * construction and says nothing about how far the row is from what a reader recognises. Put in
     * the same order, a row composed from the classes won against every baseline that needed one
     * supporting field — which is the objective read backwards.
     *
     * <p>And walked whatever the stated values spent. It is not one of them and was not competing
     * with them for what they may cost, so a consumer that walked one list until its own bound ran
     * out never reached it — which is what left a class the model can hold a row for saying the
     * search had stopped.
     */
    private static Traversal composing(WhatEachClassRequires requires, Interpretation reading,
                                       List<ResolvedOrigin> origins, Admits admits,
                                       TakingCandidates taking) {
        int[] about = about(requires.axes, reading);
        NearestAssignments.Looks looks = new NearestAssignments.Looks(MOST_LOOKS);
        for (ResolvedOrigin origin : origins) {
            if (!origin.composes()) {
                continue;
            }
            Traversal walked = gather(requires, reading, about, List.of(origin), admits, looks,
                    taking);
            if (walked != Traversal.EXHAUSTED) {
                return walked;
            }
        }
        return Traversal.EXHAUSTED;
    }

    /**
     * Every assignment these origins offer for one reading, nearest first, handed to
     * {@code taking}.
     *
     * <p>Walked by the distance the assignment comes to, and not by how many positions it moves,
     * which are two numbers: the base a walk starts from differs from the origin where the reading
     * settled a position, and a position moved back to where the origin stands brings the
     * assignment nearer. Each distance is asked of every origin in turn
     * ({@link NearestAssignments}), and an assignment is handed over as it stands, so nothing is
     * held while a distance waits to be reached.
     *
     * <p>Held to {@code looks}, the work of finding assignments, which the consumer's own bound
     * never sees where it passes over what it is handed for nothing. Out of them, the walk stops
     * and says so: the assignments past that point are work nobody did.
     */
    private static Traversal gather(WhatEachClassRequires requires, Interpretation reading,
                                    int[] about, List<ResolvedOrigin> origins, Admits admits,
                                    NearestAssignments.Looks looks, TakingCandidates taking) {
        List<Axis> axes = requires.axes;
        // What the demand asks for settled first, and each origin's own classes kept at every
        // position that can keep them beside it. Worked out once per origin: it is where that
        // origin's walk starts from and does not change with how far the walk has gone.
        List<Started> bases = new ArrayList<>();
        for (ResolvedOrigin origin : origins) {
            int[] base = standing(requires, wanting(axes, origin.stands(), reading), about,
                    admits);
            if (base != null) {
                bases.add(new Started(origin, base));   // null is this reading not being one value
            }
        }
        bases.sort(Comparator.comparingInt(started -> started.from().index()));
        int[] classes = new int[axes.size()];
        for (int i = 0; i < classes.length; i++) {
            classes[i] = axes.get(i).classes().size();
        }
        List<Walking> walks = new ArrayList<>();
        int nearest = Integer.MAX_VALUE;
        int farthest = 0;
        for (Started origin : bases) {
            int[] steps = movable(axes, about, origin.base());
            NearestAssignments walk = new NearestAssignments(origin.from().stands(), origin.base(),
                    steps, classes);
            walks.add(new Walking(origin, steps, walk));
            nearest = Math.min(nearest, walk.nearest());
            farthest = Math.max(farthest, walk.farthest());
        }
        // One distance at a time, and within it one origin's assignments before the next origin's.
        // The assignments are handed to the consumer as they stand, so a consumer that is satisfied
        // or stops leaves everything after unwalked, and nothing waits for its distance to come.
        for (int distance = nearest; distance <= farthest; distance++) {
            for (Walking walking : walks) {
                Traversal walked = visiting(requires, walking, distance, looks, taking);
                if (walked != Traversal.EXHAUSTED) {
                    return walked;
                }
            }
        }
        return Traversal.EXHAUSTED;
    }

    /** One origin's walk, and the positions it moves. */
    private record Walking(Started origin, int[] steps, NearestAssignments walk) {}

    /**
     * Every assignment {@code distance} from one origin, handed to {@code taking} in the order
     * {@link NearestAssignments} walks them.
     *
     * <p>Less what the consumer has come to pass over by the time the assignment stands, which it
     * is asked at that moment: what it learns of one parameter's value from one assignment is
     * what leaves out the next that shares it.
     */
    private static Traversal visiting(WhatEachClassRequires requires, Walking walking,
                                      int distance, NearestAssignments.Looks looks,
                                      TakingCandidates taking) {
        Started origin = walking.origin();
        ParameterProjections known = taking.known();
        ParameterProjections.Settling settling = known.settling(origin.from(), walking.steps());
        Traversal[] result = {Traversal.EXHAUSTED};
        NearestAssignments.Ended ended = walking.walk().visitAt(distance,
                new StandingTogether(requires, origin.base().clone(), walking.steps()),
                (where, from, to) -> {
                    for (int filled = from; filled <= to; filled++) {
                        if (known.leavesOut(settling, where, filled)) {
                            return true;
                        }
                    }
                    return false;
                },
                looks,
                where -> {
                    if (known.leavesOut(origin.from(), where)) {
                        return true;
                    }
                    Candidate candidate = new Candidate(origin.from(), where.clone(),
                            Delta.between(origin.from().stands(), where));
                    switch (taking.take(candidate)) {
                        case NOT_TAKEN -> {
                            result[0] = Traversal.STOPPED;
                            return false;
                        }
                        case AND_DONE -> {
                            result[0] = Traversal.SATISFIED;
                            return false;
                        }
                        case AND_MORE -> { }
                    }
                    return true;
                });
        return switch (ended) {
            case EXHAUSTED -> Traversal.EXHAUSTED;
            case DECLINED -> result[0];
            case OUT_OF_LOOKS -> {
                taking.reached(WorkFigure.ASSIGNMENTS_A_REPAIR_LOOKS_AT.at(MOST_LOOKS));
                yield Traversal.STOPPED;
            }
        };
    }

    /**
     * How many assignments a walk repairing a row looks at, across every distance and every origin
     * of one search.
     *
     * <p>Beside {@link #MOST_REPAIRS} and not in place of it. That bounds what is built, and a
     * candidate the consumer passes over before it builds anything costs it none of it; with the
     * positions of one parameter numbering in the tens and their classes in the hundreds, the
     * assignments there are to pass over are more than any search can look at.
     */
    private static final int MOST_LOOKS = 100_000;

    /**
     * Where one origin's walk for one reading starts: what the reading asks for, and the origin's
     * own classes wherever they can be kept beside it.
     *
     * <p>A pair and not a map keyed by the origin. An origin holds where its values stand, which is
     * an array, and an array's equality is its own — so a map of them works only for as long as
     * every key is the one instance that was put there, and reads as though it worked either way.
     */
    private record Started(ResolvedOrigin from, int[] base) {}

    /**
     * Which positions beside the ones a row is about it may move, in the axes' own order.
     *
     * <p><b>Only the positions the row stands somewhere at.</b> A position at no class of this row
     * is one no assignment over it moves, so counting it among the moved would count fewer positions
     * than it names — and how many were moved is what tells the search how far a candidate is. Left
     * in, a row one position from its origin was offered behind rows two away, and the number the
     * budget was spent by counted what the search reached for rather than what it moved.
     */
    private static int[] movable(List<Axis> axes, int[] about, int[] base) {
        int[] out = new int[axes.size()];
        int n = 0;
        for (int i = 0; i < axes.size(); i++) {
            if (!anchored(about, i) && base[i] != NOT_HERE) {
                out[n++] = i;
            }
        }
        return Arrays.copyOf(out, n);
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
    private static int[] stands(MeasuredInput.MeasuredAxes axes, Baseline baseline,
                                CandidateCheck check, FixtureReferences references) {
        MeasuredInput subject = axes.subject();
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
                    FixtureTemplate.named(named.reachedAs(), references.next()))
                            instanceof CandidateCheck.Built.Value(var value))) {
                return null;
            }
            observed.add(value);
        }
        Map<AxisId, Classification> where = InputClassifications.of(observed, axes);
        int[] out = composes(axes.axes());
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

    /**
     * The origins this generation has, in the order the search tries them.
     *
     * <p>Resolved once for the behavior. Where a baseline's own values sit is read through the same
     * check every candidate goes through, and asking it again for each class owed is that walk done
     * once per class for an answer that does not change with the class.
     *
     * <p>An origin nothing built is left out here, once. A distance measured from a baseline nothing
     * looked at would be measured from a guess.
     *
     * <p>The composition last, and always there. It is not one of the values the model states —
     * where it stands is where the classes put it, which the search itself named — so it is not
     * ordered among them; and it is not a baseline that failed, so nothing the baselines spend takes
     * it away.
     */
    private static List<ResolvedOrigin> resolve(MeasuredInput.MeasuredAxes axes,
                                                List<Baseline> baselines, CandidateCheck check,
                                                FixtureReferences references) {
        List<ResolvedOrigin> out = new ArrayList<>();
        for (Baseline baseline : baselines) {
            int[] stands = stands(axes, baseline, check, references);
            if (stands != null) {
                out.add(new ResolvedOrigin(new ResolvedOrigin.Origin.Stated(baseline), stands,
                        out.size()));
            }
        }
        out.add(new ResolvedOrigin(new ResolvedOrigin.Origin.Composition(), composes(axes.axes()),
                out.size()));
        return List.copyOf(out);
    }

    /** Whether {@code axis} is one of the positions an assignment is about. */
    private static boolean anchored(int[] anchors, int axis) {
        for (int each : anchors) {
            if (each == axis) {
                return true;
            }
        }
        return false;
    }

    /** Where every position stands when a row is composed from the classes alone. */
    private static int[] composes(List<Axis> axes) {
        return standing(new WhatEachClassRequires(axes), null, new int[0]);
    }

    /**
     * Whether a row of {@code inputs}, composed for the classes {@code where}, sits where the body
     * answers nothing.
     *
     * <p>Where the values landed, read off what built them as {@link #inTheClass} reads it — and
     * where nothing built them, the classes they were composed for, which is what the row says of
     * itself. Not "every class", which is what {@code inTheClass} answers for a pin it cannot
     * judge: asked that way, a run with no runtime would put every row in every part and offer
     * none.
     *
     * <p>A position whose values stand in more than one class says nothing: which of them a run
     * goes on with is no class of the row.
     */
    private static boolean answersNothingAt(WhereNothingIsAnswered answersNothing,
                                            MeasuredInput.MeasuredAxes axes, int[] where,
                                            List<FixtureTemplate> inputs, CandidateCheck check) {
        if (answersNothing.regions().isEmpty()) {
            return false;
        }
        List<ObservedValue> observed = new ArrayList<>();
        for (int p = 0; p < inputs.size() && observed != null; p++) {
            if (check.build(p, inputs.get(p)) instanceof CandidateCheck.Built.Value(var value)) {
                observed.add(value);
            } else {
                observed = null;
            }
        }
        Map<AxisId, Classification> landed =
                observed == null ? Map.of() : InputClassifications.of(observed, axes);
        Set<ClassOfAPosition> at = new HashSet<>();
        for (int axis = 0; axis < axes.size(); axis++) {
            AxisId id = axes.get(axis).id();
            if (observed != null) {
                Classification here = landed.get(id);
                if (here != null && here.classIds().size() == 1) {
                    at.add(new ClassOfAPosition(id, here.classIds().iterator().next()));
                }
            } else if (axis < where.length && where[axis] >= 0) {
                at.add(new ClassOfAPosition(id, axes.get(axis).classes().get(where[axis]).id()));
            }
        }
        return !answersNothing.everyRowAt(at).isEmpty();
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
    private static boolean inTheClass(MeasuredInput.MeasuredAxes axes, int at, String classId,
                                      List<FixtureTemplate> inputs, CandidateCheck check) {
        List<souther.compiler.observe.ObservedValue> observed = new ArrayList<>();
        for (int p = 0; p < inputs.size(); p++) {
            if (!(check.build(p, inputs.get(p)) instanceof CandidateCheck.Built.Value(var value))) {
                return true;   // nothing built it, so nothing says where it went
            }
            observed.add(value);
        }
        Classification where =
                InputClassifications.of(observed, axes).get(axes.get(at).id());
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
     * <p><b>Which fields those are is {@link Delta}'s to say and is not worked out again here.</b>
     * How far a row is from its origin is what the search ordered itself by, and which fields a
     * spread writes over is that same difference projected onto the parameters. Counted a second
     * time here, the two were free to disagree: the position the row is about was written out even
     * where the origin already stood in that class, so a row that is the model's own value came out
     * as that value with a field set to what it already held.
     *
     * <p>What a baseline cannot be written for is kept as it was composed, and silently: this is
     * how a row is written and not whether one could be. A position under a field of a field, a
     * class with no value to put there, a value the model refuses beside the
     * rest of the row — each of them leaves that parameter composed from its classes, which is a
     * row that says the same thing in more words.
     */
    private static Map<String, Written> against(MeasuredInput.MeasuredAxes axes,
                                                Delta delta, int[] where,
                                                Baseline baseline,
                                                FixtureReferences references) {
        MeasuredInput subject = axes.subject();
        Map<String, Written> out = new LinkedHashMap<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            String parameter = subject.parameters().get(p);
            Baseline.Named at = baseline.at().get(parameter);
            if (at == null) {
                continue;
            }
            FixtureTemplate named = FixtureTemplate.named(at.reachedAs(), references.next());
            List<Integer> moved = delta.under(axes.axes(), parameter);
            Written written = moved.isEmpty()
                    ? new Written(List.of(new WrittenWay(named,
                            Map.of(TermPath.of(parameter), named))), false)
                    : withPositionsMoved(subject, p, axes.axes(), moved, where, named,
                            references);
            // Left out where the baseline cannot be written for this assignment, which leaves that
            // parameter to be composed from its classes. How a row is written never decides
            // whether the model allows it — the check below asks that of every parameter alike.
            if (written != null) {
                out.put(parameter, written);
            }
        }
        return Map.copyOf(out);
    }

    /**
     * The baseline with the positions this assignment moves under one parameter set to values of
     * the classes it moves them to, or null where this cannot be written.
     *
     * <p>Walked along the paths, one step at a time, and each step written the way the language
     * writes a change at it: a field by a spread over the value it is a field of, and an element by
     * the same edit made to every element ({@link FixtureTemplate#elementWise}). What a path says is
     * where in the value a position is, so a change is written at the place the path names and
     * nothing is said about any other.
     *
     * <p>A field of a field is not written. A spread is over a value a row can name, and the record
     * a field holds is named by nothing — reaching it would mean binding it first, which is a row
     * that names values this has not been asked whether it can name. Nor is a case of a sum, which
     * a spread over the sum does not choose, nor a map's key, which an edit made to every entry
     * would write as one key filed many times. Such a parameter keeps what the classes composed for
     * it, which says the same thing and says it in full.
     *
     * <p><b>Every value of each class, and not its first.</b> A class stands for its values through
     * as many as it offers, because the first can be refused beside the rest of the value where
     * another of the class's own is not — so the baseline is written with each choice of them, the
     * first values first, and the build takes the first the model does not refuse. Written with
     * the first alone, a row the baseline could be written for came back as one this origin had
     * no way to write. How many choices are written is {@link #MAX_TUPLES}, the figure the walk
     * over the values of one parameter is held to, and where it stopped short the answer says so.
     *
     * @param moved which axes under this parameter the row does not stand where the origin does,
     *              read off the one difference the search ordered itself by
     */
    private static Written withPositionsMoved(MeasuredInput subject, int p, List<Axis> axes,
                                              List<Integer> moved, int[] where,
                                              FixtureTemplate baseline,
                                              FixtureReferences references) {
        Moves moves = new Moves();
        LocationWrites writing = new LocationWrites();
        for (int i : moved) {
            Axis axis = axes.get(i);
            // A position the row stands at no class of. It differs from where the origin stands and
            // there is no class to take a value from, so this parameter is one the baseline cannot
            // be written for.
            if (where[i] == NOT_HERE) {
                return null;
            }
            // The class's own values, and only those: a class composed through a constructor is a
            // walk this does not do, and one nothing can produce a value for has nothing to put
            // here.
            if (!(axis.classes().get(where[i]).representatives()
                    instanceof RepresentativeSource.Values values)) {
                return null;
            }
            // A place two of the moved axes are at. The baseline can be written for one of them or
            // for the other, so it writes neither and says the parameter cannot be written — which
            // is what every other thing it cannot do here answers with.
            if (writing.write(axis.path(), values.written())
                    == LocationWrites.Written.CONFLICTING
                    || !moves.put(axis.path(), values.written())) {
                return null;
            }
        }
        List<Moves> leaves = moves.leaves();
        int[] at = new int[leaves.size()];
        List<WrittenWay> ways = new ArrayList<>();
        while (true) {
            if (ways.size() == MAX_TUPLES) {
                return new Written(ways, true);   // a choice is left that was not written
            }
            for (int i = 0; i < leaves.size(); i++) {
                leaves.get(i).choose(at[i]);
            }
            FixtureTemplate way = moves.over(subject, subject.types().get(p), baseline,
                    subject.parameters().get(p), references);
            // What cannot be written is the shape of the moves and not the values chosen, so no
            // other choice writes it either.
            if (way == null) {
                return null;
            }
            // The value at each place a path ends at, where that place is one position: a place
            // under every element of a list is written at each of them, and is no one value.
            Map<TermPath, FixtureTemplate> written = new LinkedHashMap<>();
            written.put(TermPath.of(subject.parameters().get(p)), way);
            for (Moves leaf : leaves) {
                if (!leaf.path.insideAContainer()) {
                    written.put(leaf.path, leaf.chosen);
                }
            }
            ways.add(new WrittenWay(way, written));
            // The last place moved on first, which leaves the first the slowest, the way the
            // assignments a walk over the classes produces are ordered.
            int i = leaves.size() - 1;
            while (i >= 0 && ++at[i] == leaves.get(i).among.size()) {
                at[i] = 0;
                i--;
            }
            if (i < 0) {
                return new Written(ways, false);
            }
        }
    }

    /**
     * The ways one parameter is written against the value the model states, in the order to try
     * them, and whether there were ways left that were not written.
     *
     * <p>The second because a build that tried every way it was handed and had all of them refused
     * has said something about this origin only where it was handed every way there was.
     */
    private record Written(List<WrittenWay> ways, boolean cut) {

        Written {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException("a parameter written is written some way");
            }
        }
    }

    /**
     * One way a parameter is written, and the value it writes at each position it writes one at.
     *
     * <p>The second for where nothing builds the way. A container another parameter holds may be
     * handed the value at one of those positions, and what a position of a value is once built is
     * read off what was built; with nothing to build it, what the way says is all there is. A way
     * written against a value the model states writes that value by name, so what stands at a
     * field it does not move is nothing this says — only the whole value, and each field it moves
     * to a value of a class.
     *
     * @param at the value at each position this way writes one at, the parameter itself among them
     */
    private record WrittenWay(FixtureTemplate value, Map<TermPath, FixtureTemplate> at) {

        WrittenWay {
            at = Map.copyOf(at);
        }
    }

    /**
     * What one parameter's moves are, by the steps of the paths they are at: a value where a path
     * ends, and the moves further along it where it goes on.
     *
     * <p>A tree because the paths are. Two positions under one element are two fields of one
     * record, and they are one edit of each element — written as two, the second would edit the
     * list the first had already rewritten.
     */
    private static final class Moves {

        /** The values a path ending here may move this place to, any of which stands for the class
         *  it moves to, or null where no path ends here. */
        private List<FixtureTemplate> among;

        /** Which of {@link #among} the way being written moves this place to. */
        private FixtureTemplate chosen;

        /** The path that ends here, or null where none does. */
        private TermPath path;

        /** The moves under each field of the record at this place, in the order they were put. */
        private final SequencedMap<String, Moves> fields = new LinkedHashMap<>();

        /** The moves under every element of the list at this place, or null where there are none. */
        private Moves elements;

        /** Puts {@code among} where {@code path} leads, or answers false where that cannot be. */
        boolean put(TermPath path, List<FixtureTemplate> among) {
            Moves at = this;
            for (TermPath.Step step : path.steps()) {
                if (at.among != null) {
                    return false;   // a place already moved whole has nothing further to move
                }
                at = switch (step) {
                    case TermPath.Step.Field field ->
                            at.fields.computeIfAbsent(field.name(), _ -> new Moves());
                    case TermPath.Step.Element _ -> {
                        if (at.elements == null) {
                            at.elements = new Moves();
                        }
                        yield at.elements;
                    }
                    // A value moved under every key of a map is one key written as many times, and
                    // the map those entries make holds one of them.
                    case TermPath.Step.Key _, TermPath.Step.Refine _ -> null;
                };
                if (at == null) {
                    return false;
                }
            }
            if (at.among != null || !at.fields.isEmpty() || at.elements != null) {
                return false;
            }
            at.among = List.copyOf(among);
            at.chosen = at.among.getFirst();
            at.path = path;
            return true;
        }

        /** The places a path ends at, in the order the tree holds them. */
        List<Moves> leaves() {
            List<Moves> out = new ArrayList<>();
            if (among != null) {
                out.add(this);
            }
            fields.values().forEach(each -> out.addAll(each.leaves()));
            if (elements != null) {
                out.addAll(elements.leaves());
            }
            return out;
        }

        /** Moves this place to the {@code index}th of its values in the way written next. */
        void choose(int index) {
            chosen = among.get(index);
        }

        /**
         * {@code base} with these moves written over it, as a value of {@code type}, or null where
         * they cannot be written.
         *
         * @param name what an element is bound as while it is edited, read off the parameter so a
         *             reader of the row sees which value it is
         */
        FixtureTemplate over(MeasuredInput subject, Type type, FixtureTemplate base, String name,
                             FixtureReferences references) {
            if (among != null) {
                return null;   // the whole parameter moved is not a move of the baseline
            }
            if (elements != null) {
                // A list that wears no name, since what a row writes under a name is the name round
                // a value — the same question fieldsOf asks of a record, asked where a position's
                // reading is made.
                if (!fields.isEmpty() || elements.among != null
                        || TypeOps.outermost(type, subject.rules().inners()) != null
                        || !(TypeView.shapeOf(type, subject.rules().inners(), subject.symbols(),
                                subject.rules().kinds(), subject.rules().sums())
                                instanceof Shape.Sequence(Shape.Sequence.Kind kind, Type element))
                        || kind != Shape.Sequence.Kind.LIST) {
                    return null;
                }
                return FixtureTemplate.elementWise(base, name,
                        each -> elements.over(subject, element, each, name + "_", references),
                        references);
            }
            return fieldsOver(subject, type, base);
        }

        /** {@code base} with the fields this moves set, where every one of them ends here. */
        private FixtureTemplate fieldsOver(MeasuredInput subject, Type type, FixtureTemplate base) {
            if (fields.isEmpty()
                    || !(type instanceof Type.Ref(TypeSymbol built))
                    || !(subject.symbols().scope().reach(built)
                            instanceof TypeReachName.Written written)) {
                return null;
            }
            SequencedMap<String, FixtureTemplate> moved = new LinkedHashMap<>();
            for (Map.Entry<String, Moves> field : fields.entrySet()) {
                Moves under = field.getValue();
                if (under.among == null) {
                    return null;   // a field of a field, which this does not write
                }
                moved.put(field.getKey(), under.chosen);
            }
            // Written out rather than spread where the row moves every field the value has. The
            // spread is what says the row is that value with something changed, and a spread whose
            // moved fields cover the whole record says it over a value that contributes nothing —
            // the same row in more words, and a reader comparing it against what the file states
            // finds every field different.
            //
            // The values are the ones this way chose. Composing the parameter again from its
            // classes would be a different row wearing this one's answer: a rule relating two
            // positions can refuse what the classes name while the model's own value builds, which
            // is why the value the model states is where this search starts.
            List<String> declared = fieldsOf(subject, built);
            if (declared != null && moved.keySet().containsAll(declared)) {
                SequencedMap<String, FixtureTemplate> whole = new LinkedHashMap<>();
                for (String field : declared) {
                    whole.put(field, moved.get(field));
                }
                return FixtureTemplate.record(written, whole);
            }
            return FixtureTemplate.spreading(written, base, moved);
        }
    }

    /**
     * The fields a value of {@code built} has, in the order they are written, or null where it is
     * not a record.
     *
     * <p>Every field it has and not the ones its own declaration lists: a record that includes
     * another's fields has those too, and a row that wrote over the listed ones and dropped the
     * spread would drop the included ones with it.
     */
    private static List<String> fieldsOf(MeasuredInput subject, TypeSymbol built) {
        // A value written under a name is not written field by field: what the row writes is the
        // name round a value, and the fields belong to what the name wraps. So the position has to
        // wear no name as well as be a record — read where a position's reading is made, which
        // answers both, rather than walked from the declaration a second time.
        Type position = Type.ref(built);
        return TypeOps.outermost(position, subject.rules().inners()) == null
                        && TypeView.shapeOf(position, subject.rules().inners(), subject.symbols(),
                                subject.rules().kinds(), subject.rules().sums())
                                instanceof Shape.Product(TypeSymbol _,
                                        SequencedMap<String, Type> fields)
                ? List.copyOf(fields.sequencedKeySet()) : null;
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

        /**
         * What the way to the point asked that this could not compose against.
         *
         * <p>Carried out with the answer because it is what the answer was arrived at without. A
         * row composed while a condition above the line was left out may not arrive there, and a
         * search that came back empty may have come back empty over that — so a reader of either
         * gets the same account, and neither is read as though the whole way had been used.
         *
         * <p>Empty is the ordinary case and says so: every condition the walk stated was one this
         * put a value under.
         */
        CompositionAccount unrepresented();

        /**
         * Whether this is a search that came to no row and left something unlooked at: stopped by
         * a figure or a plan, or saying in its word or its offer that candidates were not all
         * looked at. A row built is not one, and neither is a search that proved nothing could
         * stand there or whose candidates were all refused.
         *
         * <p>Read from what each shape says, and never from the shape alone: an {@code Unresolved}
         * is the word a search came back with, and whether that word is a search that looked at
         * everything is the word's to say ({@link UnresolvedCombination.Reason#leavesSomethingUntried}).
         */
        default boolean stoppedShort() {
            return switch (this) {
                case BoundaryAttempt.Built _ -> false;
                case BoundaryAttempt.Unresolved it -> it.why().reason().leavesSomethingUntried()
                        || !it.why().alsoShort().isEmpty();
                case BoundaryAttempt.Stopped _, BoundaryAttempt.Unexhausted _,
                     BoundaryAttempt.Limited _, BoundaryAttempt.Unplanned _ -> true;
            };
        }

        /**
         * This attempt as it came back, with {@code account} said of it in the place of the one it
         * came back with.
         *
         * <p>For a reader that learned something about what the attempt was composed without after
         * it was made: a row stays the row it is and a word stays the word, and what is said of what
         * they were short of is the account's.
         */
        default BoundaryAttempt withAccount(CompositionAccount account) {
            return switch (this) {
                case BoundaryAttempt.Built built ->
                        new BoundaryAttempt.Built(built.row(), account, built.refused());
                case Unresolved none -> new Unresolved(none.why(), account);
                case Stopped stopped -> new Stopped(stopped.why(), stopped.met(), account);
                case Unexhausted unexhausted ->
                        new Unexhausted(unexhausted.why(), unexhausted.met(), account);
                case Limited limited -> new Limited(limited.why(), limited.by(), account);
                case Unplanned unplanned -> new Unplanned(unplanned.why(), unplanned.by(), account);
            };
        }

        /**
         * A value with the edge in it, built and accepted.
         *
         * <p><b>What it was not composed against is what this compiler could not do, and never what
         * the model settles.</b> A reader holding one of these has a row, and every entry beside it
         * says the row may not arrive for a reason somebody could work on — so a reader that acts on
         * the row and leaves the list is reading it the way it is meant. A proof that the way leaves
         * nothing is not that: it says the row does not arrive, and a list that could hold one would
         * make every existing reader of a built row wrong without a word to any of them.
         *
         * <p>Refused here rather than left to whoever assembles one. There is one place a proof can
         * come from and one place a row is assembled, and they are the same method — which is what
         * makes this cheap to hold and worth holding: the next word added beside these has the same
         * question to answer, and this is where it gets asked.
         *
         * <p><b>Built is not reached.</b> A walk held to the run of its rows ({@link RowJudge}) can
         * come back with a row whose run the judge refused: offered where the walk reached no row
         * the judge accepts and was not stopped, so that what that run did can be told. Such a row
         * is a row and is no row the search was for, and whoever walks on past this attempt —
         * another way of writing the elements, another pair of numbers — goes on past it.
         *
         * <p>A row refused is only ever returned by a walk that looked at everything there was to
         * look at ({@link #aRefusedRowStands}): where a figure ended the walk, or a way was left
         * unread, what comes back is what that walk came to, so that no layer above has a row
         * refused to hold in the place of the figure.
         *
         * @param refused whether the judge the walk was held to refused the row's run
         */
        record Built(GeneratedRow row, CompositionAccount unrepresented, boolean refused)
                implements BoundaryAttempt {

            public Built {
                for (ReachabilityGap gap : unrepresented.onTheWay()) {
                    if (gap instanceof ReachabilityGap.ProvedImpossible) {
                        throw new IllegalArgumentException("a row was built for a way no value can"
                                + " take, which is a row that does not arrive: " + gap.anchor());
                    }
                }
            }

            /** A row no judge refused. */
            public Built(GeneratedRow row, CompositionAccount unrepresented) {
                this(row, unrepresented, false);
            }
        }

        /**
         * The attempts no row came of, each of which says what it came to.
         *
         * <p>What differs between them is what a reader may do about it — raise a figure, widen
         * what this compiler writes, or nothing — and each of those is its own shape. What they
         * share is the word, which every one of them has and no two of them have for the same
         * cause. Held here so that a caller with no use for the difference reads the word without
         * choosing one of them to stand for the rest: folded to a word of the caller's own, a
         * search this compiler stopped reached an author as a model admitting no row.
         */
        sealed interface NoRow extends BoundaryAttempt {

            /** What the search came to, in the words the search came back with. */
            UnresolvedCombination why();

            /**
             * The word and what of this compiler's the search met on the way to it, as the one
             * value every other search that came to nothing is carried in.
             *
             * <p>Asked here and not taken apart by a caller. A caller reading the word off this and
             * the rest out of whichever shapes it knows about reads the word alone for every shape
             * it does not, and a search a figure stopped reaches an author as one this compiler has
             * nothing to say about.
             *
             * <p>A figure that cut the plan the search was handed, or left it nothing planned, is
             * not something the search met, and is held apart from what it did meet: the word of
             * a search over a plan cut short is that search's own answer about less than the
             * point had, and the word of one nothing was planned for says no search was made.
             */
            default CameToNothing came() {
                return switch (this) {
                    case Unresolved it -> CameToNothing.metNothing(it.why());
                    case Stopped it -> new CameToNothing(it.why(), it.met(), Set.of());
                    case Unexhausted it -> new CameToNothing(it.why(), it.met(), Set.of());
                    case Limited it ->
                            new CameToNothing(it.why(), CompositionShortfall.NONE, it.by());
                    case Unplanned it ->
                            new CameToNothing(it.why(), CompositionShortfall.NONE, it.by());
                };
            }
        }

        /** No row came of it, and why. Never a statement that none exists. */
        record Unresolved(UnresolvedCombination why, CompositionAccount unrepresented)
                implements NoRow {

            public Unresolved {
            }
        }

        /**
         * No row came of it, and a budget of this compiler's is why.
         *
         * <p>Beside {@link Unresolved} and not a field on it. A search that tried what it had and a
         * search this compiler ended leave the reader different work — only the second has a figure
         * somebody could raise — and every reader that has to tell them apart is one an exhaustive
         * switch already stops.
         *
         * <p>{@code why} is the word such a search has always come back with, read off the budgets
         * so that the two cannot part.
         */
        record Stopped(UnresolvedCombination why, CompositionShortfall met,
                       CompositionAccount unrepresented)
                implements NoRow {

            public Stopped {
                if (met.figures().isEmpty()) {
                    throw new IllegalArgumentException(
                            "a search this compiler stopped says which budget stopped it");
                }
                // The word is the budgets' to say, so this pair cannot be put here disagreeing.
                // Left to whoever builds one, the two are a copy of one answer kept beside it —
                // which is what a stop lost its budget to before it travelled at all.
                if (why.reason() != UnresolvedCombination.Reason.wordFor(met.figures())) {
                    throw new IllegalArgumentException("a search stopped by " + met.figures()
                            + " does not come back with " + why.reason());
                }
            }

            /** One at the label given, in the word its budgets come back with. */
            static Stopped at(String label, java.util.Set<CompositionBudget> by,
                              CompositionAccount unrepresented) {
                return at(label, null, CompositionShortfall.of(by), unrepresented);
            }

            /** The same, of a search that has something to say about where it stopped, and that
             *  met more than a figure on the way. */
            static Stopped at(String label, String said, CompositionShortfall met,
                              CompositionAccount unrepresented) {
                return at(label, said, new LinkedHashMap<>(), met, unrepresented);
            }

            /**
             * The same, of one whose offer was also short of what the rules about it leave.
             *
             * <p>The word stays the figure's and the sentence says the rest. A figure being reached
             * and a rule that composed nothing are two things an author acts on, and the one they
             * act on first is what the word is for — so neither is dropped for the other, and
             * neither is made into a second word.
             */
            static Stopped at(String label, String said,
                              SequencedMap<TermPath, StringOfferShortfall> alsoShort,
                              CompositionShortfall met, CompositionAccount unrepresented) {
                return new Stopped(UnresolvedCombination.atAPoint(label,
                        UnresolvedCombination.Reason.wordFor(met.figures()), said, alsoShort),
                        met, unrepresented);
            }
        }

        /**
         * No row came of it, and what this compiler writes of a population is why.
         *
         * <p>Beside {@link Stopped} and never one of its shapes. That one was holding a candidate a
         * figure had no room for, and its word is read off the figures; nothing was refused here,
         * and there is no number to read a word off or for a reader to raise. Written as a
         * {@code Stopped} with an empty set of figures, every reader of one would be reading a stop
         * that never happened.
         *
         * <p>The word is the same word all the same. What a reader concludes is that the point is
         * open because this compiler did not look at everything, which is true of both; what closes
         * it differs, and that is what travels here.
         *
         * <p>A number the search could not hold is one of these as well. Nothing was refused and
         * there is no number to raise; what reaches it is a host with more room where room is what
         * ran out, and nothing where the number has no representation at all — which of the two
         * travels here beside any population walked in part.
         */
        record Unexhausted(UnresolvedCombination why, CompositionShortfall met,
                           CompositionAccount unrepresented)
                implements NoRow {

            public Unexhausted {
                if (!met.figures().isEmpty() || met.nothing()) {
                    throw new IllegalArgumentException(
                            "a search that says it saw some of them, or could not hold a number,"
                                    + " says which, and names no figure: " + met);
                }
            }

            /** One at the label given, of a search that has something to say about what it saw. */
            static Unexhausted at(String label, String said, CompositionShortfall met,
                                  CompositionAccount unrepresented) {
                return at(label, said, new LinkedHashMap<>(), met, unrepresented);
            }

            /** The same, of one whose offer was also short of what the rules about it leave. */
            static Unexhausted at(String label, String said,
                                  SequencedMap<TermPath, StringOfferShortfall> alsoShort,
                                  CompositionShortfall met, CompositionAccount unrepresented) {
                return new Unexhausted(UnresolvedCombination.atAPoint(label,
                        UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED, said,
                        alsoShort), met, unrepresented);
            }
        }

        /**
         * A search that came to its own answer, over less than the point had.
         *
         * <p><b>Beside {@link Stopped} rather than one of its shapes.</b> A stopped search has no
         * answer but the stopping, so the word it comes back with follows from the budgets and is
         * checked against them where one is built. Here the search ran to the end of what it was
         * handed and said what it found; what the figure adds is that the thing it was handed was
         * short. So the two halves are independent, and requiring the word to be the budgets' would
         * refuse every one of these — a figure that stops no search has no word to be read off it.
         *
         * <p>What this licenses is what {@link Stopped} licenses: the question is open, and open
         * because of a figure somebody could raise. What it does not license is reading the word as
         * the whole story, which is the mistake that made a value this compiler declined to plan
         * for look like one the model admits no row at.
         */
        record Limited(UnresolvedCombination why, Set<CompositionBudget> by,
                       CompositionAccount unrepresented)
                implements NoRow {

            public Limited {
                by = Set.copyOf(by);
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an answer short of what the point had says which figure made it short");
                }
            }

            /** One at the label given, in the word the search itself came back with. */
            static Limited at(String label, UnresolvedCombination.Reason why, String said,
                              java.util.Set<CompositionBudget> by,
                              CompositionAccount unrepresented) {
                return new Limited(UnresolvedCombination.atAPoint(label, why, said), by,
                        unrepresented);
            }
        }

        /**
         * No search was made for the point: the value could not be planned.
         *
         * <p>Beside the two above and not one of them, because nothing ran. A reader of this is
         * owed the same thing a reader of {@link Stopped} is — the point is open on a figure — and
         * is owed it about a search that never happened, which is what its word says.
         */
        record Unplanned(UnresolvedCombination why, Set<CompositionBudget> by,
                         CompositionAccount unrepresented)
                implements NoRow {

            public Unplanned {
                by = Set.copyOf(by);
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a point nothing was planned for says which figure left it unplanned");
                }
            }

            /** One at the label given, in the word a reading nothing searched comes back with. */
            static Unplanned at(String label, Set<CompositionBudget> by,
                                CompositionAccount unrepresented) {
                return new Unplanned(new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.NO_READING_OF_THE_LINE_COULD_BE_SEARCHED),
                        by, unrepresented);
            }
        }
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
     * <p><b>And the item is not the whole of what a row has to be.</b> A line inside a guard or an
     * arm is reached by rows that got past what stands above it, and what stands above it is about
     * positions the item never names. So {@code reaching} is the other half and is conjoined with
     * {@code fixing} rather than filled in around it: what it asks in cases is what the rest of the
     * row is built under, and what it asks in numbers puts the positions it bounds somewhere it
     * admits. Left out, a row carried the value the line is drawn at and turned back above it — and
     * the walk that reads a row at a point then said, correctly, that it does not stand there.
     *
     * <p>One row per boundary rather than one row covering several, because a row is a question put to
     * a person and a row sitting on three edges at once is three answers they have to separate.
     *
     * <p>Nothing here decides that a boundary cannot be written at. A refusal is a refusal of the
     * candidates that were tried, and another value of the same edge may build; what comes back says
     * which of the two happened and leaves the reading to the caller.
     *
     * <p>What each position's number is measured on is not passed in. It is the subject's reading to
     * answer, and a caller handing it over would be handing an answer it worked out somewhere else —
     * for a term this reading might have standing somewhere other than where that caller found it.
     */
    public static BoundaryAttempt probeFixing(MeasuredInput subject, String label,
                                              Map<RealizationTarget, Place> fixing,
                                              NumbersAskedFor asking,
                                              Reachability.Reaching reaching, CandidateCheck check) {
        return probeFixing(subject, label, fixing, asking, reaching, check,
                StandInAttempt.REQUIRING_NOTHING, Trial.NOTHING_RUNS);
    }

    /**
     * The same, for a subject whose behavior requires dependencies to be stood in, with its rows
     * run by {@code trial}.
     *
     * <p>The stand-ins arrive with the search rather than being put on the row afterwards. A row
     * without them is a row nothing applies, so a point answered with one is a point nothing was
     * composed for — said here, where what the search came to is said, instead of by a reader that
     * takes a built row apart and rebuilds it.
     *
     * <p>And what standing them in was arrived at without joins what the search for this point's
     * own values was. Both are conditions of one way, read through two projections, and a reader of
     * the attempt is owed them as one account.
     *
     * <p>Where {@code trial} runs rows, the row taken is one the rewrites of the arms it goes
     * through answer differently on, where one is found among the first rows composed for the
     * point ({@link TellingArmsApart}). Every row composed here stands at the point, so which of
     * them is taken changes nothing about whether there is one: where none is found, the row is
     * the one told the most of them apart.
     */
    public static BoundaryAttempt probeFixing(MeasuredInput subject, String label,
                                              Map<RealizationTarget, Place> fixing,
                                              NumbersAskedFor asking,
                                              Reachability.Reaching reaching, CandidateCheck check,
                                              StandInAttempt stood, Trial trial) {
        return probeFixing(subject, label, fixing, asking, reaching, check, stood, trial,
                Optional.empty());
    }

    /**
     * The same, holding each row composed to {@code judge} as well, where there is one.
     *
     * <p>For what the way cannot say. A way states what a row has to be at the places it names, and
     * a case a search draws inside itself turns on what every node below the start comes to, which
     * no way states: whether a row is in it is for its run to say. Held to that inside the walk, a
     * row whose run was not in the case is passed over and the walk goes on to the next
     * assignment, within the figure the walk hands rows the choice at. Asked of the rows once the
     * walk had taken one, there was no next assignment to go on to.
     */
    public static BoundaryAttempt probeFixing(MeasuredInput subject, String label,
                                              Map<RealizationTarget, Place> fixing,
                                              NumbersAskedFor asking,
                                              Reachability.Reaching reaching, CandidateCheck check,
                                              StandInAttempt stood, Trial trial,
                                              Optional<RowJudge> judge) {
        // Where an element may meet something several ways, a row writing its elements alike is
        // composed along each way of choosing one for every element first. A row along one is a
        // row of the way; one of them coming to nothing says nothing of the rest, or of elements
        // that differ, so past them the way is composed as it stands and says what it did not
        // write.
        // Where the elements of a container a quantifier is over may have to differ — it asks an
        // element one of several things, a second quantifier is over it, or the item stands at a
        // number inside an element of it — the container is composed for how many of its elements
        // meet each statement first, its elements chosen one by one. A row of elements written
        // alike meets such a way only where one element meets everything asked of all of them.
        //
        // A row built with something of the way left out, as its own account says, is held back
        // while another of these may come back with nothing left out: the run of a row short of
        // the way settles nothing a rule is gone past by, so the first row built is not the row
        // taken where a later one meets the whole way. Where none does, the first built is.
        boolean apartFirst = elementsMayDiffer(reaching, fixing);
        boolean counts = reaching.boundedOnTheWay().stream()
                .anyMatch(cut -> countedOf(cut.demand()).isPresent());
        List<BoundaryAttempt> builtShort = new ArrayList<>();
        if (apartFirst) {
            BoundaryAttempt counted = probeFixingAlong(subject, label, fixing, asking, reaching,
                    check, stood, trial, true, null, judge);
            if (builtLeavingNothingOut(counted, builtShort)) {
                return counted;
            }
        }
        ElementsWrittenAlike.Choices alike = ElementsWrittenAlike.of(reaching);
        for (ElementsWrittenAlike.Alike one : alike.ways()) {
            BoundaryAttempt along = probeFixingAlong(subject, label, fixing, asking,
                    one.reaching(), check, stood, trial, false, one.leftBy(), judge);
            if (builtLeavingNothingOut(along, builtShort)) {
                return along;
            }
        }
        BoundaryAttempt whole = probeFixingAlong(subject, label, fixing, asking, reaching, check,
                stood, trial, false, alike.stoppedBy(), judge);
        if (builtLeavingNothingOut(whole, builtShort)) {
            return whole;
        }
        // And where that came to nothing, with every container a quantifier is over composed for
        // its counts. What the way as it stands came to is what is said where this comes to
        // nothing as well.
        if (!apartFirst && counts) {
            BoundaryAttempt counted = probeFixingAlong(subject, label, fixing, asking, reaching,
                    check, stood, trial, true, null, judge);
            if (builtLeavingNothingOut(counted, builtShort)) {
                return counted;
            }
        }
        return heldBack(builtShort, whole);
    }

    /**
     * The attempt that stands where none of these came back whole and reached: the first row built
     * that a judge did not refuse, short of the way as it may be, since the run of a row that took
     * what was asked took it however it was composed; otherwise, where rows a judge refused were
     * built, the first search that left something unlooked at
     * ({@link BoundaryAttempt#stoppedShort}), since a row refused is no answer that nothing was
     * left to find; otherwise the first row built, which says where its run went; otherwise
     * {@code none}, which is what the way as it stands came to and is what is said where no row
     * was built.
     */
    static BoundaryAttempt heldBack(List<BoundaryAttempt> builtShort, BoundaryAttempt none) {
        BoundaryAttempt refused = null;
        BoundaryAttempt stopped = null;
        for (BoundaryAttempt each : builtShort) {
            if (!(each instanceof BoundaryAttempt.Built built)) {
                if (stopped == null) {
                    stopped = each;
                }
            } else if (!built.refused()) {
                return each;
            } else if (refused == null) {
                refused = each;
            }
        }
        if (stopped != null && !none.stoppedShort()) {
            // The way as it stands is composed against what it states, and says so in its account;
            // what another way left unlooked at is the word. Neither replaces the other.
            return refused == null ? stopped.withAccount(none.unrepresented()) : stopped;
        }
        if (refused == null) {
            return none;
        }
        return stopped != null ? stopped : refused;
    }

    /**
     * Whether {@code attempt} is a row built with nothing its own account names as left out of
     * the way, and that no judge refused — and, where it is a row built with something left out
     * or a row refused, {@code attempt} put in {@code builtShort}.
     *
     * <p>An account naming nothing does not show nothing was left out: a condition the walk had
     * no words for is in no account ({@link CompositionAccount}). One naming something shows that
     * much was, which is all this asks of it.
     *
     * <p>A row refused is a row built, and is held back like a row built short: the next way of
     * composing may reach a row the judge accepts, and a search that stopped at the first row
     * built would never look.
     *
     * <p>A search a figure or a plan stopped is held back too, beside them, since it is what a
     * row refused must not hide ({@link #heldBack}).
     */
    static boolean builtLeavingNothingOut(BoundaryAttempt attempt,
                                          List<BoundaryAttempt> builtShort) {
        if (!(attempt instanceof BoundaryAttempt.Built built)) {
            if (attempt.stoppedShort()) {
                builtShort.add(attempt);
            }
            return false;
        }
        if (!built.refused() && built.unrepresented().onTheWay().isEmpty()
                && built.unrepresented().onAnAnswer().isEmpty()) {
            return true;
        }
        builtShort.add(attempt);
        return false;
    }

    /**
     * Whether the elements of some container a quantifier that is the whole of a statement is over
     * may have to differ for a row to meet the way: the quantifier asks an element one of several
     * things, another such quantifier is over the same container, a count — the item's, or one on
     * the way — composes the container, or {@code fixing} stands at a number inside one of its
     * elements.
     *
     * <p>A container a count composes is chosen element by element, so what a quantifier over it
     * asks of every element is asked where the elements are chosen, as how many of them meet its
     * denial; held to the region instead, what the region cannot hold of one element — that it is
     * not some value — would never reach the elements chosen.
     */
    private static boolean elementsMayDiffer(Reachability.Reaching reaching,
                                             Map<RealizationTarget, Place> fixing) {
        Set<TermPath> composedForCounts = new HashSet<>();
        for (RealizationTarget each : fixing.keySet()) {
            if (each instanceof RealizationTarget.ACount count) {
                composedForCounts.add(count.count().container());
            }
        }
        for (OnTheWay.TakenIn cut : reaching.boundedOnTheWay()) {
            if (cut.demand() instanceof RowDemand.SoMany many) {
                composedForCounts.add(AStatementAtARow.elementsOf(many.count()).container()
                        .inputPosition());
            }
        }
        Set<TermPath> quantified = new HashSet<>();
        for (OnTheWay.TakenIn cut : reaching.boundedOnTheWay()) {
            if (countedOf(cut.demand()).isEmpty()) {
                continue;
            }
            TermPath container = containerOf(cut.demand());
            if (!RowDemand.writtenAlikeAsItStands(cut.demand()) || !quantified.add(container)
                    || composedForCounts.contains(container)) {
                return true;
            }
        }
        for (RealizationTarget each : fixing.keySet()) {
            if (insideAnElementOf(each, quantified)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether {@code target} is a value placed inside an element of one of {@code containers}:
     * the element itself or a number of it, which some element of a container composed for its
     * counts is chosen holding ({@link TermRealizations}) — and nothing else is.
     */
    private static boolean insideAnElementOf(RealizationTarget target, Set<TermPath> containers) {
        return target instanceof RealizationTarget.AtOnePosition(NumericTerm.FromOnePosition term)
                && term instanceof NumericTerm.ValueOf value
                && containers.stream().anyMatch(container ->
                        value.position().isAtOrUnder(container.element()));
    }

    /**
     * {@link #probeFixing}, along a way whose demands of several ways are written as they stand.
     *
     * @param byCounts whether every container a quantifier that is the whole of a statement is
     *                 over is composed for its counts, and not only one whose elements a quantifier
     *                 asks several things of
     * @param alikeStoppedBy the figure that left a demand of several ways on {@code reaching}
     *                       unchosen, where one did: the one a way written alike was handed on
     *                       with ({@link ElementsWrittenAlike.Alike}), or the one the ways of
     *                       writing the elements alike were looked along to
     *                       ({@link ElementsWrittenAlike.Choices})
     * @param judge what each row composed is held to besides the way, where something is
     */
    private static BoundaryAttempt probeFixingAlong(MeasuredInput subject, String label,
                                                    Map<RealizationTarget, Place> fixing,
                                                    NumbersAskedFor asking,
                                                    Reachability.Reaching reaching,
                                                    CandidateCheck check, StandInAttempt stood,
                                                    Trial trial, boolean byCounts,
                                                    CompositionBudget alikeStoppedBy,
                                                    Optional<RowJudge> judge) {
        LocationWrites decided = new LocationWrites();
        // What the rest of the row has to sit beside. A field of a record is not chosen from its own
        // type once another field of that record is fixed: the rule relating them says what is left,
        // and taking the bottom of the type's range instead is how a boundary that can be written
        // came back as one every value tried was refused at.
        Map<TermPath, Place> settled = new LinkedHashMap<>();
        // What each edge's offer was short of, and not the word for it. The word says nothing about
        // which figure, which population or which number; kept as the word, a refusal that turned
        // out to be this compiler stopping could not say what stopping it cost. Kept whole, as the
        // one shortfall the edge met, so that no vocabulary of it is left out of the book.
        Map<TermPath, CompositionShortfall> heldBack = new LinkedHashMap<>();
        // Where every position of this row stands: the item's, and the ones the way to it bounds.
        // One map, because a row is one row — walked as two, the second was chosen from what the
        // declarations leave and the first from what reaches the border, and only one of them was
        // about the row being written.
        Map<RealizationTarget, NumbersAskedFor> itemAsks = new LinkedHashMap<>();
        for (RealizationTarget each : fixing.keySet()) {
            itemAsks.put(each, asking);
        }
        WhatTheWayLeaves leaves = new WhatTheWayLeaves(subject, reaching);
        Standing where = alsoOnTheWay(subject, fixing, itemAsks, check, reaching, byCounts,
                alikeStoppedBy, leaves).with(stood.account());
        // A way the rules leave nothing standing on is a way no row arrives by, so there is no row
        // to compose for this point and the rest of this would be composing one. What comes back is
        // the model's word, which is the same word the realizer's proof comes back with and is
        // reached here by the other of the two routes to it.
        //
        // <p>Said before a row is built rather than beside one. A row assembled here is a row that
        // does not arrive, and handing it over with the proof attached asks every reader of it to
        // know that the second component can take the first one away — which is what they were
        // written before this word existed and is not what {@link BoundaryAttempt.Built} means.
        for (ReachabilityGap gap : where.unrepresented().onTheWay()) {
            if (gap instanceof ReachabilityGap.ProvedImpossible) {
                return new BoundaryAttempt.Unresolved(new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE),
                        where.unrepresented());
            }
        }
        Map<RealizationTarget, Place> standing = where.at();
        Map<RealizationTarget, AskedAt> numbers = atThoseNumbers(standing,
                whatEachOfThemIsANumberOf(itemAsks, where.routed(), where.counted(), leaves));
        // And what the way asks the elements of its containers to be, which the elements are
        // written as. Where that is two things at one position inside an element, the elements are
        // written alike and no row is — which is this composer's answer and not the model's.
        ElementWrites elements = ElementWrites.of(reaching.boundedOnTheWay());
        Requirements rowIs;
        switch (elements.requiredBeside(reaching.requirements())) {
            case Requirements.Merge.Merged(Requirements both) -> rowIs = both;
            case Requirements.Merge.Conflict conflict -> {
                return new BoundaryAttempt.Unresolved(UnresolvedCombination.atAPoint(label,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        ElementWrites.writtenAlike(conflict.at())),
                        where.unrepresented());
            }
        }
        Set<TermPath> truthsWritten = new LinkedHashSet<>(reaching.truths().at().keySet());
        truthsWritten.addAll(elements.truthsAt());
        // One edge per location and not one per number. A location asked for two numbers is one
        // value to write, so the two are composed together and written once; walked one number at a
        // time, the second was a value built for a place the first had already written.
        for (Map.Entry<TermPath, SequencedMap<RealizationTarget, AskedAt>> group
                : byTheLocationTheyWrite(numbers, where.someElement()).entrySet()) {
            Edge edge = where.composedAt(group.getKey(), group.getValue(),
                    composedIn(group.getKey(), group.getValue(), reaching.region(), standing,
                            where.bounds()), subject);
            if (edge.values().isEmpty()) {
                return edge.cameToNothing(label, where.unrepresented(),
                        Collections.disjoint(group.getValue().keySet(), where.chosen()));
            }
            TermPath at = group.getKey();
            // Two terms at one location is that location asked for two things at once — a string of
            // a length and the string itself — and what a row writes at a location is one value.
            // The fixing keeps them apart ({@link Realization.Found}) and this cannot, so it says so
            // rather than writing whichever came last and offering half the point as the whole.
            //
            // Refused whatever the second edge offers, and not only where it offers something else.
            // What is recorded beside the value here — where the row settles and what the edge held
            // back — is the edge's own answer, and two edges have two of those however alike their
            // values are. Written as one, the row would carry one edge's account of a place both
            // were asked about.
            //
            // Which two locations are one is {@link LocationWrites}' answer and is asked of it once.
            // Asked here as well, this would be a second account of that, and the two would part
            // over a location inside another.
            //
            // Anything but the first ask, and not only an ask that disagrees. That two edges offer
            // the same values is not the two being one ask here, for the reason above: what travels
            // beside the values is each edge's own, and the second would be recorded as the first's.
            //
            // A container asked for how many it holds and nothing else, whose elements the way
            // narrows to a case, is asked to hold that many and not to be one of the values standing
            // for the number: written whole, it would be elements of whatever case the number's
            // composer wrote, and the way's case would have nowhere to be written. The same holds
            // for a truth the way asks of a position inside its elements.
            DeclaredBounds.CountRange holds =
                    onlyHowManyItHolds(group.getValue().keySet(), at)
                            && (narrowedStrictlyUnder(rowIs, at)
                                    || truthAskedStrictlyUnder(truthsWritten, at))
                            ? sizesOf(edge.values()) : null;
            if ((holds != null ? decided.size(at, holds) : decided.write(at, edge.values()))
                    != LocationWrites.Written.FIRST) {
                return new BoundaryAttempt.Unresolved(new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                        where.unrepresented());
            }
            if (edge.settledAt() != null) {
                settled.put(at, edge.settledAt());
            }
            heldBack.put(at, edge.met());
        }
        // What the way asks containers to hold that no region placed, and the order that lets every
        // container be composed after the parameters it is handed a value of.
        // The order is one for every way of writing them under the cases, since which parameter a
        // container is handed a value of does not turn on the case it is written under. And what a
        // count composed above hands on for each element it counts, at the counts it was asked.
        ContentsAsked asked = ContentsAsked.of(reaching.boundedOnTheWay(), numbers);
        CompositionOrder order;
        switch (CompositionOrder.of(parametersOf(subject), asked)) {
            case CompositionOrder.Result.Ordered(CompositionOrder ordered) -> order = ordered;
            case CompositionOrder.Result.Circular circular -> {
                return new BoundaryAttempt.Unresolved(UnresolvedCombination.atAPoint(label,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        circularly(circular)), where.unrepresented());
            }
        }
        // Every way of writing them under the cases the row can be, one at a time, the first that
        // composes taken: a container a name every case of a sum spreads is composed under one of
        // the cases. What the rest came to is said over every one of them, the same whichever was
        // tried first.
        ContentsAsked.UnderTheCases under = asked.underTheCases(subject.reach(), rowIs,
                truthsWritten);
        FixtureTemplate[] composed = new FixtureTemplate[order.parameters().size()];
        List<ParameterCameToNothing> cameToNothing = new ArrayList<>();
        // Every row composed here stands at the point, so each one meets what it is composed for.
        // Only where a row can be run: one nothing stands the dependencies in for is no row
        // anything applies.
        RowPreference preferring =
                stood.outcome() instanceof AnswersStoodIn.Stood(var answers)
                        ? judge.<RowPreference>map(each -> each.refusesAbsolutely()
                                        ? new ReachingWhatIsJudged(each, answers)
                                        : new TellingArmsApart(trial, answers, each))
                                .orElseGet(() -> new TellingArmsApart(trial, answers))
                : null;
        RowTaking taking = preferring == null ? RowTaking.FIRST
                : preferring.over(RowTaking.FIRST);
        boolean[] noRowAnswered = {false};
        SearchShortfall[] passedFound = {SearchShortfall.NONE};
        // The first row a judge refused, which stands where no way of writing the contents under
        // the cases reaches a row it accepts: a row built and no row the search was for, so
        // another way is tried past it.
        List<List<FixtureTemplate>> refusedKept = new ArrayList<>();
        ContentsAsked.UnderTheCases.Walked walked = under.tryEach(way -> {
            // And the value the way asks of each Bool position it read, which no edge offers and
            // no region placed — at the position each stands at in this way, which for a Bool the
            // cases share is under the case this way writes. Written beside the numbers, so a
            // location holding one of them and asked for something else as well is refused where
            // every two asks of one location are.
            LocationWrites writes = decided.copy();
            TermPath twice = null;
            TruthsAsked truths = TruthsAsked.NONE;
            switch (reaching.truths().standingAt(way.standing())) {
                case TruthsAsked.Merge.Merged(var here) -> {
                    switch (elements.truthsBeside(here, way.standing())) {
                        case TruthsAsked.Merge.Merged(var withTheElements) -> {
                            truths = here;
                            twice = withTheElements.writtenInto(writes);
                        }
                        case TruthsAsked.Merge.Conflict(var at) -> twice = at;
                    }
                }
                case TruthsAsked.Merge.Conflict(var at) -> twice = at;
            }
            if (twice != null) {
                cameToNothing.add(new ParameterCameToNothing(
                        order.parameters().indexOf(twice.head()),
                        new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                "`" + twice + "` would have to hold two values at once"),
                        SearchShortfall.NONE, Map.of()));
                return false;
            }
            // One way under one choice of cases, which is never split again: the ways a condition
            // of several ways split this into were each handed here apart. A way looked along whole
            // stays one that was, so what was not split is still said of its row.
            Reachability.Reaching thisWay = new Reachability.Reaching(reaching.region(),
                    way.taken(), truths, reaching.boundedOnTheWay(),
                    reaching.ways() instanceof Reachability.Ways.Whole(var unsplit, var figure,
                            var _, var from)
                            ? new Reachability.Ways.Whole(unsplit, figure, List.of(), from)
                            : Reachability.Ways.ONE, reaching.declined(), reaching.narrowedBy());
            WalkedInOrder came = new InOrder(subject, order, composed, standing, writes,
                    settled, thisWay, check, way.contents(), taking)
                    .from(0, ValuesHandedOn.NONE);
            switch (came) {
                case WalkedInOrder.CameToNothingAt(ParameterCameToNothing why) -> {
                    cameToNothing.add(why);
                    return false;
                }
                case WalkedInOrder.RowTaken _, WalkedInOrder.PassedOver _,
                     WalkedInOrder.Halted _ -> {
                    // A row was composed. Which one goes out is the preference's, and the first
                    // composed where nothing ranked them.
                    List<FixtureTemplate> kept = preferring == null ? null : preferring.taken();
                    if (kept != null && preferring.takenIsRefused()) {
                        if (refusedKept.isEmpty()) {
                            refusedKept.add(kept);
                        }
                        return false;
                    }
                    if (kept != null) {
                        kept.toArray(composed);
                        return true;
                    }
                    if (came instanceof WalkedInOrder.RowTaken) {
                        return true;
                    }
                    // Rows were composed and none was run to an answer: said with the rest of
                    // what the ways came to once they are all tried, as a row passed over and not
                    // as a parameter that came to nothing.
                    if (came instanceof WalkedInOrder.PassedOver(SearchShortfall its)) {
                        passedFound[0] = passedFound[0].and(its);
                    }
                    noRowAnswered[0] = true;
                    return false;
                }
            }
        });
        // No way reached a row the judge accepts and every way there is was tried: the row it
        // refused first is what comes back, built and marked refused. A walk that left ways
        // untried, by its figure or under a case nobody read, reached no row to say nothing was
        // left to find, so it comes to what that walk came to and not to a row.
        boolean refusedOnly = !refusedKept.isEmpty() && preferring.takenIsRefused()
                && aRefusedRowStands(walked, whatTheWalkLeftUnlookedAt(under.foundOut(walked),
                        cameToNothing, passedFound[0], preferring.untried()),
                        cameToNothing.stream().anyMatch(each -> !each.lookedAtWhole()));
        if (refusedOnly) {
            refusedKept.getFirst().toArray(composed);
        }
        ParameterCameToNothing failed = null;
        if (walked != ContentsAsked.UnderTheCases.Walked.COMPOSED && !refusedOnly) {
            // What every way tried came to, beside the figure where the walk stopped short of the
            // rest and a way under a case nobody read; where no way came to nothing to say it in,
            // the figure, the case nobody read, or that no case held them.
            // And, where rows were composed and none came to an answer, those rows passed over:
            // beside what the choice among rows was stopped at, which leaves the rows past it
            // untried, and what the other ways came to — none of which a row passed over takes
            // away, and a proof among them is not the walk's.
            SearchShortfall passedOver = noRowAnswered[0]
                    ? preferring.untried().and(passedFound[0]) : null;
            switch (WhatTheAlternativesCameTo.over(cameToNothing, passedOver,
                    under.foundOut(walked), PARAMETERS)) {
                case WhatTheAlternativesCameTo.Came.Said(ParameterCameToNothing said) ->
                        failed = said;
                case WhatTheAlternativesCameTo.Came.Untried(SearchShortfall found) -> {
                    return leftUntried(label, found,
                            UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                            A_CASE_WAS_NOT_READ, where.unrepresented());
                }
                case WhatTheAlternativesCameTo.Came.NothingToSayItIn<ParameterCameToNothing> _ -> {
                    return new BoundaryAttempt.Unresolved(UnresolvedCombination.atAPoint(label,
                            UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                            NO_CASE_HOLDS_THEM), where.unrepresented());
                }
                // Rows were composed and run, and none came to an answer: a fact about those rows,
                // which is not that no row reaches the point. A figure that stopped the search is
                // said as the figure; otherwise the word is the one for rows none of which was a
                // witness, or the one for what else the search left untried.
                case WhatTheAlternativesCameTo.Came.PassedOver<ParameterCameToNothing>(
                        SearchShortfall found) -> {
                    return noRowAnswered(label, found, preferring.aRunRanOut(),
                            where.unrepresented());
                }
            }
        }
        if (failed != null) {
            Outcome tried = failed.tried();
            Map<TermPath, List<FixtureTemplate>> here = failed.here();
            // What the edge under this parameter held back is learned here and not where the
            // search ran, so this is where it is put to the rule — the same rule, and not a second
            // reading of it: an offer still holding values means nothing has been exhausted, and a
            // plan short of the point is not yet anything a reader is owed.
            Outcome answered = switch (tried) {
                // None of these is a search claiming every candidate was refused, which is the one
                // claim what the edge held back bears on ({@link #whatTheEdgeHeldBack}). A search
                // that stopped, one that ran to the end of what this compiler writes, and one that
                // never ran are already saying the point is open on this compiler, and adding what
                // an edge was short of would be a second account of the same emptiness.
                //
                // Which is true in every vocabulary and not only in the figures. What the edge was
                // short of travels with the answer that is about it, and never onto one that was
                // settled before the edge's offer was in question.
                case Outcome.Built _, Outcome.Stopped _, Outcome.Unexhausted _,
                     Outcome.OfferShort _, Outcome.Unplanned _, Outcome.PassedOver _,
                     Outcome.Halted _ -> tried;
                case Outcome.Unresolved(UnresolvedCombination.Reason word, String said) -> {
                    UnresolvedCombination.Reason itsWord = failed.found().wordFor(word);
                    yield whatTheSearchCameTo(whatTheEdgeHeldBack(heldBack, here, itsWord),
                            new LinkedHashMap<>(), Set.of(),
                            new Outcome.Unresolved(itsWord, failed.found()
                                    .toldFor(word, Optional.ofNullable(said)).orElse(null)));
                }
                // Taken apart into what the search itself came to and what the plan was short of,
                // which is what the rule is asked in terms of. Handed over whole, the plan's
                // figures would be beside an offer's without anything having decided that a reader
                // is owed both.
                case Outcome.Limited(UnresolvedCombination.Reason word, String said,
                                     Set<CompositionBudget> planCut) -> {
                    UnresolvedCombination.Reason itsWord = failed.found().wordFor(word);
                    yield whatTheSearchCameTo(whatTheEdgeHeldBack(heldBack, here, itsWord),
                            new LinkedHashMap<>(), planCut,
                            new Outcome.Unresolved(itsWord, failed.found()
                                    .toldFor(word, Optional.ofNullable(said)).orElse(null)));
                }
            };
            return switch (answered) {
                case Outcome.Unresolved(UnresolvedCombination.Reason word, String said) ->
                        new BoundaryAttempt.Unresolved(
                                UnresolvedCombination.atAPoint(label, word, said),
                                where.unrepresented());
                case Outcome.Stopped(CompositionShortfall met,
                                     SequencedMap<TermPath, StringOfferShortfall> offered,
                                     String said) ->
                        BoundaryAttempt.Stopped.at(label, said, offered, met,
                                where.unrepresented());
                case Outcome.Unexhausted(CompositionShortfall met,
                                         SequencedMap<TermPath, StringOfferShortfall> offered,
                                         String said) ->
                        BoundaryAttempt.Unexhausted.at(label, said, offered, met,
                                where.unrepresented());
                // No figure stopped this, so it is not one of the two above: what a reader is told
                // is the word for an offer short of the rules, and which rule is the sentence
                // beside it.
                case Outcome.OfferShort(
                        SequencedMap<TermPath, StringOfferShortfall> offered, String said) ->
                        new BoundaryAttempt.Unresolved(
                                UnresolvedCombination.atAPoint(label,
                                        UnresolvedCombination.Reason
                                                .NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                                        said, offered),
                                where.unrepresented());
                case Outcome.Limited(UnresolvedCombination.Reason word, String said,
                                     Set<CompositionBudget> by) ->
                        BoundaryAttempt.Limited.at(label, word, said, by, where.unrepresented());
                case Outcome.Unplanned(Set<CompositionBudget> by) ->
                        BoundaryAttempt.Unplanned.at(label, by, where.unrepresented());
                // A row was composed, which was answered above and is not an account of a point
                // nothing was composed for. Nor is a value passed over or a search stopped by its
                // caller: what that came to is a parameter after it nothing was composed for, and
                // that parameter's answer is the one handed here ({@link InOrder}).
                case Outcome.Built _, Outcome.PassedOver _, Outcome.Halted _ ->
                        throw new IllegalStateException("a composed row is not something to say a"
                                + " point came to nothing in");
            };
        }
        List<FixtureTemplate> inputs = List.of(composed);
        return switch (stood.outcome()) {
            // The values stand at the point and nothing stands in for what the behavior requires,
            // so there is no row here to offer. Said as what the search came to, because a row a
            // person cannot run is not a row this composed.
            case AnswersStoodIn.NothingComposed(var why) -> new BoundaryAttempt.Unresolved(
                    new UnresolvedCombination(List.of(label), why), where.unrepresented());
            case AnswersStoodIn.Stood(var answers) -> new BoundaryAttempt.Built(
                    new GeneratedRow(List.of(new Purpose.ForAPoint(label)), inputs, answers),
                    where.unrepresented(), refusedOnly);
        };
    }

    /**
     * Whether a row a judge refused may come back as the row of a walk over the ways under the
     * cases: only when every way was tried and none was left unlooked at. A walk its figure ended,
     * or one with a way under a case nobody read, did not look at every way, so a row it refused
     * is no answer that nothing else was there to find; it comes to what that walk found out.
     */
    static boolean aRefusedRowStands(ContentsAsked.UnderTheCases.Walked walked,
                                     SearchShortfall left, boolean aParameterWasNotLookedAtWhole) {
        return walked == ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED && left.nothing()
                && !aParameterWasNotLookedAtWhole;
    }

    /**
     * What a walk over the ways under the cases left unlooked at, from every place it can be
     * said: the ways not handed over, what the parameters of each way found out, what the rows
     * passed over found out, and what the choice among rows left untried. The one value
     * {@link WhatTheAlternativesCameTo} joins, so that a row refused is held to the same account
     * as a walk that took no row.
     */
    private static SearchShortfall whatTheWalkLeftUnlookedAt(
            SearchShortfall ways, List<ParameterCameToNothing> cameToNothing,
            SearchShortfall passedOver, SearchShortfall untried) {
        SearchShortfall left = ways.and(passedOver).and(untried);
        for (ParameterCameToNothing each : cameToNothing) {
            left = left.and(each.found());
        }
        return left;
    }

    /** The parameters a row writes a value for, in the order they are declared. */
    private static List<String> parametersOf(MeasuredInput subject) {
        return subject.parameters().subList(0,
                Math.min(subject.parameters().size(), subject.types().size()));
    }

    /**
     * From how few to how many elements the values fixed at a container hold, or null where one of
     * them is not written out as its elements.
     *
     * <p>A container's own number is how many it holds, and a class of one is a run of those —
     * so the fewest and the most of the values standing for it are sizes the class takes, and
     * every size between them is one it takes as well.
     */
    private static DeclaredBounds.CountRange sizesOf(List<FixtureTemplate> values) {
        int least = Integer.MAX_VALUE;
        int most = -1;
        for (FixtureTemplate each : values) {
            Hir.Expr written = each.value();
            // Under the names it wears, each of which is written round the value it wraps.
            while (written instanceof Hir.Apply applied && applied.args().size() == 1) {
                written = applied.args().getFirst();
            }
            if (!(written instanceof Hir.ListLit(List<Hir.Expr> elements, var _, var _, var _))) {
                return null;
            }
            least = Math.min(least, elements.size());
            most = Math.max(most, elements.size());
        }
        return most < 0 ? null : new DeclaredBounds.CountRange(least, most);
    }

    /** Every count from one up, which is what a container holding something holds. */
    private static final DeclaredBounds.CountRange FROM_ONE =
            new DeclaredBounds.CountRange(1, Integer.MAX_VALUE);

    /**
     * From how few to how many a class of how many a container holds takes from one up, for a row
     * asking something inside the container as well, or null where the arithmetic could not say.
     *
     * <p>Off the set the class is about and not off the values standing for it ({@link #sizesOf}).
     * A class from none to one may stand for itself with an empty container, and a row asking the
     * container to hold an element as well needs the other count the class takes. And from one,
     * whatever the class also holds below it: what is asked inside is somewhere only in a container
     * holding something.
     */
    private static DeclaredBounds.CountRange countsOf(PartitionClass cls) {
        Recognition what = cls.recognises();
        while (what instanceof Recognition.Under under) {
            what = under.inner();
        }
        if (!(what instanceof Recognition.OfACount count)) {
            return null;
        }
        if (!(count.is().asOneRun() instanceof NumericDomain.Bounds run)) {
            return oneCountFromOne(count);
        }
        DeclaredBounds.CountRange all = countsIn(run);
        return all == null ? null : within(all, FROM_ONE);
    }

    /**
     * The least count from one up a class of more than one run takes, as the one count a container
     * is asked to hold, or null where none is found.
     *
     * <p>Such a class has no pair of ends holding only its counts, so one of them is asked for. Each
     * count stepped over is one the class takes out, so the walk is as long as what it takes out
     * and no longer.
     */
    private static DeclaredBounds.CountRange oneCountFromOne(Recognition.OfACount count) {
        List<Place> takenOut = switch (count.is()) {
            case NumericSet.AwayFrom away -> away.values();
            case NumericSet.InARunExcept except -> except.excluded();
            case NumericSet.At _, NumericSet.InARun _ -> List.of();
        };
        Endpoint low = count.is().extent().min();
        Count from = low == null ? Count.of(1) : wholeAt(low, true);
        if (from == null) {
            return null;
        }
        if (from.compareTo(Count.of(1)) < 0) {
            from = Count.of(1);
        }
        for (int step = 0; step <= takenOut.size(); step++) {
            Count each = from.plus(step);
            if (count.is().holds(each, count.carrier())) {
                int many = CountDomain.asCount(each);
                return many < 0 ? null : new DeclaredBounds.CountRange(many, many);
            }
        }
        return null;
    }

    /** The whole counts between the ends of {@code run}, or null where an end is not a count. */
    private static DeclaredBounds.CountRange countsIn(NumericDomain.Bounds run) {
        Count least = run.min() == null ? Count.ZERO : wholeAt(run.min(), true);
        Count most = run.max() == null ? null : wholeAt(run.max(), false);
        if (least == null || (run.max() != null && most == null)) {
            return null;
        }
        int fewest = least.signum() < 0 ? 0 : CountDomain.asCount(least);
        if (fewest < 0) {
            return null;
        }
        if (most == null) {
            return new DeclaredBounds.CountRange(fewest, Integer.MAX_VALUE);
        }
        if (most.signum() < 0) {
            return new DeclaredBounds.CountRange(fewest, -1);
        }
        // Past what an int holds is as many as anything is built to hold.
        int many = CountDomain.asCount(most);
        return new DeclaredBounds.CountRange(fewest, many < 0 ? Integer.MAX_VALUE : many);
    }

    /**
     * The nearest whole count inside {@code end}, going up from a lower end and down from an upper
     * one, or null where the end is not a count.
     */
    private static Count wholeAt(Endpoint end, boolean lower) {
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        Count inside = count.rounded(lower ? RoundingMode.CEILING : RoundingMode.FLOOR);
        if (!end.inclusive() && inside.compareTo(count) == 0) {
            inside = lower ? inside.plus(1) : inside.minus(1);
        }
        return inside;
    }

    /** {@code holds}, narrowed to {@code to} where there is one. */
    private static DeclaredBounds.CountRange within(DeclaredBounds.CountRange holds,
                                                    DeclaredBounds.CountRange to) {
        return to == null ? holds : new DeclaredBounds.CountRange(
                Math.max(holds.least(), to.least()), Math.min(holds.most(), to.most()));
    }

    /** What is said of a point at which rows were composed and run and none came to an answer. */
    private static final String NO_ROW_ANSWERED = "no row composed here was run to an answer";

    /** The same, where a run of one of them went past what a run may spend. */
    private static final String NO_ROW_ANSWERED_A_RUN_RAN_OUT = NO_ROW_ANSWERED
            + ", and a run went past what a run may spend";

    /**
     * What a point comes to where rows were composed and run and none came to an answer, with
     * {@code found} of what the search left untried beside them.
     *
     * <p>A figure that stopped the search is said as the figure, because the rows past it were
     * never composed. Otherwise the rows themselves are what is said, in the word for rows none of
     * which was a witness or in the one for what else was left untried — a fact about the rows
     * this compiler composed, and never that no row reaches the point.
     */
    static BoundaryAttempt noRowAnswered(String label, SearchShortfall found, boolean aRunRanOut,
                                         CompositionAccount unrepresented) {
        return leftUntried(label, found, UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                aRunRanOut ? NO_ROW_ANSWERED_A_RUN_RAN_OUT : NO_ROW_ANSWERED, unrepresented);
    }

    /**
     * What a point comes to where the search found something out that it did not have everything
     * for, with all of it: the figures it stopped at, the populations it could not enumerate and the
     * values it could not write, and which rule an offer was short of.
     *
     * <p>The shape is the one the search left, and nothing is dropped for the sake of the word. A
     * reader told only of the figure raises it, and the population is what had to be widened.
     * {@code otherwise} is the word where none of that was found out and the sentence is all there
     * is to say.
     */
    private static BoundaryAttempt leftUntried(String label, SearchShortfall found,
                                               UnresolvedCombination.Reason otherwise, String said,
                                               CompositionAccount unrepresented) {
        CompositionShortfall met = found.met();
        if (!met.figures().isEmpty()) {
            return BoundaryAttempt.Stopped.at(label, said, found.offered(), met, unrepresented);
        }
        if (!met.nothing()) {
            return BoundaryAttempt.Unexhausted.at(label, said, found.offered(), met,
                    unrepresented);
        }
        return new BoundaryAttempt.Unresolved(UnresolvedCombination.atAPoint(label,
                found.wordFor(otherwise), said, found.offered()), unrepresented);
    }

    /** What is said of a row no case of which holds every container and value it is asked of. */
    private static final String NO_CASE_HOLDS_THEM = "no case the row can be holds every"
            + " container and value the way asks to be written into one";

    /** What is said of a row every way tried of which came to nothing, beside a case whose reading
     *  stopped before it put a container or a value anywhere. */
    private static final String A_CASE_WAS_NOT_READ = "every way of writing the containers the"
            + " way hands values to came to nothing, and a case of a sum they stand under was not"
            + " read";

    /** What is said of a row whose parameters are each to hold a value of another of them. */
    private static String circularly(CompositionOrder.Result.Circular circular) {
        return "each of " + circular.parameters() + " is to hold a value of another of them, and"
                + " they are composed one after another";
    }

    /**
     * One parameter nothing was composed for, and what its search came to.
     *
     * @param parameter   which parameter
     * @param tried       what its search came to
     * @param found     what its search found out about its own candidates beside what it came to
     * @param here      the positions of it the caller had decided
     */
    private record ParameterCameToNothing(int parameter, Outcome tried, SearchShortfall found,
                                          Map<TermPath, List<FixtureTemplate>> here) {

        /**
         * Whether its search ran to the end of what it looked at and came to the word alone: a
         * figure, a population, an offer short of a rule or a plan cut is a search that did not.
         */
        boolean lookedAtWhole() {
            return tried instanceof Outcome.Unresolved(var reason, var _)
                    && !reason.leavesSomethingUntried() && found.nothing();
        }
    }

    /**
     * What composing a row at a point in order came to, for a caller that may pass rows over: the
     * same four answers {@link RowComposed} gives, with what came to nothing said at the parameter
     * it came to nothing at.
     */
    private sealed interface WalkedInOrder {

        /** A row, taken, and standing in the walk's values. */
        record RowTaken() implements WalkedInOrder {}

        /**
         * Rows were composed and every one was passed over. Not a refusal of any of them.
         *
         * @param found what the walk found out beside passing them over: the figures it stopped at
         *              and what the parameters it went on to came to, none of which a row passed
         *              over takes away
         */
        record PassedOver(SearchShortfall found) implements WalkedInOrder {}

        /** The caller stopped. */
        record Halted() implements WalkedInOrder {}

        /** No row could be composed, and the parameter it came to nothing at. */
        record CameToNothingAt(ParameterCameToNothing why) implements WalkedInOrder {}

        RowTaken TAKEN = new RowTaken();
        PassedOver PASSED_OVER = new PassedOver(SearchShortfall.NONE);
        Halted HALTED = new Halted();
    }

    /**
     * Composing the parameters of one row in the order {@link CompositionOrder} gives.
     *
     * <p><b>A parameter another one turns on is not settled at its first value.</b> The container
     * may be one no value of the first lets be built — a set of two booleans that is to hold
     * neither of them — and another value would, directly or through the parameters between them.
     * So where a parameter later in the order turns on this one, each value composed here is handed
     * on, and one the later parameter comes to nothing under is passed over for the next. Where
     * the one that came to nothing does not turn on this one, the walk stops there: nothing here
     * would be different with another value.
     *
     * <p>Where no parameter after it turns on it, the first value is the row's unless
     * {@code taking} passes the row over: every whole row is handed to it, as
     * {@link #inputsFrom} hands its rows, and a row passed over sends the walk on to the next
     * assignment the way a value a later parameter came to nothing under does.
     *
     * @param composed each parameter's value, by its declared position, filled as the walk goes
     * @param taking   what the caller makes of each whole row
     */
    private record InOrder(MeasuredInput subject, CompositionOrder order, FixtureTemplate[] composed,
                           Map<RealizationTarget, Place> standing, LocationWrites decided,
                           Map<TermPath, Place> settled, Reachability.Reaching reaching,
                           CandidateCheck check, ContentsAsked contents, RowTaking taking) {

        /**
         * What the parameters from the {@code next}-th in the order on came to.
         *
         * <p>Rows passed over are rows composed, so where one was, a value after it that came to
         * nothing is said as the rows being passed over and not as nothing composing: what the
         * caller passed them over for is its own to settle.
         *
         * @param elsewhere what stands at the positions of the parameters composed so far that a
         *                  container is handed
         */
        WalkedInOrder from(int next, ValuesHandedOn elsewhere) {
            if (next == order.order().size()) {
                return switch (taking.take(List.of(composed))) {
                    case TAKEN -> WalkedInOrder.TAKEN;
                    case PASSED -> WalkedInOrder.PASSED_OVER;
                    case STOPPED -> WalkedInOrder.HALTED;
                };
            }
            int p = order.order().get(next);
            String head = subject.parameters().get(p);
            // What this parameter's search finds out about its own candidates: one turned away for
            // standing somewhere else, which tells a search that ran out of candidates from one
            // that certified none of the ones it had, and one that built and had nothing to hand
            // on. Per parameter, since it is this parameter's search the answer is about: shared,
            // a candidate turned away under one parameter would name the reason another failed
            // for.
            FoundOut found = new FoundOut();
            CandidateCheck certified = certifying(check, subject, p, standing, found);
            Map<TermPath, List<FixtureTemplate>> here = new LinkedHashMap<>();
            // Every location the row has been asked to write, and not only the ones a number
            // stands at: a truth the way asks for is written and stands at no place.
            for (Map.Entry<TermPath, List<FixtureTemplate>> each
                    : contents.sharedAcross(decided.all()).entrySet()) {
                // A position the way also narrows is not fixed at a value here. What has to hold of
                // it is one thing said two ways — a place the item asks for, and a case the way
                // says the value turned out to be — and one location is decided once: the narrowing
                // says how the value is built and the place says which of the values built that way
                // is accepted ({@link #certifying}). Handed over as both, it is a position with two
                // accounts, which is what {@link ConstructionPlan} refuses and what it is right to
                // refuse.
                if (each.getKey().head().equals(head)
                        && reaching.requirements().at(each.getKey()) == null) {
                    here.put(each.getKey(), each.getValue());
                }
            }
            boolean awaited = order.awaited(next);
            // What the parameters after this one came to with the value handed on last, every
            // value of this one a parameter after it came to nothing under, and whether a row
            // composed with one of them was passed over.
            WalkedInOrder[] after = {null};
            List<ParameterCameToNothing> cameToNothing = new ArrayList<>();
            boolean[] passed = {false};
            // What the rows passed over left found out beside them, from every value of this one.
            SearchShortfall[] passedFound = {SearchShortfall.NONE};
            ValueTaking taking = value -> {
                composed[p] = value.value();
                after[0] = from(next + 1, elsewhere.and(value.read()));
                return switch (after[0]) {
                    case WalkedInOrder.RowTaken _ -> Acceptance.TAKEN;
                    case WalkedInOrder.PassedOver(SearchShortfall its) -> {
                        passed[0] = true;
                        passedFound[0] = passedFound[0].and(its);
                        yield Acceptance.PASSED;
                    }
                    case WalkedInOrder.Halted _ -> Acceptance.STOPPED;
                    // A parameter after this one that does not turn on this one's value cannot be
                    // composed with any other value of it either, and the walk here is stopped with
                    // what that one said. One that does may be, so the next is tried.
                    case WalkedInOrder.CameToNothingAt(ParameterCameToNothing why) -> {
                        if (!awaited || !order.mayTurnOn(why.parameter(), p)) {
                            yield Acceptance.STOPPED;
                        }
                        cameToNothing.add(why);
                        yield Acceptance.PASSED;
                    }
                };
            };
            Outcome tried = valueAt(subject, p, here, sizesUnder(decided,
                            TermPath.of(head)), settled, reaching.requirements(),
                    new Handed(contents, elsewhere), certified, found, taking);
            return switch (tried) {
                // Taken where the rest was composed with it.
                case Outcome.Built _ -> after[0];
                // Every value passed over: for a row the caller passed over, or for what a
                // parameter after it came to under each of them — said over all of them.
                case Outcome.PassedOver _ -> overTheAlternatives(cameToNothing,
                        passed[0] ? passedFound[0] : null, found.shortfall());
                // Stopped by the caller, which is the answer as it stands; or by a parameter after
                // this one that nothing could be composed for whatever this one is. Where nothing
                // after it turns on it, that is said as it came, the value before it being the
                // first; otherwise with the values before it that one came to nothing under.
                case Outcome.Halted _ -> {
                    if (!(after[0] instanceof WalkedInOrder.CameToNothingAt(
                            ParameterCameToNothing why))) {
                        yield passed[0] ? overTheAlternatives(cameToNothing, passedFound[0],
                                found.shortfall()) : after[0];
                    }
                    yield !awaited && !passed[0] ? after[0] : overTheAlternatives(
                            withFirst(why, cameToNothing), passed[0] ? passedFound[0] : null,
                            found.shortfall());
                }
                // Its own search came to nothing, which ended the walk.
                case Outcome.Unresolved _, Outcome.Stopped _, Outcome.Unexhausted _,
                     Outcome.OfferShort _, Outcome.Limited _, Outcome.Unplanned _ ->
                        overTheAlternatives(withFirst(
                                new ParameterCameToNothing(p, tried, found.shortfall(), here),
                                cameToNothing), passed[0] ? passedFound[0] : null,
                                found.shortfall());
            };
        }

        /**
         * What the alternatives came to, said as a walk: the row passed over with what was found
         * beside it where one was, and otherwise the parameter they came to nothing at.
         *
         * <p>The same composition {@link WhatTheAlternativesCameTo} gives every search that passes
         * rows, so a row passed over keeps what the others came to and a proof among them is not
         * read as the walk's. Where none was, what every value tried came to is said with what
         * this parameter's search found out about its own candidates, which is the point's to know
         * whichever parameter the word is said at: a value another parameter came to nothing
         * under is not every value there was where a value of this one was not handed on.
         */
        private static WalkedInOrder overTheAlternatives(List<ParameterCameToNothing> cameToNothing,
                                                         SearchShortfall passedOver,
                                                         SearchShortfall found) {
            return switch (WhatTheAlternativesCameTo.over(cameToNothing, passedOver, found,
                    PARAMETERS)) {
                case WhatTheAlternativesCameTo.Came.PassedOver<ParameterCameToNothing>(
                        SearchShortfall its) -> new WalkedInOrder.PassedOver(its);
                case WhatTheAlternativesCameTo.Came.Said<ParameterCameToNothing>(
                        ParameterCameToNothing said) -> new WalkedInOrder.CameToNothingAt(said);
                case WhatTheAlternativesCameTo.Came.Untried<ParameterCameToNothing> _,
                     WhatTheAlternativesCameTo.Came.NothingToSayItIn<ParameterCameToNothing> _ ->
                        throw new IllegalStateException(
                                "a value was tried and nothing is said of what came of it");
            };
        }
    }

    /**
     * The values the inputs hold that the targets are asked for — the key a count of elements, or
     * a total of them, is of — placed before the elements are composed: they are composed holding
     * them, and each is another input's.
     *
     * <p>The key of a fold asked for twice is two keys, and held at one value they would be one,
     * whose elements come to the one number asked of both: so the later is held away from the
     * earlier. A key that is what each element adds is chosen where the number is.
     *
     * @param keysPlaced the keys placed so far, by the target they are the key of, which this adds
     *                   to
     * @return the region with what was placed given to it
     */
    private static SearchRegion placeKeysAskedFor(
            Collection<Map.Entry<RealizationTarget, Place>> targets, SearchRegion region,
            MeasuredInput subject, Map<RealizationTarget, Place> out,
            Map<NumericTerm, RealizationTarget> routed, Set<RealizationTarget> chosen,
            List<ReachabilityGap> gaps, Map<RealizationTarget, Place> keysPlaced,
            WitnessSearch looking, Reachability.Reaching reaching) {
        SearchRegion here = region;
        for (Map.Entry<RealizationTarget, Place> each : targets) {
            TermPath keyAsked = each.getKey().keyAskedFor();
            if (keyAsked == null) {
                continue;
            }
            NumericTerm.FromOnePosition key = new NumericTerm.ValueOf(keyAsked);
            if (out.containsKey(RealizationTarget.of(key))) {
                continue;
            }
            Function<NumericTerm, Carrier> on = term -> {
                TermOrders orders = subject.quantities().ordersOf(term);
                return orders == null ? null : orders.observed();
            };
            if (each.getKey().keyIsTheNumber()) {
                here = here.given(key, each.getValue());
            }
            // Held away from the keys of the same fold placed already where that can be, which is
            // a way to try and not a rule: the rules and the way here may say the two are one value,
            // and a row at which they are is as much a row.
            SearchRegion apart = here;
            for (Map.Entry<RealizationTarget, Place> earlier : keysPlaced.entrySet()) {
                if (each.getKey().keyIsToldApartFrom(earlier.getKey())) {
                    apart = apart.apartFrom(key, earlier.getValue());
                }
            }
            NumericWitness.Standing placing = NumericWitness.of(apart, List.of(key), on, looking);
            if (apart != here && !(placing instanceof NumericWitness.Standing.Found)) {
                placing = NumericWitness.of(here, List.of(key), on, looking);
            }
            switch (placing) {
                case NumericWitness.Standing.Found beside -> {
                    for (NumericWitness.Standing.Found.Placed placed : beside.inFixingOrder()) {
                        RealizationTarget.OfANumber at = RealizationTarget.of(placed.term());
                        if (out.putIfAbsent(at, placed.place()) == null) {
                            routed.put(placed.term(), at);
                            chosen.add(at);
                            here = here.given(placed.term(), placed.place());
                        }
                        if (placed.term().equals(key)) {
                            keysPlaced.put(each.getKey(), placed.place());
                        }
                    }
                }
                // Said against a condition on the way where there is one; a row held to none is
                // composed with the key at no one value, which the composing says.
                case NumericWitness.Standing.ProvedImpossible _ ->
                        reaching.boundedOnTheWay().stream().findFirst().ifPresent(cut ->
                                gaps.add(new ReachabilityGap.Uncomposed(cut,
                                        new ReachabilityGap.Why.NoValueComposedForItsPositions())));
                case NumericWitness.Standing.NotFound(CompositionShortfall met) ->
                        reaching.boundedOnTheWay().stream().findFirst().ifPresent(cut ->
                                gaps.add(new ReachabilityGap.Uncomposed(cut,
                                        ReachabilityGap.Why.ofAWalkThatFoundNothing(met))));
            }
        }
        return here;
    }

    /**
     * The item's positions, and a place inside the region for each position the way to it bounds.
     *
     * <p><b>Chosen and not left to the range.</b> What the conditions above a line leave a position
     * is a run, and every value of that run reaches the line as well as any other — so one of them
     * is taken and the row is written there. Left as a run for the composer to fill from the
     * declarations, the value it took was the bottom of the declared type, which is outside the run
     * wherever a condition above the line moved it: the row then carried the line's value and turned
     * back before reaching the comparison.
     *
     * <p>One at a time, with the region told what was chosen before the next is asked. A condition
     * relating two positions leaves neither of them a run the other's choice does not move, so two
     * places taken from two independent runs meet the rules only where they happen to.
     *
     * <p>A position this cannot place is left out rather than refused. There is no order to read it
     * on, the region says nothing about it, or nothing of the carrier lies in what is left — none of
     * those is a row that cannot be written, and each is a row this composes the way it did before
     * the way was carried here at all.
     *
     * @param everyQuantifierCounted whether every container a quantifier that is the whole of a
     *                               statement is over is composed for how many of its elements
     *                               meet each statement, and not only one a quantifier asks several
     *                               things of an element over, or two quantifiers are over
     * @param itemAsks       what the item asks of each number it fixes, which is what a value
     *                       composed at its location is composed for
     * @param check          what a value's own type says of it, which a location a cut's numbers
     *                       are composed at is held to
     * @param alikeStoppedBy the figure the ways of writing the elements alike were looked along
     *                       to, where one stopped them, or null
     * @param leaves         what {@code reaching} leaves each number placed on it
     */
    private static Standing alsoOnTheWay(MeasuredInput subject, Map<RealizationTarget, Place> fixing,
                                         Map<RealizationTarget, NumbersAskedFor> itemAsks,
                                         CandidateCheck check, Reachability.Reaching reaching,
                                         boolean everyQuantifierCounted,
                                         CompositionBudget alikeStoppedBy,
                                         WhatTheWayLeaves leaves) {
        Map<RealizationTarget, Place> out = new LinkedHashMap<>(fixing);
        Map<NumericTerm, RealizationTarget> routed = new LinkedHashMap<>();
        Map<RealizationTarget, NumbersAskedFor> counted = new LinkedHashMap<>();
        // What composing each location a cut placed a number at came to, where the cut was placed:
        // the value the row is written with wherever nothing asked of the location since.
        Map<TermPath, ComposedAt> composed = new LinkedHashMap<>();
        // The numbers standing because a condition chose where, rather than the point fixing it.
        Set<RealizationTarget> chosen = new LinkedHashSet<>();
        Set<RealizationTarget> someElement = new LinkedHashSet<>();
        List<ReachabilityGap> gaps = new ArrayList<>();
        SearchRegion here = reaching.region();
        for (Map.Entry<RealizationTarget, Place> each : fixing.entrySet()) {
            // A count is no number the region holds a range of, so it narrows nothing here; what
            // the statement reads beside an element is fixed beside it as a number of its own.
            if (each.getKey() instanceof RealizationTarget.OfANumber number) {
                here = here.given(number.term(), each.getValue());
            }
        }
        // The region as the point leaves it, before any condition chose a place, which is what a
        // proof is asked of.
        SearchRegion unchosen = here;
        // Once for the input rather than once for each condition on the way. What its positions
        // admit is the same answer at every one of them, and working it out where it is spent walks
        // every position of the input once per condition.
        WitnessSearch looking = subject.witnessSearch();
        // What the row is taken to be, beginning with what the way it arrives by already settled
        // and the places the item is written at. One account for every cut, because a row is one
        // value: a name of a sum sent under a case by one cut and under another by the next would
        // be asking for a value that is both, and which of the two a name got would depend on the
        // order the cuts were read in. And a number of the item written under a case has taken
        // the row there already, so a cut's name of the same sum is written under it too.
        //
        // The item is on the way. A caller holding a reading the way may not take asks that first
        // ({@link Reachability.Reaching#writing}) and answers it without composing, so an item off
        // the way here is a caller that did not ask.
        if (!(reaching.writing(fixing.keySet())
                instanceof Reachability.Written.Under(Requirements onTheWay))) {
            throw new IllegalStateException("the item is written under a case the way it is"
                    + " reached by does not take: " + fixing.keySet() + " along "
                    + reaching.requirements());
        }
        Requirements assumed = onTheWay;
        // The value a number of how often it occurs is counted for, placed before the occurrences
        // are composed: they are composed holding it, and it is another input's.
        Map<RealizationTarget, Place> keysPlaced = new LinkedHashMap<>();
        here = placeKeysAskedFor(fixing.entrySet(), here, subject, out, routed, chosen, gaps,
                keysPlaced, looking, reaching);
        // The count the item itself asks for, which is the one count its level is — by which
        // count it is, so a condition on the way asking for the same count asks it of this one.
        Map<CountedElements.Identity, RealizationTarget.ACount> itemCounts = new LinkedHashMap<>();
        for (Map.Entry<RealizationTarget, Place> each : fixing.entrySet()) {
            if (each.getKey() instanceof RealizationTarget.ACount count) {
                itemCounts.put(count.count().identity(), count);
                counted.put(count, NumbersAskedFor.of(LevelRegion.point(
                        new Level.OfTheQuantity(Count.number(each.getValue()).exactly()))));
            }
        }
        // How many elements of a container meet a statement, as every condition on the way asks
        // it, gathered by which count it is before any is taken in: two conditions on one count
        // are met where both are, and which count that is cannot be read off either alone.
        Map<CountedElements.Identity, CountsAsked> countsOnTheWay = new LinkedHashMap<>();
        // What the conditions holding a count against a number alone leave of it, and the item's
        // own where it is that count: known before any number of the row is put anywhere, so a
        // count held against such numbers puts them where some of what is left is still there.
        Map<CountedElements.Identity, LevelRegion> leftOfACount = new LinkedHashMap<>();
        // What an element meets several ways, where it is the whole of what the quantifier asks,
        // is how many elements meet the statement: one or more of them, or none. A container
        // composed for that count is composed element by element, so its elements may meet the
        // statement different ways, which elements written alike do not — and every other
        // quantifier over it is a count of it as well, since the container is written once. A
        // container two quantifiers are over is composed for its counts where every quantifier is
        // asked to be: what each asks of an element may be what no one element is, and elements
        // written alike are the other way of meeting them, which a container no count is composed
        // for at is written by.
        Set<TermPath> byCounts = new HashSet<>();
        // A condition of several ways the way was not split at is composed past along the whole.
        // Where it states something of the elements of one container and of nothing else, the
        // container is composed against the statement whole — every way of it at once and none
        // taken first — and so composed for its counts, its elements meeting the statement each
        // their own way. Any other says so: along one of its ways the row would be composed
        // against more.
        if (reaching.ways() instanceof Reachability.Ways.Whole(var unsplit, var figure, var _,
                var _)) {
            for (OnTheWay each : unsplit) {
                Optional<RealizationTarget.ElementsMeetingTogether> stated =
                        RealizationTarget.ElementsMeetingTogether.of(subject.behavior(), each);
                if (stated.isEmpty()) {
                    gaps.add(new ReachabilityGap.LookedAlongWhole(each, figure));
                    continue;
                }
                RealizationTarget.ElementsMeetingTogether together = stated.get();
                byCounts.add(together.container());
                out.put(together, Count.of(1));
                counted.put(together, NumbersAskedFor.of(LevelRegion.point(
                        new Level.OfTheQuantity(ExactRatio.ONE))));
            }
        }
        for (OnTheWay.TakenIn cut : reaching.boundedOnTheWay()) {
            if (countedOf(cut.demand()).isEmpty()) {
                continue;
            }
            if (everyQuantifierCounted || !RowDemand.writtenAlikeAsItStands(cut.demand())) {
                byCounts.add(containerOf(cut.demand()));
            }
        }
        List<OnTheWay.TakenIn> cuts = new ArrayList<>();
        for (OnTheWay.TakenIn cut : reaching.boundedOnTheWay()) {
            cuts.add(countedOf(cut.demand()).isPresent()
                    && byCounts.contains(containerOf(cut.demand())) ? asACount(cut) : cut);
        }
        // And a number of the item inside an element of such a container is where some element
        // stands, which the container is composed holding — its elements are not written alike,
        // so there is no every element for it to be the value of.
        for (RealizationTarget each : fixing.keySet()) {
            if (insideAnElementOf(each, byCounts)) {
                someElement.add(each);
            }
        }
        for (OnTheWay.TakenIn cut : cuts) {
            if (cut.demand() instanceof RowDemand.SoMany many && !many.againstNumbers()) {
                leftOfACount.merge(CountedElements.identityOf(subject.behavior(), many.count()),
                        many.counts().values(), LevelRegion::meet);
            }
        }
        itemCounts.forEach((identity, itemCount) -> leftOfACount.merge(identity,
                counted.get(itemCount).values(), LevelRegion::meet));
        // The conditions relating numbers that are placed together, because what one of them
        // chooses is written where another's numbers are ({@link #placedTogether}), and the ones
        // already placed with an earlier one.
        Map<OnTheWay.TakenIn, List<OnTheWay.TakenIn>> relatedThroughWhatTheyWrite =
                placedTogether(cuts);
        Set<OnTheWay.TakenIn> placedWithAnother = new HashSet<>();
        // What every element of a container is to meet, where other numbers of the row are
        // written at the container and the condition is a bound on its elements rather than a
        // value of one of them ({@link ElementBound}). Whether it was is settled once every other
        // condition is placed: where nothing stands at the container by then, nothing composes it
        // under the bound, and the condition is placed as the value it otherwise is.
        Map<OnTheWay.TakenIn, ElementBound> boundsOnTheElements = boundsOnTheElements(subject,
                cuts, fixing.keySet());
        List<ElementBound> bounds = List.copyOf(boundsOnTheElements.values());
        // The counts the way asks for that are settled by nothing a condition places, each at the
        // least of what the conditions on it leave: where they will stand is known before any
        // condition is placed, so a condition whose numbers are written at the same container is
        // composed beside them rather than finding out once they are placed. Not a count held
        // against numbers of the row, nor one whose statement reads a number of anything but the
        // container's own elements — another position, or the elements of another container:
        // which elements meet it turns on where those are put, which is decided after, and
        // composed before them it would be composed for none of them.
        Map<CountedElements.Identity, CountedElements> countedBefore = new LinkedHashMap<>();
        Set<CountedElements.Identity> readingOutside = new HashSet<>();
        for (OnTheWay.TakenIn cut : cuts) {
            if (cut.demand() instanceof RowDemand.SoMany many && !many.againstNumbers()) {
                CountedElements count = CountedElements.of(subject.behavior(), many.count(),
                        subject.quantities(), many.anElementMeeting());
                if (itemCounts.containsKey(count.identity())) {
                    continue;
                }
                if (count.numbers().stream().anyMatch(
                        term -> !term.subjectPath().isAtOrUnder(count.container().element()))) {
                    readingOutside.add(count.identity());
                }
                countedBefore.merge(count.identity(), count, CountedElements::and);
            }
        }
        countedBefore.keySet().removeAll(readingOutside);
        Map<RealizationTarget, Place> countsToCome = new LinkedHashMap<>();
        Map<RealizationTarget, NumbersAskedFor> countsAsked = new LinkedHashMap<>();
        countedBefore.forEach((identity, count) -> {
            LevelRegion left = leftOfACount.get(identity);
            if (left != null && count.leastIn(left) instanceof CountedElements.Least.At(
                    Count least)) {
                RealizationTarget.ACount target = new RealizationTarget.ACount(count);
                countsToCome.put(target, least);
                countsAsked.put(target, NumbersAskedFor.of(left));
            }
        });
        // And the values the counts a condition asks for are counts of, which the container is
        // composed holding as it is for the item's own.
        here = placeKeysAskedFor(countsToCome.entrySet(), here, subject, out, routed, chosen, gaps,
                keysPlaced, looking, reaching);
        // How a value is composed where a cut's numbers stand, asked as the row is composed: in the
        // way's region, for what each number is one of with the cut's own numbers routed beside the
        // ones already standing, under the bounds on the elements.
        WayComposer composer = new WayComposer(subject, reaching.region(), unchosen, check, chosen,
                routes -> {
                    Map<NumericTerm, RealizationTarget> all = new LinkedHashMap<>(routed);
                    all.putAll(routes);
                    Map<RealizationTarget, NumbersAskedFor> asked =
                            whatEachOfThemIsANumberOf(itemAsks, all, counted, leaves);
                    countsAsked.forEach(asked::putIfAbsent);
                    return asked;
                }, bounds, countsToCome);
        for (OnTheWay.TakenIn cut : cuts) {
            if (cut.demand() instanceof RowDemand.SoMany many) {
                CountedElements count = CountedElements.of(subject.behavior(), many.count(),
                        subject.quantities(), many.anElementMeeting());
                LevelRegion counts;
                if (many.againstNumbers()) {
                    // The count is held against what numbers of the row add up to, so which counts
                    // meet it is known once those numbers stand somewhere: placed here, as numbers
                    // beside an element are, and the count asked for is the one that goes with them.
                    List<NumericTerm.FromOnePosition> added = new ArrayList<>();
                    for (NumericTerm term : NumericTerms.inOrder(many.against().coefs().keySet())) {
                        added.add(term.atOnePosition());
                    }
                    Function<NumericTerm, Carrier> on = term -> {
                        TermOrders orders = subject.quantities().ordersOf(term);
                        return orders == null ? null : orders.observed();
                    };
                    switch (NumericWitness.of(leavingACount(here, many, count,
                            leftOfACount.get(count.identity())), added, on, looking)) {
                        case NumericWitness.Standing.Found standing -> {
                            Map<NumericTerm, Place> standingAt = new LinkedHashMap<>();
                            for (NumericWitness.Standing.Found.Placed placed
                                    : standing.inFixingOrder()) {
                                RealizationTarget.OfANumber at = RealizationTarget.of(placed.term());
                                // A number already standing was given to the region, so it is
                                // placed where it stands.
                                if (out.putIfAbsent(at, placed.place()) == null) {
                                    routed.put(placed.term(), at);
                                    chosen.add(at);
                                    here = here.given(placed.term(), placed.place());
                                }
                                standingAt.put(placed.term(), placed.place());
                            }
                            counts = switch (OrderedAffineBoundary.at(many.against(), standingAt)) {
                                case ExactAnswer.Held<ExactRatio>(ExactRatio sum) ->
                                        many.countsWhere(sum);
                                case ExactAnswer.Unheld<ExactRatio> _ -> null;
                            };
                            if (counts == null) {
                                gaps.add(new ReachabilityGap.Uncomposed(cut,
                                        new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                                continue;
                            }
                        }
                        case NumericWitness.Standing.ProvedImpossible _ -> {
                            gaps.add(new ReachabilityGap.Uncomposed(cut,
                                    new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                            continue;
                        }
                        case NumericWitness.Standing.NotFound(CompositionShortfall met) -> {
                            gaps.add(new ReachabilityGap.Uncomposed(cut,
                                    ReachabilityGap.Why.ofAWalkThatFoundNothing(met)));
                            continue;
                        }
                    }
                } else {
                    counts = many.counts().values();
                }
                countsOnTheWay.merge(count.identity(),
                        new CountsAsked(count, counts, many.againstNumbers(), cut),
                        CountsAsked::and);
                continue;
            }
            // What a division leaves of a form, placed at a value of the form that leaves one of
            // the remainders asked for.
            if (cut.demand() instanceof RowDemand.OnARemainder remainder) {
                // On what each number of the form counts, which is what the form adds up: what the
                // code points of a string come to is a whole number, and not the string.
                Function<NumericTerm, Carrier> on = term -> {
                    TermOrders orders = subject.quantities().ordersOf(term);
                    return orders == null ? null : orders.answered();
                };
                switch (standingOnARemainder(here, remainder, on, looking)) {
                    case NumericWitness.Standing.Found standing -> {
                        for (NumericWitness.Standing.Found.Placed placed
                                : standing.inFixingOrder()) {
                            RealizationTarget.OfANumber at = RealizationTarget.of(placed.term());
                            if (out.putIfAbsent(at, placed.place()) == null) {
                                routed.put(placed.term(), at);
                                chosen.add(at);
                                here = here.given(placed.term(), placed.place());
                            }
                        }
                    }
                    case NumericWitness.Standing.ProvedImpossible _ -> gaps.add(
                            new ReachabilityGap.Uncomposed(cut,
                                    new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                    case NumericWitness.Standing.NotFound(CompositionShortfall met) -> gaps.add(
                            new ReachabilityGap.Uncomposed(cut,
                                    ReachabilityGap.Why.ofAWalkThatFoundNothing(met)));
                }
                continue;
            }
            // What an element meets one of several ways, with none chosen: a row whose elements
            // are written alike writes one of them into every element, and which one is chosen
            // before the row is composed ({@link ElementsWrittenAlike}). Composed with none chosen,
            // nothing is placed for it and the elements written alike are why — or the figure the
            // choosing stopped at, where it left some ways unlooked along.
            if (!RowDemand.writtenAlikeAsItStands(cut.demand())) {
                gaps.add(new ReachabilityGap.Uncomposed(cut, alikeStoppedBy == null
                        ? new ReachabilityGap.Why.ElementsWrittenAlike()
                        : ReachabilityGap.Why.TheWalkForItsPositionsWasStopped.by(
                                CompositionShortfall.of(Set.of(alikeStoppedBy)))));
                continue;
            }
            // A statement no composer writes toward: nothing is placed for it, and the run is what
            // says whether the row met it.
            if (cut.demand() instanceof RowDemand.ForTheRun(var _, var why, var past)) {
                gaps.add(new ReachabilityGap.Uncomposed(cut,
                        new ReachabilityGap.Why.NoComposerWritesIt(why, past)));
                continue;
            }
            // What an element is asked with no relation among it has no number to place: that the
            // element is another position's value is met where the container is composed
            // ({@link ContentsAsked}), and a region has nothing to say about it.
            if (placesNoNumber(cut.demand())) {
                continue;
            }
            // A bound on the elements of a container something else writes, settled once the rest
            // of the way is placed.
            if (boundsOnTheElements.containsKey(cut) || !placedWithAnother.add(cut)) {
                continue;
            }
            List<OnTheWay.TakenIn> placedAsOne =
                    relatedThroughWhatTheyWrite.getOrDefault(cut, List.of(cut));
            placedWithAnother.addAll(placedAsOne);
            // The conditions whose numbers are written where one another's are, placed as one:
            // the numbers of all of them chosen by one walk and composed together, so what one of
            // them chooses is never a value the next has to stand beside however it can.
            ReachabilityGap asOne = null;
            if (placedAsOne.size() > 1) {
                List<TakenConstraint> relations = new ArrayList<>();
                for (OnTheWay.TakenIn each : placedAsOne) {
                    relations.add(((RowDemand.Relational) each.demand()).constraint());
                }
                switch (placedIn(subject, composer, looking, here, out, someElement, assumed,
                        placedAsOne.getFirst(), relations, false)) {
                    case Placed.AtAll all -> {
                        here = taking(all, here, out, routed, composed, chosen, someElement);
                        assumed = all.assumed();
                        continue;
                    }
                    // The conditions are all on the way to the point, and the rules leave them
                    // nothing together — which is the way, and not one of them.
                    case Placed.AtNone(ReachabilityGap.ProvedImpossible _) -> {
                        gaps.add(new ReachabilityGap.ProvedImpossible(placedAsOne.getFirst()));
                        continue;
                    }
                    case Placed.AtNone(ReachabilityGap why) -> asOne = why;
                }
            }
            // The whole of what one cut comes to, arrived at before any of it is the row's. What a
            // cut takes is one decision — where each of its numbers stands, where the row writes
            // them, and what the row had to be taken as — and a reader that applied the parts as it
            // found them would leave a case chosen on the way to a cut that came to nothing.
            //
            // One at a time as well where placing them as one came to nothing: what can be placed
            // is placed, and the rest are said as conditions the row was composed without. Never
            // as more than that. Each was asked beside what the ones before it chose, which the
            // rules did not force, so what a condition placed alone came to is joined with what
            // the walk over all of them came to — a figure that stopped that walk is a figure that
            // stopped this one ({@link ReachabilityGap#overEveryWay}).
            for (OnTheWay.TakenIn each : placedAsOne) {
                switch (placing(subject, composer, looking, here, out, someElement, assumed,
                        each)) {
                    case Placed.AtNone(ReachabilityGap why) -> gaps.add(
                            asOne instanceof ReachabilityGap.Uncomposed(var _, var whyTogether)
                                    && !(why instanceof ReachabilityGap.ProvedImpossible)
                                    ? ReachabilityGap.overEveryWay(each, List.of(why,
                                            new ReachabilityGap.Uncomposed(each, whyTogether)),
                                            false)
                                    : why);
                    case Placed.AtAll all -> {
                        here = taking(all, here, out, routed, composed, chosen, someElement);
                        assumed = all.assumed();
                    }
                }
            }
        }
        // Each count the way asks for, taken in whole or not at all: the counts every condition
        // on it leaves, and a place for each number its statement reads beside an element.
        for (Map.Entry<CountedElements.Identity, CountsAsked> each : countsOnTheWay.entrySet()) {
            CountedElements count = each.getValue().count();
            RealizationTarget.ACount itemCount = itemCounts.get(each.getKey());
            RealizationTarget.ACount target =
                    itemCount != null ? itemCount : new RealizationTarget.ACount(count);
            OnTheWay.TakenIn cut = each.getValue().first();
            LevelRegion asked = each.getValue().counts();
            if (itemCount != null) {
                asked = asked.meet(counted.get(itemCount).values());
            }
            Count least;
            switch (count.leastIn(asked)) {
                case CountedElements.Least.At(Count at) -> least = at;
                // No count the conditions leave together — and the item's own, where it asks for
                // this one — is a way no row passes, which the counts settle by themselves. Not
                // where a count was held against numbers of the row: the counts it left are those
                // of the values those numbers were put at, and other values may leave some.
                case CountedElements.Least.None _ -> {
                    gaps.add(each.getValue().turnsOnTheRowsNumbers()
                            ? new ReachabilityGap.Uncomposed(cut,
                                    new ReachabilityGap.Why.NoValueComposedForItsPositions())
                            : new ReachabilityGap.ProvedImpossible(cut));
                    continue;
                }
                // A count that could not be worked out settles nothing about whether one is there.
                case CountedElements.Least.NotWorkedOut(UnheldNumber why) -> {
                    gaps.add(new ReachabilityGap.Uncomposed(cut,
                            ReachabilityGap.Why.TheWalkForItsPositionsWasStopped.by(
                                    CompositionShortfall.of(Set.of(), Set.of(),
                                            Set.of(new CompositionCapacity(
                                                    CompositionCapacity.Where
                                                            .THE_LEAST_COUNT_ASKED_FOR,
                                                    why))))));
                    continue;
                }
            }
            // The item's own count was placed with the numbers beside it where the item was.
            if (itemCount != null) {
                counted.put(target, NumbersAskedFor.of(asked));
                continue;
            }
            // Another number already written at the container, which the count is composed beside
            // or not at all — asked as a condition's numbers are asked ({@link #writtenTogether}).
            // Placed regardless, the container would be asked for both where the row is composed,
            // and nothing composing one value for them would take the whole row with it.
            List<RealizationTarget> besideTheCount = alsoWritingAt(out.keySet(), target.writeRoot());
            if (!besideTheCount.isEmpty() && !writtenTogether(besideTheCount, target, someElement)) {
                gaps.add(new ReachabilityGap.Uncomposed(cut,
                        new ReachabilityGap.Why.TwoNumbersAtOneLocation()));
                continue;
            }
            switch (count.placesBeside(here,
                    !asked.contains(new Level.OfTheQuantity(ExactRatio.ZERO)), looking)) {
                case NumericWitness.Standing.Found beside -> {
                    for (NumericWitness.Standing.Found.Placed placed : beside.inFixingOrder()) {
                        if (placed.term().subjectPath().insideAContainer()) {
                            continue;
                        }
                        RealizationTarget.OfANumber at = RealizationTarget.of(placed.term());
                        // Placed on the way, so what it is one of is what the rules leave it
                        // there. A number already standing was given to the region, so it is
                        // placed where it stands.
                        if (out.putIfAbsent(at, placed.place()) == null) {
                            routed.put(placed.term(), at);
                            chosen.add(at);
                            here = here.given(placed.term(), placed.place());
                        }
                    }
                    // The least of the counts left, which is a count this chose and not one the
                    // rules forced.
                    out.put(target, least);
                    chosen.add(target);
                    counted.put(target, NumbersAskedFor.of(asked));
                }
                // Not placed, and no proof either: the region was narrowed by the statement here
                // and not by the rules.
                case NumericWitness.Standing.ProvedImpossible _ ->
                        gaps.add(new ReachabilityGap.Uncomposed(cut,
                                new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                // And where a figure or a number not held is why, that travels.
                case NumericWitness.Standing.NotFound(CompositionShortfall met) ->
                        gaps.add(new ReachabilityGap.Uncomposed(cut,
                                ReachabilityGap.Why.ofAWalkThatFoundNothing(met)));
            }
        }
        // Each bound on the elements of a container: taken in where a number of the row stands at
        // the container, which is composed under it, and otherwise placed as the value it is when
        // nothing else writes the container.
        for (Map.Entry<OnTheWay.TakenIn, ElementBound> each : boundsOnTheElements.entrySet()) {
            if (alsoWritingAt(out.keySet(), each.getValue().container()).isEmpty()) {
                switch (placing(subject, composer, looking, here, out, someElement, assumed,
                        each.getKey())) {
                    case Placed.AtNone(ReachabilityGap why) -> gaps.add(why);
                    case Placed.AtAll all -> {
                        here = taking(all, here, out, routed, composed, chosen, someElement);
                        assumed = all.assumed();
                    }
                }
            }
        }
        return new Standing(out, routed, counted, Set.copyOf(someElement), composed,
                Collections.unmodifiableSet(new LinkedHashSet<>(chosen)), bounds,
                CompositionAccount.ofTheInput(gaps));
    }

    /**
     * The conditions that every element of a container meets something which are bounds on its
     * elements, each with the bound: a container some number of the row may be written at besides
     * — a number a condition relating numbers names, a count of its elements a condition asks
     * for, or one the item fixes — and what every element is to meet along one way, over nothing
     * but the element.
     *
     * <p>A count of its elements among them. How many elements meet a statement decides which
     * elements the container holds, so the elements of a container composed for a count are
     * chosen there — and a bound left out of that composing is a condition on every element the
     * chosen ones were never held to.
     *
     * <p>Over nothing but the element, because a bound is part of what the container is composed
     * under, and a number outside it is one the composing does not choose. And along one way: a
     * statement an element meets one of several ways is no conjunction to narrow by, and it is said
     * where it is met ({@link ElementsWrittenAlike}).
     */
    private static Map<OnTheWay.TakenIn, ElementBound> boundsOnTheElements(
            MeasuredInput subject, List<OnTheWay.TakenIn> cuts, Set<RealizationTarget> fixed) {
        List<TermPath> writtenBesides = new ArrayList<>();
        for (RealizationTarget each : fixed) {
            writtenBesides.add(each.writeRoot());
        }
        for (OnTheWay.TakenIn cut : cuts) {
            switch (cut.demand()) {
                case RowDemand.Relational(var relation) -> {
                    for (NumericTerm term : relation.terms()) {
                        writtenBesides.add(RealizationTarget.of(term).writeRoot());
                    }
                }
                case RowDemand.OnARemainder remainder -> {
                    for (NumericTerm term : remainder.terms()) {
                        writtenBesides.add(RealizationTarget.of(term).writeRoot());
                    }
                }
                case RowDemand.SoMany many -> writtenBesides.add(new RealizationTarget.ACount(
                        CountedElements.of(subject.behavior(), many.count(), subject.quantities(),
                                many.anElementMeeting())).writeRoot());
                case RowDemand.Exists _, RowDemand.ForAll _, RowDemand.ATruth _,
                     RowDemand.OneValueAtBoth _, RowDemand.ForTheRun _ -> { }
            }
        }
        Map<OnTheWay.TakenIn, ElementBound> out = new LinkedHashMap<>();
        for (OnTheWay.TakenIn cut : cuts) {
            if (!(cut.demand() instanceof RowDemand.ForAll every)
                    || !RowDemand.writtenAlikeAsItStands(every)
                    || every.relations().isEmpty()) {
                continue;
            }
            List<TakenConstraint> ofEachElement = constraints(every.relations());
            boolean overTheElement = ofEachElement.stream()
                    .flatMap(each -> each.terms().stream())
                    .allMatch(term -> term.subjectPath().isAtOrUnder(every.container().element()));
            if (overTheElement && writtenAtOneLocation(List.of(every.container()), writtenBesides)) {
                out.put(cut, new ElementBound(every.container(), ofEachElement,
                        every.holdingNone().constraint()));
            }
        }
        return out;
    }

    /**
     * What one placing takes into the row, and the region the rest of the way is placed in after
     * it.
     *
     * <p>The target each number was routed to, and never one built from the number again. Built
     * here a second time, the place the row writes would be worked out twice — once where the cut
     * was read and once where its answer is filed — and the two would part at exactly the name the
     * routing exists for.
     */
    private static SearchRegion taking(Placed.AtAll placed, SearchRegion here,
                                       Map<RealizationTarget, Place> out,
                                       Map<NumericTerm, RealizationTarget> routed,
                                       Map<TermPath, ComposedAt> composed,
                                       Set<RealizationTarget> chosen,
                                       Set<RealizationTarget> someElement) {
        routed.putAll(placed.routes());
        for (ComposedAt each : placed.composed()) {
            composed.put(each.at(), each);
        }
        SearchRegion after = here;
        for (NumericWitness.Standing.Found.Placed each : placed.standing().inFixingOrder()) {
            after = after.given(each.term(), each.place());
        }
        placed.owing().forEach((target, asked) ->
                out.put(target, placed.standing().placeOf(asked)));
        chosen.addAll(placed.owing().keySet());
        someElement.addAll(placed.someElement());
        return after;
    }

    /**
     * The conditions relating numbers on the way, each with every condition it is placed with:
     * itself and the ones whose numbers are written where its own are, and the ones written where
     * those are, in the order the way names them.
     *
     * <p><b>By what they write and not by one location.</b> A condition over two numbers written at
     * two locations is one statement about both, so it joins what is written at either: placed
     * apart, the condition at one location and the condition at the other would each be answered
     * with the other's numbers already chosen. Which two locations are one is
     * {@link LocationWrites}' answer.
     *
     * <p>Only conditions relating numbers. A condition on the elements of a container asks each
     * element, or some, something the region was never narrowed by, and is placed on its own as it
     * is ({@link #placing}).
     */
    private static Map<OnTheWay.TakenIn, List<OnTheWay.TakenIn>> placedTogether(
            List<OnTheWay.TakenIn> cuts) {
        List<OnTheWay.TakenIn> relating = new ArrayList<>();
        List<List<TermPath>> writes = new ArrayList<>();
        for (OnTheWay.TakenIn cut : cuts) {
            if (cut.demand() instanceof RowDemand.Relational(var relation)) {
                relating.add(cut);
                List<TermPath> at = new ArrayList<>();
                for (NumericTerm term : relation.terms()) {
                    at.add(RealizationTarget.of(term).writeRoot());
                }
                writes.add(at);
            }
        }
        // Each condition's group, by the first condition of it.
        int[] first = new int[relating.size()];
        for (int i = 0; i < first.length; i++) {
            first[i] = i;
        }
        for (int i = 0; i < relating.size(); i++) {
            for (int j = i + 1; j < relating.size(); j++) {
                if (writtenAtOneLocation(writes.get(i), writes.get(j))) {
                    int from = groupOf(first, j);
                    int into = groupOf(first, i);
                    if (from != into) {
                        first[Math.max(from, into)] = Math.min(from, into);
                    }
                }
            }
        }
        Map<Integer, List<OnTheWay.TakenIn>> groups = new LinkedHashMap<>();
        for (int i = 0; i < relating.size(); i++) {
            groups.computeIfAbsent(groupOf(first, i), _ -> new ArrayList<>()).add(relating.get(i));
        }
        Map<OnTheWay.TakenIn, List<OnTheWay.TakenIn>> out = new LinkedHashMap<>();
        for (List<OnTheWay.TakenIn> group : groups.values()) {
            for (OnTheWay.TakenIn each : group) {
                out.put(each, List.copyOf(group));
            }
        }
        return out;
    }

    /** The first condition of the group {@code at} is in. */
    private static int groupOf(int[] first, int at) {
        int found = at;
        while (first[found] != found) {
            found = first[found];
        }
        return found;
    }

    /** Whether some location of {@code one} and some of {@code other} are one location. */
    private static boolean writtenAtOneLocation(List<TermPath> one, List<TermPath> other) {
        for (TermPath a : one) {
            for (TermPath b : other) {
                if (LocationWrites.oneLocation(a, b)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The counts every condition on the way asks of one count, the count as all of them read it
     * ({@link CountedElements#and}), and the first of those conditions on the way, which is the one
     * a reader is sent to where they cannot be taken in.
     *
     * @param turnsOnTheRowsNumbers whether some of {@code counts} is what a count held against
     *                              numbers of the row leaves at the values those numbers were put
     *                              at — where it is, a region holding no count says those values
     *                              leave none, and nothing about the rules
     */
    private record CountsAsked(CountedElements count, LevelRegion counts,
                               boolean turnsOnTheRowsNumbers, OnTheWay.TakenIn first) {

        CountsAsked and(CountsAsked other) {
            return new CountsAsked(count.and(other.count), counts.meet(other.counts),
                    turnsOnTheRowsNumbers || other.turnsOnTheRowsNumbers, first);
        }
    }

    /**
     * {@code here} narrowed to where the numbers {@code many} adds to its count leave room for a
     * count the container can have, or {@code here} where that cannot be said.
     *
     * <p>A count is never below the least of what is left of it — what the container can hold, and
     * what the other conditions on it leave ({@code left}) — and is held against what the numbers
     * come to: where it is asked to stay under them, or to come to them, they have to come to at
     * least that least. Put first at a value that does not, the numbers leave no count at all and a
     * row that meets the statement is never looked for. Where the count is asked to be at least
     * them, or other than them, a count above any value of theirs meets it and nothing is narrowed.
     *
     * <p>For choosing the numbers this cut puts, and not given to the region the rest of the way is
     * read in: what is said here is that a value is a better first choice, which is no rule's.
     *
     * @param left what the conditions on the count that read no number of the row leave of it, or
     *             null where none does
     */
    private static SearchRegion leavingACount(SearchRegion here, RowDemand.SoMany many,
                                              CountedElements count, LevelRegion left) {
        Rel room = switch (many.met()) {
            case LT -> Rel.LT;
            case LE, EQ -> Rel.LE;
            case GE, GT, NE -> null;
        };
        if (room == null) {
            return here;
        }
        LevelRegion any = LevelRegion.of(new LevelInterval(
                Bound.at(new Level.OfTheQuantity(ExactRatio.ZERO), true), null));
        if (!(count.leastIn(left == null ? any : left)
                instanceof CountedElements.Least.At(Count least))) {
            return here;
        }
        ExactRatio constant = least.exactly().minus(many.level()).orNull();
        if (constant == null) {
            return here;
        }
        return here.assuming(new LinearForm<>(constant, many.against().coefs()), room)
                instanceof SearchRegion.Assumption.Taken(SearchRegion narrowed) ? narrowed : here;
    }

    /**
     * Where the numbers of the form {@code remainder} is of stand inside {@code here} so that it
     * leaves one of the remainders asked for, or what this found out about there being none.
     *
     * <p>Each remainder in turn, as a congruence the walk holds its numbers to: every number but
     * the last is walked as any number of the region is, from where it usually is, and the last
     * over the class the others leave it ({@link NumericWitness.Congruent}). The form is never put
     * at a value first — a value chosen before its numbers is one their own runs may not reach
     * together — and as many remainders are tried as one position on the way is tried at.
     *
     * <p>Proof that none stands only where the region leaves the numbers nothing, or no value of
     * the form leaves any of the remainders: a walk that found no assignment proves nothing, since
     * it walked some values of each number.
     */
    private static NumericWitness.Standing standingOnARemainder(SearchRegion here,
            RowDemand.OnARemainder remainder, Function<NumericTerm, Carrier> on,
            WitnessSearch looking) {
        LinearForm<NumericTerm> dividend = remainder.remainder().dividend();
        BigInteger moved = ((ExactAnswer.Held<BigInteger>) dividend.constant().floor()).value();
        BigInteger divisor = remainder.remainder().divisor();
        BigInteger step = BigInteger.ZERO;
        for (ExactRatio each : dividend.coefs().values()) {
            if (!(each.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))
                    || !each.isWhole()) {
                return new NumericWitness.Standing.NotFound(CompositionShortfall.NONE);
            }
            step = step.gcd(whole);
        }
        // What the form's coefficients reach, every multiple of the step they generate: a
        // remainder whose class holds none of those is one no value of the form leaves.
        Congruences reached = new Congruences(BigInteger.ZERO,
                step.signum() == 0 ? BigInteger.ONE : step);
        List<NumericTerm.FromOnePosition> terms = new ArrayList<>();
        for (NumericTerm term : NumericTerms.inOrder(dividend.coefs().keySet())) {
            terms.add(term.atOnePosition());
        }
        int left = CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();
        List<NumericWitness.Congruent> tried = new ArrayList<>();
        boolean cut = false;
        for (WholeNumberRuns.Run run : remainder.leaves().runs()) {
            for (BigInteger r = run.from(); !cut && r.compareTo(run.to()) <= 0;
                 r = r.add(BigInteger.ONE)) {
                if (new Congruences(r.subtract(moved), divisor).meet(reached) == null) {
                    continue;
                }
                if (left-- <= 0) {
                    cut = true;
                } else {
                    tried.add(new NumericWitness.Congruent(dividend, divisor, r));
                }
            }
        }
        NumericWitness.Standing standing = NumericWitness.of(here, terms, on, looking, tried);
        if (!cut || standing instanceof NumericWitness.Standing.Found) {
            return standing;
        }
        CompositionShortfall met = standing instanceof NumericWitness.Standing.NotFound(
                CompositionShortfall shortOf) ? shortOf : CompositionShortfall.NONE;
        return new NumericWitness.Standing.NotFound(met.and(CompositionShortfall.of(
                Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT))));
    }

    /**
     * What one cut of the way comes to, arrived at whole.
     *
     * <p><b>A value and not a sequence of changes to the row.</b> A cut is placed at every position
     * it names or at none ({@code ACutTheComposerCannotPlaceIsSaidAndNotHalfApplied}), and where
     * its numbers are written and what the row had to be taken as to write them there are part of
     * placing it — so all of it is worked out here and the caller applies all of it or none. Written
     * as assignments into the row as each number was reached, a case chosen on the way to a cut that
     * came to nothing would stay chosen, and the cut after it would be answering under a case
     * nothing was ever written under.
     *
     * @param composer        how a value is composed where the cut's numbers stand, which an
     *                        assignment of them is taken only where it composes
     * @param alreadyStanding where the row already writes, which a number asked for here has to
     *                        stand beside — read and never added to
     * @param assumed what the row is already taken to be, which every case chosen here agrees with
     */
    private static Placed placing(MeasuredInput subject, WayComposer composer,
                                  WitnessSearch looking, SearchRegion here,
                                  Map<RealizationTarget, Place> alreadyStanding,
                                  Set<RealizationTarget> someElement,
                                  Requirements assumed, OnTheWay.TakenIn cut) {
        return switch (cut.demand()) {
            // What every row past it holds, which the region a search runs over was narrowed by
            // already — so what is left there is what the rules leave, and nothing left is a
            // proof.
            case RowDemand.Relational(var relation) -> placedIn(subject, composer, looking, here,
                    alreadyStanding, someElement, assumed, cut, List.of(relation), false);
            // What an element meets, which the region was not narrowed by. Placed in a region that
            // is, for this cut alone: the element written meets it, and every element a list
            // writes is that one.
            case RowDemand.Exists exists -> asComposedOnly(cut,
                    placedIn(subject, composer, looking, here, alreadyStanding, someElement,
                            assumed, cut, constraints(exists.relations()), true),
                    noElementCanMeet(constraints(exists.relations()), subject));
            // And where no element can be written that meets them, the container holding none,
            // which every element of meets them. Closed only where neither way is open: no element
            // the rules allow meets them, and the container cannot hold none.
            case RowDemand.ForAll every -> {
                List<RowDemand.Relational> ofEachElement = every.relations();
                Placed some = placedIn(subject, composer, looking, here, alreadyStanding,
                        someElement, assumed, cut, constraints(ofEachElement), true);
                if (some instanceof Placed.AtAll) {
                    yield some;
                }
                Placed none = placedIn(subject, composer, looking, here, alreadyStanding,
                        someElement, assumed, cut, List.of(every.holdingNone().constraint()), true);
                if (none instanceof Placed.AtAll) {
                    yield none;
                }
                yield asComposedOnly(cut, some,
                        none instanceof Placed.AtNone(ReachabilityGap.ProvedImpossible _)
                                && noElementCanMeet(constraints(ofEachElement), subject));
            }
            // Passed over before it is asked: it places no number ({@link #placesNoNumber}).
            case RowDemand.ATruth truth -> throw new IllegalArgumentException(
                    "a truth is written where the row is composed and placed nowhere: " + truth);
            case RowDemand.OneValueAtBoth both -> throw new IllegalArgumentException(
                    "two values being one are written where the row is composed and placed"
                            + " nowhere: " + both);
            // Taken in beside the rest, as a demand on the container ({@link #alsoOnTheWay}).
            case RowDemand.SoMany many -> throw new IllegalArgumentException(
                    "a count is composed where its container is and placed nowhere: " + many);
            // Placed beside the counts, at a value of its form ({@link #alsoOnTheWay}).
            case RowDemand.OnARemainder remainder -> throw new IllegalArgumentException(
                    "a remainder is placed at a value of its form and not here: " + remainder);
            // Passed over before it is asked, with what the way is owed about it.
            case RowDemand.ForTheRun run -> throw new IllegalArgumentException(
                    "a statement no composer writes toward is placed nowhere: " + run);
        };
    }

    /**
     * Whether no element the rules of the input allow meets every one of {@code ofAnElement}.
     *
     * <p>Asked of what the declarations leave and of nothing the way added. A way can hold a
     * condition on the element it is walking — a rule inside a closure handed one — and that is
     * about one element; a region holding both it and these would leave nothing where two
     * elements meet the two. What the declarations leave is what every element holds, so what
     * that leaves nothing for is something no element is.
     */
    private static boolean noElementCanMeet(List<TakenConstraint> ofAnElement,
                                            MeasuredInput subject) {
        return TakenConstraint.nothingMeetsAll(ofAnElement, subject.quantities().region());
    }

    private static List<TakenConstraint> constraints(List<RowDemand.Relational> relations) {
        return relations.stream().map(RowDemand.Relational::constraint).toList();
    }

    /** The count of elements meeting the statement {@code demand} is the whole of, where it is a
     *  quantifier that is one. */
    private static Optional<Quantity.HowManyMeet> countedOf(RowDemand.OfACondition demand) {
        return switch (demand) {
            case RowDemand.Exists exists -> exists.counted();
            case RowDemand.ForAll every -> every.counted();
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                 RowDemand.OnARemainder _, RowDemand.OneValueAtBoth _, RowDemand.ForTheRun _ ->
                    Optional.empty();
        };
    }

    /** The container a quantifier is over; null for any other demand. */
    private static TermPath containerOf(RowDemand.OfACondition demand) {
        return switch (demand) {
            case RowDemand.Exists exists -> exists.container();
            case RowDemand.ForAll every -> every.container();
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                 RowDemand.OnARemainder _, RowDemand.OneValueAtBoth _, RowDemand.ForTheRun _ ->
                    null;
        };
    }

    /**
     * {@code cut}, a quantifier that is the whole of a statement about elements, as the count of
     * elements meeting the statement: one or more of them for some element, and none for every
     * element meeting its denial.
     */
    private static OnTheWay.TakenIn asACount(OnTheWay.TakenIn cut) {
        Quantity.HowManyMeet counted = countedOf(cut.demand()).orElseThrow();
        boolean some = cut.demand() instanceof RowDemand.Exists;
        return new OnTheWay.TakenIn(cut.anchor(), new RowDemand.SoMany(counted,
                some ? Rel.GE : Rel.EQ, some ? ExactRatio.ONE : ExactRatio.ZERO,
                new LinearForm<>(ExactRatio.ZERO, Map.of()), AnElementMeeting.UNREAD));
    }

    /** Whether {@code demand} asks nothing a number stands for: an element to be, or not to be,
     *  another position's value, or a position to hold one of two values. */
    private static boolean placesNoNumber(RowDemand.OfACondition demand) {
        return switch (demand) {
            case RowDemand.Relational _ -> false;
            case RowDemand.Exists exists -> exists.relations().isEmpty();
            case RowDemand.ForAll every -> every.relations().isEmpty();
            case RowDemand.ATruth _ -> true;
            // Two values on no order, which are written where the row is composed.
            case RowDemand.OneValueAtBoth _ -> true;
            // A count, which places a count of the container and the numbers beside an element.
            case RowDemand.SoMany _ -> false;
            // The numbers of the form a remainder is of.
            case RowDemand.OnARemainder _ -> false;
            // A statement no composer writes toward, which places nothing.
            case RowDemand.ForTheRun _ -> true;
        };
    }

    /**
     * What placing a cut about a container's elements came to, with nothing it found standing for
     * a proof unless {@code provedByTheDeclarations} says the rules themselves leave it nothing.
     *
     * <p>A region reads a term inside the elements as the value of one element, and a row writes
     * every element as that one. What that leaves nothing for is a row of elements written alike,
     * and the condition may still hold of a row whose elements differ — so nothing found here is
     * what this composer did, and the model's word only where the declarations alone settle it.
     */
    private static Placed asComposedOnly(OnTheWay.TakenIn cut, Placed placed,
                                         boolean provedByTheDeclarations) {
        return placed instanceof Placed.AtNone(ReachabilityGap.ProvedImpossible _)
                && !provedByTheDeclarations
                ? new Placed.AtNone(new ReachabilityGap.Uncomposed(cut,
                        new ReachabilityGap.Why.ElementsWrittenAlike()))
                : placed;
    }

    /**
     * {@code cut} placed at the numbers {@code stated} is over, in {@code here} — narrowed by each
     * of them where {@code narrowHere} says the region a search runs over was not.
     *
     * <p>Not narrowed where it was. What the way took in is in the region already, and a cut
     * handed over from elsewhere — what an answer standing a dependency in is asked — may be one
     * the region was never able to carry: narrowed again, it would be refused at the place the
     * cut is placed rather than reported as the cut it is.
     */
    private static Placed placedIn(MeasuredInput subject, WayComposer composer,
                                   WitnessSearch looking, SearchRegion here,
                                   Map<RealizationTarget, Place> alreadyStanding,
                                   Set<RealizationTarget> someElement,
                                   Requirements assumed, OnTheWay.TakenIn cut,
                                   List<TakenConstraint> stated, boolean narrowHere) {
        SearchRegion within = here;
        // The same, with nothing a condition chose standing in it, which is what a proof is asked
        // of: a cut the earlier conditions' choices leave nothing is a cut those choices leave
        // nothing, and the rules may well leave it something.
        SearchRegion unchosen = composer.unchosen();
        Set<NumericTerm> terms = new LinkedHashSet<>();
        for (TakenConstraint one : stated) {
            if (narrowHere) {
                within = one.narrowing(within);
                unchosen = one.narrowing(unchosen);
            }
            terms.addAll(one.terms());
        }
        // What the cut says, asked as the one thing it says. A cut over two positions is a
        // statement about their sum, and the rules can leave that sum nowhere while leaving each
        // position somewhere — so the positions asked one at a time answer a weaker question
        // than the cut put. Asked here, before the cut is taken apart into the positions a
        // value has to be chosen at.
        for (TakenConstraint one : stated) {
            if (one instanceof TakenConstraint.Affine affine
                    && within.projectionOf(affine.form())
                            instanceof NumericDomain.FormProjection.NothingIsLeft) {
                return new Placed.AtNone(!composer.anyChosen()
                        || unchosen.projectionOf(affine.form())
                                instanceof NumericDomain.FormProjection.NothingIsLeft
                        ? new ReachabilityGap.ProvedImpossible(cut)
                        : new ReachabilityGap.Uncomposed(cut,
                                new ReachabilityGap.Why.NoValueComposedForItsPositions()));
            }
        }
        // What routing this cut's numbers came to is kept by the search until the cut is placed.
        // Where each of them is written and which case the row was taken to be to write it there
        // are part of placing the cut, and a cut is placed at every position it names or at none —
        // so a cut that comes to nothing leaves the row the case it had, and the next cut chooses
        // as freely as this one did.
        return new CutPlacing(subject, composer, looking, within, unchosen, alreadyStanding,
                someElement, cut, List.copyOf(terms))
                .from(0, assumed, new LinkedHashMap<>(), new LinkedHashMap<>());
    }

    /**
     * The search for one cut's placing, over every place a row may write each of its numbers.
     *
     * <p><b>Which case a row is written under is part of what is searched for.</b> A name every
     * case of a sum spreads is written under one of them, and the case decides which rules the
     * value is held to: a case whose invariant keeps the number away from the cut leaves it
     * nothing, and another case beside it may leave it a run. So the question a cut puts is whether
     * some way of writing its numbers has values that stand together — and a search that settled
     * the way first and looked for values after would answer it by the order the model declared its
     * cases in.
     *
     * <p>Depth-first over the cut's numbers, one way of writing each at a time, and the values are
     * looked for once every number has a place. The ways one number may be written are narrowed by
     * what the row is already taken to be ({@link Requirements#merge}), so two names of one sum are
     * written under one case and the ways the search walks are the ones a row can be.
     *
     * <p><b>What the ways came to is joined, and a proof only where every way was proved.</b> The
     * rules leaving one way nothing say nothing about another, and a way this compiler did not get
     * to the end of may have the values the others lacked. So a cut is said to be impossible where
     * every way of writing it was shown to be, and otherwise it is a cut this did not compose for.
     *
     * <p><b>Values the region admits are a place, and a row composed with them is the witness.</b>
     * What the rules leave a number is a run, and not every number of it is one some value of the
     * input comes to: a list of three elements each at least five adds up to no ten, though nothing
     * in the run says so. So an assignment is taken only where every location its numbers are
     * written at composes with them standing there, and one that does not is stepped past as a
     * value the rules refuse is.
     *
     * @param composer        how a value is composed where the cut's numbers stand
     * @param alreadyStanding where the row already writes, which a number asked for here has to
     *                        stand beside — read and never added to
     * @param someElement     the numbers among those standing that some element of a container
     *                        is to stand at, which a condition that some element meets something
     *                        placed ({@link #writtenAmong})
     * @param unchosen        {@code here} with nothing a condition chose standing in it, which is
     *                        what the region is asked of where it says the cut has no assignment
     * @param terms           the cut's numbers, in the order the search takes them
     */
    private record CutPlacing(MeasuredInput subject, WayComposer composer, WitnessSearch looking,
                              SearchRegion here, SearchRegion unchosen,
                              Map<RealizationTarget, Place> alreadyStanding,
                              Set<RealizationTarget> someElement,
                              OnTheWay.TakenIn cut, List<NumericTerm> terms) {

        /**
         * The numbers some element of a container is to stand at, with {@code placedHere} among
         * them where this cut is that some element meets something, and not where it is that every
         * one does. One answer for every reader of it: what is grouped as some element's where an
         * assignment is composed is what is grouped so where the row is.
         */
        Set<RealizationTarget> someElementWith(Collection<RealizationTarget> placedHere) {
            if (!(cut.demand() instanceof RowDemand.Exists)) {
                return someElement;
            }
            Set<RealizationTarget> some = new LinkedHashSet<>(someElement);
            some.addAll(placedHere);
            return some;
        }

        /**
         * The placing of the cut's numbers from {@code next} on.
         *
         * @param trying what the row is taken to be with the numbers before {@code next} written
         * @param routes where the row writes each number before {@code next}
         * @param owing  each target before {@code next} a value has to be chosen for, with the
         *               number it is chosen as
         */
        Placed from(int next, Requirements trying,
                    Map<NumericTerm, RealizationTarget> routes,
                    SequencedMap<RealizationTarget, NumericTerm> owing) {
            if (next == terms.size()) {
                return witnessed(trying, routes, owing);
            }
            NumericTerm term = terms.get(next);
            // Where a row may write to move this number, which is where the number is read except
            // at a name every case of a sum spreads. Asked before anything else about the number,
            // because every question below is about the place the row writes: what else is being
            // written there, whether one value answers them all, and which location the value is
            // gathered under.
            //
            // The ways of this row: a name sent under a case takes the row with it, and the number
            // beside it is written under the same case or not at all, since no value is two cases.
            WaysToWrite ways = waysToWrite(subject, looking, term, trying);
            List<ReachabilityGap> missed = new ArrayList<>();
            for (Way way : ways.to()) {
                switch (writing(next, term, way.target(), way.taken(), routes, owing)) {
                    case Placed.AtAll placed -> {
                        return placed;
                    }
                    case Placed.AtNone(ReachabilityGap why) -> missed.add(why);
                }
            }
            return new Placed.AtNone(
                    ReachabilityGap.overEveryWay(cut, missed, ways.someNotWorkedOut()));
        }

        /** The placing with {@code term} written at {@code target}, and the rest after it. */
        private Placed writing(int next, NumericTerm term, RealizationTarget.OfANumber target,
                               Requirements trying,
                               Map<NumericTerm, RealizationTarget> routes,
                               SequencedMap<RealizationTarget, NumericTerm> owing) {
            Map<NumericTerm, RealizationTarget> routed = new LinkedHashMap<>(routes);
            routed.put(term, target);
            // This very number already stands somewhere: the item asked for it, or an earlier cut
            // did. Nothing to place, and the cut is answered at it either way. And where another
            // number of this cut is written at the same target, it is written there once: the
            // number is placed where that one is, and is no second demand on the location.
            if (alreadyStanding.containsKey(target) || owing.containsKey(target)) {
                return from(next + 1, trying, routed, owing);
            }
            // Another number taken at the same location. A row writes one value where a location
            // is, and that one value has to answer both — the hour of a time beside its minute,
            // the length of a string beside the string, how many a list holds beside what its
            // elements add up to. Whether one value can is {@link TermRealizations}' answer and is
            // asked before anything is placed here: a group it builds together is placed and
            // written once, and one it does not is a cut this could not put a value under.
            //
            // A number over a run is placed as any other is. What is chosen here is the number,
            // which the region relates to every other number the cut names; the container that
            // comes to it is composed where every number of its location is, out of what that
            // number is one of ({@link #whatEachOfThemIsANumberOf}).
            //
            // Asked of what is already standing and of what this cut has placed before it, rather
            // than of a list kept beside them, so the answer is about the demands this row actually
            // has — two numbers of one location named by one cut are as much two demands on it as a
            // number beside one standing there. Which locations are one is asked of the reader that
            // owns it, because a container written whole and a position inside it are one location
            // spelled two ways.
            List<RealizationTarget> beside = alsoWritingAt(alreadyStanding.keySet(),
                    target.writeRoot());
            beside.addAll(alsoWritingAt(owing.keySet(), target.writeRoot()));
            // And a count the way asks for that is placed once the conditions are. A count of the
            // elements meeting something decides which elements the container holds, and a number
            // nothing composes beside it gives the location up to it rather than taking it first
            // and leaving the count to be refused: what the elements come to is then read off the
            // elements the count was composed for, where the row runs.
            beside.addAll(composer.countsToComeAt(target.writeRoot()));
            List<RealizationTarget> placedHere = new ArrayList<>(owing.keySet());
            placedHere.add(target);
            if (!beside.isEmpty()
                    && !writtenTogether(beside, target, someElementWith(placedHere))) {
                return new Placed.AtNone(new ReachabilityGap.Uncomposed(cut,
                        new ReachabilityGap.Why.TwoNumbersAtOneLocation()));
            }
            SequencedMap<RealizationTarget, NumericTerm> owed = new LinkedHashMap<>(owing);
            owed.put(target, writtenAs(subject, target));
            return from(next + 1, trying, routed, owed);
        }

        /**
         * The values of every number this way of writing the cut owes, chosen together.
         *
         * <p>The whole cut at once, because a cut over two positions is one statement about the
         * pair: which values one of them may take depends on what the other took, and a value
         * chosen for the first without asking is right about its own run and wrong about the pair
         * as often as not.
         *
         * <p>Each number as it is named where the row writes it. The region reads the rules of the
         * values a question's positions stand under, so a number named under a case is answered
         * with that case's own rules; named at the sum, it is answered as though the row could be
         * any of the cases, and a value chosen there is one the case it is written under may
         * refuse.
         *
         * <p>And an assignment is the cut's once a row composes with it ({@link WayComposer}), asked
         * when every number of the cut stands somewhere: what is composed at a location is one
         * value for every number there, so a number asked about alone is asked a question the row
         * never puts.
         */
        private Placed witnessed(Requirements trying,
                                 Map<NumericTerm, RealizationTarget> routes,
                                 SequencedMap<RealizationTarget, NumericTerm> owing) {
            // A number this cut places is some element's where the cut is that some element meets
            // something, which is where the location it is composed at is.
            Set<RealizationTarget> some = someElementWith(owing.keySet());
            // What each number standing is one of, asked once for this way of writing the cut:
            // where each number is written does not turn on the values tried for them.
            Map<RealizationTarget, NumbersAskedFor> asked = composer.askedWith(routes);
            List<NumericTerm> numbers = List.copyOf(new LinkedHashSet<>(owing.values()));
            // What composing with the assignment the walk took came to. The walk takes the first
            // assignment that composes and asks nothing after it, so the last one asked about is
            // the one it took.
            List<ComposedAt> composedWith = new ArrayList<>();
            SearchRegion within = here.given(remaindersStanding(alreadyStanding));
            SearchRegion apart = keysApart(within, owing.keySet());
            NumericWitness.Standing found = NumericWitness.of(apart, numbers,
                    term -> carrierOf(term, subject.quantities()), looking,
                    assignment -> {
                        composedWith.clear();
                        return composer.composes(alreadyStanding, some, asked, owing,
                                assignment, composedWith);
                    });
            // The keys held apart are a way to try: where nothing stands that way, they are tried
            // as the rules leave them.
            if (apart != within && !(found instanceof NumericWitness.Standing.Found)) {
                found = NumericWitness.of(within, numbers,
                        term -> carrierOf(term, subject.quantities()), looking,
                        assignment -> {
                            composedWith.clear();
                            return composer.composes(alreadyStanding, some, asked, owing,
                                    assignment, composedWith);
                        });
            }
            // What the rules settle before what this compiler managed, because a reader may act on
            // the first and on none of the rest. A proof is the region's alone: an assignment no
            // row composed with is what this compiler built, and says nothing of the rules.
            //
            // And of the region with nothing a condition chose standing in it. A region narrowed by
            // an earlier condition's choice that leaves this cut nothing is that choice leaving it
            // nothing, which is no answer about the cut; a walk over such a region proves nothing
            // either, and the composer says so ({@link WayComposer}).
            //
            // And where something of this compiler's is why the walk found nothing — a budget, a
            // population composed in part, a value it could not hold — that rather than the word
            // for a walk that had everything and reached none of it.
            return switch (found) {
                case NumericWitness.Standing.Found standing -> new Placed.AtAll(standing, routes,
                        owing, List.copyOf(composedWith), some, trying);
                case NumericWitness.Standing.ProvedImpossible _ -> new Placed.AtNone(
                        !composer.anyChosen() || NumericWitness.leavesTheQuestionNothing(
                                unchosen.given(remaindersStanding(nothingChosenIn(
                                        alreadyStanding))), numbers)
                                ? new ReachabilityGap.ProvedImpossible(cut)
                                : new ReachabilityGap.Uncomposed(cut,
                                        new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                case NumericWitness.Standing.NotFound(CompositionShortfall met) ->
                        new Placed.AtNone(new ReachabilityGap.Uncomposed(cut,
                                ReachabilityGap.Why.ofAWalkThatFoundNothing(met)));
            };
        }

        /**
         * {@code region} with the key of each target owed held away from the keys of the same
         * fold already standing: the key of a fold asked for twice is two keys, and held at one
         * value they would be one, whose elements come to the one number asked of both.
         */
        private SearchRegion keysApart(SearchRegion region, Collection<RealizationTarget> owing) {
            SearchRegion apart = region;
            for (RealizationTarget owed : owing) {
                TermPath asked = owed.keyAskedFor();
                if (asked == null) {
                    continue;
                }
                for (RealizationTarget earlier : alreadyStanding.keySet()) {
                    TermPath earlierAsked = earlier.keyAskedFor();
                    Place earlierAt = earlierAsked == null ? null : alreadyStanding.get(
                            RealizationTarget.of(new NumericTerm.ValueOf(earlierAsked)));
                    if (earlierAt != null && owed.keyIsToldApartFrom(earlier)) {
                        apart = apart.apartFrom(new NumericTerm.ValueOf(asked), earlierAt);
                    }
                }
            }
            return apart;
        }

        /** {@code standing} with nothing a condition chose. */
        private Map<RealizationTarget, Place> nothingChosenIn(
                Map<RealizationTarget, Place> standing) {
            Map<RealizationTarget, Place> forced = new LinkedHashMap<>(standing);
            forced.keySet().removeIf(composer::wasChosen);
            return forced;
        }
    }

    /**
     * What became of one cut: everything placing it took, or the gap saying nothing could be put
     * under it.
     *
     * <p>Two arms and no third, because a cut is answered or it is not. A shape holding both a
     * partial placing and a gap would be the half-application this exists to make unwritable.
     */
    private sealed interface Placed {

        /**
         * The cut is answered.
         *
         * @param standing where each number this cut asked for stands
         * @param routes   where the row writes each number the cut names, the ones already standing
         *                 beside it included — what a later reader asks when it wants to know what a
         *                 number of this row was filed under
         * @param owing    each target a value was chosen for here, with the number it was chosen
         *                 as in {@code standing}
         * @param composed what composing each location those targets are written at came to,
         *                 with them standing where they do
         * @param someElement the numbers some element of a container is to stand at now that
         *                    these are written ({@link CutPlacing#someElementWith})
         * @param assumed  what the row is taken to be now that these are written
         */
        record AtAll(NumericWitness.Standing.Found standing,
                     Map<NumericTerm, RealizationTarget> routes,
                     SequencedMap<RealizationTarget, NumericTerm> owing,
                     List<ComposedAt> composed,
                     Set<RealizationTarget> someElement,
                     Requirements assumed) implements Placed {}

        /** Nothing was put under it, and this is what the way is owed about that. */
        record AtNone(ReachabilityGap why) implements Placed {}
    }

    /**
     * One place a row that is already {@code trying} may write a number at, and what the row is
     * once it does.
     *
     * <p>The row's requirements and not the place's alone. They are the place's path
     * ({@link TermPath#requirements}) taken together with what the row already was, worked out once
     * where the way was followed — so whoever writes at the place is handed the row it writes into
     * rather than asking again whether the two hold together.
     */
    private record Way(RealizationTarget.OfANumber target, Requirements taken) {}

    /**
     * Every place a row that is already something may write to move one number, and whether some
     * way to one was not followed to its end.
     *
     * <p><b>The ways of this row, and not of every value of the input.</b> A case the row cannot be
     * beside what it already is was never one of its ways: the two narrowings hold of no value
     * together, which is something the model settles and not something left unlooked at. Left in
     * and refused afterwards, it would have to be read as one or the other, and read as unlooked at
     * it keeps a cut every way of this row was shown to leave nothing from being said to be that.
     *
     * @param to               the places, in the order the model declares the cases on the way to
     *                         each
     * @param someNotWorkedOut whether a way of this row reached a place whose holding nothing worked
     *                         out. Not a place to write at, and not one shown to hold nothing
     *                         either, so a reader concluding something from every place in
     *                         {@code to} has not looked at all of them
     */
    private record WaysToWrite(List<Way> to, boolean someNotWorkedOut) {}

    /**
     * Every place a row that is already {@code trying} may write to move {@code term}.
     *
     * <p><b>The place a number is read is the place a row writes it, except at a name every case of
     * a sum spreads.</b> There the rules name the sum's own field and a row writes one of the
     * cases, so the value answering the number stands under whichever case the row turns out to be
     * — and a row asked to write at the sum's own name writes nowhere, which is how a condition
     * over such a name came back as one nothing composed a value for.
     *
     * <p><b>Every case and not one of them.</b> Which case the row is written under decides which
     * rules hold of the value, so it is not settled here: the cut being placed is what says which
     * of them can take a value, and a search that took one case for every number would answer by
     * the order the cases were declared in.
     *
     * <p><b>Asked of what the declarations came to at the place, and not of where a name stands.</b>
     * Where a name stands is structure, and structure says the same thing about a position this
     * reading answered for and about a path it never reached — so a writer that sorted by it alone
     * would offer a value at a position whose rules were never read. The three states are
     * {@link AdmittedValues.Admitted}'s, and this is the reader they were made for.
     *
     * <p>The place's own answer and not the set a search composes from. What narrows a value is the
     * number's question — a count taken of a position is not one of the position's values and is
     * not held to its set ({@link WitnessSearch#toComposeFrom}) — and where a row writes is the
     * place's, whichever number of it was asked for. Asked as the composing set, a count at a name
     * the cases share would be told a set narrows nothing and sent to write at the sum's own name.
     */
    private static WaysToWrite waysToWrite(MeasuredInput subject, WitnessSearch looking,
                                           NumericTerm term, Requirements trying) {
        NumericTerm.FromOnePosition at = term.atOnePosition();
        List<Way> to = new ArrayList<>();
        // A number no single position answers is written where its run is rebuilt, and a run has no
        // name of a sum's to be read at. Left to the sorting below, the position it does not have
        // would be the path asked about.
        if (at == null) {
            RealizationTarget.OfANumber run = RealizationTarget.of(term);
            if (trying.merge(run.writeRoot().requirements())
                    instanceof Requirements.Merge.Merged(Requirements taken)) {
                to.add(new Way(run, taken));
            }
            return new WaysToWrite(List.copyOf(to), false);
        }
        // Where the number is written, worked out the one way every writer works out where a name
        // is written ({@link WhereANameIsWritten}). A place the reading answered for is one whose
        // values were worked out; anywhere else a value written would be offered at a position
        // whose rules this compiler never read, which is the row this declines to compose however
        // it was reached. The first place is the one the number is read at, and after a crossing it
        // is the position under the cases taken to get there.
        WhereANameIsWritten written = WhereANameIsWritten.of(subject.reach(), at.position(),
                trying, here -> looking.admitted().at(here)
                        instanceof AdmittedValues.Admitted.Values);
        for (WhereANameIsWritten.Place place : written.places()) {
            to.add(new Way(place.position().equals(at.position())
                    ? new RealizationTarget.AtOnePosition(at)
                    : new RealizationTarget.AtOnePositionElsewhere(at, place.position()),
                    place.taken()));
        }
        return new WaysToWrite(List.copyOf(to), written.someNotWorkedOut());
    }

    /**
     * The number {@code target} realizes, named at the place the row writes it.
     *
     * <p><b>The one place a number read at a sum becomes the number under the case it is written
     * at.</b> The rules and the report are about the number where the rules name it, and that is
     * what {@link RealizationTarget.OfANumber#term} keeps. What a value chosen for it is held to
     * is another question: the rules of the value it is written into, which for a name every case
     * of a sum spreads are the rules of the case. The region answers a question with the rules of
     * the values its positions stand under, so the number is put to it named under the case — and
     * named at the sum, it would be answered as though the row could be any of the cases.
     *
     * <p>Asked where a value is chosen for a number of the way, which is the one place the case
     * reaches a value. What is built afterwards is built at the place chosen here, which is inside
     * what the case leaves and so inside what the sum leaves as well: a reader building at it asks
     * nothing a case could answer differently.
     */
    private static NumericTerm writtenAs(MeasuredInput subject,
                                         RealizationTarget.OfANumber target) {
        return switch (target) {
            case RealizationTarget.AtOnePosition(NumericTerm.FromOnePosition term) -> term;
            case RealizationTarget.OverARun(NumericTerm.TakenOver term) -> term;
            case RealizationTarget.AmongTheElements(NumericTerm.Multiplicity term) -> term;
            case RealizationTarget.AtItsKey(NumericTerm.ExtremeOfItsKey term) -> term;
            case RealizationTarget.UnderItsKey(NumericTerm.GatheredUnderItsKey term) -> term;
            case RealizationTarget.UnderAKey(NumericTerm.GatheredUnderAKey term) -> term;
            case RealizationTarget.AmongEveryOccurrence(
                    NumericTerm.OccurrencesOfItsValue term) -> term;
            case RealizationTarget.AmongEveryOccurrenceEqualToAKey(
                    NumericTerm.OccurrencesOfAKey term) -> term;
            case RealizationTarget.AtOnePositionElsewhere(NumericTerm.FromOnePosition term,
                                                         TermPath root) -> {
                NumericTerm moved = subject.quantities().namedAt(term, root);
                // The cases spread one field, and one field has one declared type, so what the
                // number takes of it is taken under each case as it is at the sum.
                if (moved == null) {
                    throw new IllegalStateException("`" + term + "` is written at " + root
                            + " and cannot be named there, though the cases spread one field");
                }
                yield moved;
            }
        };
    }

    /**
     * Whether the number {@code asked} realizes is one the row writes together with the ones
     * already standing beside it.
     *
     * <p>Two things have to hold and they are two questions. The numbers have to be gathered under
     * one write, which is what {@link #byTheLocationTheyWrite} does and it does it by the path —
     * so a number at a path holding another is one location and is not one write, and placing it
     * here would leave the writing to refuse the pair and the whole point with it. And one value
     * has to answer them all, which is the realizer's.
     *
     * <p>Asked against the same path the gathering uses, so the two cannot part. Asked here as
     * whether they are one location, this would admit a pair nothing afterwards puts together.
     *
     * <p>Of where the row writes and not of where the number is read. The two are one place for
     * every number but one read at a name every case of a sum spreads, and asking the reading side
     * would put such a number beside whatever else the sum's own name attracted.
     */
    private static boolean writtenTogether(List<RealizationTarget> beside,
                                           RealizationTarget asked,
                                           Set<RealizationTarget> someElement) {
        List<RealizationTarget> both = new ArrayList<>(beside.size() + 1);
        both.addAll(beside);
        both.add(asked);
        Map<TermPath, TermPath> counted = countedAmong(both);
        TermPath at = writtenAmong(asked, counted, someElement);
        for (RealizationTarget target : beside) {
            if (!writtenAmong(target, counted, someElement).equals(at)) {
                return false;
            }
        }
        // The classification is the realizer's and the word for it is this reader's. What it comes
        // back with is which way of writing one value the group has, and a reader here has nothing
        // to do with the way — what it does is place the numbers or say it could not, which is a
        // sentence about the path to a point and not about what this compiler composes.
        return TermRealizations.jointRealizationOf(both)
                instanceof TermRealizations.JointRealization.Supported;
    }

    /**
     * The numbers already being written where {@code position} is, which is what a number asked for
     * there has to stand beside.
     *
     * <p>Read off what is standing rather than kept as a set of paths alongside it. The two would
     * be one answer held twice, and what the question is about is the targets and not the paths:
     * whether a value can answer them together is asked of the numbers.
     */
    private static List<RealizationTarget> alsoWritingAt(Collection<RealizationTarget> standing,
                                                         TermPath position) {
        List<RealizationTarget> beside = new ArrayList<>();
        for (RealizationTarget target : standing) {
            if (LocationWrites.oneLocation(target.writeRoot(), position)) {
                beside.add(target);
            }
        }
        return beside;
    }

    /**
     * Where the positions of one row stand, and what the way asked that nothing could put a value
     * under.
     *
     * <p>The second is carried out with the first because it is what the row was composed without.
     * A search that could not act on a condition above the line has composed a row that may not
     * arrive there, and an account of the attempt that did not say so would have an author reading
     * "no row was seen reaching it" beside a way that says everything on it was taken in.
     *
     * @param routed where the row writes each number a condition on the way named, which is where
     *               the number is read except at a name every case of a sum spreads. Carried out
     *               because the place was chosen here: worked out again by whoever asks what a
     *               number is one of, the two would part at exactly that name and a number would be
     *               asked about under a target the row never wrote
     * @param counted the counts a condition on the way asked for, each with the counts the
     *                condition leaves, which is what the one the row stands at is one of — and
     *                each statement the elements of a container are to meet together, asked at
     *                one: holding
     * @param someElement the numbers some element of a container is to stand at, which a
     *                    condition that some element meets something placed
     * @param composed    what composing each location a cut placed numbers at came to, where the
     *                    cut was placed, by the location
     * @param chosen      the numbers standing because a condition on the way chose a place for
     *                    them, which the rules did not force there
     * @param bounds      what the conditions on the way ask every element of a container to meet
     *                    where other numbers are written at it, which the container is composed
     *                    under wherever it is composed ({@link ElementBound})
     */
    private record Standing(Map<RealizationTarget, Place> at,
                            Map<NumericTerm, RealizationTarget> routed,
                            Map<RealizationTarget, NumbersAskedFor> counted,
                            Set<RealizationTarget> someElement,
                            Map<TermPath, ComposedAt> composed,
                            Set<RealizationTarget> chosen,
                            List<ElementBound> bounds,
                            CompositionAccount unrepresented) {

        /** The same, with what standing the dependencies in was arrived at without on it. */
        Standing with(CompositionAccount answers) {
            return new Standing(at, routed, counted, someElement, composed, chosen, bounds,
                    unrepresented.and(answers));
        }

        /**
         * The value composed at {@code at} for {@code group}: the one a cut's placing composed,
         * where it was composed for this very request, and otherwise composed now.
         */
        Edge composedAt(TermPath at, SequencedMap<RealizationTarget, AskedAt> group,
                        RegionToCompose within, MeasuredInput subject) {
            ComposedAt already = composed.get(at);
            return already != null && already.answers(group, within)
                    ? already.edge()
                    : edgeAt(subject, at, group, within.region());
        }
    }

    /**
     * What a condition that every element of a container meets something asks of the container,
     * where other numbers of the row are written there: a bound on what its elements may be, and
     * not a value of one of them.
     *
     * <p><b>A bound on the elements, which a container holding none meets.</b> Every element of an
     * empty container meets anything, so the elements are held to {@code ofEachElement} where the
     * container holds some, and where nothing the rules leave an element meets them, the container
     * is composed holding none instead. Held to the bound with no way round it, a container the
     * rules leave nothing to hold would be read as one the way leaves no value — which is the
     * reading the way's own region refuses for the same reason ({@link WayToTheBorder#narrowing}).
     *
     * <p><b>Why not a value.</b> Written as a value every element is, the condition is one more
     * number at a location a total, a count or the item already writes, and two numbers of one
     * location are composed together or not at all: whichever was placed first took the location,
     * and the other was a condition the row was composed without. As a bound it is part of what
     * that location is composed under, whichever number composes it.
     *
     * @param ofEachElement what every element is to meet, along its one way
     * @param holdingNone   the container holding none
     */
    record ElementBound(TermPath container, List<TakenConstraint> ofEachElement,
                        TakenConstraint holdingNone) {

        ElementBound {
            ofEachElement = List.copyOf(ofEachElement);
        }

        /** {@code region} with the container's elements held to this bound where it holds some,
         *  and with it holding none where nothing the rules leave an element meets the bound. */
        static SearchRegion within(SearchRegion region, List<ElementBound> bounds) {
            if (bounds.isEmpty()) {
                return region;
            }
            SearchRegion holdingSome = region;
            for (ElementBound each : bounds) {
                for (TakenConstraint one : each.ofEachElement()) {
                    holdingSome = one.narrowing(holdingSome);
                }
            }
            if (holdingSome.emptiness().isEmpty()) {
                return holdingSome;
            }
            SearchRegion holdingNone = region;
            for (ElementBound each : bounds) {
                holdingNone = each.holdingNone().narrowing(holdingNone);
            }
            return holdingNone;
        }
    }

    /**
     * What composing one location came to, and the request it was composed for.
     *
     * <p>Kept so that a location a cut's placing composed is not composed a second time when the
     * row is written, and handed over only for the request it answers. A request is the location,
     * every number asked of it in the order they are asked, and the region the value is composed in
     * — the same total beside a count asked since is another request, and its value is composed
     * for it.
     */
    private record ComposedAt(TermPath at, SequencedMap<RealizationTarget, AskedAt> group,
                              RegionToCompose within, Edge edge) {

        ComposedAt {
            group = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(group));
        }

        /** Whether this was composed for {@code asked} in {@code region}. */
        boolean answers(SequencedMap<RealizationTarget, AskedAt> asked, RegionToCompose region) {
            return within.sameAs(region)
                    && List.copyOf(group.entrySet()).equals(List.copyOf(asked.entrySet()));
        }
    }

    /**
     * How a value is composed where the numbers of conditions on the way stand, for one point: in
     * the way's region, for what each number is one of, by the reader that composes every location
     * of a row ({@link #edgeAt}).
     *
     * <p>Asked of an assignment the region admits, before the conditions take it. One composer for
     * both askings, so what a condition is placed at is what the row is written with.
     *
     * <p><b>One allowance for the point.</b> How many assignments are composed for is spent over
     * every condition on the way, whichever of them asks and however the asking is split
     * ({@link CompositionBudget#ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR}).
     *
     * <p><b>A proof only of what the point fixes.</b> That the rules leave an assignment no value is
     * about the assignment and everything standing beside it. Where some of that was put there by
     * an earlier condition's choice — a value the rules did not force — what was shown is that the
     * choice leaves nothing, which says nothing of the condition, so it is said as a value not
     * composed and never as the model's answer.
     */
    private static final class WayComposer {

        private final MeasuredInput subject;
        private final SearchRegion region;
        private final SearchRegion unchosen;
        private final CandidateCheck check;
        private final Set<RealizationTarget> chosen;
        private final Function<Map<NumericTerm, RealizationTarget>,
                Map<RealizationTarget, NumbersAskedFor>> askedOf;
        private final List<ElementBound> bounds;
        private final Map<RealizationTarget, Place> countsToCome;
        private int composedFor;

        /**
         * @param region   the way's region, which a location's value is composed in
         * @param unchosen the way's region with the numbers the point fixes standing where it fixes
         *                 them and nothing a condition chose, which is what a proof is asked of
         * @param check    what a value's own type says of it, which a value composed at a location
         *                 is put to before the location is said to compose
         * @param chosen   the numbers standing because a condition on the way chose a place for
         *                 them, as they are added
         * @param askedOf  what each number of the row is one of, with these routes beside the ones
         *                 already standing ({@link #whatEachOfThemIsANumberOf})
         * @param bounds   what the conditions on the way ask every element of a container to meet
         *                 where it is no value of its own ({@link ElementBound})
         * @param countsToCome the counts the way asks for that are placed once the conditions are,
         *                     each where it will stand — composed beside a condition's numbers
         *                     where they are written at its container and one value answers both
         */
        WayComposer(MeasuredInput subject, SearchRegion region, SearchRegion unchosen,
                    CandidateCheck check, Set<RealizationTarget> chosen,
                    Function<Map<NumericTerm, RealizationTarget>,
                            Map<RealizationTarget, NumbersAskedFor>> askedOf,
                    List<ElementBound> bounds, Map<RealizationTarget, Place> countsToCome) {
            this.subject = subject;
            this.region = region;
            this.unchosen = unchosen;
            this.check = check;
            this.chosen = chosen;
            this.askedOf = askedOf;
            this.bounds = List.copyOf(bounds);
            this.countsToCome = Collections.unmodifiableMap(new LinkedHashMap<>(countsToCome));
        }

        /**
         * What each number of the row is one of, with {@code routes} beside the ones already
         * standing. Asked once for a way of writing a condition's numbers: which numbers are where
         * does not turn on the values tried for them.
         */
        Map<RealizationTarget, NumbersAskedFor> askedWith(Map<NumericTerm, RealizationTarget> routes) {
            return askedOf.apply(routes);
        }

        /** The way's region with nothing a condition chose standing in it. */
        SearchRegion unchosen() {
            return unchosen;
        }

        /** Whether some number stands because a condition on the way chose where it does. */
        boolean anyChosen() {
            return !chosen.isEmpty();
        }

        /** Whether {@code target} stands because a condition on the way chose where it does. */
        boolean wasChosen(RealizationTarget target) {
            return chosen.contains(target);
        }

        /** The counts to come written where {@code location} is. */
        List<RealizationTarget> countsToComeAt(TermPath location) {
            return alsoWritingAt(countsToCome.keySet(), location);
        }

        /**
         * Whether every location a number of {@code owing} is written at composes with those
         * numbers standing where {@code assignment} puts them beside {@code alreadyStanding}.
         *
         * <p>Every location, and the first that does not compose says why: that the rules leave the
         * location no value, where composing it showed that of numbers nothing chose, and
         * otherwise what it met of this compiler's.
         *
         * @param asked what each number standing is one of
         * @param into  told what composing each such location came to, where every one composes
         */
        NumericWitness.Composed composes(Map<RealizationTarget, Place> alreadyStanding,
                                         Set<RealizationTarget> someElement,
                                         Map<RealizationTarget, NumbersAskedFor> asked,
                                         SequencedMap<RealizationTarget, NumericTerm> owing,
                                         SequencedMap<NumericTerm, Place> assignment,
                                         List<ComposedAt> into) {
            if (composedFor >= CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR.maximum()) {
                return new NumericWitness.Composed.NotBuilt(CompositionShortfall.of(
                        Set.of(CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR)));
            }
            composedFor++;
            Map<RealizationTarget, Place> standing = new LinkedHashMap<>(alreadyStanding);
            owing.forEach((target, term) -> standing.put(target, assignment.get(term)));
            // And each count to come at a container these numbers are written at, where one value
            // answers it beside them. One nothing composes beside them is refused where it is
            // placed, and composed beside them here it would refuse every assignment instead.
            // Each at the least of the counts left, which is a count this chose and not one the
            // rules force — so what composing beside it shows is about that count, and never the
            // model's answer.
            Set<RealizationTarget> countsChosenHere = new HashSet<>();
            countsToCome.forEach((count, least) -> {
                if (standing.containsKey(count)) {
                    return;
                }
                List<RealizationTarget> beside = alsoWritingAt(standing.keySet(),
                        count.writeRoot());
                if (!Collections.disjoint(beside, owing.keySet())
                        && writtenTogether(beside, count, someElement)) {
                    standing.put(count, least);
                    countsChosenHere.add(count);
                }
            });
            Map<RealizationTarget, AskedAt> numbers = atThoseNumbers(standing, asked);
            for (Map.Entry<TermPath, SequencedMap<RealizationTarget, AskedAt>> group
                    : byTheLocationTheyWrite(numbers, someElement).entrySet()) {
                if (Collections.disjoint(group.getValue().keySet(), owing.keySet())) {
                    continue;
                }
                RegionToCompose within = composedIn(group.getKey(), group.getValue(), region,
                        standing, bounds);
                Edge edge = edgeAt(subject, group.getKey(), group.getValue(), within.region());
                // Shown to have no value, where the composing showed the rules leave none of
                // numbers nothing chose; and otherwise refused, with what of this compiler's the
                // composing met.
                if (edge.values().isEmpty()) {
                    return edge.settlesTheQuestion() && chosen.isEmpty()
                            && Collections.disjoint(group.getValue().keySet(), countsChosenHere)
                            ? new NumericWitness.Composed.Refuted()
                            : new NumericWitness.Composed.NotBuilt(edge.met());
                }
                // And some value of it that its own type's decoder does not refuse. A value refused
                // on its own is refused in every row it is put in, so a location every value of
                // which is refused composes no row — with what building the values met, which is
                // why those were the values there were to refuse.
                if (everyValueRefused(edge)) {
                    return new NumericWitness.Composed.NotBuilt(edge.met());
                }
                into.add(new ComposedAt(group.getKey(), group.getValue(), within, edge));
            }
            return new NumericWitness.Composed.Built();
        }

        /** Whether the decoder of what {@code edge} is written as refuses every one of its values
         *  on its own. Not where nothing answers for it, which refuses nothing. */
        private boolean everyValueRefused(Edge edge) {
            if (edge.writtenAt() == null) {
                return false;
            }
            for (FixtureTemplate each : edge.values()) {
                if (check.admissibility(edge.writtenAt(), each)
                        != CandidateCheck.Admissibility.REFUSED) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * What one parameter's search found out about its own candidates while it ran: one turned away
     * for reading back elsewhere, one that built and had nothing to hand on, and a demand on its
     * containers it composed without.
     *
     * <p>Told by whatever met it — the check a candidate is built through, the walk that reads
     * what a built value hands on — and read by the place that says what the search came to, as
     * one {@link SearchShortfall} joined into everything said there. A flag per kind is one more
     * thing every carrier has to be taught to pass, and one a carrier is not taught is lost
     * wherever the search goes on past it.
     */
    private static final class FoundOut {

        private SearchShortfall found = SearchShortfall.NONE;

        void turnedAway() {
            found = found.uncertifiedWhere(true);
        }

        void notHandedOn(String why) {
            found = found.notHandedOn(why);
        }

        void notHeld(String why) {
            found = found.notHeld(why);
        }

        void met(CompositionShortfall met) {
            found = found.and(SearchShortfall.of(met));
        }

        SearchShortfall shortfall() {
            return found;
        }
    }

    /**
     * {@code check}, refusing any candidate at this parameter that does not read back at the place
     * it is being built for.
     *
     * <p><b>An acceptance condition and not an assertion.</b> A candidate that reads back somewhere
     * else is one candidate the search has tried, and the search goes on to the next — the same
     * shape a class's witness is certified with. Written as a throw, or as a refusal of the whole
     * point, one candidate landing elsewhere would be reported as a point no row can be written at.
     *
     * <p>What it asks is the property {@code TermRealizations} states of itself: every value built
     * there reads back as the number it was built for, and the way that would break is "a row
     * offered at an edge it does not stand on". Asked through the reading a row's own values are
     * read by, so nothing here is a second account of where a value stands.
     *
     * <p><b>A prune and not the acceptance of the row.</b> What a candidate can be held to here is
     * one parameter's value against one place, which is cheap and is less than the question. Whether
     * a row stands at a point takes the whole row and what running it recorded, and it is
     * {@code StandingAtAPoint}'s — asked of every row that is offered, after it is composed. So a
     * candidate this lets through is one worth going on with, and never one this has declared to be
     * a row at the point.
     *
     * @param found told where a candidate was turned away for this and nothing else, which is what
     *              tells a search that ran out of candidates from one that certified none
     */
    private static CandidateCheck certifying(CandidateCheck check, MeasuredInput subject, int parameter,
                                             Map<RealizationTarget, Place> fixing,
                                             FoundOut found) {
        // What each type on the way down to a fixed number is, which every candidate is read back
        // through and none of them changes: worked out at the first candidate and read after.
        Map<Type, TypeView> views = new HashMap<>();
        return new CandidateCheck() {

            @Override
            public CandidateCheck.Built build(int at, FixtureTemplate candidate) {
                CandidateCheck.Built built = check.build(at, candidate);
                // Nothing built it, so nothing here can say where it went, and the row is offered
                // as it was composed.
                if (at != parameter
                        || !(built instanceof CandidateCheck.Built.Value(var observed))) {
                    return built;
                }
                for (Map.Entry<RealizationTarget, Place> each : fixing.entrySet()) {
                    if (!subject.parameters().get(parameter)
                            .equals(each.getKey().writeRoot().head())) {
                        continue;
                    }
                    // How many elements meet a statement turns on whatever else the statement
                    // reads, which one parameter's value does not hold. The whole-row reading that
                    // follows is what reads it.
                    if (!(each.getKey() instanceof RealizationTarget.OfANumber number)) {
                        continue;
                    }
                    // Only a reading that placed the value somewhere else turns a candidate away.
                    // A reading that could not be made says nothing about where the value is, and
                    // a search that pruned on it would be spending this compiler's own limit as
                    // though it were an answer about the value. The whole-row reading that
                    // follows is where not being able to tell is recorded.
                    if (readsBackAt(subject, parameter, observed, number, each.getValue(), views)
                            instanceof RealizationReadback.Elsewhere(String why)) {
                        found.turnedAway();
                        return new CandidateCheck.Built.Refused(why);
                    }
                }
                return built;
            }

            // What a value's own type says of it is the decoder's, and where the whole parameter
            // reads back is no part of it: passed through, so a search under a point prunes on
            // the same proofs as any other.
            @Override
            public Admissibility admissibility(Type type, FixtureTemplate candidate) {
                return check.admissibility(type, candidate);
            }
        };
    }

    /**
     * What reading one candidate back at the term's position came to.
     *
     * <p><b>Three answers, and the third is not the second.</b> A value read where it was built for
     * and a value read somewhere else are what this walk can establish; everything else is the walk
     * unable to look, and this compiler being unable to look is not the model putting the value
     * elsewhere. Held as a {@code null} beside a sentence, the two are one — the sentence is
     * written whenever a number does not come back, so a value whose observation a limit cut short
     * is refused with a sentence saying it does not stand where it plainly does.
     *
     * <p>One occurrence is enough, as it is for a row that was written: a row stands at a point
     * where one of its readings does. And a reading that could not be made at one occurrence does
     * not take back another that placed the value — the answers are looked at in that order.
     *
     * @param views what each type on the walk is, read and added to
     */
    private static RealizationReadback readsBackAt(MeasuredInput subject, int parameter,
                                                   souther.compiler.observe.ObservedValue observed,
                                                   RealizationTarget.OfANumber target,
                                                   Place at, Map<Type, TypeView> views) {
        // The orders to read it back on, asked of the reading that answered them when the value was
        // built. Carried over from there instead, the two ends of one question would be two values
        // free to part, and a row would be read back on an order nothing composed it against.
        souther.compiler.inputs.TermOrders on = subject.quantities().ordersOf(target.term());
        if (on == null) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.NoOrdersOnTheEdge());
        }
        // How often a key occurs, or what its elements come to, is read with the key's value, which
        // is another parameter's and is no part of the one candidate; the whole-row reading that
        // follows is what reads it.
        if (target.term() instanceof NumericTerm.OccurrencesOfAKey
                || target.term() instanceof NumericTerm.GatheredUnderAKey) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.TurnsOnAnotherParameter());
        }
        // Only this parameter's value is filled in: the walk reads the one the path names, and the
        // others are not this candidate's to say anything about.
        List<souther.compiler.observe.ObservedValue> row = new ArrayList<>(
                java.util.Collections.nCopies(subject.parameters().size(), null));
        row.set(parameter, observed);
        // A number of an element read off the elements beside it is read off each container whole:
        // the values at the place gathered across containers would count, or take an end of, the
        // elements of one container among those of another.
        TermPath readAt = switch (target.term()) {
            case NumericTerm.OfAnElementsNeighbours among -> among.container();
            // Every value at the place across the containers, which is what the count is among.
            case NumericTerm.FromOnePosition _, NumericTerm.TakenOver _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _ ->
                    target.term().subjectPath();
            // Every element of every container, which is what a key's elements are gathered
            // from.
            case NumericTerm.GatheredUnderItsKey gathered -> gathered.elements();
            case NumericTerm.GatheredUnderAKey asked -> asked.subjectPath();
        };
        // Over the arms, so a walk that comes to answer a third way is one this is taught about
        // rather than one read as the walk and the type disagreeing.
        return switch (subject.inputs().valuesAt(row, readAt, views)) {
            case WalkResult.CouldNotWalk<List<souther.compiler.observe.ObservedValue>> _ ->
                    new RealizationReadback.CouldNotTell(new ReadbackGap.WalkAndTypeDisagree());
            case WalkResult.Reached(List<souther.compiler.observe.ObservedValue> values) ->
                    readBack(on, values, at);
        };
    }

    /**
     * What the values the walk stood at the term's path come to, read back as the term reads them,
     * against the place the candidate was built for.
     *
     * <p>No value standing there is an answer for a number one position answers, which has no number
     * of nothing. It is not for a number over a run: a run over no values is what the walk starts
     * from, and the term's own reader says what that comes to ({@link TermOrders#readOver}). Asked
     * of the term's kind with no {@code default}, so a kind of term added is one this has to say
     * something of.
     *
     * <p>For a number of an element read off the elements beside it the values are the containers
     * the elements stand in, each read on its own ({@link AnOccurrence}); no element in any of them
     * is no value there. A container not read whole is a reading that could not be made, and never
     * a container holding nothing.
     */
    static RealizationReadback readBack(TermOrders on,
                                        List<souther.compiler.observe.ObservedValue> values,
                                        Place at) {
        NumericTerm term = on.term();
        boolean nothingToRead = switch (term) {
            case NumericTerm.OfAnElementsNeighbours _ -> values.stream().allMatch(each -> AnOccurrence.of(each)
                            instanceof AnOccurrence.Read(List<ObservedValue> held)
                            && held.isEmpty());
            case NumericTerm.FromOnePosition _, NumericTerm.OccurrencesOfItsValue _,
                 NumericTerm.GatheredUnderItsKey _ -> values.isEmpty();
            case NumericTerm.TakenOver _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderAKey _ -> false;
        };
        if (nothingToRead) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.NoValueAtThePosition());
        }
        // What the number is of, asked the way the term's own reader asks it. A number one position
        // answers is read at each value standing there, and a row stands at a point where one of
        // its readings does; a number over a run is read of all of them at once, since that is what
        // the walk was given and any one of them is not it.
        //
        // Asked of the number and not of the target realizing it. Which location the row rebuilt
        // to move the number says nothing about how the number is read back, and a way of writing
        // one added later is not a reading of its own.
        Set<Incompleteness.Code> unread = EnumSet.noneOf(Incompleteness.Code.class);
        Set<UnheldNumber> notWorkedOut = EnumSet.noneOf(UnheldNumber.class);
        // A container, or an element in one, that is not of the shape the walk and the type say:
        // no reading of it is made, which is neither the value standing elsewhere nor an
        // observation that came back short.
        boolean ofAnotherShape = false;
        // An occurrence the statement keeping some of them could not be put to.
        Set<ReadingGap> keptNotTold = new LinkedHashSet<>();
        boolean stands = switch (term) {
            // How often a value occurs, or the end of the values of a key, among the elements of
            // each container: a row stands at a point where some element's number comes to it.
            case NumericTerm.OfAnElementsNeighbours _ -> {
                boolean any = false;
                for (ObservedValue container : values) {
                    switch (AnOccurrence.of(container)) {
                        case AnOccurrence.NotRead(Incompleteness.Code why) -> unread.add(why);
                        case AnOccurrence.OfAnotherShape _ -> ofAnotherShape = true;
                        case AnOccurrence.Read(List<ObservedValue> held) -> {
                            for (TermOrders.Neighbouring<AnOccurrence.OfAnotherShape> each
                                    : readEachOf(on, held)) {
                                switch (each) {
                                    case TermOrders.Neighbouring.HeldNothing<
                                            AnOccurrence.OfAnotherShape> _ -> ofAnotherShape = true;
                                    case TermOrders.Neighbouring.Read<
                                            AnOccurrence.OfAnotherShape>(
                                            NumericTerm.Reading read) -> {
                                        switch (read) {
                                            case NumericTerm.Reading.Number number ->
                                                    any |= number.value().compareTo(at) == 0;
                                            case NumericTerm.Reading.Missing missing ->
                                                    unread.add(missing.code());
                                            case NumericTerm.Reading.NotNumber _ -> { }
                                            case NumericTerm.Reading.NotWorkedOut(
                                                    UnheldNumber why) -> notWorkedOut.add(why);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                yield any;
            }
            case NumericTerm.FromOnePosition _ -> {
                boolean any = false;
                for (souther.compiler.observe.ObservedValue value : values) {
                    switch (on.read(value)) {
                        case NumericTerm.Reading.Number number ->
                                any |= number.value().compareTo(at) == 0;
                        case NumericTerm.Reading.Missing missing -> unread.add(missing.code());
                        case NumericTerm.Reading.NotNumber _ -> { }
                        case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) ->
                                notWorkedOut.add(why);
                    }
                }
                yield any;
            }
            // A row stands at a point where some value's count among all of them comes to it.
            case NumericTerm.OccurrencesOfItsValue occurrences -> {
                boolean any = false;
                List<souther.compiler.observe.ObservedValue> counted = values;
                KeptOccurrences kept = occurrences.selection();
                if (kept != null) {
                    // Only the values the statement keeps are counted. An occurrence the
                    // statement cannot be put to may be one of them, so a count made without it
                    // is a floor and no count: nothing is read back from the values alone.
                    counted = new ArrayList<>();
                    for (souther.compiler.observe.ObservedValue value : values) {
                        switch (kept.perElement().at(new CardinalityComposer.AnElementRead(
                                kept.position(), occurrences.subjectPath(), Map.of(),
                                List.of(value)))) {
                            case AStatementAtARow.Answer.Holds _ -> counted.add(value);
                            case AStatementAtARow.Answer.Fails _ -> { }
                            case AStatementAtARow.Answer.CouldNotTell(Set<ReadingGap> why) ->
                                    keptNotTold.addAll(why);
                        }
                    }
                }
                for (NumericTerm.Reading read : on.readEachAmong(counted)) {
                    switch (read) {
                        case NumericTerm.Reading.Number number ->
                                any |= number.value().compareTo(at) == 0;
                        case NumericTerm.Reading.Missing missing -> unread.add(missing.code());
                        case NumericTerm.Reading.NotNumber _ -> { }
                        case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) ->
                                notWorkedOut.add(why);
                    }
                }
                yield any;
            }
            // A row stands at a point where some element's key comes to it, read among every
            // element of the run by the one law the elements beside an element are read by.
            case NumericTerm.GatheredUnderItsKey gathered -> {
                boolean any = false;
                List<ObservedValue> filed = values;
                KeptOccurrences kept = gathered.selection();
                if (kept != null) {
                    // Only the elements the statement keeps are filed under a key, and one it
                    // cannot be put to may be one of them: as for a count of the kept ones. Each
                    // is read back whole, so the statement is put to what it holds.
                    filed = new ArrayList<>();
                    for (ObservedValue element : values) {
                        switch (kept.perElement().at(new AWholeElement(kept.position(),
                                gathered.elements(), element, on))) {
                            case AStatementAtARow.Answer.Holds _ -> filed.add(element);
                            case AStatementAtARow.Answer.Fails _ -> { }
                            case AStatementAtARow.Answer.CouldNotTell(Set<ReadingGap> why) ->
                                    keptNotTold.addAll(why);
                        }
                    }
                }
                for (TermOrders.Neighbouring<AnOccurrence.OfAnotherShape> each
                        : readEachOf(on, filed)) {
                    switch (each) {
                        case TermOrders.Neighbouring.HeldNothing<
                                AnOccurrence.OfAnotherShape> _ -> ofAnotherShape = true;
                        case TermOrders.Neighbouring.Read<AnOccurrence.OfAnotherShape>(
                                NumericTerm.Reading read) -> {
                            switch (read) {
                                case NumericTerm.Reading.Number number ->
                                        any |= number.value().compareTo(at) == 0;
                                case NumericTerm.Reading.Missing missing ->
                                        unread.add(missing.code());
                                case NumericTerm.Reading.NotNumber _ -> { }
                                case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) ->
                                        notWorkedOut.add(why);
                            }
                        }
                    }
                }
                yield any;
            }
            // Read with another parameter's value, so the one candidate stands nowhere here; the
            // entry point answers before this is reached.
            case NumericTerm.OccurrencesOfAKey _ -> throw new IllegalStateException(
                    "how often a key occurs is read back from a whole row");
            case NumericTerm.GatheredUnderAKey _ -> throw new IllegalStateException(
                    "what a key's elements come to is read back from a whole row");
            case NumericTerm.TakenOver _ -> switch (readRun(on, values)) {
                case NumericTerm.Reading.Number number -> number.value().compareTo(at) == 0;
                case NumericTerm.Reading.Missing missing -> {
                    unread.add(missing.code());
                    yield false;
                }
                case NumericTerm.Reading.NotNumber _ -> false;
                case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) -> {
                    notWorkedOut.add(why);
                    yield false;
                }
            };
        };
        // Before a stand is taken: the count that stands was made without an occurrence that may
        // have been counted.
        if (!keptNotTold.isEmpty()) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.KeptNotTold(keptNotTold));
        }
        if (stands) {
            return new RealizationReadback.AtRequestedPlace();
        }
        // Asked before the observation gap and before the definite negative below: a number the
        // exact arithmetic could not hold is neither an observation that came back short nor a
        // value proven to stand elsewhere, and reading it as either would tell a reader more than
        // this compiler worked out.
        if (!notWorkedOut.isEmpty()) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.NotWorkedOut(notWorkedOut));
        }
        if (!unread.isEmpty()) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.Observation(unread));
        }
        if (ofAnotherShape) {
            return new RealizationReadback.CouldNotTell(new ReadbackGap.WalkAndTypeDisagree());
        }
        return new RealizationReadback.Elsewhere("it was composed to put " + term + " at " + at
                + " and does not stand there");
    }

    /**
     * What a container the walk stood at reads as, for a number of each of its elements: the
     * elements, where it was read whole and holds them in order; why it was not read, where it was
     * not; and neither, where it was read and is no container of elements.
     */
    private sealed interface AnOccurrence {

        record Read(List<ObservedValue> elements) implements AnOccurrence {}

        record NotRead(Incompleteness.Code why) implements AnOccurrence {}

        record OfAnotherShape() implements AnOccurrence {}

        static AnOccurrence of(ObservedValue container) {
            if (container.cause() != null) {
                return new NotRead(container.cause().code());
            }
            return container instanceof ObservedValue.Sequence held ? new Read(held.elements())
                    : new OfAnotherShape();
        }
    }

    /**
     * What each of {@code held}, the elements of one container, reads as {@code on}'s number among
     * them, by the one law a row's elements are read by: an element read whole that holds nothing
     * at a way the number reads is an element of another shape than the walk's, and stops what
     * its reading stops.
     */
    private static List<TermOrders.Neighbouring<AnOccurrence.OfAnotherShape>> readEachOf(
            TermOrders on, List<ObservedValue> held) {
        List<Function<ElementProjection, TermOrders.Holding<AnOccurrence.OfAnotherShape>>> each =
                new ArrayList<>(held.size());
        for (ObservedValue element : held) {
            each.add(field -> on.in(field, element) instanceof ObservedValue value
                    ? new TermOrders.Holding.Value<>(value)
                    : new TermOrders.Holding.Nothing<>(new AnOccurrence.OfAnotherShape()));
        }
        TermOrders.ElementsTogether<AnOccurrence.OfAnotherShape> together = on.together(each);
        List<TermOrders.Neighbouring<AnOccurrence.OfAnotherShape>> out =
                new ArrayList<>(each.size());
        for (Function<ElementProjection, TermOrders.Holding<AnOccurrence.OfAnotherShape>> one
                : each) {
            out.add(together.numberOf(one));
        }
        return out;
    }

    /**
     * A row holding nothing but one element of {@code container}, read back whole: a place in it
     * is walked to through the names {@code on} says are worn on the way, and anything else could
     * not be walked to, which a statement reads as not being able to tell and never as failing.
     *
     * <p>A value of another case than a narrowing on the way leaves holds nothing below it, which
     * is the element's own answer ({@link ElementProjection#in}). A field the element holds no
     * value at is told as not walked to: nothing here says it was left unwritten.
     */
    private record AWholeElement(TermPath container, TermPath element, ObservedValue held,
                                 TermOrders on) implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            ElementProjection within = ElementProjection.below(element, path);
            if (within == null) {
                return WalkResult.couldNotWalk();
            }
            ObservedValue there = on.in(within, held);
            if (there != null) {
                return WalkResult.reached(new ObservationAtPoint.Value(there));
            }
            for (ElementProjection each : within.onTheWay()) {
                if (each.narrowing() != null && on.in(each, held) == null
                        && on.in(each.narrowedFrom(), held) != null) {
                    return WalkResult.reached(ObservationAtPoint.WROTE_NOTHING);
                }
            }
            return WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return path.equals(element) ? WalkResult.reached(List.of(held))
                    : WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            return of.equals(container) ? WalkResult.reached(List.of(this))
                    : WalkResult.couldNotWalk();
        }
    }

    /**
     * What {@code on} reads of a run from the values the walk stood at its position.
     *
     * <p>For a run computed of each element those values are the elements, and each is read as one
     * element: the fields its computation reads are the fields of that element, so what is paired
     * is what the row pairs.
     *
     * <p>What a run of the program comes to where it answers ({@link TermOrders#readOverElements}),
     * so a candidate reading back at the place it was built for is one worth running and not one
     * shown to get there: its run may stop on the way.
     */
    private static NumericTerm.Reading readRun(TermOrders on, List<ObservedValue> values) {
        if (!(on.term() instanceof NumericTerm.TakenOver over)
                || !(over.source() instanceof RunSource.ComputedOccurrences)) {
            return on.readOver(values);
        }
        List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
        for (ObservedValue element : values) {
            each.add(field -> on.in(field, element));
        }
        return on.readOverElements(each);
    }

    /**
     * What reading a candidate back said about where it stands.
     *
     * <p>This walk's own vocabulary and not the one an account is written in. What is asked here is
     * one parameter's value against one place, which is a cheap prune of the search — a candidate
     * this lets through is one worth going on with, and never one this has declared to be a row at
     * the point. What settles that is the whole row, read after it is composed, and what the
     * <em>account</em> then says is written in the account's words.
     */
    sealed interface RealizationReadback {

        /** The value reads back as the number it was built for. */
        record AtRequestedPlace() implements RealizationReadback {}

        /** It reads back as some other number, and this is how that is said. */
        record Elsewhere(String why) implements RealizationReadback {}

        /** Nothing here could say where it reads, and this is what stopped the saying. */
        record CouldNotTell(ReadbackGap why) implements RealizationReadback {}
    }

    /**
     * What stopped one candidate being read back where it was built for.
     *
     * <p>Kept apart from what an account calls a gap. The cases here are this walk's own — an edge
     * that carried no orders, a path the walk and the type disagree about — and only one of them is
     * about the observation. Shared with the account's vocabulary, a prune's reasons would be
     * offered as reasons a point cannot be shown writable, and three of these have nothing to do
     * with that.
     */
    sealed interface ReadbackGap {

        /** The fixing's edge kept no orders, so there is nothing to read the value on. */
        record NoOrdersOnTheEdge() implements ReadbackGap {}

        /** The walk and the declared type disagree about the path, which the quantity reports. */
        record WalkAndTypeDisagree() implements ReadbackGap {}

        /** The row wrote no value at the position the term names. */
        record NoValueAtThePosition() implements ReadbackGap {}

        /** The number turns on the value of another parameter than the one being read back. */
        record TurnsOnAnotherParameter() implements ReadbackGap {}

        /** The statement keeping some of the occurrences could not be put to one of them, and
         *  that one may be among those counted. */
        record KeptNotTold(Set<ReadingGap> causes) implements ReadbackGap {}

        /** The observation of the value did not come back whole. */
        record Observation(Set<Incompleteness.Code> causes) implements ReadbackGap {}

        /** Every value the term read arrived, and the number one of them comes to is one the exact
         *  arithmetic could not hold. */
        record NotWorkedOut(Set<UnheldNumber> causes) implements ReadbackGap {}
    }

    /**
     * The region a group's value is composed in: the way's, and where the group holds a count or a
     * statement its elements meet together, that with every number of the row standing where the
     * row fixed it.
     *
     * <p>A count is met by elements chosen against the numbers its statement reads beside them, and
     * those are numbers of other locations, fixed with the count; so is how often a key occurs,
     * which is counted for the value of another location. Every other group is composed out
     * of its own numbers and the way's region, which is what it is handed.
     *
     * <p>Not a number inside a container. A value placed at an element is some element standing
     * there, and fixed in the region it would be every element.
     *
     * <p>And with the elements of a container written at {@code at} held to what every element of
     * it is to meet, where a condition on the way says so ({@link ElementBound}).
     *
     * @param bounds what the conditions on the way ask every element of a container to meet,
     *               where it is no value of its own
     */
    private static RegionToCompose composedIn(TermPath at,
                                              SequencedMap<RealizationTarget, AskedAt> group,
                                              SearchRegion region,
                                              Map<RealizationTarget, Place> standing,
                                              List<ElementBound> bounds) {
        List<ElementBound> here = new ArrayList<>();
        for (ElementBound each : bounds) {
            if (LocationWrites.oneLocation(each.container(), at)) {
                here.add(each);
            }
        }
        for (RealizationTarget each : group.keySet()) {
            if (each instanceof RealizationTarget.ACount
                    || each instanceof RealizationTarget.ElementsMeetingTogether
                    || each.keyAskedFor() != null) {
                Map<NumericTerm, Place> fixed = new LinkedHashMap<>();
                standing.forEach((target, place) -> {
                    if (target instanceof RealizationTarget.OfANumber number
                            && !number.term().subjectPath().insideAContainer()) {
                        fixed.put(number.term(), place);
                    }
                });
                return new RegionToCompose(region, fixed, here);
            }
        }
        return new RegionToCompose(region, null, here);
    }

    /**
     * The region a group's value is composed in, said as what it is made of: the way's region, and
     * the numbers of the row fixed in it where the group holds a count ({@link #composedIn}).
     *
     * <p>Said as its makings so that two askings of one location can be told to be one request
     * without asking whether two regions are equal, which a region does not answer: the same region
     * handed down, with the same numbers fixed in it and the same bounds on the elements, is the
     * same region to compose in. Made once where it is asked for, and kept.
     */
    private static final class RegionToCompose {

        private final SearchRegion base;
        // The numbers fixed in the base, or null where the base is composed in as it is.
        private final Map<NumericTerm, Place> fixed;
        private final List<ElementBound> bounds;
        private SearchRegion made;

        RegionToCompose(SearchRegion base, Map<NumericTerm, Place> fixed,
                        List<ElementBound> bounds) {
            this.base = base;
            this.fixed = fixed == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(fixed));
            this.bounds = List.copyOf(bounds);
        }

        SearchRegion region() {
            if (made == null) {
                made = ElementBound.within(fixed == null ? base : base.given(fixed), bounds);
            }
            return made;
        }

        /** Whether this is made of the same region handed down, with the same numbers fixed and
         *  the same bounds on the elements. */
        boolean sameAs(RegionToCompose other) {
            return base == other.base && Objects.equals(fixed, other.fixed)
                    && bounds.equals(other.bounds);
        }
    }

    /**
     * The remainders the row already stands at, each at its number.
     *
     * <p>A position's value is placed after the item's numbers are, and a remainder of it is one of
     * those: left out of what the place is chosen in, the value goes where the run begins and the
     * remainder fixed beside it is refused afterwards. Said to the region first, the run the value
     * is chosen in is the one the remainder leaves ({@code inputs.ReadQuantities}).
     *
     * <p>Only these. Any other number standing beside the value is read off it and not chosen
     * before it, which is how it has been placed and is not what this changes.
     */
    private static Map<NumericTerm, Place> remaindersStanding(
            Map<RealizationTarget, Place> standing) {
        Map<NumericTerm, Place> remainders = new LinkedHashMap<>();
        standing.forEach((target, at) -> {
            if (target instanceof RealizationTarget.OfANumber number
                    && number.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.TheFloorRemainder) {
                remainders.put(taken, at);
            }
        });
        return remainders;
    }

    /**
     * The values that stand at one position's place of the item.
     *
     * <p>The axis's own edge where the subject has an axis at this position, which is where a count
     * taken of a location is met by whatever carries that count. Where it has none — a behavior whose
     * inputs nothing bounds has no axis and its body still draws lines between them — the value is
     * written from the declared type.
     *
     * <p><b>What a number is met by is not asked, and how many locations are being fixed is not
     * either.</b> A number several values answer is asked for one of them, and the one this is
     * handed reads back as that number — which is what {@link TermRealizations} promises of
     * everything it builds, one way round and not as an inverse. Whether a second location is being
     * fixed beside this one says nothing about that promise, so a row is composed here for a number
     * many values answer exactly as it is for a number one does.
     */
    private static Edge edgeAt(MeasuredInput subject, TermPath at,
                               SequencedMap<RealizationTarget, AskedAt> group,
                               souther.compiler.inputs.SearchRegion within) {
        return edgeAt(subject, at, group, within, DemandsInside.NOTHING);
    }

    /**
     * The same, with the value asked to hold {@code inside} at positions inside it as well.
     *
     * @param at where the group is written, which {@link #byTheLocationTheyWrite} gathered it under
     */
    private static Edge edgeAt(MeasuredInput subject, TermPath at,
                               SequencedMap<RealizationTarget, AskedAt> group,
                               souther.compiler.inputs.SearchRegion within,
                               DemandsInside inside) {
        // Which value answers the number is `TermRealizations`' one answer — asked of it whatever
        // kind of number this is, so that what can be built is settled in one place. Read off the
        // kind of term here as well, an operation would gain a value nothing writes for it on the
        // day the arm for it was written, with nothing failing to say so.
        //
        // Where the value is written, which is the traversal that follows one. It stops where a
        // value is built rather than where a name is read, and that is the answer this question
        // wants: a name every case of a sum spreads is readable on a value of the sum and is not a
        // place a value is composed for. Asked here whether or not the number is one a measure was
        // drawn on: a measure says where the model divides a number and not where a value of it can
        // be put, so a search reading the second off a measure would be composing at a place this
        // walk says nothing is written.
        Type writtenAt = subject.inputs().typeAtWrittenPath(at);
        if (writtenAt == null) {
            return Edge.none(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // And both orders the value is read back on, which are the reading's. Taken off the type
        // above, the walk that answers where a value is written would be answering what a number
        // there is measured on as well, and the two are one value only for as long as no term
        // arrives where they part. Handed over as the question rather than as an answer, since a
        // group is over several terms and each of them is measured where this reading says.
        return edgeFrom(TermRealizations.allSatisfying(writtenAt, keptApartUnder(subject, at),
                group, subject.quantities(), within, subject.ruleReading(), inside), group,
                writtenAt);
    }

    /**
     * What the rules of every value whose clauses name {@code at} keep the elements of the value
     * written there apart at ({@link ConstructionRules#heldAt}) — nothing where none of them names
     * it.
     *
     * <p>Read where the plan's composing reads them, so a list built as a field of an element of
     * another list is kept apart as its own record says, whichever of the two builds it. Nothing
     * settled: what is kept apart is the same whatever a row fixes, so it is the input's answer,
     * read once for every edge at the position ({@link MeasuredInput#keptApartAt}).
     */
    private static List<List<String>> keptApartUnder(MeasuredInput subject, TermPath at) {
        return subject.keptApartAt(at);
    }

    /**
     * The row's positions gathered under the location each of them is written at.
     *
     * <p>Which is what a row is: one value per location, whatever number of the model that value
     * was asked for. Walked as the numbers alone, a location asked for two of them is two edges and
     * two values, and what the row carries is the second one.
     *
     * <p>By the path each number is written at and not by which paths reach one value. A container
     * and a position inside it are one location and are two entries here, which leaves them where
     * they were: nothing composes those together, and {@link LocationWrites} is what says so.
     *
     * <p>But for one: a container composed for how many of its elements meet something chooses its
     * elements, so a value some element of it is to stand at goes in with the counts
     * ({@link CardinalityComposer}).
     *
     * <p>The numbers as the sets they are asked for out of, which a point of a border and a class
     * both are: the arrangement is the same either way, and reading it twice would be two answers
     * to which location a number is written at.
     *
     * @param someElement the numbers among {@code standing} some element is to stand at
     */
    private static SequencedMap<TermPath, SequencedMap<RealizationTarget, AskedAt>>
            byTheLocationTheyWrite(Map<RealizationTarget, AskedAt> standing,
                                   Set<RealizationTarget> someElement) {
        Map<TermPath, TermPath> counted = countedAmong(standing.keySet());
        SequencedMap<TermPath, SequencedMap<RealizationTarget, AskedAt>> out =
                new LinkedHashMap<>();
        for (Map.Entry<RealizationTarget, AskedAt> each : standing.entrySet()) {
            out.computeIfAbsent(writtenAmong(each.getKey(), counted, someElement),
                            _ -> new LinkedHashMap<>())
                    .put(each.getKey(), each.getValue());
        }
        return out;
    }

    /**
     * The element of each container {@code with} composes for how many of its elements meet
     * something, or for a statement they meet together, and where that container is written.
     * Empty where there is neither among them, which is every row of a model that counts nothing.
     */
    private static Map<TermPath, TermPath> countedAmong(Collection<RealizationTarget> with) {
        Map<TermPath, TermPath> out = Map.of();
        for (RealizationTarget each : with) {
            TermPath container = switch (each) {
                case RealizationTarget.ACount count -> count.count().container();
                case RealizationTarget.ElementsMeetingTogether together -> together.container();
                case RealizationTarget.OfANumber _ -> null;
            };
            if (container != null) {
                if (out.isEmpty()) {
                    out = new HashMap<>();
                }
                out.put(container.element(), each.writeRoot());
            }
        }
        return out;
    }

    /**
     * Where {@code target} is written: its own root, or where it is a value some element of a
     * container composed for how many of its elements meet something is to stand at
     * ({@link #countedAmong}), that container's.
     *
     * <p>Some element and not every one. A value placed for every element of a container to meet
     * something is a value of each, and composing the container for its counts chooses elements
     * that value does not hold of; it is a second write of the location, said where it is.
     *
     * @param someElement the numbers some element is to stand at, which a condition that some
     *                    element meets something placed
     */
    private static TermPath writtenAmong(RealizationTarget target,
                                         Map<TermPath, TermPath> counted,
                                         Set<RealizationTarget> someElement) {
        if (!counted.isEmpty() && someElement.contains(target)
                && target instanceof RealizationTarget.AtOnePosition(
                        NumericTerm.FromOnePosition term)
                && term instanceof NumericTerm.ValueOf) {
            // The element itself, or a number inside it.
            for (Map.Entry<TermPath, TermPath> each : counted.entrySet()) {
                if (term.position().isAtOrUnder(each.getKey())) {
                    return each.getValue();
                }
            }
        }
        return target.writeRoot();
    }

    /**
     * Why the classes {@code where} stands at leave a number the comparisons ask for no room, or
     * null where none does or {@code held} is not what comparisons ask: the first thing composing a
     * row finds out, and found out without composing it.
     *
     * <p>A candidate this refuses is one no building could compose, so a search that is bounded in
     * what it builds does not count it among them.
     */
    private static Attempt classesLeaveNoRoom(MeasuredInput.MeasuredAxes axes, int[] where,
                                              HeldTogether held) {
        if (!(held instanceof HeldTogether.Asked holding) || holding.asked().isEmpty()) {
            return null;
        }
        SequencedMap<RealizationTarget, AskedAt> numbers =
                numbersTheClassesAdmit(axes, where, axes.subject().quantities());
        for (Map.Entry<RealizationTarget, AskedAt> each : holding.asked().entrySet()) {
            Attempt noRoom = leavesNoRoom(each.getKey(), each.getValue(), numbers.get(each.getKey()),
                    axes.subject().quantities());
            if (noRoom != null) {
                return noRoom;
            }
        }
        return null;
    }

    /**
     * Why a number asked to stand at {@code asked} has no room in {@code theClass}, the numbers
     * its class admits — or null where it has, or where the class is of no number.
     */
    private static Attempt leavesNoRoom(RealizationTarget key, AskedAt asked, AskedAt theClass,
                                        Quantities measuring) {
        // A class is of a number, so only a number is asked by both.
        if (theClass == null || !(key instanceof RealizationTarget.OfANumber number)) {
            return null;
        }
        Carrier on = carrierOf(number.term(), measuring);
        if (on != null && asked.named() != null && theClass.walking().holds(asked.named(), on)) {
            return null;
        }
        return new Attempt(null, UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                key.toString(), Optional.of("`" + key
                        + "` is asked to stand where its class leaves it no room"));
    }

    /**
     * The numbers this row's classes admit, by the number each is a class of.
     *
     * <p>Read off the classes the row sits in and not off the axes, because an axis is a number the
     * model divides and says nothing about which of its classes this row is being built for.
     *
     * <p>The sets themselves, which is what the classes mean. A number chosen out of one and
     * carried here instead would be asking whether one value answers the numbers that were picked,
     * and a no to that is no answer about the classes.
     *
     * <p>A class that narrows the position is left out. What such a class offers is the narrowing
     * and not a value of the unnarrowed position, and what stands there is composed out of the
     * narrowed type by the walk below — so a number to compose for is what the class beside it has.
     */
    private static SequencedMap<RealizationTarget, AskedAt> numbersTheClassesAdmit(
            MeasuredInput.MeasuredAxes axes, int[] where, Quantities measuring) {
        SequencedMap<RealizationTarget, AskedAt> out = new LinkedHashMap<>();
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] == NOT_HERE) {
                continue;
            }
            PartitionClass cls = axes.get(i).classes().get(where[i]);
            NumericSet admits = admitted(cls);
            if (admits != null) {
                out.put(RealizationTarget.of(cls.of()),
                        AskedAt.theClass(admits, carrierOf(cls.of(), measuring)));
            }
        }
        return out;
    }

    /**
     * What each of the row's numbers is one of, by where the number came from.
     *
     * <p>Two askings and they are asked of two things. A number the item names is one of what the
     * item leaves that position, which is the border's quantity to answer; a number placed on the
     * way is one of what the rules leave it there, which is the region and the cuts. Read off one
     * of the two for both, a position the way bounds would be answered about by an item that is
     * not about it, and a position of the item by a region that has the item's own value in it.
     *
     * <p>A position under both is under both, and what it is asked is what they leave together.
     *
     * <p>One entry for every number the row stands at, since every one of them came from the item
     * or from a cut. A number with no entry is a number this reader did not know it was placing,
     * and it is refused where the search is built rather than answered about as though the rules
     * said nothing of it.
     *
     * <p>Asked where an assignment of a cut's numbers is tested against what composing a row with
     * it comes to, and again where the row is composed: one answer to what a number is one of, so
     * the value tested is the value written.
     *
     * @param itemAsks what the item asks of each number it fixes
     * @param leaves   what the way leaves each number placed on it
     */
    private static Map<RealizationTarget, NumbersAskedFor> whatEachOfThemIsANumberOf(
            Map<RealizationTarget, NumbersAskedFor> itemAsks,
            Map<NumericTerm, RealizationTarget> routed,
            Map<RealizationTarget, NumbersAskedFor> counted, WhatTheWayLeaves leaves) {
        Map<RealizationTarget, NumbersAskedFor> out = new LinkedHashMap<>(itemAsks);
        // Every count the row stands at, which is one of the counts the item and every condition
        // on the way leave it, and every statement its elements meet together.
        counted.forEach((target, counts) -> out.merge(target, counts, leaves::met));
        // Every number a place was chosen for on the way, and not every number a cut names. A cut
        // may be met more than one way — every element meeting a condition, or a container holding
        // none — and what the row stands at is whichever way was placed; asked of the cut's numbers
        // instead, a number placed by the other way would stand with nothing saying what it is one
        // of.
        //
        // The target is the one the row was composed at, and not one built from the number here.
        // Where a row writes a number is chosen once, where the positions of the way are placed
        // ({@link Standing#routed}) — worked out again, a number read at a name every case of a sum
        // spreads would be filed under the sum's own name while the row stands at a position under
        // a case, and the search would be built for a number nothing had said what it was one of.
        routed.forEach((at, target) -> out.merge(target, leaves.of(at), leaves::met));
        return out;
    }

    /**
     * What the rules leave each number a row places on one way to a point, said once per number.
     *
     * <p>Asked every time a condition's numbers are tried against composing a row — once for each
     * way of writing them, and again for the row — and the answer is about the number, the way's
     * region and the cuts the way took in, none of which a try moves. So it is worked out the first
     * time a number is asked about and read after that.
     *
     * <p>Made for one point's composing and gone with it. The region is the way's as it was handed
     * over and nothing a condition chose since, so a number asked about after a choice still gets
     * the answer about the way and not about the branch the search is in.
     */
    private static final class WhatTheWayLeaves {

        private final MeasuredInput subject;
        private final Reachability.Reaching reaching;
        private final Map<NumericTerm, NumbersAskedFor> said = new HashMap<>();

        /** What two answers come to together, for the two as objects: a number is asked of again
         *  at every condition placed after the one that routed it, with the same two answers. */
        private final Map<NumbersAskedFor, Map<NumbersAskedFor, NumbersAskedFor>> together =
                new IdentityHashMap<>();

        WhatTheWayLeaves(MeasuredInput subject, Reachability.Reaching reaching) {
            this.subject = subject;
            this.reaching = reaching;
        }

        /** {@code held} and {@code other} met, worked out once for the pair. */
        NumbersAskedFor met(NumbersAskedFor held, NumbersAskedFor other) {
            return together.computeIfAbsent(held, _ -> new IdentityHashMap<>())
                    .computeIfAbsent(other, _ -> held.meet(other));
        }

        NumbersAskedFor of(NumericTerm at) {
            NumbersAskedFor known = said.get(at);
            if (known != null) {
                return known;
            }
            NumbersAskedFor asked = NumbersAskedFor.askedOf(at, reaching.region(),
                    carrierOf(at, subject.quantities()), reaching.boundedOnTheWay());
            said.put(at, asked);
            return asked;
        }
    }

    /**
     * Each of those numbers as one a caller picked out of what it was asking about.
     *
     * <p>Which is what a point of a border is tried with: the search settled on this number of the
     * item and the row is composed for it. What it is a number <em>of</em> travels beside it, so
     * that nothing built at this one is an answer about this one — the item holds every number the
     * rules leave beside it, and a walk of one candidate saw none of them.
     */
    private static Map<RealizationTarget, AskedAt> atThoseNumbers(
            Map<RealizationTarget, Place> standing,
            Map<RealizationTarget, NumbersAskedFor> asking) {
        Map<RealizationTarget, AskedAt> out = new LinkedHashMap<>();
        for (Map.Entry<RealizationTarget, Place> each : standing.entrySet()) {
            out.put(each.getKey(),
                    AskedAt.oneNumberOf(asking.get(each.getKey()), each.getValue()));
        }
        return out;
    }

    /** The order a term's values are counted on, or null where this reading has none for it. */
    private static Carrier carrierOf(NumericTerm term, Quantities measuring) {
        souther.compiler.inputs.TermOrders orders = measuring.ordersOf(term);
        return orders == null ? null : orders.answered();
    }

    /** The numbers a class admits of the number it is a class of, or null where it is about
     *  something a value is composed for another way. */
    private static NumericSet admitted(PartitionClass cls) {
        return cls.of() == null || cls.selects() != null ? null : cls.recognises().numbers();
    }

    /** The value composed for every number of this class's location, or null where this class is
     *  the only one of the row standing on it. */
    private static List<FixtureTemplate> answeringAllOfThem(
            Map<TermPath, List<FixtureTemplate>> together, PartitionClass cls) {
        return admitted(cls) == null
                ? null
                : together.get(RealizationTarget.of(cls.of()).writeRoot());
    }

    /**
     * The axes in the order the search fixes them.
     *
     * <p>Most classes first, and then parameter order and the path, so that two runs of one model
     * order them the same way and the rows come out in the same order twice.
     */
    static MeasuredInput.MeasuredAxes ordered(MeasuredInput subject) {
        return subject.axes().where(Axis::derivable)
                .sortedBy(Comparator.comparingInt((Axis a) -> -a.classes().size())
                        .thenComparingInt(a -> {
                            int at = subject.parameters().indexOf(a.path().head());
                            return at < 0 ? Integer.MAX_VALUE : at;
                        })
                        .thenComparing(a -> a.path().toString()));
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

    /** Where {@code id} sits among {@code axis}'s classes, or -1 where it is none of them. */
    private static int classIn(Axis axis, String id) {
        for (int c = 0; c < axis.classes().size(); c++) {
            if (axis.classes().get(c).id().equals(id)) {
                return c;
            }
        }
        return -1;
    }




    /** What a row is about, in the words the model uses. The class's label rather than its id: an id
     * is scoped by carrying its own path, and a description that carries the path already would say
     * it twice. */
    private static String label(Axis axis, int cls) {
        return axis.path() + "=" + axis.classes().get(cls).label();
    }

    /**
     * The same, for a class named the way an obligation names it.
     *
     * <p>What a report writes beside the row, worked out where the classes are rather than kept
     * beside the obligation. A label copied into the obligation would be a second spelling of the
     * class, free to disagree with the axis the day either moved.
     */
    static String labelOf(MeasuredInput subject, ClassOfAPosition owed) {
        for (Axis axis : subject.axes().axes()) {
            if (!axis.id().equals(owed.at())) {
                continue;
            }
            for (PartitionClass cls : axis.classes()) {
                if (cls.id().equals(owed.classId())) {
                    return axis.path() + "=" + cls.label();
                }
            }
        }
        throw new IllegalStateException(
                "a row was owed for a class the subject does not divide: " + owed);
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
     * <p>A row seen filling the combination and a row offered because nothing could watch it are
     * not the same thing to have found. They differ in what may afterwards be concluded from the row
     * and in whether this generation may say its rows were confirmed, so which of them it is, is the
     * answer — rather than something read back off an empty account of the run.
     *
     * <p>And coming back with nothing is three answers rather than one. A combination the model does
     * not have, a search that tried everything the combination leaves, and a search a bound stopped
     * are three different pieces of news: the first takes the combination away, the second is about
     * the model, and the third is about this search and says nothing about the model at all. Held as
     * one value with a reason inside it, the third arrived wearing the second's clothes — the last
     * candidate's refusal offered as the combination's answer, over candidates nothing tried
     * ({@link Completeness}).
     */
    private sealed interface Witness {

        /** A row seen filling the combination, carrying the witness — that being the only value
         *  which says so. */
        record Certified(GeneratedRow row, CellSelection.CertifiedWitness by) implements Witness {}

        /** A row nothing could watch, offered on the strength of the reading alone. */
        record Unconfirmed(GeneratedRow row, int[] where) implements Witness {}

        /** No reading to look at: the model does not have this combination. Never a search that
         *  failed. */
        record NoCombination(String said) implements Witness {}

        /** Every candidate of every reading was tried and none answered, and what the last of them
         *  came to. Read as the combination's answer, that is what it is: nothing was left untried
         *  behind it. */
        record Exhausted(List<String> classes, UnresolvedCombination.Reason reason, String detail,
                         Optional<String> said, SearchShortfall found)
                implements Witness {

            /**
             * The word, and with it what the search found out. An arm nothing reached is told
             * apart from an arm this compiler stopped short of by what travels beside the word,
             * and there is nothing else in the answer that tells them apart.
             */
            CameToNothing cameToNothing() {
                return found.published(classes, reason, detail, said);
            }
        }

        /**
         * A bound stopped the search with candidates it had not tried. What the ones it did try
         * came to is that candidate's news and not this combination's.
         *
         * <p>What they met of this compiler's is this combination's all the same. The bound that
         * stopped the walk over the readings is not a figure the composing of a row is held to, and
         * a figure a candidate ran into before the walk stopped is still a number somebody can
         * raise — dropped because the walk then stopped for another reason, it is a stop nothing
         * downstream can see. And an offer a candidate was short of the same: a rule somebody can
         * rewrite, whichever candidate it was offered to.
         *
         * <p>{@code boundsReached} is the bounds of this class's own the walk was compared against
         * and stopped at, as each stood there: none where what cut it short was not one of them.
         * {@code metARunNothingWatched} is whether a candidate ran and nothing could say what it
         * did, which cuts a walk short at no figure at all.
         */
        record Limited(List<String> classes, SearchShortfall found, List<Figure> boundsReached,
                       boolean metARunNothingWatched)
                implements Witness {

            public Limited {
                boundsReached = Figure.inOrder(boundsReached);
            }

            /**
             * The search stopped, which is this run's news and not the model's: said as that,
             * whatever the candidates it did try came to, and beside it what they found out.
             */
            CameToNothing cameToNothing() {
                return found.published(classes,
                        UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED, null,
                        Optional.empty());
            }
        }
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
    private static Witness witnessFor(MeasuredInput.MeasuredAxes axes,
                                      CellSelection selection, CandidateCheck check, RunOnce trial,
                                      List<ArmProbe> takes,
                                      List<ResolvedOrigin> origins, FixtureReferences references,
                                      List<StoodInAnswer> answers) {
        return witnessFor(axes, selection, check, trial, takes, List.of(), origins,
                references, answers);
    }

    /**
     * The same, for a search that is not looking on an arm's behalf.
     *
     * <p>Two lists because the arms play two parts here and only one of them is a purpose. What the
     * run is held against is {@code takes} — the claims a row filling this combination makes, which
     * is what says a candidate arrived — and what the row is composed for is what somebody was owed.
     * They are the same list where an arm is what was asked for, and they are not where a
     * combination of the body's decisions is: a cell may claim no arm at all, and a row named after
     * nothing is not a row.
     */
    private static Witness witnessFor(MeasuredInput.MeasuredAxes axes,
                                      CellSelection selection, CandidateCheck check, RunOnce trial,
                                      List<ArmProbe> takes, List<Purpose> alsoFor,
                                      List<ResolvedOrigin> origins, FixtureReferences references,
                                      List<StoodInAnswer> answers) {
        // Composed for the arms it was looked for, and not for the combination it was found at.
        // The combination is where the search went; the arms are what somebody is owed a row at.
        // One row answering two of them is two answers and not one composite thing.
        List<Purpose> composedFor = new ArrayList<>(
                takes.stream().map(Purpose.ForAnArm::new).map(Purpose.class::cast).toList());
        composedFor.addAll(alsoFor);
        return witnessing(new Reading(axes, selection, check, trial,
                List.copyOf(composedFor), null, origins, references, answers));
    }

    /**
     * A row at {@code selection} that is {@code furthermore} besides, composed for
     * {@code composedFor} alone: what a row is looked for here is not the arms the selection holds
     * it to go through, which are where it is looked for.
     */
    private static Witness witnessFor(MeasuredInput.MeasuredAxes axes,
                                      CellSelection selection, CandidateCheck check, RunOnce trial,
                                      List<Purpose> composedFor,
                                      Furthermore furthermore,
                                      List<ResolvedOrigin> origins, FixtureReferences references,
                                      List<StoodInAnswer> answers) {
        return witnessing(new Reading(axes, selection, check, trial, composedFor,
                furthermore, origins, references, answers));
    }

    /**
     * Whether a row is one a rewrite of the body answers differently on, for one rewrite, and how
     * the search for one ended where none was found.
     *
     * <p>The rewrite answering differently is the whole of the question. Whether a row stating that
     * answer would notice is then what stating it is — and what would be stated is what the body
     * answers, so a row the two answer differently on is one a person writing its answer down would
     * have noticed the rewrite with.
     *
     * <p>Runs are counted against the measure's own figure and not a share of the composing's. What
     * it bounds is runs, and a search for a row a rewrite is told by runs each candidate twice — the
     * body, and the rewrite — over values chosen again within one candidate, which the figures over
     * candidates never see. Each way the search stops is kept as itself, since which figure a wider
     * run would have to raise is what a reader of an undecided rewrite acts on.
     */
    private static final class ReplacementWitness {

        private final RunOnce trial;
        private final ReplacementOwed asked;
        private final int mostRuns;
        private int runs;
        /** Whether any row was asked about and answered alike. */
        private boolean alike;
        /** How many times this stopped a search. */
        private int stops;
        /** The ways the search stopped with something left untried, each as it was met there: at
         *  the figures it was stopped at where one is carried, at something else where it was. */
        private final Map<ReplacementDisposition.Ended, ReplacementDisposition.Met> stopped =
                new EnumMap<>(ReplacementDisposition.Ended.class);

        private ReplacementWitness(RunOnce trial, ReplacementOwed asked, int mostRuns) {
            this.trial = trial;
            this.asked = asked;
            this.mostRuns = mostRuns;
        }

        /**
         * Whether the rewrite answers {@code row} differently from the body, given what running
         * the body on it came to where a search already ran it, or null where it did not.
         */
        Acceptance of(GeneratedRow row, ObservedRun written) {
            ObservedRun body = written != null ? written : run(row);
            if (body == null) {
                return stop(ReplacementDisposition.Ended.RUNS_A_REWRITE_MAY_TAKE, runsReached());
            }
            AnswerObservation rewritten = switch (asked) {
                case ReplacementOwed.OfAnArm arm -> ranUnder(row, Rewriting.ofArms(arm.replacing()));
                case ReplacementOwed.OfAWalk walk ->
                        ranUnder(row, Rewriting.ofWalks(walk.replacing()));
                case ReplacementOwed.ByOneAnswer one -> new AnswerObservation.Answered(one.answer());
            };
            if (rewritten == null) {
                return Acceptance.STOPPED;
            }
            return switch (trial.change(body.answer(), rewritten)) {
                case CHANGED -> Acceptance.TAKEN;
                case SAME -> {
                    alike = true;
                    yield Acceptance.PASSED;
                }
                // A run that came back with no answer, or one that could not be read in full, is
                // not one the two were seen to answer alike on: it is one nothing was seen on. With
                // the figure that kept it untold, where one did.
                case COULD_NOT_TELL -> {
                    AnswerChange.Untold untold = AnswerChange.untold(body.answer(), rewritten);
                    stopped.merge(ReplacementDisposition.Ended.A_RUN_DID_NOT_COME_BACK,
                            ReplacementDisposition.Met.once(untold.figures(), untold.atNoFigure()),
                            ReplacementDisposition.Met::and);
                    yield Acceptance.PASSED;
                }
            };
        }

        /** The body run on {@code row}, once per line, or null where no run is left. */
        private ObservedRun run(GeneratedRow row) {
            return trial.run(row.toRun(), this::spend);
        }

        /**
         * What {@code row} answered run under {@code rewriting}, or null where the search stops
         * there: no run left, or a run that did not come back, each kept as the way it stopped.
         */
        private AnswerObservation ranUnder(GeneratedRow row, Rewriting rewriting) {
            Optional<AnswerObservation> answered =
                    trial.runReplacing(row.toRun(), rewriting, this::spend);
            if (answered == null) {
                stop(ReplacementDisposition.Ended.RUNS_A_REWRITE_MAY_TAKE, runsReached());
                return null;
            }
            if (answered.isEmpty()) {
                stop(ReplacementDisposition.Ended.A_RUN_DID_NOT_COME_BACK, List.of());
                return null;
            }
            return answered.get();
        }

        /** One more run of this search's own, where one is left. */
        private boolean spend() {
            if (runs >= mostRuns) {
                return false;
            }
            runs++;
            return true;
        }

        /** This stopping the search, why, and the figures it was stopped at. */
        private Acceptance stop(ReplacementDisposition.Ended why,
                                Collection<? extends Figure> at) {
            ended(why, at);
            stops++;
            return Acceptance.STOPPED;
        }

        /** The figure this was compared against when it had no run left, as it stood here. */
        private List<Figure> runsReached() {
            return List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(mostRuns));
        }

        /**
         * One way the search ended, and the figures it was stopped at there: none where nothing it
         * was compared against stopped it, which is met beside whatever figures another stop of the
         * same way was met at, and not lost among them.
         */
        private void ended(ReplacementDisposition.Ended why, Collection<? extends Figure> at) {
            stopped.merge(why, at.isEmpty() ? ReplacementDisposition.Met.AT_NO_FIGURE
                    : ReplacementDisposition.Met.at(at), ReplacementDisposition.Met::and);
        }

        /**
         * Composing the rows the search looked through stopped at {@code at}: the composing's own
         * budgets, and the bounds this class holds a search to, each as it stood where the search
         * was compared against it.
         */
        void composingStopped(Collection<? extends Figure> at) {
            if (at.isEmpty()) {
                throw new IllegalArgumentException("composing stopped at some figure, and says which");
            }
            ended(ReplacementDisposition.Ended.A_FIGURE_OF_THE_COMPOSING, at);
        }

        /**
         * The row a search over the readings of a combination took, or null.
         *
         * <p>This and the two below are where what a search for a row this asks about came to is
         * read, one for each shape a search comes back in, and the only places: whether composing
         * the rows it looked through stopped short at a figure of its own is read off what the
         * search found out, so whoever runs a search has nothing to decide about it. A search cut
         * short while this stopped it is this's to say, and is said ({@link #stop}); one that came
         * to nothing any other way leaves nothing to add, and what is said of it is what was seen
         * ({@link #ended}).
         */
        GeneratedRow tookFrom(Supplier<Witness> search) {
            int before = stops;
            Witness came = search.get();
            if (came instanceof Witness.Certified(GeneratedRow row, var _)) {
                return row;
            }
            switch (came) {
                // The walk over the readings stopped with readings it had not tried, at a bound of
                // its own or at the figures what it composed on the way met.
                case Witness.Limited limited -> {
                    List<Figure> at = new ArrayList<>(limited.boundsReached());
                    at.addAll(asFigures(limited.found().met().figures()));
                    // Cut short by a run nothing watched and by no figure: rows were composed and
                    // run, and nothing could say what they answered.
                    if (at.isEmpty() && limited.metARunNothingWatched() && stops == before) {
                        ended(ReplacementDisposition.Ended.NOTHING_RAN, List.of());
                    }
                    composingStoppedUnlessThisStoppedIt(before, at);
                }
                case Witness.Exhausted none -> composingStoppedUnlessThisStoppedIt(before,
                        asFigures(none.found().met().figures()));
                case Witness.Certified _, Witness.Unconfirmed _, Witness.NoCombination _ -> { }
            }
            return null;
        }

        /**
         * Composing stopped at every figure {@code met} holds, if it holds any.
         *
         * <p>The figures and no more of it, as at every place a search's composing is said to have
         * stopped here: what a rewrite's search ended at is a figure or something no figure decides
         * ({@link ReplacementDisposition.Met}), and what a shortfall holds besides its figures — a
         * population written in part, a number not held — is neither said nor asked for here. A
         * shortfall of those alone says nothing, and does not reach {@link #composingStopped}, which
         * is only ever told a figure.
         */
        void composingMet(CompositionShortfall met) {
            if (!met.figures().isEmpty()) {
                composingStopped(asFigures(met.figures()));
            }
        }

        /** Composing the rows the search looked through stopped at {@code figure}. */
        void composingStoppedAt(Figure figure) {
            composingStopped(List.of(figure));
        }

        /** The inputs of the row a composing took, or null ({@link #tookFrom}). */
        List<FixtureTemplate> tookFromComposing(Supplier<RowComposed> search) {
            int before = stops;
            RowComposed came = search.get();
            if (came instanceof RowComposed.Taken(List<FixtureTemplate> inputs)) {
                return inputs;
            }
            switch (came) {
                case RowComposed.PassedOver(SearchShortfall found) ->
                        composingStoppedUnlessThisStoppedIt(before,
                                asFigures(found.met().figures()));
                case RowComposed.Failed(Attempt why, OptionalInt _) ->
                        composingStoppedUnlessThisStoppedIt(before,
                                asFigures(why.found().met().figures()));
                // Stopped by what it handed its rows to: this, or the bound on how many it may be
                // handed ({@link #atMost}), which says so where it is reached.
                case RowComposed.Halted _, RowComposed.Taken _ -> { }
            }
            return null;
        }

        /** The row a search for a requirement took, or null ({@link #tookFrom}). */
        GeneratedRow tookFromSearching(Supplier<Searched> search) {
            int before = stops;
            Searched came = search.get();
            if (came.row() != null) {
                return came.row();
            }
            if (came.stoppedShort()) {
                List<Figure> at = new ArrayList<>(came.boundsReached());
                at.addAll(asFigures(came.came().met().figures()));
                composingStoppedUnlessThisStoppedIt(before, at);
            }
            return null;
        }

        /**
         * Composing stopped at {@code figures}, unless this stopped it.
         *
         * <p>None is no figure reached: a search cut short by nothing it was compared against —
         * a run nothing watched, which no run of this compiler watches more of — leaves nothing to
         * say here, and what it came to is what was seen.
         */
        private void composingStoppedUnlessThisStoppedIt(int before,
                                                         Collection<? extends Figure> figures) {
            if (stops == before && !figures.isEmpty()) {
                composingStopped(figures);
            }
        }

        /** The composing stage's budgets a search met, as the figures they are. */
        private static List<Figure> asFigures(Collection<CompositionBudget> budgets) {
            return budgets.stream().map(CompositionBudget::figure).toList();
        }

        /** How the search ended, where nothing was found: each way it stopped as it was met, and
         *  whether rows were seen answered alike. */
        Map<ReplacementDisposition.Ended, ReplacementDisposition.Met> ended() {
            Map<ReplacementDisposition.Ended, ReplacementDisposition.Met> out =
                    new EnumMap<>(ReplacementDisposition.Ended.class);
            out.putAll(stopped);
            if (alike) {
                out.put(ReplacementDisposition.Ended.EVERY_ROW_ANSWERED_ALIKE,
                        ReplacementDisposition.Met.AT_NO_FIGURE);
            }
            if (out.isEmpty()) {
                out.put(ReplacementDisposition.Ended.NOTHING_WAS_COMPOSED,
                        ReplacementDisposition.Met.AT_NO_FIGURE);
            }
            return out;
        }
    }

    /**
     * How many rows meeting one requirement {@link TellingArmsApart} ranks before the best of them
     * is taken.
     *
     * <p>Counted in rows that meet the requirement, each once, and not in rows composed: a row that
     * does not meet it is no candidate, and how many of those a walk composes on the way is the
     * walk's to bound. Counted in rows and not in runs: each row ranked is run once and once more
     * per rewrite of the arms it went through, which the requirement reads and this does not
     * choose. Its own figure, and not the one a search for a rewrite runs under
     * ({@link RewriteSearch}): that one bounds the search that decides whether a rewrite is a gap,
     * and this bounds a choice among rows that all meet what they were composed for, which decides
     * nothing.
     */
    static final int MOST_ROWS_OFFERED_FOR_THE_ARMS = 4;

    /**
     * Which of the rows a search composed for one requirement is handed a person: the first that
     * every rewrite of the arms it goes through answers differently on, or, where none is offered
     * before the figure, the one the most of them answered differently on, the earliest of those.
     *
     * <p>Over whatever says a row meets the requirement ({@link #over}), and never in place of it.
     * The first row that check takes and whose run answers is kept whatever the rewrites say, so a
     * requirement whose arms answer alike on every row is still one a row is handed out for. What the rewrites came to on
     * the row taken is not kept either: a row composed here is a question put to a person, and
     * whether its answer tells a rewrite apart is read off the answer they write
     * ({@link ReplacementOwed}).
     *
     * <p>Among rows that go one way. A row reaching other arms, or a condition coming out the other
     * way, is a row the other measures read differently, and choosing it for its rewrites would be
     * choosing what those measures see as well. Which is also why a row composed for a combination
     * of arms, or for getting past a guard, stays one: the same arms lit, and the same conditions,
     * are the same combination and the same guard passed. A row whose run answered nothing is one
     * the compiler refuses, and is never taken, the first included; where nothing can run a row,
     * the first is taken as it is composed.
     *
     * <p>Which rewrites are asked of a row is what its run went through, and not what the row was
     * composed for. A line and an arm are not one to one — a comparison may decide no fork, or
     * several — so the arms are read off the run. And they are the rewrites the measure asks of such
     * a row and no others ({@link Trial#rewritesThrough}): one it does not ask, or one no run can
     * be, is not a question the row's answer will be read for.
     *
     * <p>A run that comes back with nothing to read, or a rewrite whose run cannot be told from the
     * body's, tells nothing apart.
     */
    static final class TellingArmsApart implements RowPreference {

        /** What bounds the rows a walk hands the choice, whatever they come to. */
        private static final CompositionBudget HANDED_THE_CHOICE =
                CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW;
        private static final int MOST_ROWS_HANDED = HANDED_THE_CHOICE.maximum();

        private final RunOnce trial;
        private final List<StoodInAnswer> answers;
        /** Every row ranked so far, as it is written, so a row composed again is not ranked again. */
        private final Set<List<String>> ranked = new HashSet<>();
        /** Where the first row ranked went: the arms it passed and how its conditions came out. */
        private AlignedObservation way;
        /** The rewrites of the arms and the walks on that way, which every row compared is asked. */
        private List<RunRewrite> rewrites = List.of();
        /** The row taken so far, and how many rewrites were told apart on it. */
        private List<FixtureTemplate> best;
        private int bestTold = -1;
        /** How many rows that met the requirement were run and came to an answer. */
        private int answering;
        /** Whether a row that met the requirement was run and went past what a run may spend. */
        private boolean aRunRanOut;
        /** Whether the walk was stopped for handing more rows than it may. */
        private boolean stoppedAtItsFigure;
        /** How many rows a walk has handed here, ranked or not. */
        private int handed;

        /** What a row's run is also held to, or null where it is held to nothing. */
        private final RowJudge judge;
        /** The first row whose run answered and the judge refused, offered where the walk reaches
         *  no row it accepts. */
        private List<FixtureTemplate> refused;

        TellingArmsApart(Trial trial, List<StoodInAnswer> answers) {
            this(trial, answers, null);
        }

        /**
         * Ranking the rows {@code judge} accepts. A row it refuses is no candidate: it ranks no
         * further and moves nothing the ranking keeps, and the walk goes on to the next row. Where
         * it accepts none, the first row refused whose run answered is the row taken: not ranked
         * against the others, since what it is taken for is to say where its run went.
         */
        TellingArmsApart(Trial trial, List<StoodInAnswer> answers, RowJudge judge) {
            this.trial = runningOnce(trial);
            this.answers = List.copyOf(answers);
            this.judge = judge;
        }

        /**
         * Every row a walk composes, ranked here once {@code meets} takes it as one that meets the
         * requirement; passed over, or stopped on, where {@code meets} says so, and passed over
         * where it was ranked already.
         *
         * <p>Two figures, each of its own thing. What is ranked is bounded by
         * {@link #MOST_ROWS_OFFERED_FOR_THE_ARMS}; and the rows a walk hands here at all — ranked,
         * not meeting the requirement, or composed again — by
         * {@link CompositionBudget#ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW}. A walk over every
         * assignment of every parameter multiplies, and the rows it hands on that are no
         * candidates cost composing each time even though they cost no run.
         */
        @Override
        public RowTaking over(RowTaking meets) {
            return inputs -> {
                if (++handed > MOST_ROWS_HANDED) {
                    stoppedAtItsFigure = true;
                    return Acceptance.STOPPED;
                }
                RowToRun row = new RowToRun(inputs, answers);
                List<String> written = RunOnce.writtenAs(row);
                if (ranked.contains(written)) {
                    return Acceptance.PASSED;
                }
                Acceptance met = meets.take(inputs);
                return met == Acceptance.TAKEN ? rank(row, written) : met;
            };
        }

        /**
         * The row taken, or null where nothing offered met the requirement.
         *
         * <p>Where the judge refused every row the walk reached, the first of them — unless the
         * walk was stopped at its figure. Stopped, the rows past the figure are rows nobody looked
         * at, and a row refused is no answer to whether one of them is accepted: nothing is taken,
         * and the figure is what is told ({@link #untried}).
         */
        @Override
        public List<FixtureTemplate> taken() {
            return best != null ? best : stoppedAtItsFigure ? null : refused;
        }

        @Override
        public boolean takenIsRefused() {
            return best == null && !stoppedAtItsFigure && refused != null;
        }

        /** Whether a run of a row that met the requirement went past what a run may spend. */
        @Override
        public boolean aRunRanOut() {
            return aRunRanOut;
        }

        /**
         * Whether the walk handed more rows than {@link #HANDED_THE_CHOICE} allows and was
         * stopped, which leaves the rows past it untried.
         */
        boolean stoppedAtItsFigure() {
            return stoppedAtItsFigure;
        }

        /** The rows left untried: the figure where the walk was stopped at it, otherwise none. */
        @Override
        public SearchShortfall untried() {
            return stoppedAtItsFigure
                    ? SearchShortfall.of(CompositionShortfall.of(List.of(HANDED_THE_CHOICE)))
                    : SearchShortfall.NONE;
        }

        /** What is made of one row that meets the requirement, not ranked before. */
        private Acceptance rank(RowToRun row, List<String> written) {
            List<FixtureTemplate> inputs = row.inputs();
            ranked.add(written);
            ObservedRun ran = trial.runsRows() ? trial.run(row) : ObservedRun.nothingRan();
            // Where nothing ran the row, nothing says whether it answers; the first row is offered
            // as it is composed.
            if (ran.watched() instanceof Watched.NotRun) {
                if (best == null) {
                    best = List.copyOf(inputs);
                }
                return Acceptance.TAKEN;
            }
            // A row is a candidate only where its run answered: what it was composed to read back
            // says what the run comes to where it answers, and nothing of whether it does.
            if (!(ran.answer() instanceof AnswerObservation.Answered)) {
                aRunRanOut |= ran.answer() instanceof AnswerObservation.RanOut;
                return Acceptance.PASSED;
            }
            // A row the judge refuses is none of the rows ranked: the figure on those is a figure
            // on the candidates, and what bounds the rows refused is the rows a walk is handed.
            if (judge != null && !judge.accepts(row)) {
                if (refused == null) {
                    refused = List.copyOf(inputs);
                }
                return Acceptance.PASSED;
            }
            answering++;
            if (best == null) {
                best = List.copyOf(inputs);
                // The first row with nothing to say which arms it went through is a requirement
                // nothing here can tell rows apart at, and it is the row.
                if (!(ran.watched() instanceof Watched.Ran(AlignedObservation seen))) {
                    return Acceptance.TAKEN;
                }
                way = seen;
                rewrites = trial.rewritesThrough(seen);
            } else if (!(ran.watched() instanceof Watched.Ran(AlignedObservation seen))
                    || !seen.wentTheWayOf(way)) {
                // Only a row that goes the way the first one did, through the same arms with every
                // condition coming out the same.
                return onward();
            }
            // One way is one set of arms, so every row offered here is asked the same rewrites, and
            // a row after the first is taken over it only by telling more of them apart. Where the
            // rewrites left could not bring it past the row kept, they are not run.
            int told = 0;
            for (int i = 0; i < rewrites.size() && told + rewrites.size() - i > bestTold; i++) {
                Optional<AnswerObservation> now =
                        trial.runReplacing(row, rewrites.get(i).asked());
                if (now.isPresent()
                        && trial.change(ran.answer(), now.get()) == AnswerChange.CHANGED) {
                    told++;
                }
            }
            if (told > bestTold) {
                best = List.copyOf(inputs);
                bestTold = told;
            }
            return told == rewrites.size() ? Acceptance.TAKEN : onward();
        }

        /** The walk going on to the next row, or stopping where the figure is reached. */
        private Acceptance onward() {
            return answering < MOST_ROWS_OFFERED_FOR_THE_ARMS ? Acceptance.PASSED
                    : Acceptance.STOPPED;
        }
    }

    /**
     * What a row is held to besides the way it was composed for, decided by running it.
     *
     * <p>A function of the row alone, so the walk that composes can ask it of every row it hands
     * on. What the answer rests on — which rule the run was placed at, which case it was evidence
     * of — is the caller's: the way states what a row has to be at the places it names, and this
     * is for what only a run says.
     */
    @FunctionalInterface
    public interface RowJudge {

        /** Whether the run of {@code row} is what was looked for. */
        boolean accepts(RowToRun row);

        /**
         * Whether a row this refuses is never offered. Where it is not, a row it refuses is the
         * one offered only when the walk reaches no row it accepts, so that what the refused row
         * did can still be told.
         */
        default boolean refusesAbsolutely() {
            return true;
        }

        /**
         * {@code judge}, as a preference: the rows it accepts are the ones offered, ranked as rows
         * are, and where the walk reaches none, the first row whose run answered is offered in
         * their place, so that what that run did can still be told.
         */
        static RowJudge preferring(RowJudge judge) {
            return new RowJudge() {
                @Override
                public boolean accepts(RowToRun row) {
                    return judge.accepts(row);
                }

                @Override
                public boolean refusesAbsolutely() {
                    return false;
                }
            };
        }
    }

    /**
     * Which of the rows a walk composes for one way is taken, kept across the rows the walk hands
     * on, and what it left untried.
     */
    interface RowPreference {

        /** What the walk makes of each whole row, {@code meets} being what a row has to meet at
         *  all. */
        RowTaking over(RowTaking meets);

        /** The row taken, or null where nothing offered was. */
        List<FixtureTemplate> taken();

        /**
         * Whether the row taken is one a judge refused, offered because the walk reached none it
         * accepts ({@link RowJudge#preferring}).
         */
        default boolean takenIsRefused() {
            return false;
        }

        /** The rows left untried: the figure where the walk was stopped at it, otherwise none. */
        SearchShortfall untried();

        /** Whether a run of a row went past what a run may spend. */
        boolean aRunRanOut();
    }

    /**
     * The first row a walk composes that {@link RowJudge} accepts.
     *
     * <p>Each row once, and a row passed over sends the walk on to its next assignment, so the
     * rows tried are the rows the walk reaches, nearest first, within the figure it may hand rows
     * the choice at ({@link CompositionBudget#ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW}). A row the
     * walk is stopped before is untried and is said so ({@link #untried}): not finding one within
     * that is this compiler having looked, and says nothing of whether a row can be.
     */
    static final class ReachingWhatIsJudged implements RowPreference {

        private static final CompositionBudget HANDED_THE_CHOICE =
                CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW;
        private static final int MOST_ROWS_HANDED = HANDED_THE_CHOICE.maximum();

        private final RowJudge judge;
        private final List<StoodInAnswer> answers;
        /** Every row judged so far, as it is written, so a row composed again is not run again. */
        private final Set<List<String>> judged = new HashSet<>();
        private List<FixtureTemplate> taken;
        private boolean stoppedAtItsFigure;
        /** How many rows the walk has handed here, judged or not. */
        private int handed;

        ReachingWhatIsJudged(RowJudge judge, List<StoodInAnswer> answers) {
            this.judge = judge;
            this.answers = List.copyOf(answers);
        }

        @Override
        public RowTaking over(RowTaking meets) {
            return inputs -> {
                if (++handed > MOST_ROWS_HANDED) {
                    stoppedAtItsFigure = true;
                    return Acceptance.STOPPED;
                }
                RowToRun row = new RowToRun(inputs, answers);
                if (!judged.add(RunOnce.writtenAs(row))) {
                    return Acceptance.PASSED;
                }
                Acceptance met = meets.take(inputs);
                if (met != Acceptance.TAKEN) {
                    return met;
                }
                if (judge.accepts(row)) {
                    taken = List.copyOf(inputs);
                    return Acceptance.TAKEN;
                }
                return Acceptance.PASSED;
            };
        }

        @Override
        public List<FixtureTemplate> taken() {
            return taken;
        }

        @Override
        public SearchShortfall untried() {
            return stoppedAtItsFigure
                    ? SearchShortfall.of(CompositionShortfall.of(List.of(HANDED_THE_CHOICE)))
                    : SearchShortfall.NONE;
        }

        @Override
        public boolean aRunRanOut() {
            return false;
        }
    }

    /**
     * The row handed out for a requirement {@code first} already meets: {@code first}, or another
     * row composed at {@code where} under {@code given} that {@code meets} takes and that tells
     * more of its arms' rewrites apart ({@link TellingArmsApart}).
     *
     * <p>After the search and not inside it. What a search holds a row to may cost runs of its own
     * budget, and what the row it settled on is held to here is the same requirement read off the
     * way it went — so the search's account of what it looked at and spent is the search's, and
     * this changes only which of the rows meeting it goes out.
     *
     * <p>The walk over the candidate's values composes rows that do not meet the requirement as
     * well; where it reaches what the preference lets a walk hand it ({@link TellingArmsApart#over})
     * it stops with the rows it ranked. Nothing is owed for that — every row ranked meets the
     * requirement, and the first of them is the one the search settled on.
     */
    private static List<FixtureTemplate> tellingArmsApart(
            MeasuredInput.MeasuredAxes axes, int[] where, CandidateCheck check,
            Map<String, Written> given, Trial trial, List<StoodInAnswer> answers,
            List<FixtureTemplate> first, RowTaking meets) {
        TellingArmsApart preferring = new TellingArmsApart(trial, answers);
        RowTaking taking = preferring.over(meets);
        if (taking.take(first) == Acceptance.TAKEN) {
            return first;
        }
        composed(axes, where, HeldTogether.Asked.NOTHING, check, given, taking);
        List<FixtureTemplate> kept = preferring.taken();
        return kept == null ? first : kept;
    }

    /**
     * What a row a search has seen doing what it was looked for has to be besides, asked of the row
     * and of what its run came to — which a caller asking about the answer has to have and which
     * the search already ran for.
     */
    @FunctionalInterface
    private interface Furthermore {
        Acceptance of(GeneratedRow row, ObservedRun ran);
    }

    private static Witness witnessing(Reading reading) {
        Traversal walked = reading.selection.interpretations(reading);
        return walked == Traversal.SATISFIED ? reading.found : reading.nothing(walked);
    }

    /**
     * Looking for a row at one combination, over the readings of what it asks.
     *
     * <p>What the combination can be asking is the combination's to enumerate and how many of them
     * this may look at is this search's to bound, which are two things and were one. Counted off by
     * the enumeration, the bound was spent on combinations of names before anything asked whether a
     * value could hold them — so a combination whose first few names cannot be in one value went
     * unanswered with its readings untried.
     *
     * <p>So a reading no value can hold costs nothing here: it is not a reading. What is counted is
     * the readings this actually searched, and the bound is refused in front of the one after them
     * — which is a reading that exists and that nobody looked at, and the only thing that makes this
     * search incomplete.
     */
    private static final class Reading implements Taking<Interpretation> {

        private final MeasuredInput.MeasuredAxes axes;

        private final CellSelection selection;

        private final CandidateCheck check;

        private final RunOnce trial;

        /** What the row this composes is composed for. */
        private final List<Purpose> composedFor;

        /**
         * What a row seen filling the combination has to be besides, or null where filling it is
         * all that is asked. Where there is one, each candidate's values are chosen again until a
         * row that fills the combination is also this, since what it asks of a row is not something
         * which assignment the row stands at decides.
         */
        private final Furthermore furthermore;

        private final List<ResolvedOrigin> origins;

        /** Whether the combination offered anything at all, which tells a combination the model
         *  does not have from one whose readings are none of them one value. */
        private boolean offered;

        /** How many readings were searched, which is what this is allowed so many of. */
        private int searched;

        /** The bounds of this search's own it was compared against and stopped at, each as it
         *  stood there: the readings it may search, and the runs one reading is given. */
        private final Set<Figure> boundsReached = new HashSet<>();

        /** Whether a candidate ran and nothing could say what it did, which stops the search at no
         *  figure. */
        private boolean metARunNothingWatched;

        /** What the last candidate that composed nothing came to, for a search that tried them
         *  all. */
        private Attempt last;

        /**
         * What every candidate of every reading found out, beside the last one's word.
         *
         * <p>The same reason the walk over the classes keeps one. A figure, or an offer short of a
         * rule, is what this search ran into and stays true of it after the candidate that met it
         * is replaced, so it is added up over the readings rather than read off whichever candidate
         * came last.
         */
        private SearchShortfall foundOut = SearchShortfall.NONE;

        /** Where the last candidate stood, which is what names the combination in a report. */
        private int[] where;

        /** Whether a row was composed, run, and seen going somewhere else. */
        private boolean missed;

        private Completeness looked = Completeness.NOTHING_YET;

        /** The row, once one is seen filling the combination or offered because nothing watched
         *  it. */
        private Witness found;

        private Reading(MeasuredInput.MeasuredAxes axes, CellSelection selection,
                        CandidateCheck check, RunOnce trial,
                        List<Purpose> composedFor,
                        Furthermore furthermore,
                        List<ResolvedOrigin> origins,
                        FixtureReferences references, List<StoodInAnswer> answers) {
            this.axes = axes;
            this.requires = new WhatEachClassRequires(axes.axes());
            this.selection = selection;
            this.check = check;
            this.trial = trial;
            this.composedFor = composedFor;
            this.furthermore = furthermore;
            this.origins = origins;
            this.references = references;
            this.answers = answers;
        }

        /** What each class of this combination's positions requires, read once for every reading
         *  of it. */
        private final WhatEachClassRequires requires;

        /** The run's minter for the references what this composes will hold. */
        private final FixtureReferences references;

        /** What every row of this behavior stands its dependencies in with, which is the
         *  environment the candidate is run in and the one it goes out with. */
        private final List<StoodInAnswer> answers;

        @Override
        public Taken take(Interpretation reading) {
            offered = true;
            int[] about = about(axes.axes(), reading);
            // Whether one value can hold what this reading asks, which is the model's answer and not
            // the combination's. Asked of the classes it pins alone: what they require is required
            // whichever value the row is written against, so this does not change with the origin.
            if (standing(requires, wanting(axes.axes(), null, reading), about,
                    selection.cell()::admits)
                    == null) {
                // not a reading, and so no part of what this search is allowed
                return Taken.AND_MORE;
            }
            if (searched >= MOST_INTERPRETATIONS) {
                boundsReached.add(
                        WorkFigure.READINGS_OF_A_COMBINATION_TRIED.at(MOST_INTERPRETATIONS));
                return Taken.NOT_TAKEN;   // a reading of this combination that nobody looked at
            }
            searched++;
            // The values the model states first, nearest first, and what they may spend counted in
            // runs. Then the composition, whatever they spent: it is not one of them and was not
            // competing with them for their share, and a caller told the stated values were all
            // refused would go looking for a value the model cannot hold.
            Traversal walked = nearestFirst(requires, reading, origins, selection.cell()::admits,
                    new Running(MOST_RUNS_PER_INTERPRETATION));
            if (walked == Traversal.SATISFIED) {
                return Taken.AND_DONE;
            }
            Traversal composed = composing(requires, reading, origins, selection.cell()::admits,
                    new Running(MOST_RUNS_PER_INTERPRETATION));
            if (composed == Traversal.SATISFIED) {
                return Taken.AND_DONE;
            }
            looked = walked == Traversal.STOPPED || composed == Traversal.STOPPED
                    ? looked.cutShort() : looked.searched();
            return Taken.AND_MORE;
        }

        /** What to say when no reading answered. */
        private Witness nothing(Traversal walked) {
            if (walked == Traversal.STOPPED) {
                looked = looked.cutShort();
            }
            List<String> named =
                    where == null ? List.of() : labels(axes.axes(), selection.cell(), where);
            return switch (looked.found()) {
                // No reading to look at. Either the combination offered nothing, or none of what it
                // offered is one value — and both are the model not having this combination rather
                // than a search that failed at it.
                case Completeness.Nothing.NO_READING -> new Witness.NoCombination(offered
                        ? "the positions this combination names are not in one value"
                        : "a position this combination names has nothing left at it");
                // Something was left undone: a reading nobody looked at, or a candidate nobody ran.
                // Said as that whatever the ones that were tried came to — the miss of the third of
                // them is a fact about that candidate, and offered as the combination's answer it
                // stands for a space this never entered.
                case Completeness.Nothing.SEARCH_STOPPED ->
                        new Witness.Limited(named, foundOut, Figure.inOrder(boundsReached),
                                metARunNothingWatched);
                // Every one of these carries what every candidate found out and not what the
                // candidate whose word is said found out. Rows that went somewhere else are not
                // every row the readings had where an offer was short of a rule, and the rule is
                // said beside the word for a reader to rewrite.
                case Completeness.Nothing.LOOKED_EVERYWHERE -> {
                    if (missed) {
                        // Rows were composed and run, and went somewhere else. Which says they were
                        // not witnesses, and not that the combination is unreachable.
                        yield new Witness.Exhausted(named,
                                UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS, null,
                                Optional.empty(), foundOut);
                    }
                    if (last != null && last.row() == null) {
                        yield new Witness.Exhausted(named, last.reason(), last.detail(),
                                last.said(), foundOut);
                    }
                    // Nothing was composed and nothing was refused, which takes every reading
                    // leaving no assignment at all. Named rather than guessed at, the same way
                    // every other empty result here is.
                    yield new Witness.Exhausted(named,
                            UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED, null,
                            Optional.empty(), foundOut);
                }
            };
        }

        /**
         * Running the candidates offered for one reading, up to what that reading may cost.
         *
         * <p>Counted in runs, because a run is what this is protecting. Reaching the arm is what a
         * row for a combination has to do and only the behavior can say whether it did — so a
         * candidate the model refuses costs nothing, and neither does one whose values a run was
         * already watched at. Counted per candidate instead, a model whose rules refuse a few
         * compositions spent a reading's whole share without asking the behavior anything, and a
         * reading whose remaining candidates were all values something had already run came back
         * saying the search had stopped.
         *
         * <p>So the bound is refused in front of a candidate that needs a run there is none left
         * for. That candidate is the run nobody did, and it is the only thing here that leaves this
         * reading incomplete.
         */
        private final class Running implements TakingCandidates {

            private final int most;

            private int runs;

            /** What this has seen come of one parameter's value, which the walk leaves out. */
            private final ParameterProjections known = new ParameterProjections(axes);

            private Running(int most) {
                this.most = most;
            }

            @Override
            public void reached(Figure figure) {
                boundsReached.add(figure);
            }

            @Override
            public ParameterProjections known() {
                return known;
            }

            @Override
            public Taken take(Candidate candidate) {
                Map<String, Written> given = candidate.from().writtenAgainst(axes,
                        candidate.delta(), candidate.where(), references);
                known.written(candidate, given);
                if (!candidate.from().composes() && given.isEmpty()) {
                    // nothing here can be written against the model's value
                    return Taken.AND_MORE;
                }
                where = candidate.where();
                if (furthermore != null) {
                    return rechoosing(candidate, given);
                }
                last = build(axes, candidate.where(), HeldTogether.Asked.NOTHING, check, given,
                        answers);
                known.built(candidate, last);
                foundOut = foundOut.and(last.found());
                if (last.row() == null) {
                    // nothing composed here; another assignment may compose
                    return Taken.AND_MORE;
                }
                GeneratedRow named = new GeneratedRow(composedFor, last.row().inputs(),
                        last.row().answers());
                ObservedRun observed = ranAs(named);
                if (observed == null) {
                    return Taken.NOT_TAKEN;   // this candidate is the run nobody did
                }
                switch (observed.watched()) {
                    // Nothing can say where it went, so nothing certifies it and nothing refutes
                    // it. Offered as it was before anything ran, and said to be. Both of the ways
                    // that happens come here: nothing applied the row, or nothing was recording
                    // while it was applied and it answered.
                    case Watched.NotRun _ -> {
                        found = new Witness.Unconfirmed(named, candidate.where());
                        return Taken.AND_DONE;
                    }
                    case Watched.NoAccount _ -> {
                        // Applied and not recorded, so a run that did not answer is as much no
                        // witness here as where it was recorded.
                        if (!(observed.answer() instanceof AnswerObservation.Answered)) {
                            missed = true;
                            return Taken.AND_MORE;
                        }
                        found = new Witness.Unconfirmed(named, candidate.where());
                        return Taken.AND_DONE;
                    }
                    case Watched.Ran ran -> {
                        // A run that did not answer is no witness, wherever it went before it
                        // stopped: a row that aborts is one the compiler refuses — at an
                        // `unreachable` it is E1911 — and what it lit, it lit on the way to nothing.
                        // Nor is one that went past what a run may spend, which given more might
                        // have answered and has not.
                        if (!(observed.answer() instanceof AnswerObservation.Answered)) {
                            missed = true;
                            return Taken.AND_MORE;
                        }
                        // Through the one thing that can say a row filled a combination, which is
                        // the same thing a row already in the file is put through.
                        Optional<CellSelection.CertifiedWitness> seen =
                                selection.certifying(candidate.where(), ran.seen());
                        if (seen.isPresent()) {
                            // The row that goes out is the one filling the combination, the way
                            // it went — which is the same combination filled, and so the same
                            // certificate — that tells the most of its arms' rewrites apart.
                            List<FixtureTemplate> told = tellingArmsApart(axes, candidate.where(),
                                    check, given, trial, answers, named.inputs(), RowTaking.FIRST);
                            found = new Witness.Certified(told.equals(named.inputs()) ? named
                                    : new GeneratedRow(composedFor, told, named.answers()),
                                    seen.get());
                            return Taken.AND_DONE;
                        }
                        missed = true;
                    }
                }
                return Taken.AND_MORE;
            }

            /**
             * What running {@code named} came to, run once per line however many places a row of
             * it was looked for; or null where it has not been run and this reading has no run
             * left.
             *
             * <p>What a run of one row did is one fact: two arms searched on their own can come to
             * the same line, and running them again would be the same row applied twice and counted
             * twice ({@link RunOnce}).
             */
            private ObservedRun ranAs(GeneratedRow named) {
                return trial.run(named.toRun(), () -> {
                    if (runs >= most) {
                        boundsReached.add(WorkFigure.RUNS_FOR_ONE_READING.at(most));
                        return false;
                    }
                    runs++;
                    return true;
                });
            }

            /**
             * One candidate, its values chosen again until a row seen filling the combination is
             * also what {@link #furthermore} asks.
             *
             * <p>Seen filling it first, because that is what being looked for here means; and a
             * row nothing watched cannot be, so it is no answer to a search that needs a run to say
             * anything. What the walk over the values runs out on is said as what it is: the
             * values composed and passed over, or a run there was none left for, or the values
             * refused.
             */
            private Taken rechoosing(Candidate candidate, Map<String, Written> given) {
                RowComposed came = composed(axes, candidate.where(), HeldTogether.Asked.NOTHING,
                        check, given, inputs -> {
                            GeneratedRow named = new GeneratedRow(composedFor, inputs, answers);
                            ObservedRun observed = ranAs(named);
                            if (observed == null) {
                                return Acceptance.STOPPED;
                            }
                            if (!(observed.watched() instanceof Watched.Ran ran)) {
                                metARunNothingWatched = true;
                                return Acceptance.STOPPED;
                            }
                            // No witness, for the reason one built at once is none.
                            if (!(observed.answer() instanceof AnswerObservation.Answered)) {
                                missed = true;
                                return Acceptance.PASSED;
                            }
                            Optional<CellSelection.CertifiedWitness> seen =
                                    selection.certifying(candidate.where(), ran.seen());
                            if (seen.isEmpty()) {
                                missed = true;
                                return Acceptance.PASSED;
                            }
                            Acceptance asked = furthermore.of(named, observed);
                            if (asked == Acceptance.TAKEN) {
                                found = new Witness.Certified(named, seen.get());
                            }
                            return asked;
                        });
                return switch (came) {
                    case RowComposed.Taken _ -> Taken.AND_DONE;
                    // Not a refusal, and what the walk found out on the way to the rows passed over
                    // is found out all the same: a figure it stopped at, or an offer a way beside
                    // them was short of, is a row the search may yet have.
                    case RowComposed.PassedOver(SearchShortfall its) -> {
                        foundOut = foundOut.and(its);
                        yield Taken.AND_MORE;
                    }
                    case RowComposed.Halted _ -> Taken.NOT_TAKEN;
                    case RowComposed.Failed(Attempt why, var _) -> {
                        last = why;
                        known.built(candidate, why);
                        foundOut = foundOut.and(why.found());
                        yield Taken.AND_MORE;
                    }
                };
            }
        }
    }

    /** The positions one reading is about, in the axes' own order. Asked of the axes rather than
     *  walked off {@code reading}: what {@link Interpretation#pins} answers is what is bound to a
     *  position, not which positions there are, and asking each in turn is what puts this in the
     *  axes' order without a sort standing in for one. */
    private static int[] about(List<Axis> axes, Interpretation reading) {
        int[] found = new int[axes.size()];
        int n = 0;
        for (int i = 0; i < axes.size(); i++) {
            if (reading.pins().containsKey(i)) {
                found[n++] = i;
            }
        }
        return Arrays.copyOf(found, n);
    }




    // --- turning classes into a row -------------------------------------------------------------

    /**
     * What building one assignment came to.
     *
     * @param found   what the search found out beside its word, whole ({@link SearchShortfall})
     * @param localTo the parameter whose value this came to nothing at, where it came to nothing at
     *                one parameter alone. A parameter is built from what stands under it and
     *                nothing else ({@link #valueFor}), so what came of it is a fact about that
     *                parameter's classes — whether the model refused the value or the search for
     *                it stopped. One said of the row as a whole is not, and has none
     */
    private record Attempt(GeneratedRow row, UnresolvedCombination.Reason reason, String detail,
                           Optional<String> said, SearchShortfall found, OptionalInt localTo) {

        Attempt(GeneratedRow row, UnresolvedCombination.Reason reason, String detail,
                Optional<String> said, SearchShortfall found) {
            this(row, reason, detail, said, found, OptionalInt.empty());
        }

        Attempt(GeneratedRow row, UnresolvedCombination.Reason reason, String detail,
                Optional<String> said) {
            this(row, reason, detail, said, SearchShortfall.NONE);
        }

        /** The same, said to have come to nothing at {@code parameter} alone. */
        Attempt localTo(int parameter) {
            return new Attempt(row, reason, detail, said, found, OptionalInt.of(parameter));
        }

        static Attempt of(GeneratedRow row) {
            return new Attempt(row, null, null, Optional.empty());
        }

        /**
         * One that came to nothing having found out something beside its word on the way.
         *
         * <p>What it found out travels beside the word rather than being read for one and dropped.
         * The word says the question is open; only this says whether a number somebody raises, or
         * a rule somebody rewrites, reaches it — which is the whole of what tells a figure from
         * work nobody has done.
         *
         * <p>{@code said} is what the search said of itself, so it goes where a reader is told
         * which case of the word this was, and the combination stays what the attempt is about.
         */
        static Attempt no(UnresolvedCombination.Reason reason, String said,
                          SearchShortfall found) {
            return new Attempt(null, reason, null, Optional.ofNullable(said), found);
        }

        /**
         * One whose search came to {@code came} having found out {@code found} about its own
         * candidates, in the word for all of it and with what is to be told beside it
         * ({@link SearchShortfall#wordFor}, {@link SearchShortfall#toldFor}).
         *
         * <p>The word is settled here, where the attempt is made, because the walk over
         * alternatives reads it to decide what is a proof: a search whose candidates were not
         * all refused by the model, said in the word it came to, would be read as one that was.
         */
        static Attempt over(UnresolvedCombination.Reason came, String detail,
                            Optional<String> told, SearchShortfall found) {
            return new Attempt(null, found.wordFor(came), detail, found.toldFor(came, told),
                    found);
        }
    }

    /**
     * What the comparisons a row is held to ask of it, put together, or why they cannot be.
     *
     * <p>Two answers, because a row held to two comparisons is held to both at once and they may
     * not meet: the same number asked to stand at two places, a position asked to be two cases, or
     * a way the rules leave nothing on. Any of those is a row this assignment cannot be, which is
     * what a candidate that composes nothing says.
     */
    private sealed interface HeldTogether {

        /**
         * Everything the comparisons ask, in the vocabulary a row is composed in.
         *
         * @param asked    each number a comparison asks a term to stand at, and every number the
         *                 rules leave it beside that one — the comparisons' own terms and the
         *                 positions the way to them bounds
         * @param standing where each of those numbers was chosen to stand, which a candidate is
         *                 held to as it is built
         * @param required the cases the way to the comparisons takes the row through
         * @param reaching what the way to the last of them leaves the row, which the ways to the
         *                 ones before it are part of
         * @param contents what the way and the conditions held ask containers to hold that no
         *                 number places
         * @param someElement the numbers some element of a container is to stand at, which they
         *                    are grouped by where the row is composed as where they were placed
         * @param composed what composing each location a condition placed numbers at came to,
         *                 for the request it answers ({@link Standing#composed})
         * @param bounds   what the conditions on the way ask every element of a container to meet,
         *                 which a container written here is composed under ({@link Standing#bounds})
         */
        record Asked(SequencedMap<RealizationTarget, AskedAt> asked,
                     Map<RealizationTarget, Place> standing, Requirements required,
                     Reachability.Reaching reaching, ContentsAsked contents,
                     Set<RealizationTarget> someElement, Map<TermPath, ComposedAt> composed,
                     List<ElementBound> bounds)
                implements HeldTogether {

            /** Nothing held: the row is what its classes are. */
            static final Asked NOTHING = new Asked(new LinkedHashMap<>(), Map.of(),
                    Requirements.NONE, null, ContentsAsked.NONE, Set.of(), Map.of(), List.of());
        }

        record Refused(Attempt why) implements HeldTogether {}
    }

    /**
     * What the parts of one way past a guard come to together, where the way is all of them at
     * once ({@link #partsHeld}).
     *
     * @param noRowGoes whether some part is one no row goes, which settles the way whatever the
     *                  others say
     * @param why       every reason a part cannot be held: nothing found for it, or every way of
     *                  holding it would write a stated value afresh
     * @param unlooked  every figure that left a part's ways unlooked at before one was kept
     * @param parts     the ways each part can be held along, where none of the above stands in
     *                  the way
     * @param cutShort  every figure that left out some way of holding a part that is held
     */
    record PartsHeld(boolean noRowGoes, Set<RepairShortfall.Barrier> why,
                     Set<CompositionBudget> unlooked, List<List<HeldOutcome>> parts,
                     Set<CompositionBudget> cutShort) {

        PartsHeld {
            why = InDeclaredOrder.of(why);
            unlooked = InDeclaredOrder.of(unlooked);
            parts = parts.stream().map(List::copyOf).toList();
            cutShort = InDeclaredOrder.of(cutShort);
        }
    }

    /**
     * The parts of one way, {@code each} what brings a run through one part, put together — the
     * ways of holding each that {@code kept} keeps.
     *
     * <p>The law for parts beside the one for alternatives ({@link HeldOutcome.Bringing#oneOf}).
     * A way is all of its parts at once, so one no row goes settles it; short of that, every
     * reason any part cannot be held and every figure that left one unlooked at is said, none
     * standing in for another — told the first of two, a reader who deals with it meets the next.
     */
    static PartsHeld partsHeld(List<HeldOutcome.Bringing> each, Predicate<HeldOutcome> kept) {
        List<List<HeldOutcome>> parts = new ArrayList<>();
        Set<CompositionBudget> cutShort = EnumSet.noneOf(CompositionBudget.class);
        Set<RepairShortfall.Barrier> why = EnumSet.noneOf(RepairShortfall.Barrier.class);
        Set<CompositionBudget> unlooked = EnumSet.noneOf(CompositionBudget.class);
        boolean noRowGoes = false;
        for (HeldOutcome.Bringing part : each) {
            switch (part) {
                case HeldOutcome.Bringing.NoValueCanStandThere _ -> noRowGoes = true;
                case HeldOutcome.Bringing.NothingFound _ ->
                        why.add(RepairShortfall.Barrier.NOTHING_HOLDS_A_ROW_TO_IT);
                case HeldOutcome.Bringing.LeftUnlooked(Set<CompositionBudget> figures) ->
                        unlooked.addAll(figures);
                case HeldOutcome.Bringing.Found found -> {
                    switch (found.keeping(kept)) {
                        case HeldOutcome.Bringing.Kept.Some(var some) -> {
                            cutShort.addAll(some.cutShort());
                            parts.add(some.ways());
                        }
                        case HeldOutcome.Bringing.Kept.NoneLookedAtWas(var figures) ->
                                unlooked.addAll(figures);
                        case HeldOutcome.Bringing.Kept.None _ ->
                                why.add(RepairShortfall.Barrier.IT_WOULD_REWRITE_A_STATED_VALUE);
                    }
                }
            }
        }
        return new PartsHeld(noRowGoes, why, unlooked, parts, cutShort);
    }

    /**
     * {@code held}, put together.
     *
     * <p>Every way put together, each condition once, along the choices the ways made
     * ({@link HeldOutcome#along}), and refused where no row takes it so. A later guard stands below
     * an earlier one and its way usually takes the earlier one's in, but not always — a way read
     * through several copies holds only what each copy's way does — and what the row was held to
     * above is what it has to be wherever it goes next.
     *
     * @param check what a value's own type says of it, which a location the way's numbers are
     *              composed at is held to
     */
    private static HeldTogether heldTogether(MeasuredInput subject, List<HeldOutcome> held,
                                             CandidateCheck check) {
        List<RowDemand.AtAPoint> points = new ArrayList<>();
        for (HeldOutcome each : held) {
            for (RowDemand demand : each.demands()) {
                switch (demand) {
                    case RowDemand.AtAPoint point -> points.add(point);
                    // A condition's own demand is on the way the row is held to
                    // ({@link ReachingCuts#heldAt}), and is composed with the rest of it below.
                    case RowDemand.OfACondition _ -> { }
                }
            }
        }
        Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
        // What each point asks of the numbers it fixes, a number two points fix asked what both
        // leave it.
        Map<RealizationTarget, NumbersAskedFor> itemAsks = new LinkedHashMap<>();
        for (RowDemand.AtAPoint each : points) {
            for (RealizationTarget at : each.fixing().keySet()) {
                itemAsks.merge(at, each.asking(), NumbersAskedFor::meet);
            }
            for (Map.Entry<RealizationTarget, Place> at : each.fixing().entrySet()) {
                Place already = fixing.putIfAbsent(at.getKey(), at.getValue());
                if (already != null && !already.equals(at.getValue())) {
                    return new HeldTogether.Refused(new Attempt(null,
                            UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                            at.getKey().toString(), Optional.of("`" + at.getKey()
                                    + "` would have to stand at two places at once")));
                }
            }
        }
        // A way no row takes along the ways the row was held past the guards above, in the word
        // for why — the same words a way to a point no row takes is said in.
        Reachability.Reaching reaching;
        switch (HeldOutcome.along(held, subject.quantities().region())) {
            case Reachability.Reaching taken -> reaching = taken;
            case Reachability.NothingReaches _ -> {
                return new HeldTogether.Refused(new Attempt(null,
                        UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH, null,
                        Optional.empty()));
            }
            case Reachability.NothingComesOutThatWay _ -> {
                return new HeldTogether.Refused(new Attempt(null,
                        UnresolvedCombination.Reason.A_CONDITION_NEVER_COMES_OUT_THAT_WAY, null,
                        Optional.empty()));
            }
            case Reachability.NumbersLeaveNone _ -> {
                return new HeldTogether.Refused(new Attempt(null,
                        UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE, null,
                        Optional.empty()));
            }
        }
        Requirements required;
        switch (reaching.writing(fixing.keySet())) {
            case Reachability.Written.Under(Requirements both) -> required = both;
            case Reachability.Written.OffTheWay(RealizationTarget each) -> {
                return new HeldTogether.Refused(new Attempt(null,
                        UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                        each.writeRoot().toString(), Optional.of("`" + each.writeRoot()
                                + "` is written under a case the way to it does not take")));
            }
        }
        WhatTheWayLeaves leaves = new WhatTheWayLeaves(subject, reaching);
        Standing where = alsoOnTheWay(subject, fixing, itemAsks, check, reaching, false, null,
                leaves);
        for (ReachabilityGap gap : where.unrepresented().onTheWay()) {
            if (gap instanceof ReachabilityGap.ProvedImpossible) {
                return new HeldTogether.Refused(new Attempt(null,
                        UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE, null,
                        Optional.empty()));
            }
        }
        // What each number the way placed is a number of, whether or not a point is held beside it:
        // a row held to a condition's own demand alone stands at the numbers the way placed and at
        // no point. And each point's own numbers, asked of what the points ask.
        Map<RealizationTarget, AskedAt> numbers = atThoseNumbers(where.at(),
                whatEachOfThemIsANumberOf(itemAsks, where.routed(), where.counted(), leaves));
        return new HeldTogether.Asked(new LinkedHashMap<>(numbers), where.at(), required, reaching,
                ContentsAsked.of(reaching.boundedOnTheWay(), numbers), where.someElement(),
                where.composed(), where.bounds());
    }

    /**
     * What this row's classes ask of the positions strictly inside {@code location}, and the cases
     * {@code alsoRequired} names there — handed to whatever composes the value written whole at it.
     */
    private static DemandsInside inside(MeasuredInput.MeasuredAxes axes, int[] where,
                                        TermPath location, Requirements alsoRequired) {
        Map<TermPath, List<FixtureTemplate>> among = new LinkedHashMap<>();
        Requirements required = strictlyUnder(alsoRequired, Set.of(location), true);
        for (int i = 0; i < axes.size(); i++) {
            TermPath path = axes.get(i).path();
            if (where[i] == NOT_HERE || !isStrictlyUnder(path, location)) {
                continue;
            }
            PartitionClass cls = axes.get(i).classes().get(where[i]);
            // A class with values of its own hands over all of them, which is what stands for the
            // class whichever case it is — a case that carries nothing is named by writing it —
            // and any of which may be the one the rest of the value can stand beside. A class that
            // only says which case a position is hands over the case, and what stands under it is
            // built under it.
            if (cls.representatives() instanceof RepresentativeSource.Values values) {
                among.put(path, values.written());
                continue;
            }
            if (required.merge(strictlyUnder(axes.get(i).requiring(cls), Set.of(location), true))
                    instanceof Requirements.Merge.Merged(Requirements both)) {
                required = both;
            }
        }
        return new DemandsInside(among, required);
    }

    /**
     * Whether the {@code counting}th position is how many a container holds and this row stands at
     * a class of some position inside that container, asked as the pair space asks it
     * ({@link ClassCoexistence#standsInside}).
     */
    private static boolean somethingStandsInside(MeasuredInput.MeasuredAxes axes, int[] where,
                                                 int counting) {
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] != NOT_HERE
                    && ClassCoexistence.standsInside(axes.get(i), axes.get(counting))) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code path} names a position inside {@code location} and not the location. */
    private static boolean isStrictlyUnder(TermPath path, TermPath location) {
        return path.isAtOrUnder(location) && !path.equals(location);
    }

    /**
     * The refinements of {@code from} strictly inside one of {@code locations} where {@code inside}
     * is true, and every other one where it is false.
     */
    private static Requirements strictlyUnder(Requirements from, Set<TermPath> locations,
                                              boolean inside) {
        Map<TermPath, CasesLeft> kept = new LinkedHashMap<>();
        from.refinements().forEach((path, refinement) -> {
            boolean under = locations.stream().anyMatch(each -> isStrictlyUnder(path, each));
            if (under == inside) {
                kept.put(path, refinement);
            }
        });
        return new Requirements(kept, from.crossings());
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
     *
     * <p>The parameters {@code given} names are written as it says instead of composed, which is
     * what makes a value the model already states an origin of the search rather than a
     * rewrite of its answer. Composed first and rewritten after, a row the baseline could have been
     * written for came back as one nothing composed — a representative chosen from the classes
     * alone breaks a rule relating two positions while the model's own value does not — and a row
     * the baseline needed nothing beside came back carrying whatever the composition had needed.
     *
     * <p>{@code answers} is what the row stands its target's dependencies in with, which is the
     * same for every row of one behavior here: what a class or an arm asks about is the positions,
     * and nothing on that route asks a dependency for one answer over another. It is carried in
     * rather than put on afterwards because a row without it is a row nothing applies, and a
     * candidate the search ran in one environment and published in another was certified for a row
     * nobody is offered.
     *
     * <p>{@code held} is what the comparisons the row is held to ask of it, beside its classes —
     * demands of the same standing, put together with them before anything is composed. A number a
     * comparison asks a term to stand at joins the numbers the classes admit, a position the way
     * to the comparison bounds is placed where the way leaves it, and a value written whole at a
     * location — a list filled to a total — is composed holding what the classes ask of the
     * positions inside it, so the location is written once.
     */
    private static Attempt build(MeasuredInput.MeasuredAxes axes, int[] where,
                                 HeldTogether held,
                                 CandidateCheck check, Map<String, Written> given,
                                 List<StoodInAnswer> answers) {
        return switch (composed(axes, where, held, check, given, RowTaking.FIRST)) {
            // The values, and no name. What a row is about is what it was composed for, which is
            // the caller's question and not this one's: this is handed an assignment and does not
            // know whether it is a class, a combination the body decides together, or an edge.
            // Named here from the assignment, a row would say every position it happened to hold,
            // and a row composed for one class would carry three in its name.
            case RowComposed.Taken(List<FixtureTemplate> inputs) ->
                    Attempt.of(new GeneratedRow(List.of(new Purpose.Unstated()), inputs, answers));
            case RowComposed.Failed(Attempt why, var _) -> why;
            case RowComposed.PassedOver _, RowComposed.Halted _ -> throw new IllegalStateException(
                    "the first row composed is taken, so nothing is passed over or stopped");
        };
    }

    /**
     * What a caller makes of each whole row the composing of one candidate comes to.
     *
     * <p>Beside {@link ValueTaking} and over it: that one is asked of a parameter's value, and this of
     * the row once every parameter has one. A row passed over sends the walk of the last parameter
     * on to its next assignment, and that walk running out sends the one before it on — so every
     * row the candidate's classes can be written as is reached, nearest first, while the caller
     * goes on passing.
     */
    @FunctionalInterface
    interface RowTaking {

        Acceptance take(List<FixtureTemplate> inputs);

        /** The first row composed, which is what every search but a witness's wants. */
        RowTaking FIRST = _ -> Acceptance.TAKEN;
    }

    /**
     * {@code taking}, handed at most {@code most} rows: the one after is refused as the work nobody
     * did, and {@code reached} is told. A walk handing rows on until one is taken goes through every
     * assignment of every parameter against every one of the others, so it is bounded by how many
     * rows it composes and not only by what is done with each.
     */
    private static RowTaking atMost(int most, Runnable reached, RowTaking taking) {
        int[] handed = {0};
        return inputs -> {
            if (handed[0] >= most) {
                reached.run();
                return Acceptance.STOPPED;
            }
            handed[0]++;
            return taking.take(inputs);
        };
    }

    /** What composing one candidate came to, for a caller that may pass rows over. */
    private sealed interface RowComposed {

        /** A row, taken. */
        record Taken(List<FixtureTemplate> inputs) implements RowComposed {}

        /**
         * Rows were composed and every one was passed over. Not a refusal of any of them.
         *
         * @param found what the walk found out on the way, whole: a figure it stopped at before
         *              trying everything, an offer an alternative beside the rows was short of, a
         *              candidate turned away. Nothing where every row there was was composed and
         *              passed over; anything here is a row the search may yet be offered
         */
        record PassedOver(SearchShortfall found) implements RowComposed {}

        /** The caller stopped, having run out of what deciding costs it. */
        record Halted() implements RowComposed {}

        /**
         * No row could be composed, and why.
         *
         * @param at the parameter nothing was composed for, where it came to nothing at one; empty
         *           where it is the row as a whole — its classes, what it is held to — that left
         *           nothing to compose
         */
        record Failed(Attempt why, OptionalInt at) implements RowComposed {

            /** Nothing composed for the row as a whole. */
            static Failed ofTheRow(Attempt why) {
                return new Failed(why, OptionalInt.empty());
            }

            /** Nothing composed for the parameter at {@code parameter}. */
            static Failed at(int parameter, Attempt why) {
                return new Failed(why, OptionalInt.of(parameter));
            }
        }
    }

    /** Rows that came to nothing, as {@link WhatTheAlternativesCameTo} reads and writes them. */
    private static final WhatTheAlternativesCameTo.Vocabulary<RowComposed.Failed> ROWS =
            new WhatTheAlternativesCameTo.Vocabulary<>() {

                @Override
                public boolean proves(RowComposed.Failed one) {
                    return one.why().reason() != null && one.why().reason().provesInfeasible();
                }

                @Override
                public UnresolvedCombination.Reason word(RowComposed.Failed one) {
                    return one.why().reason();
                }

                @Override
                public SearchShortfall found(RowComposed.Failed one) {
                    return one.why().found();
                }

                @Override
                public RowComposed.Failed carrying(RowComposed.Failed said, SearchShortfall found) {
                    Attempt was = said.why();
                    return new RowComposed.Failed(new Attempt(null, found.wordFor(was.reason()),
                            was.detail(), was.said(), found, was.localTo()), said.at());
                }
            };

    /**
     * Parameters nothing was composed for, as {@link WhatTheAlternativesCameTo} reads and writes
     * them.
     */
    private static final WhatTheAlternativesCameTo.Vocabulary<ParameterCameToNothing> PARAMETERS =
            new WhatTheAlternativesCameTo.Vocabulary<>() {

                @Override
                public boolean proves(ParameterCameToNothing one) {
                    return one.tried() instanceof Outcome.Unresolved(var reason, var _)
                            && reason.provesInfeasible();
                }

                @Override
                public UnresolvedCombination.Reason word(ParameterCameToNothing one) {
                    return switch (one.tried()) {
                        case Outcome.Unresolved(UnresolvedCombination.Reason why, var _) -> why;
                        case Outcome.Stopped stopped -> stopped.why();
                        case Outcome.Unexhausted some -> some.why();
                        case Outcome.OfferShort _ ->
                                UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED;
                        case Outcome.Limited(UnresolvedCombination.Reason why, var _, var _) -> why;
                        case Outcome.Unplanned _ ->
                                UnresolvedCombination.Reason.NO_READING_OF_THE_LINE_COULD_BE_SEARCHED;
                        case Outcome.Built _, Outcome.PassedOver _, Outcome.Halted _ ->
                                throw new IllegalStateException(
                                        "a parameter something was composed for came to nothing");
                    };
                }

                @Override
                public SearchShortfall found(ParameterCameToNothing one) {
                    SearchShortfall its = switch (one.tried()) {
                        case Outcome.Stopped stopped ->
                                SearchShortfall.of(stopped.met(), stopped.offered());
                        case Outcome.Unexhausted some ->
                                SearchShortfall.of(some.met(), some.offered());
                        case Outcome.OfferShort offer ->
                                SearchShortfall.of(CompositionShortfall.NONE, offer.offered());
                        case Outcome.Limited(var _, var _, Set<CompositionBudget> by) ->
                                SearchShortfall.of(CompositionShortfall.of(by));
                        case Outcome.Unplanned(Set<CompositionBudget> by) ->
                                SearchShortfall.of(CompositionShortfall.of(by));
                        case Outcome.Unresolved _ -> SearchShortfall.NONE;
                        case Outcome.Built _, Outcome.PassedOver _, Outcome.Halted _ ->
                                throw new IllegalStateException(
                                        "a parameter something was composed for came to nothing");
                    };
                    return its.and(one.found());
                }

                /**
                 * In the outcome for what was found out: a figure's, what this compiler does not
                 * write, or an offer short of the rules — and where only a candidate turned away, a
                 * way nobody read or a candidate not handed on is more, the outcome as it was in
                 * the word for what was found out ({@link SearchShortfall#wordFor}), with why a
                 * candidate was not handed on beside it. This outcome has no place to keep either,
                 * so the word is where they go: a proof kept as it was beside a way nobody read is
                 * a proof published over a search that did not have everything.
                 */
                @Override
                public ParameterCameToNothing carrying(ParameterCameToNothing said,
                                                       SearchShortfall found) {
                    String detail = switch (said.tried()) {
                        case Outcome.Unresolved(var _, String its) -> its;
                        case Outcome.Stopped stopped -> stopped.detail();
                        case Outcome.Unexhausted some -> some.detail();
                        case Outcome.OfferShort(var _, String its) -> its;
                        case Outcome.Limited(var _, String its, var _) -> its;
                        case Outcome.Unplanned _, Outcome.Built _, Outcome.PassedOver _,
                             Outcome.Halted _ -> null;
                    };
                    CompositionShortfall met = found.met();
                    Outcome carried = !met.figures().isEmpty()
                            ? new Outcome.Stopped(met, found.offered(), detail)
                            : !met.nothing() ? new Outcome.Unexhausted(met, found.offered(), detail)
                            : !found.offered().isEmpty()
                            ? new Outcome.OfferShort(found.offered(), detail)
                            : switch (said.tried()) {
                                case Outcome.Unresolved(UnresolvedCombination.Reason why,
                                                        String its) ->
                                        new Outcome.Unresolved(found.wordFor(why),
                                                found.toldFor(why, Optional.ofNullable(its))
                                                        .orElse(null));
                                case Outcome.Limited(UnresolvedCombination.Reason why, String its,
                                                     Set<CompositionBudget> by) ->
                                        new Outcome.Limited(found.wordFor(why),
                                                found.toldFor(why, Optional.ofNullable(its))
                                                        .orElse(null), by);
                                case Outcome.Stopped _, Outcome.Unexhausted _,
                                     Outcome.OfferShort _, Outcome.Unplanned _, Outcome.Built _,
                                     Outcome.PassedOver _, Outcome.Halted _ -> said.tried();
                            };
                    return new ParameterCameToNothing(said.parameter(), carried, found,
                            said.here());
                }
            };

    /**
     * What a walk over alternatives for a row none of which was taken came to
     * ({@link WhatTheAlternativesCameTo}), as a row composed comes to it: where no alternative came
     * to nothing to say it in, what kept the rest untried — a figure, or a way under a case nobody
     * read, said as that — and otherwise what {@code nothingTried} says.
     *
     * @param passedOver what the walks of the rows passed over found out, or null where none was
     * @param alsoFound  what the walk found out beside the alternatives that came to nothing
     *                   ({@link WhatTheAlternativesCameTo#over})
     */
    private static RowComposed overTheAlternatives(List<RowComposed.Failed> cameToNothing,
                                                   SearchShortfall passedOver,
                                                   SearchShortfall alsoFound,
                                                   Supplier<RowComposed> nothingTried) {
        return switch (WhatTheAlternativesCameTo.over(cameToNothing, passedOver, alsoFound,
                ROWS)) {
            case WhatTheAlternativesCameTo.Came.PassedOver(SearchShortfall found) ->
                    new RowComposed.PassedOver(found);
            case WhatTheAlternativesCameTo.Came.Said(RowComposed.Failed said) -> said;
            case WhatTheAlternativesCameTo.Came.Untried(SearchShortfall found) ->
                    RowComposed.Failed.ofTheRow(new Attempt(null,
                            found.wordFor(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE), null,
                            found.unread() ? Optional.of(A_CASE_WAS_NOT_READ) : Optional.empty(),
                            found));
            case WhatTheAlternativesCameTo.Came.NothingToSayItIn<RowComposed.Failed> _ ->
                    nothingTried.get();
        };
    }

    /** {@code found} beside what was found out before, where nothing before is null. */
    private static SearchShortfall joined(SearchShortfall before, SearchShortfall found) {
        return before == null ? found : before.and(found);
    }

    /**
     * {@link #build}, with every row composed handed to {@code taking} until it takes one.
     */
    private static RowComposed composed(MeasuredInput.MeasuredAxes axes, int[] where,
                                        HeldTogether held, CandidateCheck check,
                                        Map<String, Written> given, RowTaking taking) {
        MeasuredInput subject = axes.subject();
        LocationWrites decided = new LocationWrites();
        HeldTogether.Asked holding;
        switch (held) {
            case HeldTogether.Refused(Attempt why) -> {
                return RowComposed.Failed.ofTheRow(why);
            }
            case HeldTogether.Asked asked -> holding = asked;
        }
        // The numbers this row stands at: the ones its classes admit, and the ones the comparisons
        // ask for. A number asked by both is asked at the comparison's place, which has to be one
        // the class admits — a class and a comparison that leave a number nowhere between them are
        // a row that would have to be two things at once.
        SequencedMap<RealizationTarget, AskedAt> numbers =
                numbersTheClassesAdmit(axes, where, subject.quantities());
        for (Map.Entry<RealizationTarget, AskedAt> each : holding.asked().entrySet()) {
            AskedAt asked = each.getValue();
            AskedAt theClass = numbers.get(each.getKey());
            Attempt noRoom = leavesNoRoom(each.getKey(), asked, theClass, subject.quantities());
            if (noRoom != null) {
                return RowComposed.Failed.ofTheRow(noRoom);
            }
            // A class is of a number, so only a number is asked by both.
            if (theClass != null && each.getKey() instanceof RealizationTarget.OfANumber) {
                asked = new AskedAt(asked.about().meet(theClass.about()), asked.walked());
            }
            numbers.put(each.getKey(), asked);
        }
        // One value per location, for as many of its numbers as this row's classes stand on. Each
        // class composed a value for the number it was built at, so two classes of one location
        // arrive holding two values — and a row that wrote either of them would decide one class
        // while being offered as covering both. Composed here instead, before anything is written,
        // by the reader that answers this for the points of a border ({@link #edgeAt}).
        Map<TermPath, List<FixtureTemplate>> together = new LinkedHashMap<>();
        // The locations whose value was composed holding what the classes ask inside them. What
        // those classes stand for is in that value, so they write nothing of their own.
        Set<TermPath> composedWhole = new LinkedHashSet<>();
        // Gathered as the numbers were when the conditions placed them, so a value some element is
        // to stand at goes in with the counts here as it did there.
        for (Map.Entry<TermPath, SequencedMap<RealizationTarget, AskedAt>> group
                : byTheLocationTheyWrite(numbers, holding.someElement()).entrySet()) {
            boolean asHeld = group.getValue().keySet().stream()
                    .anyMatch(holding.asked()::containsKey);
            // A location asked for one number, which the class standing at it holds a value for
            // already — composed by this same owner, for this same number, when the class was made.
            // So what is composed here is what more than one of them takes: one value answering
            // every number of the location at once, which no class holds because no class is asked
            // about the numbers beside its own. And what a comparison asks, which no class holds
            // either.
            if (group.getValue().size() < 2 && !asHeld) {
                continue;
            }
            DemandsInside insideIt = asHeld
                    && TermRealizations.composesWhatIsInside(group.getValue().keySet())
                    ? inside(axes, where, group.getKey(), holding.required())
                    : DemandsInside.NOTHING;
            // What a condition held is composed in is what its placing composed it in, and where
            // that placing composed this very request with nothing asked inside it, that value.
            Edge composed;
            if (asHeld) {
                RegionToCompose within = composedIn(group.getKey(), group.getValue(),
                        holding.reaching().region(), holding.standing(), holding.bounds());
                ComposedAt already = holding.composed().get(group.getKey());
                composed = insideIt.isEmpty() && already != null
                        && already.answers(group.getValue(), within)
                        ? already.edge()
                        : edgeAt(subject, group.getKey(), group.getValue(), within.region(),
                                insideIt);
            } else {
                composed = edgeAt(subject, group.getKey(), group.getValue(),
                        subject.quantities().region(), insideIt);
            }
            if (!insideIt.isEmpty()) {
                composedWhole.add(group.getKey());
            }
            if (composed.values().isEmpty()) {
                // What the composing said, and not a sentence about the location holding two
                // values: a location asked for numbers nothing here writes one value for is what
                // that reader reports, in the words it reports it in. Which are never that no such
                // value exists — whether one does is not a question anything on this route asked.
                //
                // And with the word what it met, for the reason every other reader of an edge
                // carries it: the word says the question is open and only this says whether
                // anything a reader could raise reaches it. Taken as the word alone, a group this
                // compiler writes none of the values for arrives as a search that left something
                // untried with nothing of this compiler's beside it.
                return RowComposed.Failed.ofTheRow(new Attempt(null, composed.reason(),
                        group.getKey().toString(), Optional.ofNullable(composed.said()),
                        SearchShortfall.of(composed.met())));
            }
            together.put(group.getKey(), composed.values());
        }
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
                // Which position, and which two it would have to be. The reason is the category a
                // reader acts on and this is the sentence that says which case of it this was —
                // without it an author is told a row is impossible and left to work out why.
                Requirements.Merge.Conflict against = (Requirements.Merge.Conflict) both;
                return RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                        at, Optional.of("`" + against.at() + "` would have to be both "
                                + against.one().spelled() + " and "
                                + against.other().spelled())));
            }
            required = merged.requirements();
            PartitionClass cls = axes.get(i).classes().get(where[i]);
            switch (cls.representatives()) {
                // A class that narrows the position states the narrowing and nothing else. What
                // stands at the narrowed position is built there, out of the narrowed type — which
                // is where the values this class would have offered came from in the first place.
                //
                // Said once for every kind of case, because a class narrows or it does not: a case
                // holding a record offers no value and a case wrapping one offers the value it
                // wraps, and taking the second as a value of the unnarrowed position is one
                // location decided twice, under two names. The plan reads the first of them and the
                // class fixed at the narrowed position is never looked at.
                case RepresentativeSource.Values values -> {
                    // The one composed for every number of this location where there was more than
                    // one, and the class's own where this class is the only one standing on it.
                    List<FixtureTemplate> write = answeringAllOfThem(together, cls);
                    // Inside a value composed whole for a comparison, what this class stands for
                    // is already in it.
                    boolean inThatValue = composedWhole.stream()
                            .anyMatch(each -> isStrictlyUnder(path, each));
                    List<FixtureTemplate> offered = write == null ? values.written() : write;
                    // A class of how many a container holds, beside a class of this row standing
                    // inside it, asks the container to hold that many and not to be one of the
                    // values standing for the class: written whole, the container would leave the
                    // position inside it nowhere to be written. Built to hold what is asked inside
                    // it, to a size the class takes from one up ({@link #countsOf}).
                    DeclaredBounds.CountRange holds = null;
                    if (write == null && somethingStandsInside(axes, where, i)) {
                        holds = countsOf(cls);
                        if (holds == null) {
                            DeclaredBounds.CountRange standingFor = sizesOf(offered);
                            holds = standingFor == null ? null : within(standingFor, FROM_ONE);
                        }
                    }
                    if (cls.selects() == null && !inThatValue
                            && (holds != null ? decided.size(path, holds)
                                    : decided.write(path, offered))
                                    == LocationWrites.Written.CONFLICTING) {
                        // Two of this row's classes are of one location and offer different values
                        // for it. Taking either leaves the other's class unanswered while the row
                        // is offered as covering it, so neither is taken.
                        return RowComposed.Failed.ofTheRow(new Attempt(null,
                                UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, at,
                                Optional.of("`" + path
                                        + "` would have to hold two values at once")));
                    }
                }
                // Not a value but how one is arrived at: the walk below builds one at this position,
                // field by field, the way it builds every other record. What it is built through is
                // already in the requirements, which is where the plan reads it.
                case RepresentativeSource.Compose _ -> { }
                // What the class said about itself. A class that recorded why nothing was produced
                // for it knows something this does not, and the two answers are not the same claim:
                // one is that nothing was arrived at, and the other is that nothing can be. Read as
                // the first, a case somebody can write in one line is reported as a row that does
                // not exist.
                case RepresentativeSource.NothingProducible cannot -> {
                    return RowComposed.Failed.ofTheRow(new Attempt(null,
                            UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, at,
                            Optional.of(cannot.why())));
                }
                // And the other of those two answers. Nothing was arrived at and the class says so
                // as what stopped the arriving, which is a figure somebody can raise or work
                // nobody has done — never that the class holds no value.
                case RepresentativeSource.NotArrivedAt stopped -> {
                    return RowComposed.Failed.ofTheRow(new Attempt(null,
                            stopped.met().figures().isEmpty()
                                    ? UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED
                                    : UnresolvedCombination.Reason.wordFor(stopped.met().figures()),
                            at, Optional.of(stopped.why()), SearchShortfall.of(stopped.met())));
                }
            }
        }
        // The cases the comparisons take the row through, beside the ones its classes do. Then
        // what stands inside a value composed whole is that value's, and not something the rest of
        // the parameter is planned against: the plan does not look under a location it is handed.
        if (!(required.merge(holding.required())
                instanceof Requirements.Merge.Merged(Requirements withTheWay))) {
            return RowComposed.Failed.ofTheRow(new Attempt(null,
                    UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                    null, Optional.of("the way to a comparison the row is held to takes a case"
                            + " its classes do not")));
        }
        // And what the way asks the elements of its containers to be, which the elements are
        // written as. Where that is two things at one position inside an element, beside each
        // other or beside the classes, the elements are written alike and no row is — which is
        // this composer's answer and not the model's.
        ElementWrites elements = holding.reaching() == null
                ? ElementWrites.of(List.of())
                : ElementWrites.of(holding.reaching().boundedOnTheWay());
        switch (elements.requiredBeside(withTheWay)) {
            case Requirements.Merge.Merged(Requirements both) -> withTheWay = both;
            case Requirements.Merge.Conflict conflict -> {
                return RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        conflict.at().toString(),
                        Optional.of(ElementWrites.writtenAlike(conflict.at()))));
            }
        }
        required = strictlyUnder(withTheWay, composedWhole, false);
        // And the locations only a comparison asked about, which no class wrote. Not one the row
        // is narrowed at: what has to hold of it is then one thing said two ways — the case it is,
        // and the place it stands at — and the case says how it is built while the place is what
        // a candidate built that way is held to, as a point of a border is ({@link #probeFixing}).
        for (Map.Entry<TermPath, List<FixtureTemplate>> each : together.entrySet()) {
            if (decided.at(each.getKey()) == null && required.at(each.getKey()) == null
                    && decided.write(each.getKey(), each.getValue())
                            != LocationWrites.Written.FIRST) {
                return RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        each.getKey().toString(), Optional.of("`" + each.getKey()
                                + "` would have to hold two values at once")));
            }
        }
        TruthsAsked truthsAsked = holding.reaching() == null ? TruthsAsked.NONE
                : holding.reaching().truths();
        // The order is one for every way of writing the containers under the cases, since which
        // parameter a container is handed a value of does not turn on the case it is written
        // under.
        CompositionOrder order;
        switch (CompositionOrder.of(parametersOf(subject), holding.contents())) {
            case CompositionOrder.Result.Ordered(CompositionOrder ordered) -> order = ordered;
            case CompositionOrder.Result.Circular circular -> {
                return RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, null,
                        Optional.of(circularly(circular))));
            }
        }
        // Every way of writing what the containers are handed under the cases this row can be,
        // one at a time: a way whose rows were all passed over or came to nothing may be followed
        // by one under another case that does not. What they came to is said over every one of
        // them, with the figure where the walk stopped short of the rest.
        Requirements rowIs = required;
        Set<TermPath> truthsWritten = new LinkedHashSet<>(truthsAsked.at().keySet());
        truthsWritten.addAll(elements.truthsAt());
        ContentsAsked.UnderTheCases under = holding.contents().underTheCases(subject.reach(),
                rowIs, truthsWritten);
        RowComposed[] stoppedWith = {null};
        SearchShortfall[] passedOver = {null};
        List<RowComposed.Failed> cameToNothing = new ArrayList<>();
        ContentsAsked.UnderTheCases.Walked walked = under.tryEach(way -> {
            // And the value the way to the comparisons asks of each Bool position it read, beside
            // what the classes wrote — at the position each stands at in this way, which for a Bool
            // the cases share is under the case this way writes. A class of the position holding
            // the other value is a row that would have to be both, which is no combination the
            // model has — said as that, the way a class and a comparison leaving a number nowhere
            // between them are.
            LocationWrites writes = decided.copy();
            TruthsAsked truths;
            switch (truthsAsked.standingAt(way.standing())) {
                case TruthsAsked.Merge.Merged(var here) -> truths = here;
                case TruthsAsked.Merge.Conflict(var at) -> {
                    cameToNothing.add(RowComposed.Failed.ofTheRow(new Attempt(null,
                            UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                            at.toString(), Optional.of("`" + at + "` is asked by the way to"
                                    + " hold both values"))));
                    return false;
                }
            }
            TermPath twice = truths.writtenInto(writes);
            if (twice != null) {
                cameToNothing.add(RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                        twice.toString(), Optional.of("`" + twice + "` is asked by the way to"
                                + " hold " + truths.at().get(twice)
                                + " and is written another value"))));
                return false;
            }
            // Then what the elements are asked, written beside it: two things at one position
            // inside an element are elements written alike, and not a row the model has none of.
            TermPath alike;
            switch (elements.truthsBeside(truths, way.standing())) {
                case TruthsAsked.Merge.Merged(var withTheElements) -> {
                    truths = withTheElements;
                    alike = withTheElements.writtenInto(writes);
                }
                case TruthsAsked.Merge.Conflict(var at) -> alike = at;
            }
            if (alike != null) {
                cameToNothing.add(RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, alike.toString(),
                        Optional.of(ElementWrites.writtenAlike(alike)))));
                return false;
            }
            Set<TermPath> writtenAt = new LinkedHashSet<>(together.keySet());
            writtenAt.addAll(truths.at().keySet());
            RowComposed came = inputsFrom(new RowBeingComposed(axes, given, check, holding,
                    way.contents(), writtenAt, writes, way.taken(), taking, order), 0,
                    new FixtureTemplate[order.parameters().size()], ValuesHandedOn.NONE);
            return switch (came) {
                case RowComposed.Taken _, RowComposed.Halted _ -> {
                    stoppedWith[0] = came;
                    yield true;
                }
                case RowComposed.PassedOver(SearchShortfall found) -> {
                    passedOver[0] = joined(passedOver[0], found);
                    yield false;
                }
                case RowComposed.Failed failed -> {
                    cameToNothing.add(failed);
                    yield false;
                }
            };
        });
        if (walked == ContentsAsked.UnderTheCases.Walked.COMPOSED) {
            return stoppedWith[0];
        }
        return overTheAlternatives(cameToNothing, passedOver[0], under.foundOut(walked),
                () -> RowComposed.Failed.ofTheRow(new Attempt(null,
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, null,
                        Optional.of(NO_CASE_HOLDS_THEM))));
    }

    /**
     * What every parameter of one candidate is composed against, settled before the first of them
     * is: the locations decided, what the classes and the comparisons require, and what the caller
     * makes of each row.
     *
     * @param contents what the containers are handed, written under the cases this row is being
     *                 tried as ({@link ContentsAsked.UnderTheCases#tryEach})
     * @param order    the order the parameters are composed in, and what each turns on
     */
    private record RowBeingComposed(MeasuredInput.MeasuredAxes axes, Map<String, Written> given,
                                    CandidateCheck check, HeldTogether.Asked holding,
                                    ContentsAsked contents, Set<TermPath> composedAt,
                                    LocationWrites decided, Requirements required,
                                    RowTaking taking, CompositionOrder order) {}

    /**
     * The row from the {@code next}-th parameter in the order on, with {@code composed} holding
     * what the ones before it were composed as.
     *
     * <p>A parameter is composed out of its own positions and of the values handed to its
     * containers, so what one of them can be written as turns on another only where it is handed
     * one of that other's values. Where it is not, a parameter nothing can be composed for is that
     * whatever stands before it, and is said at once. What does turn on the others is whether the
     * caller takes the row, so each value a parameter's walk composes is handed on to the
     * parameters after it, and the walk goes on to its next assignment only where every row
     * written with that value was passed over — or, where a parameter after it is handed one of its
     * values, where that one came to nothing.
     *
     * @param elsewhere what stands at the positions of the parameters composed so far that a
     *                  container is handed
     */
    private static RowComposed inputsFrom(RowBeingComposed row, int next,
                                          FixtureTemplate[] composed,
                                          ValuesHandedOn elsewhere) {
        MeasuredInput subject = row.axes().subject();
        CandidateCheck check = row.check();
        CompositionOrder order = row.order();
        if (next == order.order().size()) {
            List<FixtureTemplate> whole = List.of(composed);
            return switch (row.taking().take(whole)) {
                case TAKEN -> new RowComposed.Taken(whole);
                case PASSED -> new RowComposed.PassedOver(SearchShortfall.NONE);
                case STOPPED -> new RowComposed.Halted();
            };
        }
        int p = order.order().get(next);
        String head = subject.parameters().get(p);
        // Whether what came of this parameter is about its own classes alone, which it is not
        // where a container of it is handed a value of another.
        boolean alone = order.alone(p);
        // Whether a parameter after this one turns on its value, which is what another value of
        // this one could change.
        boolean awaited = order.awaited(next);
        Written written = row.given().get(head);
        if (written != null) {
            // Written as the caller says, and put through the same check a composed value goes
            // through: how a row is written never decides whether the model allows it. The first
            // way the model does not refuse, since each is the same value with a class's own
            // values chosen differently — and the next of them where a parameter after this one
            // came to nothing on what this one hands it.
            //
            // And what a container of another parameter is handed is read off what was built, the
            // way it is for a composed value ({@link HandedOn}): a way written against a value the
            // model states names that value, and what stands at a field it does not move is the
            // boundary's to say. The row goes on naming the value.
            ContentsAsked.ToHandOn read = row.contents().handedOnFrom(head);
            boolean stood = false;
            List<RowComposed.Failed> cameToNothing = new ArrayList<>();
            Optional<String> refused = Optional.empty();
            // A way that built and had nothing to hand on is one more way this did not go on
            // with, and is said with whatever the others came to: not every way refused, and not
            // the ways that stood being every way there was.
            FoundOut found = new FoundOut();
            for (WrittenWay way : written.ways()) {
                ValuesHandedOn handedOn;
                switch (HandedOn.of(check.build(p, way.value()), way::at, read, subject.inputs(),
                        subject.ruleReading())) {
                    case HandedOn.Came.Values(var at) -> handedOn = at;
                    case HandedOn.Came.Refused(String why) -> {
                        refused = Optional.of(why);
                        continue;
                    }
                    case HandedOn.Came.NotWritable(String why) -> {
                        found.notHandedOn(why);
                        continue;
                    }
                }
                stood = true;
                composed[p] = way.value();
                RowComposed rest = inputsFrom(row, next + 1, composed, elsewhere.and(handedOn));
                if (awaited && rest instanceof RowComposed.Failed failed
                        && failed.at().isPresent()
                        && order.mayTurnOn(failed.at().getAsInt(), p)) {
                    cameToNothing.add(failed);
                    continue;
                }
                return rest;
            }
            // Every way that stood came to nothing under a parameter after this one: what they
            // came to, over all of them, and beside it the figure the ways were cut at, since a
            // way never handed over may be the one that parameter could be composed with.
            SearchShortfall alsoFound = (written.cut()
                    ? SearchShortfall.of(CompositionShortfall.of(
                            Set.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES)))
                    : SearchShortfall.NONE).and(found.shortfall());
            if (stood) {
                return overTheAlternatives(cameToNothing, null, alsoFound, () -> {
                    throw new IllegalStateException(
                            "a way stood and nothing is said of what came of it");
                });
            }
            // Every way handed over was refused, which says the origin cannot be written for
            // this assignment only where every way there was was handed over — and only where
            // each was refused by the model. A way that built and had nothing to hand on is this
            // compiler's, said as why, and the value the author chose stays the row's rather than
            // being composed afresh.
            // The model's own refusal is said only where it is what the word says; and the
            // attempt is this parameter's alone except where a value was not handed on, which
            // turns on what the parameters after it are to be handed.
            boolean notHandedOn = alsoFound.notHandedOn().isPresent();
            Attempt none = Attempt.over(UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                    head, written.cut() || notHandedOn ? Optional.empty() : refused, alsoFound);
            return RowComposed.Failed.at(p, notHandedOn ? atThis(none, p, alone)
                    : none.localTo(p));
        }
        // Held to where the comparisons' numbers were chosen to stand, the way a row at a point of
        // a border is: a candidate built for a number has to read back as it. Whether one was
        // turned away for reading back elsewhere is what this parameter's search found out, and
        // goes with what it came to, the way it does on the way to a point ({@link InOrder}) —
        // and so does a candidate that built and had nothing to hand on.
        FoundOut found = new FoundOut();
        CandidateCheck checking = row.holding().standing().isEmpty() ? check
                : certifying(check, subject, p, row.holding().standing(), found);
        // What the parameters after this one came to, with the value this walk handed on last;
        // every value of this one a parameter after it came to nothing under; and what the walks
        // of the rows passed over found out, where any was.
        RowComposed[] after = {null};
        List<RowComposed.Failed> cameToNothing = new ArrayList<>();
        SearchShortfall[] passedOver = {null};
        Outcome tried = valueFor(subject, p, row.axes().axes(), row.composedAt(),
                row.decided(), row.required(), new Handed(row.contents(), elsewhere),
                checking, found, value -> {
                    composed[p] = value.value();
                    after[0] = inputsFrom(row, next + 1, composed, elsewhere.and(value.read()));
                    return switch (after[0]) {
                        case RowComposed.Taken _ -> Acceptance.TAKEN;
                        case RowComposed.PassedOver(SearchShortfall thoseFound) -> {
                            passedOver[0] = joined(passedOver[0], thoseFound);
                            yield Acceptance.PASSED;
                        }
                        case RowComposed.Halted _ -> Acceptance.STOPPED;
                        // A parameter after this one that does not turn on this one's value cannot
                        // be composed with any other value of it either, and the walk here is
                        // stopped with what that one said. One that does may be, directly or
                        // through the parameters between them, so the next is tried.
                        case RowComposed.Failed failed -> {
                            if (failed.at().isEmpty()
                                    || !order.mayTurnOn(failed.at().getAsInt(), p)) {
                                yield Acceptance.STOPPED;
                            }
                            cameToNothing.add(failed);
                            yield Acceptance.PASSED;
                        }
                    };
                });
        // What this parameter's own search came to, where it came to nothing, is one more
        // alternative beside the values a parameter after it came to nothing under, and said with
        // them. What it found out about its own candidates goes with each of them, and the
        // refusals it stands among are said as what they are: candidates that did not stand where
        // they were built for, or that built and had nothing to hand on ({@link Attempt#over}).
        RowComposed.Failed own = switch (tried) {
            case Outcome.Built _, Outcome.PassedOver _, Outcome.Halted _ -> null;
            // The word alone, because there was nothing of this compiler's beside it. A search that
            // met no figure and walked to the end of what this writes has nothing for a reader to
            // raise, and an empty account of what it met is what says so.
            case Outcome.Unresolved(UnresolvedCombination.Reason why, String said) ->
                    RowComposed.Failed.at(p, atThis(Attempt.over(why, null,
                            Optional.ofNullable(said), found.shortfall()), p, alone));
            // The figure's word, and beside it both what the offer was short of and what the search
            // met. A figure being reached and a rule that gave no value are two things an author
            // acts on, and the one that decides what they do first is the word.
            case Outcome.Stopped stopped -> RowComposed.Failed.at(p, atThis(Attempt.no(stopped.why(),
                    stopped.detail(), SearchShortfall.of(stopped.met(), stopped.offered())
                            .and(found.shortfall())), p, alone));
            case Outcome.Unexhausted some -> RowComposed.Failed.at(p, atThis(Attempt.no(some.why(),
                    some.detail(), SearchShortfall.of(some.met(), some.offered())
                            .and(found.shortfall())), p, alone));
            // The word for an offer that was not everything, and beside it which rule of the
            // position none of the values came from. Carried rather than folded into the word: an
            // author rewriting a rule and an author allowing more act on the same category and go
            // to different places, and which rule it was is what sends them.
            case Outcome.OfferShort(
                    SequencedMap<TermPath, StringOfferShortfall> offered, String said) ->
                    RowComposed.Failed.at(p, atThis(Attempt.no(
                            UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                            said, SearchShortfall.of(CompositionShortfall.NONE, offered)
                                    .and(found.shortfall())), p, alone));
            // The word the search came to, and beside it the figure that made what it was handed
            // short of the position. Neither half follows from the other — a search that refused
            // everything it was given did so over less than there was — so a reader is told both
            // what happened and that a number of this compiler's is why it happened over so little.
            case Outcome.Limited(UnresolvedCombination.Reason why, String said,
                                 Set<CompositionBudget> by) ->
                    RowComposed.Failed.at(p, atThis(Attempt.over(why, null,
                            Optional.ofNullable(said),
                            SearchShortfall.of(CompositionShortfall.of(by))
                                    .and(found.shortfall())), p, alone));
            // A value nothing planned, in the word for a reading no search could be made of, with
            // the figure that left the plan unable to reach what was asked for.
            case Outcome.Unplanned(Set<CompositionBudget> by) ->
                    RowComposed.Failed.at(p, atThis(Attempt.no(UnresolvedCombination.Reason
                            .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED, null,
                            SearchShortfall.of(CompositionShortfall.of(by))), p, alone));
        };
        return switch (tried) {
            case Outcome.Built _ -> after[0];
            // Stopped by the caller, which is the answer as it stands; or by a parameter after this
            // one that nothing could be composed for whatever this one is, which is said with the
            // values before it that one after it came to nothing under.
            case Outcome.Halted _ -> after[0] instanceof RowComposed.Failed stopping
                    ? overTheAlternatives(withFirst(stopping, cameToNothing), passedOver[0],
                            found.shortfall(), () -> stopping)
                    : after[0];
            // Every value passed over: for a row the caller passed over, or for what a parameter
            // after this one came to under each of them — beside every value of this one that
            // was turned away or not handed on, which none of those says anything about.
            case Outcome.PassedOver _ -> overTheAlternatives(cameToNothing, passedOver[0],
                    found.shortfall(), () -> new RowComposed.PassedOver(SearchShortfall.NONE));
            // This parameter's own search came to nothing. Said as what it came to, the way a
            // search that passed rows and then stopped is ({@link #over}): with what the rows
            // passed over and the values a parameter after it came to nothing under found out
            // beside it.
            case Outcome.Unresolved _, Outcome.Stopped _, Outcome.Unexhausted _,
                 Outcome.OfferShort _, Outcome.Limited _, Outcome.Unplanned _ ->
                    overTheAlternatives(withFirst(own, cameToNothing), null,
                            passedOver[0] == null ? SearchShortfall.NONE : passedOver[0],
                            () -> own);
        };
    }

    /** {@code first}, and {@code rest} after it. */
    private static <T> List<T> withFirst(T first, List<T> rest) {
        List<T> out = new ArrayList<>();
        out.add(first);
        out.addAll(rest);
        return out;
    }

    /**
     * {@code why}, said to have come to nothing at parameter {@code p} alone where it did: where
     * none of its containers is handed a value of another parameter. Where one is, what came of it
     * turns on that other's value too, and another value there may compose what this did not.
     */
    private static Attempt atThis(Attempt why, int p, boolean alone) {
        return alone ? why.localTo(p) : why;
    }

    /** How many the containers of the parameter at {@code root} are asked to hold. */
    private static Map<TermPath, DeclaredBounds.CountRange> sizesUnder(LocationWrites decided,
                                                                        TermPath root) {
        Map<TermPath, DeclaredBounds.CountRange> out = new LinkedHashMap<>();
        decided.sizes().forEach((at, holds) -> {
            if (at.head().equals(root.head())) {
                out.put(at, holds);
            }
        });
        return out;
    }

    /**
     * One parameter's value, searched for on its own.
     *
     * <p>Each parameter is built and refused on its own — the check is the model's constructor for that
     * one type, and a rule relating two of them is not something a model can write. So the choices
     * under one parameter and the choices under another do not multiply, and searching them together
     * would spend the bound on assignments that differ only in a parameter already settled. Two
     * parameters of eight either-or fields are two searches of 256, not one of 65,536.
     *
     * <p>What a condition on the way relates across parameters is a value one of them was composed
     * as written into a container of another, and that is handed over ({@code handed}) rather than
     * searched for together: the parameter it is read off is composed first, and its value is what
     * the container holds.
     */
    private static Outcome valueFor(MeasuredInput subject, int p, List<Axis> axes,
                                    Set<TermPath> composedAt, LocationWrites decided,
                                    Requirements required, Handed handed, CandidateCheck check,
                                    FoundOut found, ValueTaking taking) {
        TermPath at = TermPath.of(subject.parameters().get(p));
        Map<TermPath, List<FixtureTemplate>> here = new LinkedHashMap<>();
        for (Axis axis : axes) {
            List<FixtureTemplate> already = decided.at(axis.path());
            if (axis.path().head().equals(at.head()) && already != null) {
                here.put(axis.path(), already);
            }
        }
        // And every location a value was composed for, which need not be a position anything
        // divides: a list filled to a total is written where the total is taken, and no axis may
        // stand there.
        for (TermPath location : composedAt) {
            List<FixtureTemplate> already = decided.at(location);
            if (location.head().equals(at.head()) && already != null) {
                here.putIfAbsent(location, already);
            }
        }
        // And what is decided under a position held to one value with one of this parameter's, at
        // the same place here: one value at both is asked what either is asked.
        handed.asked().sharedAcross(decided.all()).forEach((location, values) -> {
            if (location.head().equals(at.head()) && decided.at(location) == null) {
                here.putIfAbsent(location, values);
            }
        });
        return valueAt(subject, p, here, sizesUnder(decided, at), settledIn(here), required,
                handed, check, found, taking);
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

    /**
     * One parameter's value, with the positions the caller fixed already decided.
     *
     * <p>{@code additional} is what has to hold besides whatever the fixed paths already state.
     * What a path under a refinement requires is read from the path, where it is written, and the
     * plan puts the two together — so a caller with nothing of its own to add hands over nothing
     * and loses none of it.
     *
     * @param handed what this parameter's containers are to hold and to hold nothing equal to, and
     *               what the parameters composed before it came to where those are read
     * @param asked  how many the containers of this parameter a class asked to hold so many are to
     *               hold ({@link LocationWrites#size})
     *
     * <p><b>And once more where a value built was passed over for not holding one value with
     * another position, or two.</b> What the parameter's own walk offers a position is what its
     * rules leave it, and that may be one value where two are asked for. So the position is then
     * offered values of its type apart from one another — one more than the values it is to be none
     * of, which is the fewest that holds one other than all of them — or, held to one value with a
     * position of this parameter, the value built there. The walk is made once more with those, and
     * what came of it is the answer; what of this compiler's that met goes with it.
     */
    private static Outcome valueAt(MeasuredInput subject, int p,
                                   Map<TermPath, List<FixtureTemplate>> decided,
                                   Map<TermPath, DeclaredBounds.CountRange> asked,
                                   Map<TermPath, Place> settled,
                                   Requirements additional, Handed handed, CandidateCheck check,
                                   FoundOut found, ValueTaking taking) {
        Composing[] made = {null};
        // One count of the cases planned under for a rule above, across both walks and every sum
        // they plan under: what multiplies is the cases of each such sum, and a count per sum would
        // let the product past it.
        CasesUnderARule cases = new CasesUnderARule();
        Outcome first = valueAtOnce(subject, p, decided, asked, settled, additional, handed, check,
                found, taking, made, cases);
        if (first instanceof Outcome.Built || first instanceof Outcome.PassedOver
                || first instanceof Outcome.Halted || made[0] == null
                || made[0].notHeld().isEmpty()) {
            return first;
        }
        found.notHeld(made[0].notHeld().getFirst());
        Map<TermPath, List<FixtureTemplate>> offered = offeredApart(subject, decided, made[0],
                found);
        return offered == null ? first : valueAtOnce(subject, p, offered, asked, settled,
                additional, handed, check, found, taking, new Composing[1], cases);
    }

    /**
     * What is left of the one count of cases planned under for a rule above, and whether the
     * attempt last made under one came to a position its rules leave nothing at.
     *
     * <p>The mark is the attempt's answer and is read by the walk that made it, straight after:
     * a case settled by its rules before anything was searched is not one the count is spent on.
     */
    private static final class CasesUnderARule {

        private int left = CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER.maximum();
        private boolean leftNothing;
    }

    /**
     * {@code decided}, with each position of the value {@code composing} composed that is held to
     * one value with another, or two, offered values to choose from where the walk that came to
     * nothing passed a value over for it; null where none is.
     *
     * <p>A position held apart from values built elsewhere is offered values of its type apart from
     * one another, one more than those, and none of them; one held to a position of the same value
     * is offered what was built there, and so is that position. What looking for them met goes into
     * {@code found}: fewer than were asked for is a type with no more values, or a figure.
     */
    private static Map<TermPath, List<FixtureTemplate>> offeredApart(
            MeasuredInput subject, Map<TermPath, List<FixtureTemplate>> decided,
            Composing composing, FoundOut found) {
        Map<TermPath, List<FixtureTemplate>> out = new LinkedHashMap<>(decided);
        boolean added = false;
        Map<TermPath, Set<String>> apartFrom = new LinkedHashMap<>();
        for (ContentsAsked.HeldTo each : composing.here().heldTo()) {
            if (!each.same()) {
                apartFrom.computeIfAbsent(each.at(), _ -> new LinkedHashSet<>())
                        .add(each.value().text());
            }
        }
        Map<TermPath, FixtureTemplate> last = composing.lastBuilt() == null ? Map.of()
                : composing.lastBuilt();
        for (RowDemand.OneValueAtBoth each : composing.here().alongside()) {
            FixtureTemplate built = last.get(each.one());
            if (built == null) {
                continue;
            }
            if (each.same()) {
                if (!decided.containsKey(each.one()) && !decided.containsKey(each.other())) {
                    out.put(each.one(), List.of(built));
                    out.put(each.other(), List.of(built));
                    added = true;
                }
            } else {
                apartFrom.computeIfAbsent(each.other(), _ -> new LinkedHashSet<>())
                        .add(built.text());
            }
        }
        for (Map.Entry<TermPath, Set<String>> each : apartFrom.entrySet()) {
            Type type = typeOf(composing.plan().at(each.getKey()));
            if (type == null || decided.containsKey(each.getKey())) {
                continue;
            }
            Proposals values = Witnesses.distinctValuesOf(type, each.getValue().size() + 1,
                    subject.ruleReading(), Set.of());
            found.met(values.met());
            List<FixtureTemplate> others = values.values().stream()
                    .filter(value -> !each.getValue().contains(value.text())).toList();
            if (!others.isEmpty()) {
                out.put(each.getKey(), others);
                added = true;
            }
        }
        return added ? out : null;
    }

    /** Whether one of {@code decided} is {@code at} or a position under it. */
    private static boolean decidedAtOrUnder(Set<TermPath> decided, TermPath at) {
        for (TermPath each : decided) {
            if (each.isAtOrUnder(at)) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code required} narrows a position inside {@code at}, and not {@code at}, to a
     *  case. */
    private static boolean narrowedStrictlyUnder(Requirements required, TermPath at) {
        for (TermPath each : required.refinements().keySet()) {
            if (isStrictlyUnder(each, at)) {
                return true;
            }
        }
        return false;
    }

    /** Whether one of {@code truths} is a position under {@code at}, and not {@code at}. */
    private static boolean truthAskedStrictlyUnder(Set<TermPath> truths, TermPath at) {
        for (TermPath each : truths) {
            if (isStrictlyUnder(each, at)) {
                return true;
            }
        }
        return false;
    }

    /** Whether every number of {@code group} is how many the container at {@code at} holds. */
    private static boolean onlyHowManyItHolds(Collection<RealizationTarget> group, TermPath at) {
        for (RealizationTarget each : group) {
            if (!(each instanceof RealizationTarget.OfANumber number
                    && number.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.HowManyItHolds
                    && taken.position().equals(at))) {
                return false;
            }
        }
        return !group.isEmpty();
    }

    /** Whether {@code required} narrows {@code at}, or a position under it, to a case. */
    private static boolean narrowedAtOrUnder(Requirements required, TermPath at) {
        for (TermPath each : required.refinements().keySet()) {
            if (each.isAtOrUnder(at)) {
                return true;
            }
        }
        return false;
    }

    /** The type the plan composes at {@code node}, or null where it is a value given whole. */
    private static Type typeOf(ConstructionPlan.Node node) {
        return switch (node) {
            case null -> null;
            case ConstructionPlan.Slot slot -> slot.type();
            case ConstructionPlan.Held held -> held.type();
            case ConstructionPlan.Built built -> built.type();
            case ConstructionPlan.Exact _ -> null;
        };
    }

    /**
     * {@link #valueAt}'s walk made once, with the composing it was made through put in
     * {@code through}.
     */
    private static Outcome valueAtOnce(MeasuredInput subject, int p,
                                       Map<TermPath, List<FixtureTemplate>> decided,
                                       Map<TermPath, DeclaredBounds.CountRange> asked,
                                       Map<TermPath, Place> settled,
                                       Requirements additional, Handed handed,
                                       CandidateCheck check, FoundOut found, ValueTaking taking,
                                       Composing[] through, CasesUnderARule cases) {
        // Every call answers whether it searched anything, and starts from "it did": a caller
        // reads the answer straight after the call, and a call that says nothing of it has not
        // left what an earlier call did.
        cases.leftNothing = false;
        // Where a value has to be built under this parameter, worked out once. What each position
        // may take, the search that chooses them one at a time, and the composing of what was chosen
        // all read this, so there is no second reading of the declarations for one of them to
        // disagree with.
        TermPath root = TermPath.of(subject.parameters().get(p));
        // How many the rules say a list at a position holds at the fewest, read from the same
        // reading of the parameter the values are chosen against. A list built around an element
        // has to meet that too: a row holding an element in the class and breaking the rule about
        // how many the list holds is not a row.
        ConstructionRules rules = ConstructionRules.of(subject, settled);
        // A container handed values is built to hold them, and not chosen whole. What a class or a
        // number fixed there is how many it holds — a container's own number is its size, and a
        // class of one is a run of sizes — so it is built to a size among the ones fixed, and the
        // values that were fixed are not what the row writes. Where a value fixed there is one
        // this cannot count, it stays fixed and is said below as nothing composed.
        //
        // What the containers are handed is worked out first, out of what the parameters before
        // this one were built as: a demand asked over every element of one of them is asked once
        // for each element it holds, and not at all where it holds none. A value handed on that
        // says no one value is this compiler's to say, and another value of the parameter it was
        // read off may say one.
        ContentsAsked.Here here;
        switch (handed.asked().resolvedFor(root.head(), handed.elsewhere())) {
            case ContentsAsked.Resolution.Resolved(ContentsAsked.Here resolved) -> here = resolved;
            case ContentsAsked.Resolution.Unresolved(String why) -> {
                return new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        why);
            }
        }
        // A demand left open is composed without, so whatever this search comes to is said with
        // it: a row the search did not find may be one meeting it.
        here.notComposed().ifPresent(found::notHandedOn);
        ConstructionPlan.ContentsComposed handedHere =
                handed.asked().composedUnder(root.head(), here);
        Map<TermPath, List<FixtureTemplate>> fixed = new LinkedHashMap<>(decided);
        Map<TermPath, DeclaredBounds.CountRange> sized = new LinkedHashMap<>();
        for (Map.Entry<TermPath, List<FixtureTemplate>> each : decided.entrySet()) {
            DeclaredBounds.CountRange counted = handedHere.handedTo(each.getKey())
                    ? sizesOf(each.getValue()) : null;
            if (counted != null) {
                fixed.remove(each.getKey());
                sized.put(each.getKey(), counted);
            }
        }
        asked.forEach((at, holds) -> sized.merge(at, holds, Generator::within));
        // A position held to one value with one composed before this is written as that value,
        // which is what holding it is. Not where something else already decides it or a position
        // under it, nor where it or a position under it is narrowed to a case: one location is
        // decided once, and the case and the value would be two accounts of it
        // ({@link ConstructionPlan}). There, the value built is held to it instead
        // ({@link Composing#attempt}).
        for (ContentsAsked.HeldTo each : here.heldTo()) {
            if (each.same() && !decidedAtOrUnder(fixed.keySet(), each.at())
                    && !narrowedAtOrUnder(additional, each.at())) {
                fixed.put(each.at(), List.of(each.value()));
            }
        }
        ConstructionPlan.Result planned = ConstructionPlan.of(subject.types().get(p), root,
                subject.rules().inners(), subject.symbols(), subject.rules().kinds(),
                subject.rules().sums(),
                fixed.keySet(), additional, handedHere,
                (at, building) -> new ConstructionPlan.ItMayHold(
                        within(heldRange(rules, at, building, subject.ruleReading()),
                                sized.get(at)),
                        ElementsKeptApart.heldBy(rules.heldAt(at))),
                rules::speaksUnder);
        ConstructionPlan plan;
        switch (planned) {
            case ConstructionPlan.Result.Planned made -> plan = made.plan();
            // What the model settles, which is not something this fell short of. Said before
            // anything was searched for and standing however far the search then went, so no figure
            // of this compiler's stands beside it: an author raising one would raise it and be told
            // the same thing.
            case ConstructionPlan.Result.Refused(ConstructionPlan.ModelRefusal why) -> {
                return switch (why) {
                    // The same answer the class search gives when two classes select different
                    // refinements of one position.
                    case ConstructionPlan.ModelRefusal.Conflict against ->
                            new Outcome.Unresolved(
                                    UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH,
                                    "`" + against.at() + "` would have to be both "
                                            + against.one().spelled() + " and "
                                            + against.other().spelled());
                    case ConstructionPlan.ModelRefusal.NoRoom noRoom ->
                            new Outcome.Unresolved(
                                    UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                    "`" + noRoom.at() + "` would have to hold " + noRoom.needed()
                                            + " for the value placed in it, and the rules leave"
                                            + " room for " + noRoom.holds().most());
                };
            }
            // What the caller asked for is under a position the plan stopped short of reading, so
            // there is nothing to search: a row composed against such a plan would be one the
            // caller's own value is missing from. Nothing here ran, so nothing here has a search's
            // word to give — what travels is the figure, and what a reader is told is that no
            // search could be made rather than what one found.
            case ConstructionPlan.Result.Beyond(Set<CompositionBudget> by) -> {
                return new Outcome.Unplanned(by);
            }
            // Something is asked for under a position that holds nothing until a narrowing says
            // what stands there, and this search has not said which. There is no plan, so nothing
            // was searched and nothing was refused: what a reader is owed is that no value was
            // composed and where the way down stopped. Said as a row nothing composes rather than
            // as a failure of this compiler, because a model reaches it — a class may state a
            // narrowing below a position nothing narrows.
            case ConstructionPlan.Result.Unnarrowed(TermPath where, List<Refinement> narrowings) -> {
                return new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        narrowings.isEmpty()
                                ? "`" + where + "` holds nothing that could be built under it"
                                : "`" + where + "` stands at "
                                        + narrowings.stream().map(Refinement::spelled)
                                                .collect(java.util.stream.Collectors.joining(" or "))
                                        + ", and nothing said which of them the value under it is");
            }
            // A rule of a value above names a field under a position that holds nothing until a
            // narrowing says what stands there, and nobody asked which. Planned under each case in
            // turn, so the field is a position held to that rule, and the first that composes is
            // the answer. A case whose plan composes nothing says nothing of the next one, so what
            // comes back where none composes is what the first case searched came to, unless the
            // figure stopped the rest.
            //
            // Counted where a case was searched, and not where its rules left a position nothing
            // before anything was searched: that case is settled by the rules, and a count spent
            // on it is a case further on never tried.
            case ConstructionPlan.Result.UnderEachCase(TermPath where, List<Refinement> under) -> {
                Outcome first = null;
                boolean firstSearched = false;
                for (Refinement each : under) {
                    if (!(additional.merge(where.refine(each).requirements())
                            instanceof Requirements.Merge.Merged(Requirements narrowed))) {
                        continue;
                    }
                    if (cases.left == 0) {
                        return new Outcome.Stopped(CompositionShortfall.of(
                                Set.of(CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER)),
                                new LinkedHashMap<>(), null);
                    }
                    // Taken before the case is planned: a sum under it asks the same count, and one
                    // asked only afterwards lets every sum on the way down pass it.
                    cases.left--;
                    Outcome made = valueAtOnce(subject, p, decided, asked, settled, narrowed,
                            handed, check, found, taking, through, cases);
                    if (made instanceof Outcome.Built || made instanceof Outcome.PassedOver
                            || made instanceof Outcome.Halted) {
                        return made;
                    }
                    boolean searched = !cases.leftNothing;
                    if (!searched) {
                        cases.left++;
                    }
                    if (first == null || (searched && !firstSearched)) {
                        first = made;
                        firstSearched = searched;
                    }
                }
                // What this planning under the cases came to is that some case was searched, and
                // that is what a plan above it counts: the cases of a sum inside a case are this
                // call's own, and the flag a case left behind is not the answer of the call.
                cases.leftNothing = !firstSearched;
                return first != null ? first
                        : new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                "`" + where + "` stands at no case the row can be");
            }
        }
        // A position a container of this value is handed the value at, which this plan holds no
        // position at: it is inside a value chosen whole, and what stands inside that is nothing
        // the plan writes — and a container of this value is composed before anything builds it,
        // so the plan is all there is to read it from. Said here, before anything is searched for,
        // rather than as every value composed coming to nothing for want of a value to hand over —
        // which would read as the model refusing them. A position a container of another
        // parameter is handed is not asked here: that is read off what was built ({@link
        // HandedOn}), where a value chosen whole has every part it holds.
        ConstructionPlan.ContentsComposed contents = handedHere;
        for (TermPath read : handed.asked().readWithin(root.head())) {
            if (plan.at(read) == null) {
                return new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        "a container is handed the value at `" + read + "`, which is inside a"
                                + " value composed whole");
            }
        }
        // And a container handed values that the plan does not build: one fixed at a value this
        // cannot count, or one inside a value chosen whole. What it is to hold would be asked of
        // nothing, and the row composed would stand for a condition it was never made to meet.
        for (TermPath container : contents.paths()) {
            if (contents.handedTo(container)
                    && !(plan.at(container) instanceof ConstructionPlan.Held)) {
                return new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        "`" + container + "` is to hold a value handed to it, and is written as a"
                                + " whole value this does not build");
            }
        }
        Choices choices = choicesOf(subject, plan, fixed, rules);
        if (choices.missingAt() != null) {
            // Marked for a walk planning under each case, which counts only the cases it searched:
            // one whose rules leave a position nothing was settled before anything was searched.
            if (choices.leftNothingAt() != null) {
                cases.leftNothing = true;
                // The model's answer where the rules leave the position nothing without anything
                // the caller settled — under the narrowings this row is asked under, which are the
                // combination's own — and this compiler's where a value settled beside it is why.
                boolean byTheRules = settled.isEmpty() || ConstructionRules.of(subject, Map.of())
                        .limitsAt(choices.leftNothingAt()).leavesNothing();
                return new Outcome.Unresolved(byTheRules
                        ? UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE
                        : UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, choices.missingAt());
            }
            // A position nothing stands at is the declarations' answer where the plan reached
            // everything, and this compiler's where it did not: what the search would have been
            // offered at a position the plan stopped short of is whole values of a type it declined
            // to look inside, and none being available is that decision and not a fact about the
            // model.
            //
            // And where building what was offered met a figure, the position may have nothing
            // because of it, which is the offer being short and not the declarations' answer.
            return whatTheSearchCameTo(choices.met(), new LinkedHashMap<>(),
                    choices.missingUnderAFigure(),
                    new Outcome.Unresolved(UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                            choices.missingAt()));
        }
        // One for every pass below, so what one of them found refused is known to the others.
        Composing composing =
                new Composing(p, plan, subject.inputs(), subject.ruleReading(), check,
                        handed.asked(), here, found);
        through[0] = composing;
        Outcome product = walk(choices, composing, taking, subject.ruleReading());
        // A value taken is the answer, and so is every value composed being passed over or the
        // caller stopping: what the pass below is for is values the walk could not compose, and
        // these were composed.
        if (product instanceof Outcome.Built || product instanceof Outcome.PassedOver
                || product instanceof Outcome.Halted) {
            return product;
        }
        // Every position took its value knowing only what the caller had settled, so a rule relating
        // two of them was satisfied only where the lists happened to already hold a pair that does.
        // Asked again choosing one position at a time, each from what is left once the ones before it
        // are asserted, which is the only way `a < b` is met in general.
        // Handed to the caller as every value the walk composes is: the caller is what composes the
        // parameters after this one, so a value it was never handed is a row with nothing after it.
        // The rules of the value being composed, read once for the whole search. Every position's
        // turn is answered by taking what the positions before it took onto this, which is the
        // reading a settling states and not a second one of the declaration.
        ConditionedCandidates candidates = new ConditionedCandidates(subject.ruleReading(), rules);
        Outcome conditioned = conditioned(plan, fixed, settled, composing, candidates);
        if (conditioned instanceof Outcome.Built(ComposedValue value)) {
            return switch (taking.take(value)) {
                case TAKEN -> conditioned;
                case PASSED -> new Outcome.PassedOver();
                case STOPPED -> new Outcome.Halted();
            };
        }
        // A pass that stopped at its bound has not tried everything it had, and neither pass may be
        // reported as though it had: `ALL_CANDIDATES_REJECTED` is what a reader is told nothing else
        // can be written at, and a search still holding assignments it never composed has not
        // established that.
        CompositionShortfall met = CompositionShortfall.NONE;
        for (Outcome each : List.of(product, conditioned)) {
            // Both passes' shortfalls and not one of them. Neither pass outranks the other here:
            // each stopped where it stopped, and a reader wanting to know what would let this go
            // further is owed every budget that would — and, in every other vocabulary, whatever
            // either pass walked in part or could not hold, which is not shown to be nothing by
            // the other pass having met a figure.
            if (each instanceof Outcome.Stopped(CompositionShortfall its, var _, String _)) {
                met = met.and(its);
            }
            if (each instanceof Outcome.Unexhausted(CompositionShortfall its, var _, String _)) {
                met = met.and(its);
            }
        }
        // Every value that was offered was refused, which is only the whole story where every value
        // the rules allow was offered. A position that read a count past what a row is built to carry,
        // or that has more pairings than are built at once, held something back, and saying so is the
        // difference between a fact about the model and a fact about this.
        HeldBack held = heldBack(subject, plan, choices, candidates, composing);
        // And what the rules about the positions left out of the offer, which a figure being
        // reached does not answer for. A search stopped at one position and given less than it
        // could have been at another is short both ways, and an author is owed the figure and the
        // rule — sent only the figure, they raise it and meet the same block. Beside a pass that
        // stopped, what the offer was short of as well: a reader raising the pass's figure would
        // meet the offer's next.
        if (!met.nothing()) {
            CompositionShortfall both = met.and(held.offer());
            return both.figures().isEmpty()
                    ? new Outcome.Unexhausted(both, held.offered(), null)
                    : new Outcome.Stopped(both, held.offered(), null);
        }
        // What each of them was short of, handed over unmerged and unranked. Which of the two a
        // reader is owed is one decision and it is made in one place.
        return whatTheSearchCameTo(held.offer(), held.offered(), held.plan(), product);
    }

    /**
     * What the search came to, said as an answer about the whole point or as one about less.
     *
     * <p>The one place that decides it, because the decision is one sentence: an ordinary answer
     * over a plan that stopped short is not an answer about everything the point had. Made at each
     * of the places a search can come back empty, the places would part — and the way they part is
     * that one of them says the model has nothing here, which is the reading this exists to stop.
     *
     * <p>A row is an answer whatever the plan gave up on. What the figure took away is positions
     * the row did not need, and a reader owed something about a value they have in hand is a reader
     * being told about this compiler's bookkeeping.
     */
    private static Outcome whatTheSearchCameTo(CompositionShortfall offer,
                                               SequencedMap<TermPath, StringOfferShortfall> offered,
                                               Set<CompositionBudget> planCut, Outcome came) {
        return switch (came) {
            case Outcome.Unresolved(UnresolvedCombination.Reason why, String detail) -> {
                // An offer still holding values outranks a plan short of the point, and does not
                // join it. A position that was never offered everything its rules allow leaves a
                // search that has not tried what it had — so nothing here has been exhausted, and
                // the plan being short is not yet anything a reader is owed: raise the offer's
                // figure and the search may compose a row without the plan changing at all. Said
                // together, an author is sent to raise a figure that would change nothing.
                //
                // Which holds however the offer came to be short of everything, and the two ways it
                // does are not joined either. One is a figure to raise and one is work nobody has
                // done, so what outranks the plan is that the offer is incomplete, and what a
                // reader is then told is which of the two made it so.
                // And all of it together where there is more than one, since none is another's
                // absence: a figure refused a candidate, a population was walked in part, a number
                // could not be held, and a reader owed one of them is owed the rest. Kept as the
                // stop alone, the others are lost at the one boundary that had them.
                if (!offer.figures().isEmpty()) {
                    yield new Outcome.Stopped(offer, offered, detail);
                }
                if (!offer.nothing()) {
                    yield new Outcome.Unexhausted(offer, offered, detail);
                }
                // And the third way the offer was short of everything, which is neither of the two
                // above and is not a figure. Every value the search had was tried, so nothing here
                // is a number to raise; what is short is what the position had to give it, and the
                // word says so instead of saying the refusals were the whole story.
                //
                // Of that word and not of every word a search comes back with. What a shortfall
                // here bears on is the claim that the refusals were of everything there was, and
                // the other words claim something else — a reading that settled the position, a
                // walk that put nothing forward — which a value never composed does not touch.
                if (!offered.isEmpty() && why == UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
                    yield new Outcome.OfferShort(offered, detail);
                }
                yield planCut.isEmpty() ? came : new Outcome.Limited(why, detail, planCut);
            }
            // A search a figure stopped already names one, and nothing here turns that into a
            // second account of the same emptiness. A row stands whatever the plan gave up on, and
            // a value nothing planned had no search for this to be about.
            case Outcome.Built _, Outcome.Stopped _, Outcome.Unexhausted _, Outcome.OfferShort _,
                 Outcome.Limited _, Outcome.Unplanned _, Outcome.PassedOver _,
                 Outcome.Halted _ -> came;
        };
    }

    /**
     * What the one edge under this parameter held back, where the refusal is of the values it
     * offered.
     *
     * <p>Values that were never built were not among the ones refused, so what the edge held back
     * is part of why a reader was told nothing could be written. Asked in one place, because every
     * outcome that can come back saying every candidate was refused is owed the same reading —
     * spelled at one of them, the others report a refusal of values that were never offered.
     *
     * <p>Only where one edge offered them. A point of a form fixes several positions under one
     * parameter, and which of their edges the refusal was about is not something this knows; taken
     * from whichever came first, the reason named the wrong position's search.
     */
    private static CompositionShortfall whatTheEdgeHeldBack(
            Map<TermPath, CompositionShortfall> heldBack,
            Map<TermPath, List<FixtureTemplate>> here, UnresolvedCombination.Reason why) {
        if (here.size() != 1 || why != UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return CompositionShortfall.NONE;
        }
        return heldBack.getOrDefault(here.keySet().iterator().next(), CompositionShortfall.NONE);
    }

    /**
     * Whether {@code axis} stands inside a container the rules leave no room in.
     *
     * <p>Asked of the containers the position is inside and not of the position itself: what a rule
     * capping a container at none says is that nothing stands at any position under it, whatever
     * the values there could otherwise be. Asked of every one of them, because a position two
     * containers deep needs each of them to hold something — read off the outermost alone, a list of
     * lists whose inner lists hold nothing was offered rows for what the inner lists hold.
     */
    private static boolean holdsNothing(MeasuredInput subject, Axis axis) {
        for (TermPath inside : axis.path().containersHoldingIt()) {
            // A position of the input, because the axis is at one and a container it stands inside
            // is a position the same reading found on the way down to it.
            if (subject.quantities().mostHeldAt(
                    new souther.compiler.inputs.PositionId(inside)) < 1) {
                return true;
            }
        }
        return false;
    }

    /**
     * From how few to how many the rules let the value built at {@code path} hold.
     *
     * <p>Both ends off one reading of {@code rules}, which is the reading the values are chosen
     * against. A collection built around an element has to meet both — the floor says how many it
     * holds in all, and the cap says whether that many fit — and taken
     * as two readings the two answered about different states of the row.
     */
    private static DeclaredBounds.CountRange heldRange(ConstructionRules rules, TermPath path,
                                                       Type building,
                                                       RuleReadingContext reading) {
        return Partitions.heldRange(building, reading, rules.heldAt(path));
    }

    /**
     * Why a position of this parameter offered less than its rules allow, or nothing where none
     * did.
     *
     * <p>Off the builds the values were chosen from, handed in rather than made again: what
     * building each position's offer met ({@code Choices.met}), what building the values the
     * conditioned pass chose among met ({@link ConditionedCandidates#met}), and what composing the
     * assignments met ({@code Composing.met}). A second build here would be a second answer about
     * the same values, and one that read the rules without what the row fixed would say "every
     * value tried was refused" of a position whose values were never built. A position the caller
     * fixed was given its value and was offered nothing, so it held nothing back.
     *
     * <p>Here and not in what each pass comes back with. A pass says what stopped the pass; what
     * the values it was given were short of is one fact about the offer, and said by a pass it
     * would be said again by every pass that was given them.
     *
     * <p>Every figure each of them met, and not the first or the strongest. Two positions stopped
     * by two budgets are two things this compiler declined to do, and a reader asking what would
     * let the search go further is owed both.
     */
    private static HeldBack heldBack(MeasuredInput subject, ConstructionPlan plan,
                                     Choices choices, ConditionedCandidates candidates,
                                     Composing composing) {
        // And what the rules about the strings at each position left out of what was offered there.
        // Every position's, for the reason every position's figure is here: two positions short of
        // two different things are two things this compiler did not offer, and a reader asking why
        // nothing was taken is owed both.
        return new HeldBack(choices.met().and(candidates.met()).and(composing.met()),
                offeredShortOf(subject, plan), plan.cutBy());
    }

    /**
     * What the rules about each position's strings left out of the offer there, under the position
     * it is about.
     *
     * <p>Under the position, because a reader is being sent to a rule. A row fixes several
     * positions and the rule that composed nothing is written at one of them, so a shortfall
     * gathered into one heap names whichever position the reader guesses.
     *
     * <p>Asked wherever a search came back without a row and not only where no figure was reached.
     * A figure and a rule that composed nothing are two things to act on: an author handed the
     * figure alone raises it and meets the same block, with the rule that gave no value still
     * giving none.
     */
    private static SequencedMap<TermPath, StringOfferShortfall> offeredShortOf(
            MeasuredInput subject, ConstructionPlan plan) {
        SequencedMap<TermPath, StringOfferShortfall> out = new LinkedHashMap<>();
        for (ConstructionPlan.Slot each : plan.slots()) {
            StringOfferShortfall here = Partitions.notOffered(each.type(), subject.ruleReading());
            if (!here.isEmpty()) {
                out.merge(each.at(), here, StringOfferShortfall::and);
            }
        }
        return out;
    }

    /**
     * What a search of this parameter had less of than the point had.
     *
     * <p><b>Two ways of having less, and they are neither one set of budgets nor a choice made
     * here.</b> A position that offered fewer values than its rules allow leaves a search that was
     * not given everything there was to try; a plan that stopped short of a position leaves a
     * search whose answer is about fewer positions than the value has. The figures look alike and
     * what a reader is owed differs, so putting them in one set would leave the only way back being
     * to ask a budget which kind of shortfall it was — and the same figure is either, depending on
     * where it was reached.
     *
     * <p>Which of the two a reader is owed is decided in one place
     * ({@link #whatTheSearchCameTo}) and not here. Decided here as well, the rule would be written
     * twice, and the second reader to learn of a short offer — the one that learns it only after
     * the search came back — would have nowhere to say so.
     *
     * <p><b>Both are this compiler's, and nothing read here says the model refuses anything.</b>
     * What the model settles about a collection with no room for what is placed in it is settled
     * where the plan is made ({@link ConstructionPlan.ModelRefusal.NoRoom}), before any of this
     * ran. Asked again here, it would be asked of a search that had already happened — and
     * whichever answer came back first would be the one a reader got.
     *
     * @param offer   what the offers were short of
     * @param offered what the rules about each position's strings left out of the offer there,
     *                under the position it is about. The same kind of shortfall said in the other
     *                vocabulary: no figure of this compiler's stopped it, and what a reader does
     *                about it is read a rule rather than raise a number
     * @param plan    what the plan was short of. Any of them may be empty, and all being empty is a
     *                search that had the whole of what the point had
     */
    private record HeldBack(CompositionShortfall offer,
                            SequencedMap<TermPath, StringOfferShortfall> offered,
                            Set<CompositionBudget> plan) {

        private HeldBack {
            plan = Set.copyOf(plan);
        }
    }

    /**
     * One parameter's value, chosen a position at a time.
     *
     * <p>Depth first, so that a position is chosen against a projection that already has the ones
     * before it in it. The projection is the same one the whole search started from — what the
     * rules of every value reaching a position leave it — asked again with the assignment so far
     * settled into them ({@link ConstructionRules#limitsAt}).
     *
     * <p>Second, and not instead. What it costs is a reading of the record's rules per position per
     * branch, and the search in front of it answers most rows without any of that; running this one
     * first would spend it on every row to change none of them.
     */
    private static Outcome conditioned(ConstructionPlan plan,
                                       Map<TermPath, List<FixtureTemplate>> decided,
                                       Map<TermPath, Place> settled,
                                       Composing composing, ConditionedCandidates candidates) {
        List<ConstructionPlan.Slot> found = plan.slots();
        // What the caller fixed goes first, so that everything chosen after it is chosen beside it.
        // A class stands for one value and a boundary is one value, and neither is worth deciding
        // after the positions whose range it settles.
        List<ConstructionPlan.Slot> positions = new ArrayList<>(
                found.stream().filter(each -> decided.containsKey(each.at())).toList());
        positions.addAll(
                found.stream().filter(each -> !decided.containsKey(each.at())).toList());
        Budget budget = new Budget();
        ComposedValue built = descend(positions, 0, new LinkedHashMap<>(),
                new LinkedHashMap<>(settled), decided, composing, budget, candidates);
        if (built != null) {
            return new Outcome.Built(built);
        }
        // What the values chosen from met is the offer's, and is said with the offer's.
        return budget.cutShort
                ? new Outcome.Stopped(CompositionShortfall.of(
                        java.util.Set.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES)),
                        new LinkedHashMap<>(), null)
                : new Outcome.Unresolved(UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                        null);
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
     * Every assignment one parameter's search composes, put through one place.
     *
     * <p><b>The bound is spent only on an assignment whose answer is not already known.</b> Two
     * kinds are known without composing them. One holds a value its own type refuses
     * ({@link CandidateCheck#admissibility}), which is refused in every value holding it. The other
     * is one this search already composed and saw refused — the product walk's second pass walks
     * every assignment of its first again before it reaches what was held back, and the conditioned
     * search can arrive at an assignment the product walk tried. Neither is composed, and neither
     * counts against {@link CompositionBudget#ASSIGNMENTS_A_SEARCH_COMPOSES}: what the bound limits
     * is the questions this search had to put to the decoder, and those were not questions.
     *
     * <p>Here and not at each pass, because a pass that asked for itself would be the pass that
     * forgot to. The first assignment a pass tries is asked about like every other.
     *
     * <p>Known by what the assignment writes at each position, and not by the values' trees, for
     * the reason {@code FixturesAtTheBoundary} keeps its answers by text: two occurrences of one
     * named value differ in their trees and write the same thing.
     */
    private static final class Composing {

        private final int parameter;
        private final ConstructionPlan plan;
        private final BehaviorInputs inputs;
        private final RuleReadingContext reading;
        private final CandidateCheck check;
        private final ContentsAsked.Here here;
        private final ContentsAsked.ToHandOn handedOn;
        private final Map<TermPath, Type> typeAt = new HashMap<>();
        private final Set<Map<TermPath, String>> refused = new HashSet<>();

        /** Why each value built and passed over for not holding what two positions are asked to
         *  hold did not, in the order they were built. */
        private final List<String> notHeld = new ArrayList<>();

        /** What the last of those was built as at each position held to another, or null where
         *  none was. */
        private Map<TermPath, FixtureTemplate> lastBuilt;

        /**
         * What of this compiler's composing an assignment met. An assignment a figure kept from
         * being composed was never put to the decoder, so the search that comes back without a row
         * has not had everything it chose refused, and says so with this.
         */
        private CompositionShortfall met = CompositionShortfall.NONE;

        /**
         * Told of every value built and not handed on. Not read here: what the search comes to is
         * said where the parameter's search is answered, beside whatever its alternatives came to,
         * and a value not handed on is said there however the rest of the search went.
         */
        private final FoundOut found;

        Composing(int parameter, ConstructionPlan plan, BehaviorInputs inputs,
                  RuleReadingContext reading, CandidateCheck check, ContentsAsked asked,
                  ContentsAsked.Here here, FoundOut found) {
            this.parameter = parameter;
            this.plan = plan;
            this.inputs = inputs;
            this.reading = reading;
            this.check = check;
            this.here = here;
            this.found = found;
            this.handedOn = asked.handedOnFrom(plan.root().at().head());
            for (ConstructionPlan.Slot each : plan.slots()) {
                typeAt.put(each.at(), each.type());
            }
        }

        /**
         * Whether the value's own type refuses it at {@code at}. False where the plan says no type
         * there: nothing was asked, and nothing unasked is a refusal.
         */
        boolean refusedAlone(TermPath at, FixtureTemplate value) {
            Type type = typeAt.get(at);
            return type != null && check.admissibility(type, value)
                    == CandidateCheck.Admissibility.REFUSED;
        }

        /** What of this compiler's composing the assignments so far met. */
        CompositionShortfall met() {
            return met;
        }

        /** The plan composed against. */
        ConstructionPlan plan() {
            return plan;
        }

        /** What the parameter's positions are asked, with what was handed on put in. */
        ContentsAsked.Here here() {
            return here;
        }

        /** Why each value built and passed over for not holding what two positions are asked to
         *  hold did not; empty where none was. */
        List<String> notHeld() {
            return List.copyOf(notHeld);
        }

        /** What the last value passed over that way was built as at each position held to
         *  another, or null where none was. */
        Map<TermPath, FixtureTemplate> lastBuilt() {
            return lastBuilt;
        }

        /** What putting one assignment to the decoder came to, or that it did not need putting. */
        Tried attempt(Map<TermPath, FixtureTemplate> chosen, Budget budget) {
            Map<TermPath, String> written = new HashMap<>();
            for (Map.Entry<TermPath, FixtureTemplate> each : chosen.entrySet()) {
                if (refusedAlone(each.getKey(), each.getValue())) {
                    return new Tried.Known();
                }
                written.put(each.getKey(), each.getValue().text());
            }
            if (refused.contains(written)) {
                return new Tried.Known();
            }
            if (!budget.spend()) {
                return new Tried.OutOfBudget();
            }
            FromTheAssignment values = new FromTheAssignment(chosen, plan, here);
            Proposals built = compose(plan.root(), values, reading);
            met = met.and(built.met());
            if (built.isEmpty()) {
                refused.add(written);
                return new Tried.Refused();
            }
            FixtureTemplate composed = built.values().getFirst();
            return switch (HandedOn.of(check.build(parameter, composed),
                    () -> values.read(handedOn.positions(), reading), handedOn, inputs, reading)) {
                case HandedOn.Came.Values(var read) -> {
                    // What was built at each position held to another, against what it is held
                    // to. Not the model refusing it: another value of the same classes may hold it.
                    Map<TermPath, FixtureTemplate> builtAt = new LinkedHashMap<>();
                    read.chosen().forEach((at, standing) -> builtAt.put(at, standing.value()));
                    if (here.notHeldBy(builtAt) instanceof String why) {
                        refused.add(written);
                        notHeld.add(why);
                        lastBuilt = builtAt;
                        yield new Tried.NotHeld();
                    }
                    yield new Tried.Built(new ComposedValue(composed, read));
                }
                case HandedOn.Came.Refused _ -> {
                    refused.add(written);
                    yield new Tried.Refused();
                }
                case HandedOn.Came.NotWritable(String why) -> {
                    refused.add(written);
                    found.notHandedOn(why);
                    yield new Tried.NotHandedOn();
                }
            };
        }

        /** What {@link #attempt} came to. */
        sealed interface Tried {

            /** Composed, and the decoder took it. */
            record Built(ComposedValue value) implements Tried {}

            /** Composed, and refused. */
            record Refused() implements Tried {}

            /**
             * Composed and built, and what a container of another parameter is to be handed out
             * of it is nothing this can write — which is not the model refusing it.
             */
            record NotHandedOn() implements Tried {}

            /**
             * Composed and built, and not holding one value with another position, or two, as
             * the way asks — which is not the model refusing it either.
             */
            record NotHeld() implements Tried {}

            /** Known refused without composing it, so nothing was spent. */
            record Known() implements Tried {}

            /** Not composed, because the bound is spent. */
            record OutOfBudget() implements Tried {}
        }
    }

    /**
     * The assignment this branch leads to, or null where none of them builds.
     *
     * @param chosen  what the positions before this one took
     * @param settled the numbers among them, which is what a projection can be asked about
     * @param budget  assignments left to compose, shared down the whole search
     * @param candidates what a position can take under a settling, shared down the whole search
     */
    private static ComposedValue descend(List<ConstructionPlan.Slot> positions, int index,
                                           Map<TermPath, FixtureTemplate> chosen,
                                           Map<TermPath, Place> settled,
                                           Map<TermPath, List<FixtureTemplate>> decided,
                                           Composing composing, Budget budget,
                                           ConditionedCandidates candidates) {
        if (index == positions.size()) {
            return composing.attempt(chosen, budget) instanceof Composing.Tried.Built(var value)
                    ? value : null;
        }
        ConstructionPlan.Slot position = positions.get(index);
        TermPath where = position.at();
        for (FixtureTemplate candidate
                : candidatesAt(position, settled, decided, candidates)) {
            // Refused by its own type, so refused in every assignment under this branch: the branch
            // is not walked ({@link Composing} says why).
            if (composing.refusedAlone(where, candidate)) {
                continue;
            }
            chosen.put(where, candidate);
            Place number = Counts.writtenIn(candidate.value());
            if (number != null) {
                settled.put(where, number);
            }
            ComposedValue found = descend(positions, index + 1, chosen, settled,
                    decided, composing, budget, candidates);
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
    private static List<FixtureTemplate> candidatesAt(ConstructionPlan.Slot position,
                                                      Map<TermPath, Place> settled,
                                                      Map<TermPath, List<FixtureTemplate>> decided,
                                                      ConditionedCandidates candidates) {
        List<FixtureTemplate> fixed = decided.get(position.at());
        if (fixed != null) {
            return fixed;
        }
        return candidates.at(position, settled);
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
     * @param met       what of this compiler's building the positions' offers met. Taken from the
     *                  build that made {@code values}, so that what a reader is told the offer was
     *                  short of is that build's own answer and not a second build's
     */
    private record Choices(ConstructionPlan plan, List<TermPath> at,
                           List<List<FixtureTemplate>> values,
                           List<List<FixtureTemplate>> reserves, String missingAt,
                           TermPath leftNothingAt,
                           Set<CompositionBudget> missingUnderAFigure,
                           List<Displacing> displacing, CompositionShortfall met) {

        Choices {
            missingUnderAFigure = Set.copyOf(missingUnderAFigure);
            displacing = Collections.unmodifiableList(new ArrayList<>(displacing));
        }

        static Choices missing(ConstructionPlan plan, String at,
                               Set<CompositionBudget> under, CompositionShortfall met) {
            return new Choices(plan, List.of(), List.of(), List.of(), at, null, under, List.of(),
                    met);
        }

        /** None, because the rules leave the position {@code at} no value under what this plan
         *  was made with. */
        static Choices leavingNothingAt(ConstructionPlan plan, TermPath at) {
            return new Choices(plan, List.of(), List.of(), List.of(),
                    "the rules leave no value at `" + at + "`", at, Set.of(), List.of(),
                    CompositionShortfall.NONE);
        }

        /**
         * The same positions, each offering beside what it holds back the value its rules leave
         * next to the first — or, at a position an axis decides, what the axis decided.
         *
         * <p>Worked out only when asked. Nothing refused a value here: every value the positions
         * offered was composed and passed over, so what is wanted is a different value and not a
         * value the rules allow more readily. Asked of every search, this would be a reading of
         * every position's rules for the one search that wants it.
         */
        List<List<FixtureTemplate>> displaced(RuleReadingContext reading) {
            List<List<FixtureTemplate>> out = new ArrayList<>();
            for (int i = 0; i < values.size(); i++) {
                Displacing slot = displacing.get(i);
                if (slot == null) {
                    out.add(values.get(i));
                    continue;
                }
                List<FixtureTemplate> here = new ArrayList<>(values.get(i));
                // What building these met is what building the position's offer met, which
                // {@link #met} already holds.
                for (FixtureTemplate each : Partitions.displacedRepresentativesOf(slot.type(),
                        reading, slot.limits()).values()) {
                    if (here.stream().noneMatch(had -> had.text().equals(each.text()))) {
                        here.add(each);
                    }
                }
                out.add(List.copyOf(here));
            }
            return List.copyOf(out);
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
     * @param left    the rules of every value reaching a position, with what the caller settled
     *                taken in — the reading the plan was made against, handed over rather than read
     *                again, since the two are one reading and a second one would be the same
     *                declarations worked out twice for every point
     */
    private static Choices choicesOf(MeasuredInput subject, ConstructionPlan plan,
                                     Map<TermPath, List<FixtureTemplate>> decided,
                                     ConstructionRules left) {
        RuleReadingContext reading = subject.ruleReading();
        List<TermPath> paths = new ArrayList<>(decided.keySet());
        List<List<FixtureTemplate>> values = new ArrayList<>(decided.values());
        // A position the caller fixed holds nothing back: it was given the value it is to take.
        List<List<FixtureTemplate>> reserves = new ArrayList<>(
                java.util.Collections.nCopies(paths.size(), List.<FixtureTemplate>of()));
        // And is not displaced either, for the same reason.
        List<Displacing> displacing =
                new ArrayList<>(Collections.nCopies(paths.size(), (Displacing) null));
        CompositionShortfall met = CompositionShortfall.NONE;
        for (ConstructionPlan.Slot slot : plan.slots()) {
            if (paths.contains(slot.at())) {
                continue;   // an axis decides here
            }
            FieldDomains.ConstructionLimits limits = left.limitsAt(slot.at());
            NumericDomain.Bounds here = limits.values();
            // A position the rules leave no value at, under the narrowings this plan was made with
            // and what the caller settled: no value is offered, and that is said as itself.
            if (limits.leavesNothing()) {
                return Choices.leavingNothingAt(plan, slot.at());
            }
            Proposals stands = subject.representativesHolding(slot.type(), limits);
            met = met.and(stands.met());
            if (stands.isEmpty()) {
                // Nothing could be written at all: a position of a type nothing stands for. Which is
                // not the same as a value that was written and refused, and reporting it as one sends
                // the author looking for a rule relating two inputs that has nothing to do with it.
                //
                // And where this is a position the plan stopped short at, nothing standing for it is
                // that decision rather than a fact about the model: what such a position is offered
                // is whole values of a type this declined to look inside. Read off the plan's own
                // leaf and not off whether the plan was cut anywhere, so a figure reached at one
                // position is never the reason given for another having nothing — and for the same
                // reason, what building the offer met is this position's own.
                return Choices.missing(plan, slot.at() + ": " + Type.show(slot.type()),
                        slot.leaf() instanceof ConstructionPlan.Leaf.Beneath(var cutBy)
                                ? cutBy : Set.of(), stands.met());
            }
            paths.add(slot.at());
            values.add(stands.values());
            reserves.add(Partitions.inReserve(slot.type(), reading, here, stands.values()));
            displacing.add(new Displacing(slot.type(), limits));
        }
        return new Choices(plan, paths, values, reserves, null, null, Set.of(), displacing, met);
    }

    /** What a position's value is displaced within: its type, and what its rules leave of it. */
    private record Displacing(Type type, FieldDomains.ConstructionLimits limits) {}

    /**
     * A row stands at no class of this axis.
     *
     * <p>Not a class this could not choose. A position under a narrowing the row does not meet is
     * one the row is not at — the reading of a written row says the same of it, standing nowhere
     * below a case it is not — so the assignment has nothing to say there and says that.
     */
    private static final int NOT_HERE = -1;

    /**
     * Where every position stands for a row about the class at {@code at}, keeping what
     * {@code from} put at the positions that can keep it.
     *
     * <p>The row is about one class, so what it requires is settled first and everything else is
     * chosen beside it. A position whose own narrowing the row does not meet stands at no class of
     * it — offered its first class regardless, every row about a class under one case of a sum
     * would ask to be another case as well, and none of them would be composed.
     *
     * @return which axis the row is about, or {@link #NOT_HERE} where it is about none
     */
    private static int[] standing(WhatEachClassRequires requires, int[] from, int[] anchors) {
        return standing(requires, from, anchors, (_, _) -> true);
    }

    /** Whether {@code cls} at {@code axis} and a class already standing in {@code where} leave
     *  each other no room ({@link WhatEachClassRequires#leaveNoRoom}). */
    private static boolean leavesNoRoomBeside(WhatEachClassRequires requires, int[] where,
                                              int axis, int cls) {
        for (int other = 0; other < where.length; other++) {
            if (other != axis && where[other] != NOT_HERE
                    && requires.leaveNoRoom(axis, cls, other, where[other])) {
                return true;
            }
        }
        return false;
    }

    /**
     * The same preference, with {@code cls} put at {@code at}.
     *
     * <p>What a row about one class starts from: the class it is for, and whatever an origin put at
     * the positions beside it.
     */
    private static int[] wanting(List<Axis> axes, int[] from, Interpretation reading) {
        int[] wanted = new int[axes.size()];
        java.util.Arrays.fill(wanted, NOT_HERE);
        if (from != null) {
            System.arraycopy(from, 0, wanted, 0, Math.min(from.length, wanted.length));
        }
        for (int i = 0; i < axes.size(); i++) {
            if (reading.pins().containsKey(i)) {
                wanted[i] = reading.pins().get(i);
            }
        }
        return wanted;
    }

    /** Which classes of a position something outside the requirements will have. */
    private interface Admits {

        boolean at(int axis, int cls);
    }

    /**
     * The same, among the classes {@code admits} allows — which is what a cell of the body's own
     * combinations leaves at each position.
     *
     * <p>Null where the anchors cannot be in one value, which is not an assignment that failed but a
     * combination the model does not have.
     *
     * @param anchors which positions the assignment is about, in the order they are settled. They
     *                take the class {@code from} gives them and keep it; everything else is chosen
     *                beside them. The one place a preference becomes a legal assignment: a caller
     *                counting classes off produces what it would like, and this is what says which
     *                of it a value can be
     */
    private static int[] standing(WhatEachClassRequires requires, int[] from, int[] anchors,
                                  Admits admits) {
        List<Axis> axes = requires.axes;
        int[] where = new int[axes.size()];
        java.util.Arrays.fill(where, NOT_HERE);
        // What the row is about, settled before anything is chosen beside it. A class never
        // contradicts its own position: what a path requires is required at the positions above it,
        // and what a class selects is selected at the position itself.
        Requirements required = Requirements.NONE;
        for (int at : anchors) {
            if (from == null || from[at] == NOT_HERE) {
                continue;
            }
            if (leavesNoRoomBeside(requires, where, at, from[at])) {
                return null;
            }
            where[at] = from[at];
            if (!(required.merge(axes.get(at).requiring(axes.get(at).classes().get(from[at])))
                    instanceof Requirements.Merge.Merged merged)) {
                return null;
            }
            required = merged.requirements();
        }
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] != NOT_HERE || anchored(anchors, i)) {
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
            // And beside what already stands: a class leaving a container nothing to hold is no
            // class beside one inside it, and a position with no class that can be beside them
            // takes none.
            int kept = from != null && i < from.length && from[i] != NOT_HERE
                    && admits.at(here, from[i])
                    && soFar.compatibleWith(axis.requiring(axis.classes().get(from[i])))
                    && !leavesNoRoomBeside(requires, where, here, from[i])
                    ? from[i]
                    : standingAt(axis, c -> admits.at(here, c) && soFar.compatibleWith(
                            axis.requiring(axis.classes().get(c)))
                            && !leavesNoRoomBeside(requires, where, here, c));
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
     * What a caller makes of each value the walk over one parameter's assignments composes.
     *
     * <p>The walk's order is the walk's and what is wanted is the caller's. A value the model takes
     * is handed over as soon as it is composed; one the caller passes over leaves the walk going on
     * to the next assignment, nearest first, as a refused one does — and what the caller wants is
     * never read into which assignments there are.
     */
    @FunctionalInterface
    private interface ValueTaking {

        Acceptance take(ComposedValue value);
    }

    /**
     * One parameter's value as composed, and what stands at the positions of it another
     * container is handed.
     *
     * <p>Both, because the second is of the first: a container under another parameter that is to
     * hold the value at one of this one's positions holds what this value has there. Read where it
     * is built ({@link Composing#attempt}), off what the boundary built, and carried with it: the
     * text of the value is what a row writes, and is not what a position of it is once built.
     *
     * @param value the parameter's value
     * @param read  what stands at each position of it another parameter's container is handed
     */
    private record ComposedValue(FixtureTemplate value, ValuesHandedOn read) {}

    /**
     * What came of trying the assignments for one parameter: its value, or why there is none.
     *
     * <p><b>Four states and not a record whose fields make them.</b> Held as a value beside a
     * reason beside a set of budgets, what may stand with what was something every reader worked
     * out again, and the arm that had to be added here is one whose fields overlap two of the
     * others. Written as arms, a reader that has one of them has everything that arm carries and
     * nothing that belongs to another.
     */
    private sealed interface Outcome {

        /** A value was composed, and the caller took it. */
        record Built(ComposedValue composed) implements Outcome {}

        /**
         * Values were composed, and the caller passed over every one of them.
         *
         * <p>Not a refusal. Each was a value the model takes, and what it was not is the value the
         * caller was looking for — so nothing here is said about the position, and the search
         * having run to its end is no claim that no such value exists.
         */
        record PassedOver() implements Outcome {}

        /** The caller stopped the search, having run out of what deciding costs it. */
        record Halted() implements Outcome {}

        /** None was, and no figure of this compiler's is why. */
        record Unresolved(UnresolvedCombination.Reason why, String detail) implements Outcome {}

        /**
         * Every value the search was given was refused, and it was not given everything the
         * position had.
         *
         * <p>Beside {@link Unresolved} and not a shape of it. That one is a search whose answer is
         * about what it looked at and about everything there was to look at; here a rule about the
         * position composed nothing, so the two are the same refusals and not the same news.
         *
         * <p>Beside {@link Stopped} as well, and the difference is what a reader does. A stopped
         * search was holding a value a figure had no room for; nothing was held back here — the
         * value was never worked out, and there is no number over the search that reaches it.
         *
         * @param offered what the rules about each position's strings left out of the offer there,
         *                under the position it is about
         * @param detail  where the search was, in the words the rest of these use
         */
        record OfferShort(SequencedMap<TermPath, StringOfferShortfall> offered, String detail)
                implements Outcome {

            public OfferShort {
                if (offered.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an offer short of the rules says which rule it was short of");
                }
                offered = new LinkedHashMap<>(offered);
            }
        }

        /**
         * A search this compiler stopped before it had tried what it held.
         *
         * <p>No word of its own, because the word such a search comes back with is the budgets' to
         * say and is read off them wherever it is wanted. Kept here as well, the two could part.
         */
        record Stopped(CompositionShortfall met,
                       SequencedMap<TermPath, StringOfferShortfall> offered,
                       String detail) implements Outcome {

            public Stopped {
                offered = new LinkedHashMap<>(offered);
                if (met.figures().isEmpty()) {
                    throw new IllegalArgumentException(
                            "a search this compiler stopped says which figure stopped it");
                }
            }

            /** The word a search these stopped comes back with. */
            UnresolvedCombination.Reason why() {
                return UnresolvedCombination.Reason.wordFor(met.figures());
            }
        }

        /**
         * A search that ran through everything this compiler writes, which is not everything there
         * is.
         *
         * <p><b>Beside {@link Stopped} and never a shape of it.</b> A stopped search was holding a
         * candidate a figure had no room for, and raising the figure tries it. Nothing was refused
         * here: what this compiler writes ran out, and what reaches the rest is somebody writing
         * more of it. Held as one, a reader is sent to raise a number that changes nothing.
         *
         * <p>The word is the same word, and that is not the two being one thing. What a reader
         * concludes is alike — the point is open because this compiler did not look at everything —
         * and what closes it is not, which is why the populations travel rather than the word alone.
         *
         * <p>A number the search could not hold is here too, and for the same reason: nothing was
         * refused and nothing is there to raise. What reaches it is a host with more room where
         * room ran out, and nothing where no representation of the number exists.
         */
        record Unexhausted(CompositionShortfall met,
                           SequencedMap<TermPath, StringOfferShortfall> offered, String detail)
                implements Outcome {

            public Unexhausted {
                offered = new LinkedHashMap<>(offered);
                if (!met.figures().isEmpty() || met.nothing()) {
                    throw new IllegalArgumentException(
                            "a search that says it saw some of them, or could not hold a number,"
                                    + " says which, and names no figure: " + met);
                }
            }

            /** The word such a search comes back with, which says the point is open on this
             *  compiler and names nothing to raise. */
            UnresolvedCombination.Reason why() {
                return UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;
            }
        }

        /**
         * No search was run: the value could not be planned.
         *
         * <p>No word, because a word here is a search's answer and none was made. The one thing
         * known is which figure left the plan unable to reach what the caller asked for, and
         * whoever turns this into an account says so in words about a search that did not happen.
         *
         * <p>Apart from {@link Limited} for the same reason it is apart at the account: the two
         * leave a reader the same work and did not happen the same way, and an outcome that held
         * both would have the history recoverable only from which fields were filled in.
         */
        record Unplanned(Set<CompositionBudget> by) implements Outcome {

            public Unplanned {
                by = Set.copyOf(by);
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a value nothing planned says which figure left it unplanned");
                }
            }
        }

        /**
         * The search came to an answer of its own, and that answer is not the whole of what there
         * was to look at.
         *
         * <p><b>Both halves are its own information, which is what tells this from {@link
         * Stopped}.</b> A stopped search has no outcome but the stopping, so its word follows from
         * the budgets. Here the search ran to the end of what it was given and said what it found —
         * every candidate refused, or nothing composed — and separately the thing it was given was
         * short. Neither half is recoverable from the other, so no rule relates {@code why} to
         * {@code by} and none may be written: a figure that stops no search has no word, and asking
         * these budgets for one is what refuses to answer.
         *
         * <p>What a reader is owed is the ordinary word and the figure both. Told only the word, a
         * point this compiler declined to plan for is counted as one the model admits no row at;
         * told only the figure, a reader is looking for a search that never stopped.
         */
        record Limited(UnresolvedCombination.Reason why, String detail,
                       Set<CompositionBudget> by) implements Outcome {

            public Limited {
                by = Set.copyOf(by);
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an answer short of what there was says which figure made it short");
                }
            }
        }
    }

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
    private static Outcome walk(Choices choices, Composing composing, ValueTaking taking,
                                RuleReadingContext reading) {
        Outcome walked = ordinarily(choices, composing, taking);
        // And where every value composed was passed over, once more with each position displaced
        // to the value its rules leave next to its first. What was looked for is a different value,
        // and the ordinary offer is one value at a position whose rules leave it a whole range.
        if (!(walked instanceof Outcome.PassedOver)) {
            return walked;
        }
        Outcome displaced = over(choices.at(), choices.displaced(reading), composing, taking);
        return displaced instanceof Outcome.Unresolved(UnresolvedCombination.Reason why, String _)
                && why == UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED ? walked : displaced;
    }

    /** The ordinary passes: what the positions offer, and then what they held back as well. */
    private static Outcome ordinarily(Choices choices, Composing composing, ValueTaking taking) {
        Outcome tried = over(choices.at(), choices.values(), composing, taking);
        // Only where the ordinary assignments ran out. A search that stopped at the bound has not
        // tried them all, and starting a wider one in front of the ones it never reached would spend
        // what is left on assignments further from what the model says the row is about, while the
        // nearer ones stay untried.
        //
        // Ran out with every value passed over is ran out as well: what the caller is looking for
        // was not among what the positions ordinarily offer, which is what holding something back
        // is for.
        boolean ranOut = tried instanceof Outcome.PassedOver
                || (tried instanceof Outcome.Unresolved(UnresolvedCombination.Reason why,
                        String _) && why == UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED);
        if (!ranOut || !choices.anythingHeldBack()) {
            return tried;
        }
        // The assignments of the first pass are all in this one too, nearest first, and each is
        // known refused: the second pass reaches what was held back without spending on them.
        Outcome widened = over(choices.at(), choices.widened(), composing, taking);
        // Passed over in the first pass and refused in the second is still a pass that composed
        // values the model takes, and saying every candidate was refused would be saying it did not.
        return tried instanceof Outcome.PassedOver
                && widened instanceof Outcome.Unresolved(UnresolvedCombination.Reason why,
                        String _) && why == UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED
                ? tried : widened;
    }

    /**
     * One pass over one set of choices, from the assignment where every position takes its first
     * value outward.
     *
     * <p><b>The positions are walked over what their own types do not refuse.</b> A value its type
     * refuses is refused in every assignment holding it ({@link Composing}), so the walk is over
     * the product of what is left, nearest first in that product. Walked over everything offered
     * instead, those assignments would only be passed over, but every one of them would still be
     * enumerated on the way to the rest — as many as the product of the offers, which the bound
     * does not limit because nothing was composed.
     *
     * <p>Narrowed only once the first assignment is refused. Most searches end at it, and asking
     * about the first assignment's own values, which {@link Composing#attempt} does, is all they
     * need.
     *
     * <p>A position left with nothing is every assignment refused, and is said as that: the values
     * were offered and refused, which is not a position nothing could be offered at.
     */
    private static Outcome over(List<TermPath> at, List<List<FixtureTemplate>> offered,
                                Composing composing, ValueTaking taking) {
        int positions = at.size();
        Budget budget = new Budget();
        int[] first = new int[positions];
        // Whether some value was composed and passed over, which is what tells a walk that ran out
        // of values the model takes from one that ran out of values the caller takes.
        boolean passed = false;
        if (composing.attempt(assigned(at, offered, first), budget)
                instanceof Composing.Tried.Built(var value)) {
            switch (taking.take(value)) {
                case TAKEN -> {
                    return new Outcome.Built(value);
                }
                case STOPPED -> {
                    return new Outcome.Halted();
                }
                case PASSED -> passed = true;
            }
        }
        List<List<FixtureTemplate>> values = new ArrayList<>();
        for (int i = 0; i < positions; i++) {
            TermPath here = at.get(i);
            values.add(offered.get(i).stream()
                    .filter(each -> !composing.refusedAlone(here, each)).toList());
        }
        if (values.stream().anyMatch(List::isEmpty)) {
            return passed ? new Outcome.PassedOver()
                    : new Outcome.Unresolved(UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                            null);
        }
        ArrayDeque<int[]> next = new ArrayDeque<>();
        Set<String> seen = new LinkedHashSet<>();
        next.add(first);
        seen.add(Arrays.toString(first));
        // The values already handed to the caller, by how they are written. The walk below starts
        // again from the first assignment over what is left, which composes the value the caller
        // has just passed over, and asking it twice is a second run for the same answer.
        Set<List<String>> handed = new LinkedHashSet<>();
        if (passed) {
            handed.add(writtenAs(assigned(at, offered, first)));
        }

        // Recorded where the bound is reached rather than read afterwards off what was left behind.
        // A walk that stopped and a walk that ran out are told apart by the queue today and would go
        // on being told apart by it until the day a second thing empties it.
        boolean stopped = false;
        while (!next.isEmpty()) {
            int[] assignment = next.poll();
            Map<TermPath, FixtureTemplate> chosen = assigned(at, values, assignment);
            switch (composing.attempt(chosen, budget)) {
                case Composing.Tried.Built(var value) -> {
                    if (handed.add(writtenAs(chosen))) {
                        switch (taking.take(value)) {
                            case TAKEN -> {
                                return new Outcome.Built(value);
                            }
                            case STOPPED -> {
                                return new Outcome.Halted();
                            }
                            case PASSED -> passed = true;
                        }
                    }
                }
                case Composing.Tried.OutOfBudget _ -> stopped = true;
                case Composing.Tried.Refused _, Composing.Tried.NotHandedOn _,
                     Composing.Tried.NotHeld _, Composing.Tried.Known _ -> { }
            }
            if (stopped) {
                break;
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
        // Nothing left to try is every assignment refused; a bound reached is the search having
        // stopped, and the difference is what the reader is owed. Neither carries a detail: what
        // these are about is the combination, and a detail is read as the position that is the fact
        // behind several of them.
        if (stopped) {
            return new Outcome.Stopped(CompositionShortfall.of(
                    Set.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES)),
                    new LinkedHashMap<>(), null);
        }
        return passed ? new Outcome.PassedOver()
                : new Outcome.Unresolved(UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                        null);
    }

    /** An assignment as the values it puts at each position are written, in the positions' order. */
    private static List<String> writtenAs(Map<TermPath, FixtureTemplate> chosen) {
        List<String> out = new ArrayList<>();
        chosen.forEach((at, value) -> out.add(at + "=" + value.text()));
        return out;
    }

    /** What one assignment puts at each position. */
    private static Map<TermPath, FixtureTemplate> assigned(List<TermPath> at,
                                                          List<List<FixtureTemplate>> values,
                                                          int[] assignment) {
        Map<TermPath, FixtureTemplate> chosen = new LinkedHashMap<>();
        for (int i = 0; i < at.size(); i++) {
            chosen.put(at.get(i), values.get(i).get(assignment[i]));
        }
        return chosen;
    }

    /**
     * The value at one position of the plan: what the assignment chose there, or a record built out
     * of the positions under it.
     *
     * <p>Nothing where the assignment put nothing at a position the plan asks for one at, where a
     * name this module cannot write leaves no value to write, and where a container the plan fills
     * is past a figure of this compiler's — which last is said by what comes back with it. The walk
     * that collected the choices and this one read this plan's positions, so the two cannot
     * disagree about where they are.
     *
     * <p>What was built is handed back to the recipe that said how to build it, which puts on the
     * names the position writes its values under. The composing and the writing are one recipe
     * because they are one fact about the position: a class of {@code data DecisionN = Decision}
     * composes an {@code Approved} and the row carries {@code DecisionN(Approved { id = 1 })}.
     * Composed without that, the row carries a value of a type the parameter does not declare.
     */
    private static Proposals compose(ConstructionPlan.Node node, FromTheAssignment values,
                                     RuleReadingContext reading) {
        return PlanComposer.compose(node, values, reading);
    }

    /**
     * What one parameter's containers are handed when it is composed: what is asked of them, and
     * what the parameters composed before it came to at the positions a value is read at.
     *
     * @param asked     what the way asks of containers' contents, for every parameter
     * @param elsewhere what stands at a position of another parameter, where that one was composed
     *                  before this
     */
    private record Handed(ContentsAsked asked, ValuesHandedOn elsewhere) {}

    /**
     * The values of a plan as the search's assignment settled them.
     *
     * <p>Every position of the plan is one the search chose at, so every field of a record is
     * composed from what stands under it and nothing here reads a rule. What is left where a
     * position has nothing is nothing: a row missing a value the plan asks for is not a row.
     *
     * <p>A value a container is handed is what stands at its position: composed out of this
     * assignment where the position is of this value, and what the parameter it is of was composed
     * as where it is of another.
     */
    private record FromTheAssignment(Map<TermPath, FixtureTemplate> chosen,
                                     ConstructionPlan plan, ContentsAsked.Here here)
            implements PlanComposer.Values {

        @Override
        public Proposals at(ConstructionPlan.Slot slot) {
            return Proposals.ofNullable(chosen.get(slot.at()));
        }

        @Override
        public ContainerContents contentsOf(TermPath container, PlanComposer.Under under) {
            return here.contentsOf(container, value -> {
                ConstructionPlan.Node node = plan.at(value);
                if (node == null) {
                    return null;
                }
                Proposals composed = under.of(node);
                return composed.isEmpty() ? null : composed.values().getFirst();
            });
        }

        /**
         * What the assignment puts at each of {@code positions}, leaving out a position nothing
         * composes.
         *
         * <p>What a value hands on where nothing built it, and only then: built, what stands at a
         * position of it is read off what the boundary built ({@link Composing#attempt}).
         */
        Map<TermPath, FixtureTemplate> read(Set<TermPath> positions, RuleReadingContext reading) {
            Map<TermPath, FixtureTemplate> out = new LinkedHashMap<>();
            for (TermPath each : positions) {
                ConstructionPlan.Node node = plan.at(each);
                Proposals value = node == null ? Proposals.NONE : compose(node, this, reading);
                if (!value.isEmpty()) {
                    out.put(each, value.values().getFirst());
                }
            }
            return out;
        }

        @Override
        public Partitions.FieldsChosen under(ConstructionPlan.Built built,
                                             PlanComposer.Under under) {
            SequencedMap<String, FixtureTemplate> fields = new LinkedHashMap<>();
            CompositionShortfall met = CompositionShortfall.NONE;
            for (Map.Entry<String, ConstructionPlan.Node> each : built.under().entrySet()) {
                Proposals value = under.of(each.getValue());
                met = met.and(value.met());
                if (value.isEmpty()) {
                    return new Partitions.FieldsChosen(null, met);
                }
                fields.put(each.getKey(), value.values().getFirst());
            }
            return new Partitions.FieldsChosen(fields, met);
        }
    }

    /**
     * What a row is to carry where a boundary is drawn: the values to try there, why there are none
     * where there are none, and the number the position itself is thereby settled at.
     *
     * <p>The last is a number only sometimes. A line on the content of a location settles that
     * location at it, and what the rest of the record may hold is read from the rules relating them;
     * a line on a count taken of a location settles no number inside it, and saying it did would tell
     * the rest of the row that a string's length is the number the string holds.
     *
     * <p>The orders the values were built against are not among them. Reading a value back asks the
     * same question building it asked, and the reading is what answers it both times — kept here,
     * an answer would travel from the one to the other and the two would be free to part.
     *
     * @param writtenAt the type of what is written where the values go, as the walk that follows
     *                  one answered it — null where it answered none and nothing was composed.
     *                  Carried so that a reader of the values asks their type's decoder of them
     *                  without asking that walk a second time
     */
    record Edge(TermRealizations.Realization came, Place settledAt, Type writtenAt) {

        static Edge none(UnresolvedCombination.Reason why) {
            return new Edge(new TermRealizations.Realization.None(why), null, null);
        }

        List<FixtureTemplate> values() {
            return came instanceof TermRealizations.Realization.Built built
                    ? built.values() : List.of();
        }

        /**
         * What this edge found, beside the word, or null where it has nothing to add.
         *
         * <p>Carried from the walk that composed nothing rather than worked out here. Two walks
         * come back with one word and what they met differs, and a reader left with the word alone
         * would be telling them apart by what the sentence does not say.
         *
         * <p>A sentence, so what an account carries it as is what the point said, and never the
         * position several combinations share ({@link UnresolvedCombination#detail()}).
         */
        String said() {
            return switch (came) {
                case TermRealizations.Realization.None none -> none.detail();
                case TermRealizations.Realization.Unexhausted some -> some.detail();
                case TermRealizations.Realization.Built _,
                     TermRealizations.Realization.Stopped _,
                     TermRealizations.Realization.NoNumberTheDeclarationsAdmit _ -> null;
            };
        }

        /**
         * What this edge met of this compiler's, as the account a caller carries beside the word.
         *
         * <p>Every vocabulary in one value because that is what an account of an attempt holds,
         * and none is read for another on the way in: {@link CompositionShortfall} keeps the
         * figures somebody could raise apart from the populations nobody has written the rest of
         * and the numbers only a host with more room, or nothing, would hold.
         */
        CompositionShortfall met() {
            return came.shortfall();
        }

        /**
         * Whether the rules were shown to leave no number at what this edge was asked, which is
         * about the model and about the combination this edge ran at.
         *
         * <p>Asked rather than read off {@link #reason()}, which says what this compiler composed
         * and says it to every reader. Whether what was shown about the numbers settles what
         * somebody is owed a row at turns on what is owed, so the one reader for which the two are
         * the same question asks for it and the rest are not handed it.
         */
        boolean settlesTheQuestion() {
            return came instanceof TermRealizations.Realization.NoNumberTheDeclarationsAdmit;
        }

        /** What to report where no value was offered here at all. */
        UnresolvedCombination.Reason reason() {
            return switch (came) {
                case TermRealizations.Realization.None none -> none.why();
                case TermRealizations.Realization.Stopped stopped ->
                        UnresolvedCombination.Reason.wordFor(stopped.met().figures());
                // The same word a figure comes back with, and for the same reason a reader has: the
                // point is open because this compiler did not look at everything, not because the
                // model answered. What differs is what would close it, which is the sentence beside
                // the word and not the word.
                case TermRealizations.Realization.Unexhausted _ ->
                        UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;
                // Nothing was composed, which is what every caller of this may take from it. That
                // the rules were shown to leave no number is about the combination this edge ran
                // at, and whether that settles what somebody is owed a row at turns on what is
                // owed — so it is asked for ({@link #settlesTheQuestion()}) by the reader that
                // knows, and is not carried in a word every reader takes.
                case TermRealizations.Realization.NoNumberTheDeclarationsAdmit _ ->
                        UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE;
                case TermRealizations.Realization.Built _ -> throw new IllegalStateException(
                        "an edge that offered values asked why it offered none");
            };
        }

        /**
         * What an edge that offered nothing comes to, as the outcome an account is handed.
         *
         * <p><b>Which arm it is decided here and nowhere else.</b> An edge is short of everything
         * there is in as many vocabularies as {@link CompositionShortfall} holds, and a caller
         * choosing the arm by asking one of them whether it is empty is a caller that has to be
         * taught every vocabulary there will ever be, and silently drops the ones it was not.
         * Asked of the shortfall whole, a vocabulary added travels in it rather than being a
         * silence at every caller.
         *
         * <p>The figures first, because only they name something anybody could raise; the rest
         * travels with them all the same, since a stop does not make it untrue.
         *
         * @param ofWhatThePointFixes whether every number this edge was composed for stands where
         *                            the point put it, and none where a condition on the way chose
         *                            to. Only then is what composing settled about the numbers
         *                            about the point: a number a condition chose is one the rules
         *                            did not force, and that it leaves nothing is that choice's
         */
        BoundaryAttempt cameToNothing(String label,
                                      CompositionAccount unrepresented,
                                      boolean ofWhatThePointFixes) {
            CompositionShortfall met = met();
            if (!met.figures().isEmpty()) {
                return BoundaryAttempt.Stopped.at(label, said(), met, unrepresented);
            }
            if (!met.nothing()) {
                return BoundaryAttempt.Unexhausted.at(label, said(), met, unrepresented);
            }
            // A row at a point is one row at one thing somebody is owed, and this edge is the
            // search for it — so what the search settled about the numbers is what the point comes
            // to. Which is the one place the proof is published, because it is the one place where
            // what was walked and what is owed are the same question.
            return new BoundaryAttempt.Unresolved(
                    UnresolvedCombination.atAPoint(label,
                            settlesTheQuestion() && ofWhatThePointFixes
                                    ? UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE
                                    : reason(),
                            said()),
                    unrepresented);
        }

    }

    /**
     * One realization as an edge of the search.
     *
     * <p>Where the root itself is settled, and where it is not. A term that is a location's content
     * is fixed at the place the line was drawn on; a term that is what an operation answered leaves
     * the root free, since the number is not what stands there — so what the search records as
     * settled is the one and not the other. The one question here the variant genuinely settles, and
     * asked of the variant.
     *
     * <p>A location asked for several numbers settles at none of them. What is settled is a place on
     * the root's own order, and a group is over numbers taken of the root — which numbers go in one
     * group is {@link TermRealizations#jointRealizationOf}, and the content of the location is not
     * among the ones it puts together.
     */
    private static Edge edgeFrom(TermRealizations.Realization made,
                                 SequencedMap<RealizationTarget, AskedAt> group, Type writtenAt) {
        if (group.size() != 1) {
            return new Edge(made, null, writtenAt);
        }
        Place settled = switch (group.firstEntry().getKey()) {
            // And only where the set asked for is one number. A class admits a run of them, so what
            // a row written for one stands at is whichever of them the value was built at — which
            // is the composer's answer and not something this could read off the question.
            case RealizationTarget.OfANumber number -> switch (number.term()) {
                case NumericTerm.ValueOf _ ->
                        group.firstEntry().getValue().walking() instanceof NumericSet.At one
                                ? one.value() : null;
                // What an operation answered is not what its root holds — three characters is not
                // the position standing at three, and a hundred is not what the list adding up to
                // it holds. Nor is how many of a string's code points are in a class, what they
                // come to, or how often a value occurs among the elements beside it, or the end of
                // the values of a key, which another element of the key may hold.
                case NumericTerm.TakenOf _, NumericTerm.CodePointClassCount _,
                     NumericTerm.CodePointValueSum _, NumericTerm.CodePointAt _,
                     NumericTerm.WholeUnitsOf _, NumericTerm.Multiplicity _,
                     NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                     NumericTerm.TakenOver _, NumericTerm.ExtremeOfItsKey _,
                     NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> null;
            };
            // Nor is how many of its elements meet a statement, or that they meet one together.
            case RealizationTarget.ACount _, RealizationTarget.ElementsMeetingTogether _ -> null;
        };
        return new Edge(made, settled, writtenAt);
    }

    private Generator() {}
}
