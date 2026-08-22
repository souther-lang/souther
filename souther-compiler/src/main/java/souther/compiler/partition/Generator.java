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
import java.util.TreeSet;

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
    public record Subject(BehaviorInputs inputs, List<Axis> axes) {

        public Subject {
            axes = List.copyOf(axes);
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
     * One row's worth of input, and which classes it was written to sit in.
     *
     * @param classes one {@code path=class} per divided position, in the order the axes were ordered
     * @param inputs  one value per parameter, in the order the behavior takes them
     */
    public record GeneratedRow(List<String> classes, List<FixtureTemplate> inputs) {

        public GeneratedRow {
            classes = List.copyOf(classes);
            inputs = List.copyOf(inputs);
        }

        /** What the row is about, in the form a row's description is written in. */
        public String description() {
            return String.join(" x ", classes);
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
            NO_REASON_RECORDED
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
     * Whether a value written this way can be built at all.
     *
     * <p>The one thing a generator cannot work out for itself. A record's fields can constrain each
     * other, and whether two values are allowed together is the derived decoder's answer, not a rule
     * that can be read off the types one at a time.
     */
    @FunctionalInterface
    public interface CandidateCheck {

        /** Empty where the value builds; the reason it did not, otherwise. */
        Optional<String> refuse(int parameter, FixtureTemplate candidate);

        /** Nothing is refused — what a caller with no runtime to build against uses. */
        CandidateCheck ANY = (_, _) -> Optional.empty();
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
        List<Axis> ordered = ordered(subject);
        // A position where some row's value could not be read is a position nothing is known about.
        // A row generated for a class there may be a row that is already written, and telling an
        // author to write one is worse than saying nothing: it is a specific piece of work that is
        // already done.
        List<GenerationReason> undecided = new ArrayList<>();
        List<Axis> axes = new ArrayList<>();
        for (Axis axis : ordered) {
            if (readEverywhere(axis, existing)) {
                axes.add(axis);
            } else {
                undecided.add(new GenerationReason.PositionWithheld(axis.id()));
            }
        }
        if (axes.isEmpty()) {
            return new GenerationResult(List.of(), List.of(), undecided);
        }
        // Both, because one does not imply the other. A behavior with one divided position has no
        // pairs at all and can still have a class nothing has been written in, and a set of rows that
        // covers every pair can still miss a class of a position the pairs happened to fix elsewhere.
        Set<Pair> pairs = pairsOf(axes);
        Set<Pair> singles = singlesOf(axes);
        for (ObservedRow row : existing) {
            cover(pairs, singles, axes, reachedIn(row.at(), axes));
        }

        List<GeneratedRow> rows = new ArrayList<>();
        List<UnresolvedCombination> unresolved = new ArrayList<>();
        List<GenerationReason> reasons = new ArrayList<>(undecided);
        List<Placement> written = new ArrayList<>();
        for (ObservedRow row : existing) {
            written.add(new Placement.Written(whereIn(row.at(), axes), row.watched()));
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
                switch (witnessFor(subject, axes, pairs, selection, check, trial)) {
                    case Witness.None none -> unresolved.add(new UnresolvedCombination(
                            none.classes(), none.reason(), none.detail(), none.said()));
                    case Witness.Certified found -> {
                        rows.add(found.row());
                        written.add(new Placement.Composed(found.by().where(),
                                new Watched.Ran(found.by().seen())));
                        cover(pairs, singles, axes, found.by().where());
                    }
                    case Witness.Unconfirmed offer -> {
                        rows.add(offer.row());
                        written.add(new Placement.Composed(offer.where(), new Watched.NoAccount()));
                        cover(pairs, singles, axes, offer.where());
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
        int pairsLeft = 0;
        while (!pairs.isEmpty() || !singles.isEmpty()) {
            if (rows.size() >= MAX_ROWS) {
                pairsLeft = pairs.size() + singles.size();
                // Both sets: the count is of both, and reporting one of them would promise more
                // than it names.
                for (Set<Pair> remaining : List.of(pairs, singles)) {
                    for (Pair still : remaining) {
                        unresolved.add(new UnresolvedCombination(labels(axes, still),
                                UnresolvedCombination.Reason.SEARCH_LIMIT));
                    }
                }
                break;
            }
            Pair seed = (pairs.isEmpty() ? singles : pairs).iterator().next();
            int[] where = assign(axes, pairs, seed);
            Attempt built = build(subject, axes, where, check);
            if (built.row() != null) {
                rows.add(built.row());
                cover(pairs, singles, axes, where);
            } else {
                // The seed leaves the sets either way: it is answered, and leaving it in would put the
                // same combination through the same values on the next turn and never finish.
                pairs.remove(seed);
                singles.remove(seed);
                unresolved.add(new UnresolvedCombination(labels(axes, seed), built.reason(),
                        built.detail(), built.said()));
            }
        }
        // Said once, at the end, and about both spaces. A search that ran out on the cells stopped
        // whether or not the pairs had anything left to do, and two limits reported apart would be
        // read as two searches.
        if (cellsLeft + pairsLeft > 0) {
            reasons.add(new GenerationReason.SearchLimit(axes.get(0).id().behavior(),
                    cellsLeft + pairsLeft));
        }
        if (unconfirmed) {
            reasons.add(new GenerationReason.RowsNotConfirmed(axes.get(0).id().behavior()));
        }
        if (withheld > 0) {
            reasons.add(new GenerationReason.CombinationsWithheld(axes.get(0).id().behavior(),
                    withheld));
        }
        return new GenerationResult(rows, unresolved, reasons);
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
        return new BoundaryAttempt.Built(new GeneratedRow(List.of(label), inputs));
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

    // --- the pair space -------------------------------------------------------------------------

    /** One class of one position against one class of another. Positions are held as their order in
     * the ordered axes, so the natural order of these is the lexicographic order the search takes. */
    private record Pair(int left, int leftClass, int right, int rightClass)
            implements Comparable<Pair> {

        /** One class of one position on its own, which is what a position with no other position to
         * be paired against still owes a row for. */
        static Pair alone(int at, int cls) {
            return new Pair(at, cls, -1, -1);
        }

        boolean alone() {
            return right < 0;
        }

        @Override
        public int compareTo(Pair other) {
            return Comparator.comparingInt(Pair::left).thenComparingInt(Pair::right)
                    .thenComparingInt(Pair::leftClass).thenComparingInt(Pair::rightClass)
                    .compare(this, other);
        }
    }

    /**
     * The axes in the order the search fixes them.
     *
     * <p>Most classes first, which is what makes a greedy pass need fewer rows: the position with the
     * most classes is the one that forces rows however it is ordered, so every other position rides
     * along with it. Parameter order and then the path settle the rest, so that two runs of the same
     * model order them the same way.
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

    private static Set<Pair> pairsOf(List<Axis> axes) {
        Set<Pair> all = new TreeSet<>();
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                for (int a = 0; a < axes.get(i).classes().size(); a++) {
                    for (int b = 0; b < axes.get(j).classes().size(); b++) {
                        all.add(new Pair(i, a, j, b));
                    }
                }
            }
        }
        return all;
    }

    private static Set<Pair> singlesOf(List<Axis> axes) {
        Set<Pair> all = new TreeSet<>();
        for (int i = 0; i < axes.size(); i++) {
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                all.add(Pair.alone(i, c));
            }
        }
        return all;
    }

    /** Whether every existing row said where it sat at this position. One that did not leaves the
     * position undecided: what the rows cover there is unknown, so what they do not cover is unknown
     * too. */
    private static boolean readEverywhere(Axis axis, List<ObservedRow> existing) {
        for (ObservedRow row : existing) {
            Classification where = row.at().get(axis.id());
            if (where != null && !(where instanceof Classification.Classified)) {
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

    /** The same, of a row this generation composed, which sits in one class per position. */
    private static void cover(Set<Pair> pairs, Set<Pair> singles, List<Axis> axes, int[] where) {
        List<int[]> each = new ArrayList<>(where.length);
        for (int at : where) {
            each.add(at < 0 ? new int[0] : new int[] {at});
        }
        cover(pairs, singles, axes, each);
    }

    /**
     * What one row covers, over every class it reached at every position.
     *
     * <p>A row reaching more than one class at a position covers each of them, and meets each of
     * them against whatever the position beside it holds. Read as one class it would cover the
     * first of them and leave the rest owed, which is a row the author already wrote being asked
     * for again.
     */
    private static void cover(Set<Pair> pairs, Set<Pair> singles, List<Axis> axes,
                              List<int[]> where) {
        for (int i = 0; i < axes.size(); i++) {
            for (int one : where.get(i)) {
                singles.remove(Pair.alone(i, one));
                for (int j = i + 1; j < axes.size(); j++) {
                    for (int other : where.get(j)) {
                        pairs.remove(new Pair(i, one, j, other));
                    }
                }
            }
        }
    }

    /**
     * A row this generation counts the combinations against: where it sits, what came of running
     * it, and whose row it is.
     *
     * <p>Whose it is, because being unable to say where a row went costs different things for the
     * two. A row the author wrote is in the file whatever this can establish about it, so passing
     * over a combination it may fill risks nothing worse than a combination left owed — while
     * offering one risks handing them work they have already done. A row this search composed is in
     * nobody's file, so counting one it cannot judge is reading a reading back as evidence for
     * itself.
     */
    private sealed interface Placement {

        int[] where();

        Watched watched();

        /** A row that is in the author's file. */
        record Written(int[] where, Watched watched) implements Placement {}

        /** A row this search composed on this pass. */
        record Composed(int[] where, Watched watched) implements Placement {}
    }

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
            } else if (row instanceof Placement.Written && selection.cell().holds(row.where())) {
                maybe = true;
            }
        }
        return maybe ? new CombinationStanding.MayBeWritten() : new CombinationStanding.Owed();
    }

    /** Every position fixed: the seed's two as the seed says, and each of the rest at whichever class
     * brings in the most combinations nothing covers yet. */
    private static int[] assign(List<Axis> axes, Set<Pair> uncovered, Pair seed) {
        InteractionCells.Cell cell = InteractionCells.Cell.anything(axes);
        pin(cell, seed.left(), seed.leftClass());
        if (!seed.alone()) {
            pin(cell, seed.right(), seed.rightClass());
        }
        return assign(axes, uncovered, cell);
    }

    /** Everything but {@code cls} taken away from the position, which is what fixing it is. */
    private static void pin(InteractionCells.Cell cell, int axis, int cls) {
        java.util.Arrays.fill(cell.allowed()[axis], false);
        cell.allowed()[axis][cls] = true;
    }

    /**
     * The same, from whatever {@code cell} leaves each position.
     *
     * <p>A position it leaves several classes is chosen among those the same way a position it says
     * nothing about is chosen among all of them: what the cell does not settle is room the pairs are
     * spent in, and there is no reason to spend less of it where the room is narrower.
     */
    private static int[] assign(List<Axis> axes, Set<Pair> uncovered, InteractionCells.Cell cell) {
        int[] where = new int[axes.size()];
        java.util.Arrays.fill(where, -1);
        // The positions the cell leaves one class first, so the rest are chosen against them rather
        // than against whatever the walk happened to reach earlier.
        for (int i = 0; i < axes.size(); i++) {
            int only = -1;
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (cell.admits(i, c)) {
                    only = only < 0 ? c : -1;
                    if (only < 0) {
                        break;
                    }
                }
            }
            where[i] = only;
        }
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] >= 0) {
                continue;
            }
            // A position this row is not about still has to hold something, and every class of an
            // axis is one a row can be written at: what the rules refuse is not a class of the
            // position at all.
            int best = -1;
            int bestGain = -1;
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (!cell.admits(i, c)) {
                    continue;
                }
                int gain = 0;
                for (int j = 0; j < axes.size(); j++) {
                    if (j == i || where[j] < 0) {
                        continue;
                    }
                    Pair pair = i < j ? new Pair(i, c, j, where[j]) : new Pair(j, where[j], i, c);
                    if (uncovered.contains(pair)) {
                        gain++;
                    }
                }
                if (gain > bestGain) {
                    bestGain = gain;
                    best = c;
                }
            }
            where[i] = best;   // every axis here has a class, so there is always one to place
        }
        return where;
    }

    /** What a row is about, in the words the model uses. The class's label rather than its id: an id
     * is scoped by carrying its own path, and a description that carries the path already would say
     * it twice. */
    private static String label(Axis axis, int cls) {
        return axis.path() + "=" + axis.classes().get(cls).label();
    }

    private static List<String> labels(List<Axis> axes, int[] where) {
        List<String> out = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] >= 0) {
                out.add(label(axes.get(i), where[i]));
            }
        }
        return out;
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

    private static List<String> labels(List<Axis> axes, Pair pair) {
        String left = label(axes.get(pair.left()), pair.leftClass());
        return pair.alone() ? List.of(left)
                : List.of(left, label(axes.get(pair.right()), pair.rightClass()));
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
    private static Witness witnessFor(Subject subject, List<Axis> axes, Set<Pair> uncovered,
                                      CellSelection selection, CandidateCheck check, Trial trial) {
        InteractionCells.Cell cell = selection.cell();
        List<int[]> tried = new ArrayList<>();
        Attempt last = null;
        int[] where = null;
        boolean missed = false;
        for (int candidate = 0; candidate < MOST_CANDIDATES; candidate++) {
            int[] at = assignment(axes, uncovered, cell, candidate, tried);
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
            GeneratedRow named = new GeneratedRow(labels(axes, cell, at), last.row().inputs());
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
     * <p>The first is the pair search's: every position the combination does not settle goes to
     * whichever class brings in the most combinations nothing covers yet, which is what makes the
     * rows a combination needs rows the pair space wanted anyway. The rest are the assignments the
     * combination admits, counted off in order — a fixed order, so the same model offers the same
     * rows twice.
     *
     * <p>Bounded by how many have been tried rather than by a walk over the space: at most
     * {@link #MOST_CANDIDATES} assignments are ever tried, so one of the first that many is one
     * that has not been.
     */
    private static int[] assignment(List<Axis> axes, Set<Pair> uncovered,
                                    InteractionCells.Cell cell, int candidate, List<int[]> tried) {
        if (candidate == 0) {
            return assign(axes, uncovered, cell);
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
    private static Attempt build(Subject subject, List<Axis> axes, int[] where, CandidateCheck check) {
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
            Outcome tried = valueFor(subject, p, axes, decided, recipes, check);
            if (tried.value() == null) {
                return Attempt.no(tried.reason(), tried.detail());
            }
            inputs.add(tried.value());
        }
        return Attempt.of(new GeneratedRow(labels(axes, where), inputs));
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
                decided.keySet(), recipes, path -> leastHeld(under, path));
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

    /** How many the rules say the list at {@code path} holds at the fewest, or zero where they say
     *  nothing about how many. */
    private static int leastHeld(FieldDomains rules, TermPath path) {
        String field = fieldUnder(path);
        FieldDomains.Held held = field == null ? null : rules.heldAt(field);
        if (held == null || held.bounds() == null) {
            return 0;
        }
        souther.compiler.numeric.Endpoint floor = held.bounds().min();
        if (floor == null || !(floor.at() instanceof souther.compiler.numeric.Count count)) {
            return 0;
        }
        java.math.BigDecimal at = floor.inclusive() ? count.at()
                : count.at().add(java.math.BigDecimal.ONE);
        return at.signum() <= 0 ? 0 : at.min(java.math.BigDecimal.valueOf(64)).intValue();
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
