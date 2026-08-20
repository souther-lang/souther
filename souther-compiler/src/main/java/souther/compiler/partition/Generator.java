package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
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

    /** How deep a record is built. Past this a value stops being anything an author recognises as one
     * input, and a type that refers to itself would not stop at all. */
    private static final int MAX_DEPTH = 8;

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

    // --- filling the pairs ----------------------------------------------------------------------

    /**
     * Rows for the two-class combinations the existing rows do not sit in.
     *
     * <p>Greedy and deterministic, in the shape IPO has: take the first combination nothing covers, fix
     * those two positions, and choose every other position for how many further uncovered combinations
     * it brings in. Ties go to the lower index, the axes are ordered before anything starts, and nothing
     * consults a clock or a hash order — the same model and the same rows produce the same rows twice.
     */
    public static GenerationResult fill(Subject subject,
                                        List<Map<AxisId, Classification>> existing,
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
    public static GenerationResult fill(Subject subject,
                                        List<Map<AxisId, Classification>> existing,
                                        CandidateCheck check,
                                        List<souther.compiler.interaction.Interaction> groups) {
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
        for (Map<AxisId, Classification> row : existing) {
            cover(pairs, singles, axes, whereIn(row, axes));
        }

        List<GeneratedRow> rows = new ArrayList<>();
        List<UnresolvedCombination> unresolved = new ArrayList<>();
        List<GenerationReason> reasons = new ArrayList<>(undecided);
        List<int[]> written = new ArrayList<>();
        for (Map<AxisId, Classification> row : existing) {
            written.add(whereIn(row, axes));
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
        while (anyLeft && rows.size() < MAX_ROWS) {
            anyLeft = false;
            for (int g = 0; g < byGroup.size() && rows.size() < MAX_ROWS; g++) {
                InteractionCells.Group group = byGroup.get(g);
                if (taken[g] >= group.size()) {
                    continue;
                }
                int[] fixed = group.at(taken[g]++);
                anyLeft = true;
                if (fixed == null) {
                    // The factors this choice takes disagree about a position, so it is not a
                    // combination the body has a path to and there is nothing to ask for.
                    continue;
                }
                if (sits(written, fixed)) {
                    // A cell a row already sits in is a cell nothing is owed for.
                    continue;
                }
                int[] where = assign(axes, pairs, fixed);
                Attempt built = build(subject, axes, where, check);
                if (built.row() == null) {
                    unresolved.add(new UnresolvedCombination(labels(axes, fixed), built.reason(),
                            built.detail(), built.said()));
                    continue;
                }
                // Named for the cell it was composed for, which is the positions the decisions
                // read. What the pass below filled the rest of the row with is what this row turns
                // out to settle beside that, and a name carrying it would move when nothing about
                // the row had.
                rows.add(new GeneratedRow(labels(axes, fixed), built.row().inputs()));
                written.add(where);
                cover(pairs, singles, axes, where);
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
                return edgeOf(axis, carrier, at, subject.symbols());
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
        if (!path.fields().isEmpty()) {
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
    private static boolean readEverywhere(Axis axis, List<Map<AxisId, Classification>> existing) {
        for (Map<AxisId, Classification> row : existing) {
            Classification where = row.get(axis.id());
            if (where != null && !(where instanceof Classification.Classified)) {
                return false;
            }
        }
        return true;
    }

    /** Which class each ordered axis fell in for one row, or -1 where the row did not say. */
    private static int[] whereIn(Map<AxisId, Classification> row, List<Axis> axes) {
        int[] at = new int[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            at[i] = -1;
            if (row.get(axes.get(i).id()) instanceof Classification.Classified in) {
                for (int c = 0; c < axes.get(i).classes().size(); c++) {
                    if (axes.get(i).classes().get(c).id().equals(in.classId())) {
                        at[i] = c;
                        break;
                    }
                }
            }
        }
        return at;
    }

    private static void cover(Set<Pair> pairs, Set<Pair> singles, List<Axis> axes, int[] where) {
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] < 0) {
                continue;
            }
            singles.remove(Pair.alone(i, where[i]));
            for (int j = i + 1; j < axes.size(); j++) {
                if (where[j] >= 0) {
                    pairs.remove(new Pair(i, where[i], j, where[j]));
                }
            }
        }
    }

    /** Whether a row already written fixes every position {@code fixed} does, the same way. */
    private static boolean sits(List<int[]> written, int[] fixed) {
        for (int[] row : written) {
            boolean all = true;
            for (int i = 0; i < fixed.length && all; i++) {
                all = fixed[i] < 0 || (i < row.length && row[i] == fixed[i]);
            }
            if (all) {
                return true;
            }
        }
        return false;
    }

    /** Every position fixed: the seed's two as the seed says, and each of the rest at whichever class
     * brings in the most combinations nothing covers yet. */
    private static int[] assign(List<Axis> axes, Set<Pair> uncovered, Pair seed) {
        int[] fixed = new int[axes.size()];
        java.util.Arrays.fill(fixed, -1);
        fixed[seed.left()] = seed.leftClass();
        if (!seed.alone()) {
            fixed[seed.right()] = seed.rightClass();
        }
        return assign(axes, uncovered, fixed);
    }

    /** The same, from however many positions the seed fixes. */
    private static int[] assign(List<Axis> axes, Set<Pair> uncovered, int[] fixed) {
        int[] where = fixed.clone();
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

    private static List<String> labels(List<Axis> axes, Pair pair) {
        String left = label(axes.get(pair.left()), pair.leftClass());
        return pair.alone() ? List.of(left)
                : List.of(left, label(axes.get(pair.right()), pair.rightClass()));
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
        Choices choices = choicesOf(subject.types().get(p),
                TermPath.of(subject.parameters().get(p)), subject.symbols(), decided, settled,
                recipes);
        if (choices.missingAt() != null) {
            return new Outcome(null, UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    choices.missingAt());
        }
        Outcome product = walk(subject, p, choices, recipes, check);
        if (product.value() != null) {
            return product;
        }
        // Every position took its value knowing only what the caller had settled, so a rule relating
        // two of them was satisfied only where the lists happened to already hold a pair that does.
        // Asked again choosing one position at a time, each from what is left once the ones before it
        // are asserted, which is the only way `a < b` is met in general.
        Outcome conditioned = conditioned(subject, p, decided, settled, recipes, check);
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
        UnresolvedCombination.Reason held = heldBack(subject, p, decided, settled, recipes);
        return held == null ? product : new Outcome(null, held, null);
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
                                                         Map<String, List<FixtureTemplate>> decided,
                                                         Map<String, Place> settled,
                                                         Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        List<Position> found = new ArrayList<>();
        TermPath root = TermPath.of(subject.parameters().get(p));
        Type declared = subject.types().get(p);
        positionsUnder(declared, root, subject.symbols(), 0, found, decided.keySet(), recipes);
        FieldDomains rules = rulesOf(declared, subject.symbols(), under(root, settled));
        UnresolvedCombination.Reason held = null;
        for (Position each : found) {
            String field = fieldUnder(root, each.path());
            UnresolvedCombination.Reason here = Partitions.notBuilt(each.type(), subject.symbols(),
                    field == null ? null : rules.heldAt(field));
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
    private static Outcome conditioned(Subject subject, int p,
                                       Map<String, List<FixtureTemplate>> decided,
                                       Map<String, Place> settled,
                                       Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                       CandidateCheck check) {
        Type type = subject.types().get(p);
        TermPath at = TermPath.of(subject.parameters().get(p));
        List<Position> found = new ArrayList<>();
        positionsUnder(type, at, subject.symbols(), 0, found, decided.keySet(), recipes);
        // What the caller fixed goes first, so that everything chosen after it is chosen beside it.
        // A class stands for one value and a boundary is one value, and neither is worth deciding
        // after the positions whose range it settles.
        List<Position> positions = new ArrayList<>(
                found.stream().filter(each -> decided.containsKey(each.path())).toList());
        positions.addAll(found.stream().filter(each -> !decided.containsKey(each.path())).toList());
        Budget budget = new Budget();
        FixtureTemplate built = descend(subject, p, positions, 0, new LinkedHashMap<>(),
                new LinkedHashMap<>(settled), decided, recipes, check, budget);
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

    /** One position of a row: where it is, and what it holds. */
    private record Position(String path, Type type) {}

    /**
     * The assignment this branch leads to, or null where none of them builds.
     *
     * @param chosen  what the positions before this one took
     * @param settled the numbers among them, which is what a projection can be asked about
     * @param budget  assignments left to compose, shared down the whole search
     */
    private static FixtureTemplate descend(Subject subject, int p, List<Position> positions, int index,
                                           Map<String, FixtureTemplate> chosen,
                                           Map<String, Place> settled,
                                           Map<String, List<FixtureTemplate>> decided,
                                           Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                           CandidateCheck check, Budget budget) {
        if (index == positions.size()) {
            if (!budget.spend()) {
                return null;
            }
            FixtureTemplate whole = compose(subject.types().get(p),
                    TermPath.of(subject.parameters().get(p)), chosen, subject.symbols(), 0, recipes);
            return whole != null && check.refuse(p, whole).isEmpty() ? whole : null;
        }
        Position position = positions.get(index);
        for (FixtureTemplate candidate : candidatesAt(subject, p, position, settled, decided)) {
            chosen.put(position.path(), candidate);
            Place number = Counts.writtenIn(candidate.value());
            if (number != null) {
                settled.put(position.path(), number);
            }
            FixtureTemplate found = descend(subject, p, positions, index + 1, chosen, settled,
                    decided, recipes, check, budget);
            if (found != null) {
                return found;
            }
            chosen.remove(position.path());
            settled.remove(position.path());
            if (budget.cutShort) {
                return null;
            }
        }
        return null;
    }

    /** What one position can take, given what the positions before it took. */
    private static List<FixtureTemplate> candidatesAt(Subject subject, int p, Position position,
                                                      Map<String, Place> settled,
                                                      Map<String, List<FixtureTemplate>> decided) {
        List<FixtureTemplate> fixed = decided.get(position.path());
        if (fixed != null) {
            return fixed;
        }
        TermPath at = TermPath.of(subject.parameters().get(p));
        FieldDomains left = rulesOf(subject.types().get(p), subject.symbols(), under(at, settled));
        String field = fieldUnder(at, position.path());
        return Partitions.displacedRepresentativesOf(position.type(), subject.symbols(),
                field == null ? null : left.at(field),
                field == null ? null : left.heldAt(field));
    }

    /** The positions under one parameter, in the order they are composed. The same rule
     * {@link #choicesUnder} walks, so that the two agree about where a row chooses anything. */
    private static void positionsUnder(Type type, TermPath at, Symbols symbols, int depth,
                                       List<Position> out, java.util.Set<String> decided,
                                       Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        if (decided.contains(at.toString())) {
            out.add(new Position(at.toString(), type));
            return;
        }
        type = shaped(type, at, recipes);
        // Read the way the walk that derived the axes reads it, so that the two agree about where
        // the positions are. A record under a name is a record: `data SlotN = Slot` has the fields
        // of `Slot`, and a generator that stopped at the name had no positions where the derivation
        // had two.
        Shape shape = TypeView.of(type, symbols).shape();
        if (depth < MAX_DEPTH && shape instanceof Shape.Product product
                && !product.fields().isEmpty()) {
            for (Map.Entry<String, Type> field : product.fields().entrySet()) {
                positionsUnder(field.getValue(), at.then(field.getKey()), symbols,
                        depth + 1, out, decided, recipes);
            }
            return;
        }
        out.add(new Position(at.toString(), type));
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
     */
    private record Choices(List<String> at, List<List<FixtureTemplate>> values,
                           List<List<FixtureTemplate>> reserves, String missingAt) {

        static Choices missing(String at) {
            return new Choices(List.of(), List.of(), List.of(), at);
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
     * <p>The same walk the values are composed by, which is what keeps the two agreeing about where the
     * positions are. A record is not a position but the fields under it are, and a position the caller
     * has already decided keeps what it was given.
     *
     * @param decided what the caller fixed: the classes of an axis, or the single value a boundary is
     *                to be reached at
     */
    private static Choices choicesOf(Type type, TermPath at, Symbols symbols,
                                     Map<String, List<FixtureTemplate>> decided,
                                     Map<String, Place> settled,
                                     Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        List<String> paths = new ArrayList<>(decided.keySet());
        List<List<FixtureTemplate>> values = new ArrayList<>(decided.values());
        // A position the caller fixed holds nothing back: it was given the value it is to take.
        List<List<FixtureTemplate>> reserves = new ArrayList<>(
                java.util.Collections.nCopies(paths.size(), List.<FixtureTemplate>of()));
        String missing = choicesUnder(type, at, symbols, 0, paths, values, reserves,
                rulesOf(type, symbols, under(at, settled)), at, recipes);
        return missing != null ? Choices.missing(missing)
                : new Choices(paths, values, reserves, null);
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
    private static FieldDomains rulesOf(Type type, Symbols symbols, Map<String, Count> settled) {
        return type instanceof Type.Ref ref
                && symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data && !data.newtype()
                ? FieldDomains.of(ref.name(), data, symbols, settled) : FieldDomains.NONE;
    }

    /** What a position under a parameter is called where the parameter's own rules name it, or null
     * where the position is the parameter itself. */
    private static String fieldUnder(TermPath root, String path) {
        String prefix = root + ".";
        return path.startsWith(prefix) ? path.substring(prefix.length()) : null;
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

    /** The positions under one parameter, appended in the order they are composed. Returns the path
     * nothing can be written at, where there is one. */
    private static String choicesUnder(Type type, TermPath at, Symbols symbols, int depth,
                                       List<String> paths, List<List<FixtureTemplate>> values,
                                       List<List<FixtureTemplate>> reserves,
                                       FieldDomains left, TermPath root,
                                       Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        if (paths.contains(at.toString())) {
            return null;   // an axis decides here
        }
        type = shaped(type, at, recipes);
        Shape shape = TypeView.of(type, symbols).shape();
        if (depth < MAX_DEPTH && shape instanceof Shape.Product product
                && !product.fields().isEmpty()) {
            for (Map.Entry<String, Type> field : product.fields().entrySet()) {
                String missing = choicesUnder(field.getValue(), at.then(field.getKey()), symbols,
                        depth + 1, paths, values, reserves, left, root, recipes);
                if (missing != null) {
                    return missing;
                }
            }
            return null;
        }
        String field = at.fields().isEmpty() ? null : String.join(".", at.fields());
        souther.compiler.numeric.NumericDomain.Bounds here = field == null ? null : left.at(field);
        List<FixtureTemplate> stands = Partitions.representativesHolding(type, symbols, here,
                field == null ? null : left.heldAt(field));
        if (stands.isEmpty()) {
            // Nothing could be written at all: a position of a type nothing stands for. Which is not
            // the same as a value that was written and refused, and reporting it as one sends the
            // author looking for a rule relating two inputs that has nothing to do with it.
            return at + ": " + Type.show(type);
        }
        paths.add(at.toString());
        values.add(stands);
        reserves.add(Partitions.inReserve(type, symbols, here));
        return null;
    }

    /**
     * The type a value is built at, which is the declared one unless a class named a constructor.
     *
     * <p>Only what is being built moves. The position's declared type is still the sum, and the axis
     * still says so — a class of it saying which case a witness takes is not the position becoming
     * that case, and reading the two as one would have a later reader believe the model declares
     * something it does not.
     */
    private static Type shaped(Type type, TermPath at,
                               Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        RepresentativeSource.Evaluation.Compose compose = recipes.get(at.toString());
        return compose == null ? type : Type.ref(compose.through());
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
    private static Outcome walk(Subject subject, int p, Choices choices,
                                Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                CandidateCheck check) {
        Outcome tried = over(subject, p, choices.at(), choices.values(), recipes, check);
        // Only where the ordinary assignments ran out. A search that stopped at the bound has not
        // tried them all, and starting a wider one in front of the ones it never reached would spend
        // what is left on assignments further from what the model says the row is about, while the
        // nearer ones stay untried.
        if (tried.value() != null || !choices.anythingHeldBack()
                || tried.reason() != UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return tried;
        }
        return over(subject, p, choices.at(), choices.widened(), recipes, check);
    }

    /** One pass over one set of choices, from the assignment where every position takes its first
     * value outward. */
    private static Outcome over(Subject subject, int p, List<String> at,
                                List<List<FixtureTemplate>> values,
                                Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                                CandidateCheck check) {
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
            FixtureTemplate built = compose(subject.types().get(p),
                    TermPath.of(subject.parameters().get(p)), chosen, subject.symbols(), 0, recipes);
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
     * The value at one position: what the assignment chose there, or a record built out of its
     * fields. Null only where the walk that collected the choices and this one disagree.
     *
     * <p>What was built is handed back to the recipe that said how to build it, which puts on the
     * names the position writes its values under. The composing and the writing are one recipe
     * because they are one fact about the position: a class of {@code data DecisionN = Decision}
     * composes an {@code Approved} and the row carries {@code DecisionN(Approved { id = 1 })}.
     * Composed without that, the row carries a value of a type the parameter does not declare.
     */
    private static FixtureTemplate compose(Type type, TermPath at, Map<String, FixtureTemplate> chosen,
                                           Symbols symbols, int depth,
                                           Map<String, RepresentativeSource.Evaluation.Compose> recipes) {
        FixtureTemplate here = chosen.get(at.toString());
        if (here != null) {
            return here;
        }
        RepresentativeSource.Evaluation.Compose recipe = recipes.get(at.toString());
        TypeView view = TypeView.of(shaped(type, at, recipes), symbols);
        if (depth < MAX_DEPTH && view.shape() instanceof Shape.Product product
                && !product.fields().isEmpty()) {
            Map<String, FixtureTemplate> built = new LinkedHashMap<>();
            for (Map.Entry<String, Type> field : product.fields().entrySet()) {
                FixtureTemplate value = compose(field.getValue(), at.then(field.getKey()), chosen,
                        symbols, depth + 1, recipes);
                if (value == null) {
                    return null;
                }
                built.put(field.getKey(), value);
            }
            // Under the names the position is written with, which the reading that found the fields
            // took off to find them. A row at a `data SlotN = Slot` carries `SlotN(Slot { ... })`,
            // and a value composed without them is of a type the parameter does not declare.
            List<TypeReachName.Written> worn = new ArrayList<>();
            for (TypeOps.Layer layer : view.wrappers()) {
                if (!(symbols.scope().reach(layer.named()) instanceof TypeReachName.Written written)) {
                    return null;   // a name this module cannot write leaves no value to write
                }
                worn.add(written);
            }
            if (!(symbols.scope().reach(product.name()) instanceof TypeReachName.Written written)) {
                return null;
            }
            FixtureTemplate record = RepresentativeSource.under(worn,
                    FixtureTemplate.record(written, built));
            return recipe == null ? record : recipe.written(record);
        }
        return null;
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
    private static Edge edgeOf(Axis axis, Carrier carrier, Place at, Symbols symbols) {
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
        Witnesses.Sized built = Witnesses.ofSize(holder, size, symbols, Set.of());
        if (built.values().isEmpty()) {
            return Edge.none(Witnesses.reasonForSize(holder, size, symbols));
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : built.values()) {
            out.add(Witnesses.wrapped(axis.type(), each, symbols));
        }
        return new Edge(out, null, null, built.heldBack());
    }

    private Generator() {}
}
