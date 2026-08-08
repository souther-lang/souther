package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.BigDecimal;
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
 * <p>What it reports is not only the rows. A combination it could produce nothing for is said out loud,
 * with which of the three things happened — no value can be written for one of its classes, every value
 * it tried was refused at construction, or the search stopped before deciding. A generator that returned
 * only the rows it managed would read as though the rest were covered.
 */
public final class Generator {

    /** How many rows one call will write. Past this the output stops being something a person reads
     * and pastes, and a model that wants more than this has axes it should be measured at fewer of. */
    static final int MAX_ROWS = 200;

    /** How many assignments of values one parameter is tried at. The choices multiply, so this is a
     * bound on the search and not on any one position — and reaching it is reported as the search
     * having stopped, which is a different thing from every assignment having been refused. */
    private static final int MAX_TUPLES = 256;

    /** How deep a record is built. Past this a value stops being anything an author recognises as one
     * input, and a type that refers to itself would not stop at all. */
    private static final int MAX_DEPTH = 8;

    /** The behavior a row would be written for: what its inputs are called, what they are, and where
     * the model divides them. */
    public record Subject(List<String> parameters, List<Type> types, List<Axis> axes,
                          Symbols symbols) {

        public Subject {
            parameters = List.copyOf(parameters);
            types = List.copyOf(types);
            axes = List.copyOf(axes);
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
     */
    public record UnresolvedCombination(List<String> classes, Reason reason, String detail) {

        public enum Reason {
            /** One of the classes has no value that can be written for it. */
            NO_REPRESENTATIVE,
            /** Every value tried was refused at construction. */
            ALL_CANDIDATES_REJECTED,
            /** The search stopped before it got here. */
            SEARCH_LIMIT
        }

        public UnresolvedCombination {
            classes = List.copyOf(classes);
        }

        public UnresolvedCombination(List<String> classes, Reason reason) {
            this(classes, reason, null);
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
                                   List<Incompleteness> incompleteness) {

        public static final GenerationResult NONE =
                new GenerationResult(List.of(), List.of(), List.of());

        public GenerationResult {
            rows = List.copyOf(rows);
            unresolved = List.copyOf(unresolved);
            incompleteness = List.copyOf(incompleteness);
        }

        public boolean isEmpty() {
            return rows.isEmpty() && unresolved.isEmpty();
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
        List<Axis> ordered = ordered(subject);
        // A position where some row's value could not be read is a position nothing is known about.
        // A row generated for a class there may be a row that is already written, and telling an
        // author to write one is worse than saying nothing: it is a specific piece of work that is
        // already done.
        List<Incompleteness> undecided = new ArrayList<>();
        List<Axis> axes = new ArrayList<>();
        for (Axis axis : ordered) {
            if (readEverywhere(axis, existing)) {
                axes.add(axis);
            } else {
                undecided.add(Incompleteness.of(Incompleteness.Code.VALUE_UNREADABLE,
                        Incompleteness.Scope.POSITION, axis.path().toString()));
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
        List<Incompleteness> incompleteness = new ArrayList<>(undecided);
        while (!pairs.isEmpty() || !singles.isEmpty()) {
            if (rows.size() >= MAX_ROWS) {
                int left = pairs.size() + singles.size();
                incompleteness.add(Incompleteness.of(Incompleteness.Code.SEARCH_LIMIT, Incompleteness.Scope.MODULE,
                        left + " combinations past the row limit"));
                // Both sets: the count above is of both, and reporting one of them would promise
                // more than it names.
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
            if (where == null) {
                // Some other position has no class a row may be written at, so no row reaches this
                // combination however it is filled. Answered rather than attempted.
                pairs.remove(seed);
                singles.remove(seed);
                unresolved.add(new UnresolvedCombination(labels(axes, seed),
                        UnresolvedCombination.Reason.NO_REPRESENTATIVE));
                continue;
            }
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
                        built.detail()));
            }
        }
        return new GenerationResult(rows, unresolved, incompleteness);
    }

    /**
     * What building a row at one boundary came to: the row, or why there is none.
     *
     * <p>Exactly one of the two. A caller measuring the boundary reads whether a row was built, which
     * is a value that went through the decoder and so a witness that the edge can be written; a caller
     * offering work to a person reads the row itself. The attempt is made once and both read it.
     */
    public record BoundaryAttempt(GeneratedRow row, UnresolvedCombination unresolved) {

        public boolean built() {
            return row != null;
        }
    }

    /**
     * A row at one boundary, built through the module's own decoders.
     *
     * <p>One row per boundary rather than one row covering several, because a row is a question put to
     * a person and a row sitting on three edges at once is three answers they have to separate.
     *
     * <p>Nothing here decides that a boundary cannot be written at. A refusal is a refusal of the
     * candidates that were tried, and another value of the same edge may build; what comes back says
     * which of the two happened and leaves the reading to the caller.
     */
    public static BoundaryAttempt probe(Subject subject, BoundaryObligation obligation,
                                        CandidateCheck check) {
        Axis axis = subject.axes().stream().filter(a -> a.id().equals(obligation.axis())).findFirst()
                .orElse(null);
        if (axis == null) {
            return new BoundaryAttempt(null, new UnresolvedCombination(List.of(),
                    UnresolvedCombination.Reason.NO_REPRESENTATIVE));
        }
        String label = axis.path() + " = " + written(obligation.value());
        FixtureTemplate at = valueOf(obligation.value(), axis.type(), subject.symbols());
        if (at == null) {
            return new BoundaryAttempt(null, new UnresolvedCombination(List.of(label),
                    UnresolvedCombination.Reason.NO_REPRESENTATIVE));
        }
        List<FixtureTemplate> inputs = new ArrayList<>();
        // What the rest of the row has to sit beside. A field of a record is not chosen from its
        // own type once another field of that record is fixed: the rule relating them says what
        // is left, and taking the bottom of the type's range instead is how a boundary that can
        // be written came back as one every value tried was refused at.
        BigDecimal settledAt = numberOf(obligation.value());
        Map<String, BigDecimal> settled = settledAt == null ? Map.of()
                : Map.of(axis.path().toString(), settledAt);
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            Map<String, List<FixtureTemplate>> here =
                    TermPath.of(subject.parameters().get(p)).head().equals(axis.path().head())
                            ? Map.of(axis.path().toString(), List.of(at)) : Map.of();
            Outcome tried = valueAt(subject, p, here, settled, check);
            if (tried.value() == null) {
                return new BoundaryAttempt(null,
                        new UnresolvedCombination(List.of(label), tried.reason(), tried.detail()));
            }
            inputs.add(tried.value());
        }
        return new BoundaryAttempt(new GeneratedRow(List.of(label), inputs), null);
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

    /**
     * Whether a row may be written at this class of this position.
     *
     * <p>A row at a class the body rules out reaches an {@code unreachable} and is E1911, so offering
     * one hands the author work the compiler will refuse. Asked by index because everything here
     * addresses a class by its place in the axis.
     */
    private static boolean open(Axis axis, int cls) {
        return !axis.excluded().contains(axis.classes().get(cls).id());
    }

    private static Set<Pair> pairsOf(List<Axis> axes) {
        Set<Pair> all = new TreeSet<>();
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                for (int a = 0; a < axes.get(i).classes().size(); a++) {
                    for (int b = 0; b < axes.get(j).classes().size(); b++) {
                        if (open(axes.get(i), a) && open(axes.get(j), b)) {
                            all.add(new Pair(i, a, j, b));
                        }
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
                if (open(axes.get(i), c)) {
                    all.add(Pair.alone(i, c));
                }
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

    /** Every position fixed: the seed's two as the seed says, and each of the rest at whichever class
     * brings in the most combinations nothing covers yet. */
    private static int[] assign(List<Axis> axes, Set<Pair> uncovered, Pair seed) {
        int[] where = new int[axes.size()];
        java.util.Arrays.fill(where, -1);
        where[seed.left()] = seed.leftClass();
        if (!seed.alone()) {
            where[seed.right()] = seed.rightClass();
        }
        for (int i = 0; i < axes.size(); i++) {
            if (where[i] >= 0) {
                continue;
            }
            // A position this row is not about still has to hold something, and what it holds has to
            // be writable: filling it with a class the body rules out would make the whole row
            // E1911, whichever gap it was generated for.
            int best = -1;
            int bestGain = -1;
            for (int c = 0; c < axes.get(i).classes().size(); c++) {
                if (!open(axes.get(i), c)) {
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
            if (best < 0) {
                return null;   // every class of this position is ruled out: no row can be written
            }
            where[i] = best;
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

    private record Attempt(GeneratedRow row, UnresolvedCombination.Reason reason, String detail) {}

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
        for (int i = 0; i < axes.size(); i++) {
            List<FixtureTemplate> candidates =
                    axes.get(i).classes().get(where[i]).representatives().candidates();
            if (candidates.isEmpty()) {
                return new Attempt(null, UnresolvedCombination.Reason.NO_REPRESENTATIVE,
                        label(axes.get(i), where[i]));
            }
            decided.put(axes.get(i).path().toString(), candidates);
        }
        List<FixtureTemplate> inputs = new ArrayList<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            Outcome tried = valueFor(subject, p, axes, decided, check);
            if (tried.value() == null) {
                return new Attempt(null, tried.reason(), tried.detail());
            }
            inputs.add(tried.value());
        }
        return new Attempt(new GeneratedRow(labels(axes, where), inputs), null, null);
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
                                    CandidateCheck check) {
        TermPath at = TermPath.of(subject.parameters().get(p));
        Map<String, List<FixtureTemplate>> here = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.path().head().equals(at.head())
                    && decided.containsKey(axis.path().toString())) {
                here.put(axis.path().toString(), decided.get(axis.path().toString()));
            }
        }
        return valueAt(subject, p, here, settledIn(here), check);
    }

    /**
     * The positions a caller fixed at one number.
     *
     * <p>Only where the position has a single value to take. A class offers one value to stand for
     * it, and that is the one the row will carry, so the rest of the record can be chosen beside it;
     * a position still holding several is not settled at all and nothing is claimed of it.
     */
    private static Map<String, BigDecimal> settledIn(Map<String, List<FixtureTemplate>> decided) {
        Map<String, BigDecimal> out = new LinkedHashMap<>();
        decided.forEach((path, candidates) -> {
            if (candidates.size() == 1) {
                BigDecimal number = writtenNumber(candidates.get(0).value());
                if (number != null) {
                    out.put(path, number);
                }
            }
        });
        return out;
    }

    /** The number a fixture is, reaching through the newtype it may be wrapped in. */
    private static BigDecimal writtenNumber(Ast.Expr written) {
        return switch (written) {
            case Ast.IntLit i -> BigDecimal.valueOf(i.value());
            case Ast.DecimalLit d -> d.value();
            case Ast.Neg n -> {
                BigDecimal inner = writtenNumber(n.operand());
                yield inner == null ? null : inner.negate();
            }
            case Ast.Apply a when a.args().size() == 1 -> writtenNumber(a.args().get(0));
            case null, default -> null;
        };
    }

    /** One parameter's value, with the positions the caller fixed already decided. */
    private static Outcome valueAt(Subject subject, int p,
                                   Map<String, List<FixtureTemplate>> decided,
                                   Map<String, BigDecimal> settled,
                                   CandidateCheck check) {
        Choices choices = choicesOf(subject.types().get(p),
                TermPath.of(subject.parameters().get(p)), subject.symbols(), decided, settled);
        return choices.missingAt() != null
                ? new Outcome(null, UnresolvedCombination.Reason.NO_REPRESENTATIVE,
                        choices.missingAt())
                : walk(subject, p, choices, check);
    }

    /**
     * Every position a row chooses a value at, in the order they are decided.
     *
     * @param at        the paths, so that an assignment can be read back as which value went where
     * @param values    what each of those positions can take, never empty
     * @param missingAt the position nothing at all can be written at, where there is one — which is
     *                  not a choice to make but a reason there is no row
     */
    private record Choices(List<String> at, List<List<FixtureTemplate>> values, String missingAt) {

        static Choices missing(String at) {
            return new Choices(List.of(), List.of(), at);
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
                                     Map<String, BigDecimal> settled) {
        List<String> paths = new ArrayList<>(decided.keySet());
        List<List<FixtureTemplate>> values = new ArrayList<>(decided.values());
        // One reading of the parameter, not one per record inside it. A clause on the outer record
        // says what is left for a position two levels down, and a reading rebuilt at the inner record
        // has never seen it.
        FieldDomains left = type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && !data.newtype()
                ? FieldDomains.of(ref.name(), data, symbols, under(at, settled)) : FieldDomains.NONE;
        String missing = choicesUnder(type, at, symbols, 0, paths, values, left, at);
        return missing != null ? Choices.missing(missing) : new Choices(paths, values, null);
    }

    /** The settled positions of one parameter, named the way the reading of that parameter names
     * them: from the value itself, with the parameter dropped. */
    private static Map<String, BigDecimal> under(TermPath root, Map<String, BigDecimal> settled) {
        if (settled.isEmpty()) {
            return Map.of();
        }
        Map<String, BigDecimal> out = new LinkedHashMap<>();
        String prefix = root + ".";
        settled.forEach((path, number) -> {
            if (path.startsWith(prefix)) {
                out.put(path.substring(prefix.length()), number);
            }
        });
        return out;
    }

    /** The positions under one parameter, appended in the order they are composed. Returns the path
     * nothing can be written at, where there is one. */
    private static String choicesUnder(Type type, TermPath at, Symbols symbols, int depth,
                                       List<String> paths, List<List<FixtureTemplate>> values,
                                       FieldDomains left, TermPath root) {
        if (paths.contains(at.toString())) {
            return null;   // an axis decides here
        }
        if (depth < MAX_DEPTH && type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && !data.newtype()) {
            Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
            if (!fields.isEmpty()) {
                for (Map.Entry<String, Type> field : fields.entrySet()) {
                    String missing = choicesUnder(field.getValue(), at.then(field.getKey()), symbols,
                            depth + 1, paths, values, left, root);
                    if (missing != null) {
                        return missing;
                    }
                }
                return null;
            }
        }
        List<FixtureTemplate> stands = Partitions.representativesOf(type, symbols,
                at.fields().isEmpty() ? null : left.at(String.join(".", at.fields())));
        if (stands.isEmpty()) {
            // Nothing could be written at all: a position of a type nothing stands for. Which is not
            // the same as a value that was written and refused, and reporting it as one sends the
            // author looking for a rule relating two inputs that has nothing to do with it.
            return at + ": " + Type.show(type);
        }
        paths.add(at.toString());
        values.add(stands);
        return null;
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
     */
    private static Outcome walk(Subject subject, int p, Choices choices, CandidateCheck check) {
        int positions = choices.at().size();
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
                chosen.put(choices.at().get(i), choices.values().get(i).get(assignment[i]));
            }
            FixtureTemplate built = compose(subject.types().get(p),
                    TermPath.of(subject.parameters().get(p)), chosen, subject.symbols(), 0);
            if (built != null && check.refuse(p, built).isEmpty()) {
                return new Outcome(built, null, null);
            }
            for (int i = 0; i < positions; i++) {
                if (assignment[i] + 1 >= choices.values().get(i).size()) {
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

    /** The value at one position: what the assignment chose there, or a record built out of its
     * fields. Null only where the walk that collected the choices and this one disagree. */
    private static FixtureTemplate compose(Type type, TermPath at, Map<String, FixtureTemplate> chosen,
                                           Symbols symbols, int depth) {
        FixtureTemplate here = chosen.get(at.toString());
        if (here != null) {
            return here;
        }
        if (depth < MAX_DEPTH && type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && !data.newtype()) {
            Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
            if (!fields.isEmpty()) {
                Map<String, FixtureTemplate> built = new LinkedHashMap<>();
                for (Map.Entry<String, Type> field : fields.entrySet()) {
                    FixtureTemplate value = compose(field.getValue(), at.then(field.getKey()), chosen,
                            symbols, depth + 1);
                    if (value == null) {
                        return null;
                    }
                    built.put(field.getKey(), value);
                }
                return FixtureTemplate.record(ref.name(), built);
            }
        }
        return null;
    }

    /** A boundary value written the way the position takes it: bare where the position is a number,
     * wrapped where it is a newtype over one. */
    private static FixtureTemplate valueOf(ObservedValue value, Type type, Symbols symbols) {
        BigDecimal number = numberOf(value);
        if (number == null) {
            return null;
        }
        Type base = TypeOps.base(type, symbols);
        FixtureTemplate bare = base == Type.DECIMAL ? FixtureTemplate.decimal(number)
                : number.stripTrailingZeros().scale() > 0 ? FixtureTemplate.decimal(number)
                        : FixtureTemplate.integer(number.longValueExact());
        if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                && data.newtype()) {
            return FixtureTemplate.newtype(ref.name(), bare);
        }
        return bare;
    }

    private static String written(ObservedValue value) {
        BigDecimal number = numberOf(value);
        return number == null ? String.valueOf(value) : number.stripTrailingZeros().toPlainString();
    }

    private static BigDecimal numberOf(ObservedValue value) {
        return switch (value) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            case ObservedValue.Constructed c when c.field("value") != null -> numberOf(c.field("value"));
            case null, default -> null;
        };
    }

    private Generator() {}
}
