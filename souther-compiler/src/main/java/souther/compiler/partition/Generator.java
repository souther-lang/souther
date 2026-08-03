package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
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
     * Rows at the boundaries nothing has been written at.
     *
     * <p>One row per boundary rather than one row covering several, because a row is a question put to
     * a person and a row sitting on three edges at once is three answers they have to separate.
     */
    public static GenerationResult forBoundaries(Subject subject, List<BoundaryObligation> unmet,
                                                 CandidateCheck check) {
        List<GeneratedRow> rows = new ArrayList<>();
        List<UnresolvedCombination> unresolved = new ArrayList<>();
        for (BoundaryObligation each : unmet) {
            Axis axis = subject.axes().stream().filter(a -> a.id().equals(each.axis())).findFirst()
                    .orElse(null);
            if (axis == null) {
                continue;
            }
            String label = axis.path() + " = " + written(each.value());
            FixtureTemplate at = valueOf(each.value(), axis.type(), subject.symbols());
            if (at == null) {
                unresolved.add(new UnresolvedCombination(List.of(label),
                        UnresolvedCombination.Reason.NO_REPRESENTATIVE));
                continue;
            }
            Map<String, FixtureTemplate> byPath = new LinkedHashMap<>();
            byPath.put(axis.path().toString(), at);
            Composed composed = inputsOf(subject, byPath, check);
            if (composed.inputs() == null) {
                unresolved.add(new UnresolvedCombination(List.of(label), composed.reason(),
                        composed.detail()));
                continue;
            }
            rows.add(new GeneratedRow(List.of(label), composed.inputs()));
        }
        return new GenerationResult(rows, unresolved, List.of());
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
            int best = 0;
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
     * <p>Each class offers more than one value, and they are tried in order: a value refused at
     * construction says nothing about the class, only about that value, and the next one may well
     * build. What is tried is the same index at every position at once, which keeps the attempts linear
     * in the longest candidate list rather than multiplying them.
     */
    private static Attempt build(Subject subject, List<Axis> axes, int[] where, CandidateCheck check) {
        int deepest = 0;
        for (int i = 0; i < axes.size(); i++) {
            List<FixtureTemplate> candidates =
                    axes.get(i).classes().get(where[i]).representatives().candidates();
            if (candidates.isEmpty()) {
                return new Attempt(null, UnresolvedCombination.Reason.NO_REPRESENTATIVE,
                        label(axes.get(i), where[i]));
            }
            deepest = Math.max(deepest, candidates.size());
        }
        for (int attempt = 0; attempt < deepest; attempt++) {
            Map<String, FixtureTemplate> byPath = new LinkedHashMap<>();
            for (int i = 0; i < axes.size(); i++) {
                List<FixtureTemplate> candidates =
                        axes.get(i).classes().get(where[i]).representatives().candidates();
                byPath.put(axes.get(i).path().toString(),
                        candidates.get(Math.min(attempt, candidates.size() - 1)));
            }
            Composed composed = inputsOf(subject, byPath, check);
            if (composed.inputs() != null) {
                return new Attempt(new GeneratedRow(labels(axes, where), composed.inputs()), null,
                        null);
            }
            if (composed.reason() == UnresolvedCombination.Reason.NO_REPRESENTATIVE) {
                // Another candidate changes nothing: the position has no values at all.
                return new Attempt(null, composed.reason(), composed.detail());
            }
        }
        return new Attempt(null, UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED, null);
    }

    /**
     * One value per parameter, or null where one of them could not be produced or would not build.
     *
     * <p>Several axes on one parameter are one value, not several: {@code request.kind} and
     * {@code request.cost} are two positions of one {@code Request}, and a row writes one of those.
     */
    private static Composed inputsOf(Subject subject, Map<String, FixtureTemplate> byPath,
                                     CandidateCheck check) {
        List<FixtureTemplate> inputs = new ArrayList<>();
        for (int p = 0; p < subject.parameters().size() && p < subject.types().size(); p++) {
            TermPath at = TermPath.of(subject.parameters().get(p));
            Composition built = compose(subject.types().get(p), at, byPath, subject.symbols(), 0);
            if (built.value() == null) {
                // Nothing could be written at all: a field of a type nothing stands for. Which is not
                // the same as a value that was written and refused, and reporting it as one sends the
                // author looking for a rule relating two inputs that has nothing to do with it.
                return new Composed(null, UnresolvedCombination.Reason.NO_REPRESENTATIVE,
                        built.missingAt());
            }
            if (check.refuse(p, built.value()).isPresent()) {
                return new Composed(null, UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED, null);
            }
            inputs.add(built.value());
        }
        return new Composed(inputs, null, null);
    }

    /** One attempt at a row's inputs: the values, or why there are none. */
    private record Composed(List<FixtureTemplate> inputs, UnresolvedCombination.Reason reason,
                            String detail) {}

    /** One position's value, or the position that had none. */
    private record Composition(FixtureTemplate value, String missingAt) {}

    /** The value at one position: what an axis fixed there, or a record built out of its fields, or a
     * value that stands for the type. Null where nothing can be written. */
    private static Composition compose(Type type, TermPath at, Map<String, FixtureTemplate> byPath,
                                       Symbols symbols, int depth) {
        FixtureTemplate fixed = byPath.get(at.toString());
        if (fixed != null) {
            return new Composition(fixed, null);
        }
        if (depth < MAX_DEPTH && type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && !data.newtype()) {
            Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
            if (!fields.isEmpty()) {
                Map<String, FixtureTemplate> built = new LinkedHashMap<>();
                for (Map.Entry<String, Type> field : fields.entrySet()) {
                    Composition value = compose(field.getValue(), at.then(field.getKey()), byPath,
                            symbols, depth + 1);
                    if (value.value() == null) {
                        return value;   // the field that had none, not the record that wanted it
                    }
                    built.put(field.getKey(), value.value());
                }
                return new Composition(FixtureTemplate.record(ref.name(), built), null);
            }
        }
        List<FixtureTemplate> stands = Partitions.representativesOf(type, symbols);
        return stands.isEmpty() ? new Composition(null, at + ": " + Type.show(type))
                : new Composition(stands.get(0), null);
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
