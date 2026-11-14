package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.LongAdder;
import java.util.function.Function;

/**
 * Rules that are all sums of the same growing prefix, read in the coordinates where each of those
 * sums is one position.
 *
 * <p>A chain of {@code a_k = a_(k-1) + p_k} states, for every {@code k}, a bound on
 * {@code p_1 + ... + p_k} beside a bound on each {@code p_k}. Written over the {@code p}s every
 * sum names every position before it, and a reading that asks what the rest of a sum leaves has
 * a premise to look at for each of them. Written over {@code s_k = p_1 + ... + p_k} the same rules
 * are a bound on {@code s_k} and a bound on {@code s_k - s_(k-1)}: the shapes the difference
 * closure holds exactly, and which it closes without reading any rule against another.
 *
 * <p>The coordinates are the positions in the order of the prefixes, the positions of the first
 * prefix first in the order the caller's {@link CanonicalOrder} puts them in, and each position is
 * the difference of its coordinate and the one before it. That is a change of basis of determinant
 * one over the whole numbers, so the rules in the new coordinates and the rules as they were have
 * the same whole-number solutions, each position being the same value read through it.
 *
 * <p><b>What its answer being exact rests on, and where each of it is checked.</b> Chosen only
 * where it comes to something the difference closure holds exactly, and each assumption has the one
 * place it is checked at, so that a rule or a question that breaks one is met there and not after:
 *
 * <ul>
 *   <li>every rule is a half-space, every position is a whole number, the rules' supports are
 *       prefixes one position longer than the one before, and every position is in a prefix:
 *       {@link #over};</li>
 *   <li>every number the change writes is one the exact arithmetic holds, every rule it writes is a
 *       bound on one coordinate or on the difference of two, and every bound is a whole number the
 *       positions reach — a closure of whole-number differences is exact for these and for no other
 *       bound, so a rule built as it stands with a bound between two whole numbers has no basis:
 *       {@link #over};</li>
 *   <li>every hop of the closure of the differences was one the exact arithmetic could sum, and
 *       every position's bounds are ones it can write: {@link #over};</li>
 *   <li>what a question comes to can be summed, which the closure does when it is asked and not
 *       before: {@link #highest}, which does not answer a form it cannot sum, as it does not
 *       answer a form that is not one coordinate or the difference of two.</li>
 * </ul>
 *
 * <p>Where any of the first three is not so there is no basis, and the rules are closed as they are
 * stated. Which of two positions of the shortest prefix is the first is not the order the rules
 * arrived in, and does not change what any position is left.
 *
 * <p>A basis is chosen for a part of the rules and not for all of them at once, since rules of
 * another part leave no basis to choose. So the closure of the parts is no wider than the closure of
 * the rules in one run, and is exact where that is an approximation ({@link ClosedState}).
 *
 * @param <A> what a position of the rules is
 */
final class PrefixBasis<A> {

    private static final CanonicalOrder<Integer> BY_PLACE = Integer::compare;

    /** The coordinate each position is the difference of with the one before it. */
    private final Map<A, Integer> places;

    /** The rules in the coordinates, their differences closed. */
    private final Closed closed;

    /** What each position is left, which is the whole of what the rules leave it; null where the
     *  rules leave nothing. */
    private final Box<A> box;

    /**
     * What the closure of the rules in the coordinates answers. Rules that bound a coordinate or
     * the difference of two neighbours, which is every rule of a chain of prefix sums, are closed
     * along the chain ({@link ChainBounds}); any other rule the basis accepts is closed by
     * {@link DifferenceBounds}, whose answers the first gives for the rules it takes.
     */
    interface Closed {

        boolean holdsNothing();

        boolean everyHopWasComposed();

        ExactCut upperBoundOf(int coordinate);

        ExactCut lowerBoundOf(int coordinate);

        ExactCut differenceBound(int a, int b);

        boolean differenceBoundWasComposed(int a, int b);
    }

    /** The closure by {@link DifferenceBounds}, for rules that are not bounds along a chain. */
    private record Differences(DifferenceBounds<Integer> of) implements Closed {

        @Override
        public boolean holdsNothing() {
            return of.holdsNothing();
        }

        @Override
        public boolean everyHopWasComposed() {
            return of.everyHopWasComposed();
        }

        @Override
        public ExactCut upperBoundOf(int coordinate) {
            return of.upperBoundOf(coordinate);
        }

        @Override
        public ExactCut lowerBoundOf(int coordinate) {
            return of.lowerBoundOf(coordinate);
        }

        @Override
        public ExactCut differenceBound(int a, int b) {
            return of.differenceBound(a, b);
        }

        @Override
        public boolean differenceBoundWasComposed(int a, int b) {
            return of.differenceBoundWasComposed(a, b);
        }
    }

    /** The rules this basis was made from, in the order they were handed over. */
    private final List<AffineConstraint<A>> rules;

    /** The rules in the coordinates, one for each of {@link #rules}. */
    private final List<AffineConstraint<Integer>> moved;

    /** How many positions the shortest and the longest prefix hold. */
    private final int smallest;
    private final int largest;

    /** Every position the rules weigh, in the order the rules name them. */
    private final Set<A> positions;

    /**
     * What a form weighs over the coordinates, kept for the forms asked of the bases that follow
     * one another: a basis made from the one before keeps the places that one had, so what was
     * worked out with them is what it would work out again.
     *
     * <p>Only the last of a line writes on, as {@link souther.compiler.collect.AppendOnly} does: a
     * basis made from one that has another made from it starts a line of its own, since the
     * positions the two add are placed apart. An entry is read by a basis that holds as many places
     * as the one that made it did, and not by one with fewer.
     */
    private static final class Line<A> {

        private int written;

        private Line(int written) {
            this.written = written;
        }
    }

    /**
     * A form's weights over the coordinates, the line of bases they were worked out on, and how many
     * places the basis that worked them out held. Kept by the form ({@link Weighed}), and read by a
     * basis of the same line that holds as many places and not by one that holds fewer.
     */
    record Prepared<A>(Object line, int placed, Map<Integer, ExactRatio> weights) {}

    private static final LongAdder TERMS_READ = new LongAdder();

    private static final LongAdder CLOSED_BY_EVERY_PAIR = new LongAdder();

    /**
     * How many bases have been closed by {@link DifferenceBounds}, the difference of every pair of
     * coordinates, and not along the chain ({@link ChainBounds}), for the same test as
     * {@link #termsRead}. A chain of prefix sums is closed along the chain, and a basis closed by
     * every pair is the whole of what made it cost the square of its length.
     */
    static long closedByEveryPair() {
        return CLOSED_BY_EVERY_PAIR.sum();
    }

    /** The closure of {@code moved} where they are not bounds along a chain. */
    private static Closed closedByEveryPair(List<AffineConstraint<Integer>> moved) {
        CLOSED_BY_EVERY_PAIR.increment();
        return new Differences(DifferenceBounds.over(moved, BY_PLACE));
    }

    /**
     * How many positions of a rule the bases made so far have read, for a test holding what a path
     * costs to how many rules it says and not how many pairs of them: that is a shape and not a
     * speed. A basis made from the one before reads the rules added and no others.
     */
    static long termsRead() {
        return TERMS_READ.sum();
    }

    private final Line<A> line;

    /**
     * The positions of the shortest prefix in the order the places were given them in, which is
     * the one thing of the order a basis rests on: the places of every position after them follow
     * from which prefix adds it. A basis is made from this one only for an order that puts these in
     * the same places, each before the next ({@link #following}).
     */
    private final List<A> first;

    private PrefixBasis(Map<A, Integer> places, Closed closed, List<AffineConstraint<A>> rules,
                        List<AffineConstraint<Integer>> moved, int smallest, int largest,
                        Set<A> positions, Line<A> line, List<A> first) {
        this.line = line;
        this.first = first;
        this.places = places;
        this.closed = closed;
        this.rules = rules;
        this.moved = moved;
        this.smallest = smallest;
        this.largest = largest;
        this.positions = positions;
        this.box = closed.holdsNothing() ? null : boxOf(places.keySet());
    }

    /** How many rules this was made from. */
    int ruleCount() {
        return rules.size();
    }

    /** Every position the rules this was made from weigh, in the order they name them. */
    Set<A> positions() {
        return positions;
    }

    /** What a basis says of how high a form comes to. */
    sealed interface Highest {

        /** The form comes to no more than {@code at}, which it reaches. */
        record Within(ExactCut at) implements Highest {}

        /** Nothing bounds the form above. */
        record Unbounded() implements Highest {}

        /** This basis does not say: the form is not one it answers, or the exact arithmetic could
         *  not hold what it comes to. Not that nothing bounds it — the rules as they are stated are
         *  to be asked. */
        record NotAnswered() implements Highest {}

        Unbounded UNBOUNDED = new Unbounded();
        NotAnswered NOT_ANSWERED = new NotAnswered();
    }

    /**
     * The basis the rules are read in, or null where they have none that answers exactly and
     * completely: the rules, the positions and the closure of their differences are all of a kind
     * the difference closure holds exactly, every hop of it was one the exact arithmetic could sum,
     * and every position's bounds are ones it can write. Without that a basis would leave less than
     * the rules as they are stated do, and this is where that is decided and nowhere after.
     */
    static <A> PrefixBasis<A> over(List<AffineConstraint<A>> constraints,
                                   Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        Set<Set<A>> distinct = new HashSet<>();
        List<Set<A>> supports = new ArrayList<>();
        List<List<Map.Entry<A, ExactRatio>>> walked = new ArrayList<>(constraints.size());
        Set<A> positions = new LinkedHashSet<>();
        for (AffineConstraint<A> rule : constraints) {
            if (!(rule instanceof AffineConstraint.HalfSpace<A> half)) {
                return null;
            }
            List<Map.Entry<A, ExactRatio>> entries = half.form().entriesIn(order);
            TERMS_READ.add(entries.size());
            Set<A> support = new HashSet<>();
            for (Map.Entry<A, ExactRatio> each : entries) {
                if (spacing.apply(each.getKey()) != Granularity.DISCRETE) {
                    return null;
                }
                support.add(each.getKey());
                positions.add(each.getKey());
            }
            walked.add(entries);
            if (support.size() >= 2 && distinct.add(support)) {
                supports.add(support);
            }
        }
        if (supports.isEmpty()) {
            return null;
        }
        supports.sort((a, b) -> Integer.compare(a.size(), b.size()));
        for (int at = 1; at < supports.size(); at++) {
            if (supports.get(at).size() != supports.get(at - 1).size() + 1
                    || !supports.get(at).containsAll(supports.get(at - 1))) {
                return null;
            }
        }
        Map<A, Integer> places = placesOf(supports, order);
        if (places == null) {
            return null;
        }
        List<AffineConstraint<Integer>> moved = new ArrayList<>(constraints.size());
        for (int at = 0; at < constraints.size(); at++) {
            AffineConstraint.HalfSpace<A> half =
                    (AffineConstraint.HalfSpace<A>) constraints.get(at);
            AffineConstraint.HalfSpace<Integer> there =
                    half(weighed(walked.get(at), places), half.bound());
            if (there == null || !DifferenceBounds.canHold(there, BY_PLACE)
                    || !onTheWholeNumbers(there.bound())) {
                return null;
            }
            moved.add(there);
        }
        Closed closed = ChainBounds.over(moved);
        if (closed == null) {
            closed = closedByEveryPair(moved);
        }
        if (!closed.everyHopWasComposed()) {
            return null;
        }
        List<A> first = new ArrayList<>(supports.getFirst());
        first.sort(order);
        PrefixBasis<A> basis = new PrefixBasis<>(places, closed, List.copyOf(constraints), moved,
                supports.getFirst().size(), supports.getLast().size(),
                Collections.unmodifiableSet(positions), new Line<>(places.size()),
                Collections.unmodifiableList(first));
        return basis.holdsNothing() || basis.box != null ? basis : null;
    }

    /**
     * Whether a basis made from this one, for the rules these are the very ones of followed by
     * others, rests on what this rests on: every position of the rules whole-numbered as it was,
     * and the order putting the positions of the shortest prefix in the same places. The rules being
     * the same says neither — the rules added name some of the positions, and the spacing and the
     * order are the question's, which may have changed for the rest.
     */
    private boolean restsOnWhatThisRestsOn(Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        for (A position : positions) {
            if (spacing.apply(position) != Granularity.DISCRETE) {
                return false;
            }
        }
        for (int at = 1; at < first.size(); at++) {
            if (order.compare(first.get(at - 1), first.get(at)) >= 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * The basis {@code constraints} are read in, made from {@code before}, the basis of the rules
     * they are the very ones followed by others, so that the rules before are not read again; or
     * null where this cannot say, in which case {@link #over} is asked.
     *
     * <p>What a rule is read to is its support and its place in the coordinates, and neither
     * depends on the rules after it while the prefixes keep their places: a rule added is one
     * whose support is one of the prefixes there are, or the longest of them with one more
     * position. A rule that is not asks {@link #over}, which says whether there is a basis at all.
     * The answer is the one {@link #over} gives for the same rules — what is read of the rules before
     * is what it was read to — at a cost of the rules added and not of all of them.
     */
    static <A> PrefixBasis<A> following(PrefixBasis<A> before, List<AffineConstraint<A>> constraints,
                                        Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        int had = before.rules.size();
        if (constraints.size() <= had || !before.restsOnWhatThisRestsOn(spacing, order)) {
            return null;
        }
        for (int at = 0; at < had; at++) {
            if (constraints.get(at) != before.rules.get(at)) {
                return null;
            }
        }
        Map<A, Integer> places = new HashMap<>(before.places);
        Set<A> positions = new LinkedHashSet<>(before.positions);
        int largest = before.largest;
        List<AffineConstraint.HalfSpace<A>> added = new ArrayList<>(constraints.size() - had);
        List<List<Map.Entry<A, ExactRatio>>> walked = new ArrayList<>(constraints.size() - had);
        for (int at = had; at < constraints.size(); at++) {
            if (!(constraints.get(at) instanceof AffineConstraint.HalfSpace<A> half)) {
                return null;
            }
            List<Map.Entry<A, ExactRatio>> entries = half.form().entriesIn(order);
            TERMS_READ.add(entries.size());
            for (Map.Entry<A, ExactRatio> each : entries) {
                if (spacing.apply(each.getKey()) != Granularity.DISCRETE) {
                    return null;
                }
                positions.add(each.getKey());
            }
            int size = entries.size();
            if (size >= 2) {
                if (size < before.smallest || size > largest + 1) {
                    return null;
                }
                int unplaced = 0;
                A fresh = null;
                for (Map.Entry<A, ExactRatio> each : entries) {
                    Integer place = places.get(each.getKey());
                    if (place == null) {
                        unplaced++;
                        fresh = each.getKey();
                    } else if (place >= size) {
                        return null;
                    }
                }
                if (size == largest + 1) {
                    if (unplaced != 1) {
                        return null;
                    }
                    places.put(fresh, largest);
                    largest = size;
                } else if (unplaced != 0) {
                    return null;
                }
            }
            walked.add(entries);
            added.add(half);
        }
        List<AffineConstraint<Integer>> moved = new ArrayList<>(before.moved);
        for (int at = 0; at < added.size(); at++) {
            AffineConstraint.HalfSpace<Integer> there =
                    half(weighed(walked.get(at), places), added.get(at).bound());
            if (there == null || !DifferenceBounds.canHold(there, BY_PLACE)
                    || !onTheWholeNumbers(there.bound())) {
                return null;
            }
            moved.add(there);
        }
        Closed closed = ChainBounds.over(moved);
        if (closed == null) {
            closed = closedByEveryPair(moved);
        }
        if (!closed.everyHopWasComposed()) {
            return null;
        }
        Map<A, Integer> placed = Map.copyOf(places);
        Line<A> line;
        synchronized (before.line) {
            if (before.line.written == before.places.size()) {
                line = before.line;
                line.written = placed.size();
            } else {
                line = new Line<>(placed.size());
            }
        }
        PrefixBasis<A> basis = new PrefixBasis<>(placed, closed, List.copyOf(constraints),
                moved, before.smallest, largest, Collections.unmodifiableSet(positions), line,
                before.first);
        if (!basis.holdsNothing() && basis.box == null) {
            return null;
        }
        long[] counting = COUNTING_FOLLOWED;
        if (counting != null) {
            counting[0]++;
        }
        return basis;
    }

    /** Where a test in this package counts the bases made from the basis before, and null everywhere
     *  else. What a basis answers is the same however it was made, so how it was made has nowhere
     *  else to be read. */
    static long[] COUNTING_FOLLOWED;

    /**
     * Whether a bound is one a closure of whole-number differences is exact for: a whole number the
     * positions reach, which is how a bound on whole-number positions is written when the rules were
     * read ({@link AffineConstraint#of}). A rule built as it stands, with a bound between two whole
     * numbers or one they do not reach, is closed by a real-valued closure to a bound no whole number
     * attains, and is not one this is exact for.
     */
    private static boolean onTheWholeNumbers(ExactCut bound) {
        return bound.inclusive() && bound.at().isWhole();
    }

    /** The place of each position, or null where a position is in no prefix or two of the first
     *  prefix cannot be told apart. */
    private static <A> Map<A, Integer> placesOf(List<Set<A>> supports, CanonicalOrder<A> order) {
        Map<A, Integer> places = new HashMap<>();
        List<A> first = new ArrayList<>(supports.getFirst());
        first.sort(order);
        for (int at = 1; at < first.size(); at++) {
            if (order.compare(first.get(at - 1), first.get(at)) == 0) {
                return null;
            }
        }
        first.forEach(position -> places.put(position, places.size()));
        for (Set<A> support : supports.subList(1, supports.size())) {
            A added = null;
            for (A position : support) {
                if (!places.containsKey(position)) {
                    added = position;
                }
            }
            if (added == null) {
                return null;
            }
            places.put(added, places.size());
        }
        return places;
    }

    /**
     * What {@code weights} come to over the coordinates, or null where a position is in no prefix
     * or a number is not one the exact arithmetic holds. A weight on a position is a weight on its
     * coordinate and the opposite weight on the one before.
     */
    private static <A> Map<Integer, ExactRatio> weighed(Iterable<Map.Entry<A, ExactRatio>> weights,
                                                        Map<A, Integer> places) {
        Map<Integer, ExactRatio> out = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : weights) {
            Integer at = places.get(each.getKey());
            if (at == null || !added(out, at, each.getValue())
                    || (at > 0 && !added(out, at - 1, each.getValue().negated()))) {
                return null;
            }
        }
        out.values().removeIf(ExactRatio::isZero);
        return out;
    }

    private static boolean added(Map<Integer, ExactRatio> weights, int at, ExactRatio by) {
        ExactRatio now = weights.getOrDefault(at, ExactRatio.ZERO).plus(by).orNull();
        if (now == null) {
            return false;
        }
        weights.put(at, now);
        return true;
    }

    /** The rule {@code weights <= bound} over the coordinates, in lowest terms, or null. */
    private static AffineConstraint.HalfSpace<Integer> half(Map<Integer, ExactRatio> weights,
                                                            ExactCut bound) {
        if (weights == null
                || !(CanonicalForm.of(weights) instanceof CanonicalForm.Scaled<Integer> scaled)) {
            return null;
        }
        ExactRatio at = bound.at().dividedBy(scaled.by()).orNull();
        return at == null ? null
                : new AffineConstraint.HalfSpace<>(scaled.form(), new ExactCut(at, bound.inclusive()));
    }

    boolean holdsNothing() {
        return closed.holdsNothing();
    }

    /**
     * What each position is left, which is the whole of what the rules leave it: nothing sound
     * narrows a position this does not. Asked only where the rules leave something.
     */
    Box<A> box() {
        return box;
    }

    /**
     * What {@code form} weighs over the coordinates, or null where a position is in no prefix or a
     * number is not one the exact arithmetic holds. Kept with the form: it is read again, by this
     * basis or by one of the line it is on, and not weighed again. What is null is not kept, since a
     * position that is in no prefix here may be in one of the next.
     */
    private Map<Integer, ExactRatio> weighedOver(Weighed<A> form) {
        Prepared<A> kept = form.prepared();
        if (kept != null && kept.line() == line && kept.placed() <= places.size()) {
            return kept.weights();
        }
        Map<Integer, ExactRatio> weights = weighed(form.coefs().entrySet(), places);
        // A form of one position or two is weighed as fast as it is looked up.
        if (weights != null && form.coefs().size() > 2) {
            form.prepared(new Prepared<>(line, places.size(), weights));
        }
        return weights;
    }

    /** What each position is left, or null where one of its bounds is not one this can write. */
    private Box<A> boxOf(Set<A> positions) {
        Map<A, ExactCut> least = new LinkedHashMap<>();
        Map<A, ExactCut> most = new LinkedHashMap<>();
        for (A position : positions) {
            Highest above = highest(Weighed.of(Map.of(position, ExactRatio.ONE)), ExactRatio.ZERO);
            Highest below = highest(Weighed.of(Map.of(position, ExactRatio.ONE.negated())),
                    ExactRatio.ZERO);
            if (above instanceof Highest.Within within) {
                most.put(position, within.at());
            } else if (!(above instanceof Highest.Unbounded)) {
                return null;
            }
            if (below instanceof Highest.Within within) {
                least.put(position,
                        new ExactCut(within.at().at().negated(), within.at().inclusive()));
            } else if (!(below instanceof Highest.Unbounded)) {
                return null;
            }
        }
        return new Box<>(least, most);
    }

    /**
     * How high {@code form} weighs, plus {@code constant}, comes to: exactly, for a form that comes
     * to one coordinate or to the difference of two in the basis, such as a position or a prefix
     * sum, and not answered for anything else.
     *
     * <p>Exact because the closure of whole-number differences is: a bound it holds on a coordinate
     * or a difference is reached by a solution of the rules, so nothing sound bounds the form
     * lower, and no bound is missing, every hop of it having been summed ({@link #over}). That the
     * form is bounded by nothing and that the exact arithmetic could not hold what it comes to are
     * different answers, and are told apart. Asked only where the rules leave something.
     */
    Highest highest(Weighed<A> form, ExactRatio constant) {
        Map<Integer, ExactRatio> weights = weighedOver(form);
        if (weights == null) {
            return Highest.NOT_ANSWERED;
        }
        List<Map.Entry<Integer, ExactRatio>> terms = new ArrayList<>(weights.entrySet());
        ExactCut bound;
        ExactRatio weight;
        if (terms.size() == 1) {
            weight = terms.getFirst().getValue();
            bound = weight.signum() > 0 ? closed.upperBoundOf(terms.getFirst().getKey())
                    : closed.lowerBoundOf(terms.getFirst().getKey());
        } else if (terms.size() == 2) {
            Map.Entry<Integer, ExactRatio> up = terms.getFirst();
            Map.Entry<Integer, ExactRatio> down = terms.getLast();
            if (up.getValue().signum() < 0) {
                up = terms.getLast();
                down = terms.getFirst();
            }
            weight = up.getValue();
            if (!weight.equals(down.getValue().negated())
                    || !closed.differenceBoundWasComposed(up.getKey(), down.getKey())) {
                return Highest.NOT_ANSWERED;
            }
            bound = closed.differenceBound(up.getKey(), down.getKey());
        } else {
            return Highest.NOT_ANSWERED;
        }
        if (bound == null) {
            return Highest.UNBOUNDED;
        }
        ExactRatio scaled = weight.times(bound.at()).orNull();
        ExactRatio at = scaled == null ? null : scaled.plus(constant).orNull();
        return at == null ? Highest.NOT_ANSWERED
                : new Highest.Within(new ExactCut(at, bound.inclusive()));
    }
}
