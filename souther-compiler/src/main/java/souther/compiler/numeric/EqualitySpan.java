package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a set of equalities comes to together: the sums that are a combination of them, and what
 * each other sum is once they are taken out of it.
 *
 * <p>Held as an echelon form and not as a reduced one. Each equality is put in terms of the
 * equalities already held and then kept as it is; no equality held is rewritten when another is
 * added. A reduced form rewrites every equality that names the position a new one is solved for, so
 * a chain of equalities each naming the next costs the square of its length in weights updated, and
 * a bound on that work threw the whole set away. Here a sum is read by taking the equalities in the
 * order they were added: each takes its own position out of the sum, and none that comes later
 * names it again, so one pass is the whole of it.
 *
 * <p>What is read of it does not turn on which position each equality was solved for. A sum written
 * without any position solved for is the one the sum is equal to wherever the equalities hold, and
 * two sums that are equal wherever the equalities hold are written alike: the difference of the two
 * is a combination of the equalities, and a combination is written as nothing. So {@link #residue}
 * answers the same under any naming of the positions and under any order the equalities were
 * said in, which is what asking each way of solving for each position and counting the ways is not
 * able to.
 *
 * <p>What is read does not turn on the naming, and neither does what it costs to read. An equality
 * is solved for the position that the fewest equalities of the set name, so a position a single
 * equality names is taken out of it and out of nothing else: a chain whose every equality has a
 * position of its own costs its length, whichever of the positions it names carry the lower names.
 * Which of positions that the same number of equalities name is solved for is the last of them in
 * the order, which decides nothing about the cost where they are alike in the set.
 *
 * <p>An equality is left out where the numbers it needs cannot be held, which says less and nothing
 * false. Where the equalities contradict each other there is nothing to read. Past
 * {@link #MOST_UPDATES} updates of a weight in all, the equalities held until then are what is
 * read: each of them is a consequence of the set, so a sum shown from them is shown, and the ones
 * not reached are no more than left out.
 *
 * @param <A> what a position is
 */
final class EqualitySpan<A> {

    /** The most weights the equalities of one set may update, taken together. */
    static final int MOST_UPDATES = 200_000;

    /** {@code Σ coefs·position + constant}. */
    record Residue<A>(Map<A, ExactRatio> coefs, ExactRatio constant) {}

    /** The weight an equality, said at {@code at}th among the equalities, gives a position. */
    private record Cell(int at, ExactRatio weight) {}

    /** An equality solved for {@code pivot}: {@code pivot + Σ rest = at}. */
    private record Solving<A>(A pivot, Map<A, ExactRatio> rest, ExactRatio at) {}

    private final CanonicalOrder<A> order;
    private final List<Solving<A>> solvings;

    private EqualitySpan(CanonicalOrder<A> order, List<Solving<A>> solvings) {
        this.order = order;
        this.solvings = List.copyOf(solvings);
    }

    /**
     * What the equalities among {@code rules} come to, or null where there is nothing to read: none
     * of them could be taken, or they contradict each other. Those held when the work ran out
     * ({@link #MOST_UPDATES}) are what is read.
     */
    static <A> EqualitySpan<A> of(List<AffineConstraint<A>> rules, CanonicalOrder<A> order) {
        return of(rules, order, MOST_UPDATES);
    }

    /** The same, with the work it may spend said: a smaller one reads the equalities it reached
     *  before it was spent, in the order they were stated. */
    static <A> EqualitySpan<A> of(List<AffineConstraint<A>> rules, CanonicalOrder<A> order,
                                  int mostUpdates) {
        Map<A, List<Cell>> named = new HashMap<>();
        int at = 0;
        for (AffineConstraint<A> each : rules) {
            if (each instanceof AffineConstraint.Equality<A> equality) {
                for (Map.Entry<A, ExactRatio> position : equality.form().entriesIn(order)) {
                    named.computeIfAbsent(position.getKey(), _ -> new ArrayList<>())
                            .add(new Cell(at, position.getValue()));
                }
                at++;
            }
        }
        Building<A> building = new Building<>(order, named, mostUpdates);
        for (AffineConstraint<A> each : rules) {
            if (!(each instanceof AffineConstraint.Equality<A> equality)) {
                continue;
            }
            switch (building.take(equality)) {
                case CONTRADICTS -> {
                    return null;
                }
                case OUT_OF_WORK -> {
                    return building.solvings.isEmpty() ? null
                            : new EqualitySpan<>(order, building.solvings);
                }
                case HELD -> { }
            }
        }
        return building.solvings.isEmpty() ? null : new EqualitySpan<>(order, building.solvings);
    }

    /**
     * {@code form + constant} with the equalities taken out of it, or null where the numbers
     * cannot be held.
     */
    Residue<A> residue(CanonicalForm<A> form, ExactRatio constant) {
        Map<A, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : form.entriesIn(order)) {
            coefs.put(each.getKey(), each.getValue());
        }
        return reducedBy(solvings, coefs, constant, null);
    }

    /**
     * {@code coefs + constant} with the position of each equality taken out, in the order the
     * equalities were added, or null where the numbers cannot be held. {@code updates} counts the
     * weights updated where it is given.
     */
    private static <A> Residue<A> reducedBy(List<Solving<A>> solvings, Map<A, ExactRatio> coefs,
                                            ExactRatio constant, int[] updates) {
        ExactRatio at = constant;
        for (Solving<A> solving : solvings) {
            ExactRatio weight = coefs.remove(solving.pivot());
            if (weight == null) {
                continue;
            }
            // What taking one equality out costs is how many weights it names, whether or not the
            // numbers go on being held: counted as they are updated, a cost would be the divisions
            // done before one failed, which turns on the order the positions are walked in.
            if (updates != null) {
                updates[0] -= solving.rest().size();
                if (updates[0] < 0) {
                    return null;
                }
            }
            for (Map.Entry<A, ExactRatio> each : solving.rest().entrySet()) {
                ExactRatio moved = weight.times(each.getValue()).orNull();
                ExactRatio had = coefs.getOrDefault(each.getKey(), ExactRatio.ZERO);
                ExactRatio now = moved == null ? null : had.minus(moved).orNull();
                if (now == null) {
                    return null;
                }
                if (now.isZero()) {
                    coefs.remove(each.getKey());
                } else {
                    coefs.put(each.getKey(), now);
                }
            }
            ExactRatio taken = weight.times(solving.at()).orNull();
            at = taken == null ? null : at.plus(taken).orNull();
            if (at == null) {
                return null;
            }
        }
        return new Residue<>(coefs, at);
    }

    /** The equalities being taken, one at a time. */
    private static final class Building<A> {

        /** What taking one equality came to. */
        private enum Taken {
            /** It is held, or said already, or left out for numbers that cannot be held. */
            HELD,
            /** It is false beside the ones held. */
            CONTRADICTS,
            /** There was no work left to put it in terms of the ones held. */
            OUT_OF_WORK
        }

        private final CanonicalOrder<A> order;
        /** The equalities of the whole set that name each position, and by what weight: the
         *  position's column, which is what two positions are told apart by. */
        private final Map<A, List<Cell>> named;
        private final List<Solving<A>> solvings = new ArrayList<>();
        private final int[] updates;

        private Building(CanonicalOrder<A> order, Map<A, List<Cell>> named, int mostUpdates) {
            this.order = order;
            this.named = named;
            this.updates = new int[] {mostUpdates};
        }

        private Taken take(AffineConstraint.Equality<A> equality) {
            Map<A, ExactRatio> coefs = new LinkedHashMap<>();
            for (Map.Entry<A, ExactRatio> each : equality.form().entriesIn(order)) {
                coefs.put(each.getKey(), each.getValue());
            }
            Residue<A> left = reducedBy(solvings, coefs, equality.at().negated(), updates);
            if (updates[0] < 0) {
                return Taken.OUT_OF_WORK;
            }
            if (left == null) {
                // The numbers this equality needs cannot be held, so it is left out.
                return Taken.HELD;
            }
            if (left.coefs().isEmpty()) {
                // Said already, or said against itself.
                return left.constant().isZero() ? Taken.HELD : Taken.CONTRADICTS;
            }
            // Solved for the first position, in an order the names have no part in, whose weight
            // the others can be divided by: fewest equalities of the set naming it, which leaves
            // a position only this equality names out of every later one and so keeps the updates
            // of a chain to its length; then the size of its weight, then its sign. What each
            // choice costs is then the same for two namings of one set, which is what keeps the
            // work a reading may spend from showing the names. Only positions of one count, one
            // weight, are told apart by the order, and for those the cost is the same under a
            // renaming. A position whose weight the others cannot be divided by is passed over
            // for the next, so the equality is left out only where no position of it can be
            // solved for.
            List<Map.Entry<A, ExactRatio>> walked = order.walking(left.coefs().entrySet(),
                    Map.Entry::getKey);
            List<Map.Entry<A, ExactRatio>> toTry = new ArrayList<>(walked);
            Collections.reverse(toTry);
            toTry.sort(Comparator
                    .<Map.Entry<A, ExactRatio>>comparingInt(
                            each -> named.getOrDefault(each.getKey(), List.of()).size())
                    .thenComparing((one, other) -> columnsCompared(named.get(one.getKey()),
                            named.get(other.getKey())))
                    .thenComparing(each -> each.getValue().abs())
                    .thenComparingInt(each -> each.getValue().signum()));
            for (Map.Entry<A, ExactRatio> pivot : toTry) {
                Solving<A> solving = solvedFor(pivot, walked, left.constant());
                if (updates[0] < 0) {
                    return Taken.OUT_OF_WORK;
                }
                if (solving != null) {
                    solvings.add(solving);
                    break;
                }
            }
            return Taken.HELD;
        }

        /** The columns of two positions of one size, the first equality that tells them apart
         *  deciding: by which equality it is and then by its weight there. Two positions with one
         *  column are exchanged by a renaming that leaves the set as it is. */
        private static int columnsCompared(List<Cell> one, List<Cell> other) {
            for (int i = 0; i < Math.min(one.size(), other.size()); i++) {
                int by = Integer.compare(one.get(i).at(), other.get(i).at());
                if (by == 0) {
                    by = one.get(i).weight().compareTo(other.get(i).weight());
                }
                if (by != 0) {
                    return by;
                }
            }
            return 0;
        }

        /** {@code walked + constant} solved for {@code pivot}, or null where the weights cannot
         *  be held divided by its, or where the work ran out: every division is one of the weights
         *  updated that {@link EqualitySpan#MOST_UPDATES} bounds, so what a position that cannot be solved for
         *  costs is spent from the same work as reading the equalities is. */
        private Solving<A> solvedFor(Map.Entry<A, ExactRatio> pivot,
                                     List<Map.Entry<A, ExactRatio>> walked, ExactRatio constant) {
            // What trying a position costs is the width of the equality whichever way it comes
            // out, and not the divisions done before one failed: that is the order the positions
            // are walked in, which is the names', and a cost that turned on it would show them.
            updates[0] -= walked.size();
            if (updates[0] < 0) {
                return null;
            }
            Map<A, ExactRatio> rest = new LinkedHashMap<>();
            for (Map.Entry<A, ExactRatio> each : walked) {
                if (!each.getKey().equals(pivot.getKey())) {
                    ExactRatio scaled = each.getValue().dividedBy(pivot.getValue()).orNull();
                    if (scaled == null) {
                        return null;
                    }
                    rest.put(each.getKey(), scaled);
                }
            }
            ExactRatio at = constant.negated().dividedBy(pivot.getValue()).orNull();
            return at == null ? null : new Solving<>(pivot.getKey(), rest, at);
        }
    }
}
