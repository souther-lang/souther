package souther.compiler.numeric;

import java.util.ArrayList;
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
 * <p>An equality is left out where the numbers it needs cannot be held, which says less and nothing
 * false. Past {@link #MOST_UPDATES} updates of a weight in all, or where the equalities contradict
 * each other, there is nothing to read: either is a fact about the whole set and not about any one
 * equality of it.
 *
 * @param <A> what a position is
 */
final class EqualitySpan<A> {

    /** The most weights the equalities of one set may update, taken together. */
    static final int MOST_UPDATES = 200_000;

    /** {@code Σ coefs·position + constant}. */
    record Residue<A>(Map<A, ExactRatio> coefs, ExactRatio constant) {}

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
     * of them could be taken, they contradict each other, or they are more work than
     * {@link #MOST_UPDATES}.
     */
    static <A> EqualitySpan<A> of(List<AffineConstraint<A>> rules, CanonicalOrder<A> order) {
        Building<A> building = new Building<>(order);
        for (AffineConstraint<A> each : rules) {
            if (each instanceof AffineConstraint.Equality<A> equality && !building.take(equality)) {
                return null;
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
            for (Map.Entry<A, ExactRatio> each : solving.rest().entrySet()) {
                if (updates != null && --updates[0] < 0) {
                    return null;
                }
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

        private final CanonicalOrder<A> order;
        private final List<Solving<A>> solvings = new ArrayList<>();
        private final int[] updates = {MOST_UPDATES};

        private Building(CanonicalOrder<A> order) {
            this.order = order;
        }

        /** False where the set is past what is read: it contradicts itself or is too much work. */
        private boolean take(AffineConstraint.Equality<A> equality) {
            Map<A, ExactRatio> coefs = new LinkedHashMap<>();
            for (Map.Entry<A, ExactRatio> each : equality.form().entriesIn(order)) {
                coefs.put(each.getKey(), each.getValue());
            }
            Residue<A> left = reducedBy(solvings, coefs, equality.at().negated(), updates);
            if (updates[0] < 0) {
                return false;
            }
            if (left == null) {
                // The numbers this equality needs cannot be held, so it is left out.
                return true;
            }
            if (left.coefs().isEmpty()) {
                // Said already, or said against itself.
                return left.constant().isZero();
            }
            // Solved for the position the order walks last: which one is of no account to what is
            // read, and the same one for the same rules is what keeps the solvings the same.
            List<Map.Entry<A, ExactRatio>> walked = order.walking(left.coefs().entrySet(),
                    Map.Entry::getKey);
            Map.Entry<A, ExactRatio> last = walked.getLast();
            Map<A, ExactRatio> rest = new LinkedHashMap<>();
            for (Map.Entry<A, ExactRatio> each : walked) {
                if (!each.getKey().equals(last.getKey())) {
                    ExactRatio scaled = each.getValue().dividedBy(last.getValue()).orNull();
                    if (scaled == null) {
                        return true;
                    }
                    rest.put(each.getKey(), scaled);
                }
            }
            ExactRatio at = left.constant().negated().dividedBy(last.getValue()).orNull();
            if (at != null) {
                solvings.add(new Solving<>(last.getKey(), rest, at));
            }
            return true;
        }
    }
}
