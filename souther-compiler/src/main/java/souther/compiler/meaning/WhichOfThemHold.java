package souther.compiler.meaning;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

/**
 * A relation over how many of some statements hold, as the choices of which of them hold that put
 * the number where the relation does ({@link Quantity.HowManyHold}).
 *
 * <p>Only the choices the relation admits are made, and each of them once. Where it admits every
 * count from some number up, a choice is a fewest set of statements that come to that number, and
 * the rest may hold or not — so {@code count >= 1} over eighteen statements is eighteen choices and
 * not every way the eighteen could come out. Otherwise a choice is a set that comes to one count it
 * admits exactly, with every other statement failing: a relation faces one way
 * ({@link Relation.OneWay}), so that is a single count, and fewer than some number is read as the
 * denial of that number or more.
 *
 * <p>A statement written more than once is one statement weighed as many times: the same value
 * meets it as often as it was written or not at all.
 */
final class WhichOfThemHold {

    /** Each statement once, in the order first written. */
    private final List<Proposition> statements;

    /** How many times each of {@link #statements} was written. */
    private final List<Integer> weights;

    /** Which counts the relation admits, by how many hold. */
    private final boolean[] admitted;

    /** How many choices the reading that counted the statements makes of one comparison. */
    private final long mostChoices;

    private WhichOfThemHold(List<Proposition> statements, List<Integer> weights,
                            boolean[] admitted, long mostChoices) {
        this.statements = statements;
        this.weights = weights;
        this.admitted = admitted;
        this.mostChoices = mostChoices;
    }

    /**
     * {@code relation} read as which of its statements hold, or null where it is over anything but
     * one count of statements, or a count the arithmetic could not hold.
     */
    static WhichOfThemHold of(Relation relation) {
        if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().size() != 1
                || !(form.coefs().keySet().iterator().next()
                        instanceof Quantity.HowManyHold(List<Proposition> each, long mostChoices))) {
            return null;
        }
        Map<String, Proposition> once = new LinkedHashMap<>();
        Map<String, Integer> written = new LinkedHashMap<>();
        for (Proposition one : each) {
            once.putIfAbsent(one.key(), one);
            written.merge(one.key(), 1, Integer::sum);
        }
        ExactRatio by = form.coefs().values().iterator().next();
        boolean[] admitted = new boolean[each.size() + 1];
        for (int holding = 0; holding <= each.size(); holding++) {
            if (!(by.times(ExactRatio.of(holding)).flatMap(weighed -> weighed.plus(form.constant()))
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio at))) {
                return null;
            }
            admitted[holding] = rel.holds(at.signum());
        }
        return new WhichOfThemHold(List.copyOf(once.values()), List.copyOf(written.values()),
                admitted, mostChoices);
    }

    /** How many choices this is written as, counted no further than one past {@code most}. */
    long choices(long most) {
        long[] made = {0};
        walk(chosen -> ++made[0] <= most);
        return made[0];
    }

    /** Some one of the choices holding, or null where they are more than the reading that counted
     *  the statements makes. */
    Proposition writtenWithinWhatIsMade() {
        List<Proposition> ways = new ArrayList<>();
        walk(chosen -> ways.add(chosen) && ways.size() <= mostChoices);
        return ways.size() > mostChoices ? null : Proposition.any(ways);
    }

    /**
     * Each choice handed to {@code made} as what it states, until it answers false.
     */
    private void walk(Predicate<Proposition> made) {
        int all = weights.stream().mapToInt(Integer::intValue).sum();
        int fewest = firstAdmitted();
        int most = lastAdmitted();
        if (fewest < 0) {
            return;
        }
        if (fewest == 0 && most == all && admitsEveryCountBetween(fewest, most)) {
            made.test(new Proposition.Always(true));
            return;
        }
        if (most == all && admitsEveryCountBetween(fewest, most)) {
            fewestComingTo(fewest, made);
        } else {
            for (int holding = fewest; holding <= most; holding++) {
                if (admitted[holding] && !exactly(holding, made)) {
                    return;
                }
            }
        }
    }

    private int firstAdmitted() {
        for (int holding = 0; holding < admitted.length; holding++) {
            if (admitted[holding]) {
                return holding;
            }
        }
        return -1;
    }

    private int lastAdmitted() {
        for (int holding = admitted.length - 1; holding >= 0; holding--) {
            if (admitted[holding]) {
                return holding;
            }
        }
        return -1;
    }

    private boolean admitsEveryCountBetween(int fewest, int most) {
        for (int holding = fewest; holding <= most; holding++) {
            if (!admitted[holding]) {
                return false;
            }
        }
        return true;
    }

    /**
     * Each fewest set of statements that comes to {@code at} or more, holding; whether every one was
     * handed on.
     *
     * <p>Taken heaviest first, a set is fewest where it comes short until its last and lightest
     * member, so it is made where that member takes it to the number and grown no further.
     */
    private boolean fewestComingTo(int at, Predicate<Proposition> made) {
        List<Integer> order = heaviestFirst();
        return fewest(order, leftAfter(order), 0, 0, at, new ArrayList<>(), made);
    }

    private boolean fewest(List<Integer> order, int[] left, int from, int sum, int at,
                           List<Proposition> chosen, Predicate<Proposition> made) {
        for (int next = from; next < order.size() && sum + left[next] >= at; next++) {
            int one = order.get(next);
            chosen.add(statements.get(one));
            boolean going = sum + weights.get(one) >= at
                    ? made.test(Proposition.all(chosen))
                    : fewest(order, left, next + 1, sum + weights.get(one), at, chosen, made);
            chosen.removeLast();
            if (!going) {
                return false;
            }
        }
        return true;
    }

    /**
     * Each set of statements coming to exactly {@code at}, with every other statement failing;
     * whether every one was handed on.
     */
    private boolean exactly(int at, Predicate<Proposition> made) {
        List<Integer> order = heaviestFirst();
        return exactly(order, leftAfter(order), 0, 0, at, new boolean[statements.size()], made);
    }

    private boolean exactly(List<Integer> order, int[] left, int from, int sum, int at,
                            boolean[] chosen, Predicate<Proposition> made) {
        if (sum == at) {
            List<Proposition> parts = new ArrayList<>(statements.size());
            for (int one = 0; one < statements.size(); one++) {
                parts.add(chosen[one] ? statements.get(one) : statements.get(one).denied());
            }
            return made.test(Proposition.all(parts));
        }
        for (int next = from; next < order.size() && sum + left[next] >= at; next++) {
            int one = order.get(next);
            if (sum + weights.get(one) > at) {
                continue;
            }
            chosen[one] = true;
            boolean going = exactly(order, left, next + 1, sum + weights.get(one), at, chosen,
                    made);
            chosen[one] = false;
            if (!going) {
                return false;
            }
        }
        return true;
    }

    /** The statements by how many times each was written, most first and otherwise in order. */
    private List<Integer> heaviestFirst() {
        List<Integer> order = new ArrayList<>(statements.size());
        for (int one = 0; one < statements.size(); one++) {
            order.add(one);
        }
        order.sort(Comparator.comparingInt((Integer one) -> weights.get(one)).reversed());
        return order;
    }

    /** How many times the statements from each place in {@code order} on were written. */
    private int[] leftAfter(List<Integer> order) {
        int[] left = new int[order.size() + 1];
        for (int at = order.size() - 1; at >= 0; at--) {
            left[at] = left[at + 1] + weights.get(order.get(at));
        }
        return left;
    }
}
