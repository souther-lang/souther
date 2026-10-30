package souther.compiler.meaning;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

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
 *
 * <p>What is walked to make them is no more than what is made. A set is grown only where what is
 * left of the statements can still take it to the number — every one of them added, for a fewest
 * set, and some of them coming to exactly what is missing, for an exact one — so every step of
 * the walk is on the way to a choice, and a count no set comes to is found to have none without
 * looking at any.
 */
final class WhichOfThemHold {

    /** How many choices a relation comes to before it is a count: a count of one is no count. */
    private static final long ONE_CHOICE = 1;

    /** Each statement once, in the order first written. */
    private final List<Proposition> statements;

    /** How many times each of {@link #statements} was written. */
    private final List<Integer> weights;

    /** Which counts the relation admits, by how many hold. */
    private final boolean[] admitted;

    private WhichOfThemHold(List<Proposition> statements, List<Integer> weights,
                            boolean[] admitted) {
        this.statements = statements;
        this.weights = weights;
        this.admitted = admitted;
    }

    /**
     * {@code relation} read as which of its statements hold, or null where it is over anything but
     * one count of statements, or a count the arithmetic could not hold.
     */
    static WhichOfThemHold of(Relation relation) {
        if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().size() != 1
                || !(form.coefs().keySet().iterator().next()
                        instanceof Quantity.HowManyHold(List<Proposition> each))) {
            return null;
        }
        Map<Spelling, Proposition> once = new LinkedHashMap<>();
        Map<Spelling, Integer> written = new LinkedHashMap<>();
        for (Proposition one : each) {
            once.putIfAbsent(one.spelling(), one);
            written.merge(one.spelling(), 1, Integer::sum);
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
                admitted);
    }

    /** The same count, held as {@code held} holds it. */
    static WhichOfThemHold of(Proposition.SoManyHold held) {
        boolean[] admitted = new boolean[held.weight() + 1];
        held.admitted().forEach(count -> admitted[count] = true);
        return new WhichOfThemHold(held.statements(), held.weights(), admitted);
    }


    /**
     * What the relation states: the one choice it comes to, where it comes to no more than one
     * (or to none, which no row is) — and otherwise the statements and the counts it admits, held
     * as they are ({@link Proposition.SoManyHold}).
     *
     * <p>The count is what is stated and the choices are one way of writing it, so a count is held
     * whenever it is a count. With one choice nothing is chosen, and the choice is the same
     * statement said again. Exactly one of {@code n} is {@code n} choices of {@code n} statements
     * and exactly four of eight is seventy: how many of them there are is no part of what is
     * stated, and a reader that reads a count does not take it apart. One that reads only
     * conjunctions and disjunctions is handed the choices ({@link CountsWrittenOut}).
     *
     * <p>One relation is stated one way, whichever reader made it: which way turns on the
     * statements and the counts alone, and on no figure a reader has in hand.
     */
    Proposition stated() {
        Written within = written(ONE_CHOICE,
                CompositionBudget.PARTS_A_DERIVATION_CONCLUDES.maximum(),
                CompositionBudget.READINGS_OF_ONE_CONDITION,
                CompositionBudget.PARTS_A_DERIVATION_CONCLUDES);
        if (within.choices() != null) {
            return within.choices();
        }
        List<Integer> byKey = new ArrayList<>(statements.size());
        for (int one = 0; one < statements.size(); one++) {
            byKey.add(one);
        }
        byKey.sort(Comparator.comparing((Integer one) -> statements.get(one).spelling()));
        List<Proposition> kept = new ArrayList<>(statements.size());
        List<Integer> weighed = new ArrayList<>(statements.size());
        byKey.forEach(one -> {
            kept.add(statements.get(one));
            weighed.add(weights.get(one));
        });
        List<Integer> counts = new ArrayList<>();
        for (int count = 0; count < admitted.length; count++) {
            if (admitted[count]) {
                counts.add(count);
            }
        }
        return SharedPropositions.shared(new Proposition.SoManyHold(kept, weighed, counts));
    }

    /**
     * The choices written out, where they are no more than {@code choicesFigure} allows and come to
     * no more parts than {@code partsFigure} does — or none, and the figure they were past.
     *
     * @param choices   the choices within both figures, or null
     * @param stoppedAt the figure they were past, or null where they were within both
     * @param parts     how many parts {@code choices} come to written out, and nought where there
     *                  are none — what a reader walking them is charged
     */
    record Written(Proposition choices, CompositionBudget stoppedAt, long parts) {}

    /**
     * What {@link Written} says of the choices, held to {@code choicesFigure} by how many they are
     * and to {@code partsFigure} by how many parts they come to.
     *
     * <p>Each choice is counted as it is made, in the parts a step is counted in — the same count
     * the figure is of, however deep a statement goes — so a walk past the parts stops at the
     * choice that takes it past and makes no more. Counted once for all of them: a statement and
     * its denial are in many choices, and are counted the first time and known after.
     */
    Written written(CompositionBudget choicesFigure, CompositionBudget partsFigure) {
        return written(choicesFigure.maximum(), partsFigure.maximum(), choicesFigure, partsFigure);
    }

    /** The same, held to {@code mostChoices} and {@code mostParts}, which {@code choicesFigure}
     *  and {@code partsFigure} are named for where the choices are past one of them. */
    private Written written(long mostChoices, long mostParts, CompositionBudget choicesFigure,
                            CompositionBudget partsFigure) {
        // One counting for every choice: the statements are the same in each, and each, and each
        // denial of one, is counted once and then known.
        Conclusion counting = Conclusion.countingTo(partsFigure);
        List<Proposition> ways = new ArrayList<>();
        long[] parts = {1};
        boolean[] pastTheChoices = {false};
        boolean whole = walk(chosen -> {
            if (ways.size() == mostChoices) {
                pastTheChoices[0] = true;
                return false;
            }
            parts[0] += counting.partsWrittenOut(chosen);
            if (parts[0] > mostParts) {
                return false;
            }
            ways.add(chosen);
            return true;
        });
        if (pastTheChoices[0]) {
            return new Written(null, choicesFigure, 0);
        }
        Proposition written = whole ? Proposition.any(ways) : null;
        long counted = written == null ? 0 : counting.partsWrittenOut(written);
        return written != null && counted <= mostParts ? new Written(written, null, counted)
                : new Written(null, partsFigure, 0);
    }

    /**
     * Each choice handed to {@code made} as what it states, until it answers false; whether every
     * one was handed on.
     */
    private boolean walk(Predicate<Proposition> made) {
        int all = weights.stream().mapToInt(Integer::intValue).sum();
        int fewest = firstAdmitted();
        int most = lastAdmitted();
        if (fewest < 0) {
            return true;
        }
        if (fewest == 0 && most == all && admitsEveryCountBetween(fewest, most)) {
            return made.test(new Proposition.Always(true));
        }
        if (most == all && admitsEveryCountBetween(fewest, most)) {
            return fewestComingTo(fewest, made);
        }
        for (int holding = fewest; holding <= most; holding++) {
            if (admitted[holding] && !exactly(holding, made)) {
                return false;
            }
        }
        return true;
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
     * member, so it is made where that member takes it to the number and grown no further. A set
     * that every statement left would take to the number still does with one of them in it, so the
     * walk never steps where no set is made.
     */
    private boolean fewestComingTo(int at, Predicate<Proposition> made) {
        List<Integer> order = heaviestFirst();
        int[] left = new int[order.size() + 1];
        for (int place = order.size() - 1; place >= 0; place--) {
            left[place] = left[place + 1] + weights.get(order.get(place));
        }
        return fewest(order, left, 0, 0, at, new ArrayList<>(), made);
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
     *
     * <p>Which counts the statements from each place on can come to is worked out first, and a
     * statement is taken only where those after it can come to what is still missing.
     */
    private boolean exactly(int at, Predicate<Proposition> made) {
        List<Integer> order = heaviestFirst();
        boolean[][] reach = new boolean[order.size() + 1][at + 1];
        reach[order.size()][0] = true;
        for (int place = order.size() - 1; place >= 0; place--) {
            int weight = weights.get(order.get(place));
            for (int count = 0; count <= at; count++) {
                reach[place][count] = reach[place + 1][count]
                        || (count >= weight && reach[place + 1][count - weight]);
            }
        }
        // No set coming to it is every set handed on.
        return !reach[0][at]
                || exactly(order, reach, 0, at, new boolean[statements.size()], made);
    }

    private boolean exactly(List<Integer> order, boolean[][] reach, int from, int missing,
                            boolean[] chosen, Predicate<Proposition> made) {
        if (missing == 0) {
            List<Proposition> parts = new ArrayList<>(statements.size());
            for (int one = 0; one < statements.size(); one++) {
                parts.add(chosen[one] ? statements.get(one) : statements.get(one).denied());
            }
            return made.test(Proposition.all(parts));
        }
        for (int next = from; next < order.size() && reach[next][missing]; next++) {
            int one = order.get(next);
            int weight = weights.get(one);
            if (weight > missing || !reach[next + 1][missing - weight]) {
                continue;
            }
            chosen[one] = true;
            boolean going = exactly(order, reach, next + 1, missing - weight, chosen, made);
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
}
