package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.atomic.LongAdder;

/**
 * The premises of a round over two positions, indexed so that how high a form comes to by any one
 * premise is found without reading every premise.
 *
 * <p>A premise {@code g·(x, j) <= b} leaves a form {@code c·(x, j)} at most
 * {@code b + (c - g)·E}, where {@code E} is the end of each position the sign of what the premise
 * leaves of it runs it up to ({@link FormReach#fromTheEndsWithout}). Which end each position is
 * read at depends only on whether {@code g} is below, at or above {@code c} in it, so the premises
 * fall into nine places by where they stand against the form, and in each the candidate is
 * {@code c·E + (b - g·E)}: a term of the form and a term of the premise. The lowest of the second
 * over the premises of a place is a minimum over an orthant of the premises' weights, which is what
 * is kept here: a tree over one weight with the other sorted and prefix-minimised at each node for
 * the four places where both weights differ from the form's, and a sorted strip for each weight a
 * place shares with it.
 *
 * <p>The closed differences are a second route to a bound: a premise whose residual weighs the two
 * positions by one amount and its negation is bounded by that amount of the difference between them.
 * Those premises are the ones of one sum of weights, so they are kept in a strip for each sum.
 *
 * <p>How a premise reads against the ends is the same as {@link FormReach} reads it and not a second
 * account of it: what comes back here is held to {@link FormReach#fromTheEndsWithout} at the
 * premise it names, so a bound that the exact arithmetic could hold only in one of the two orders it
 * was added in is read as it always was.
 */
final class ReachIndex {

    /** How many premises have been put into an index and how many questions have been asked of one. */
    private static final LongAdder STEPS = new LongAdder();

    static long steps() {
        return STEPS.sum();
    }

    /** What a premise leaves of a form once the form's own terms are taken off, which premise it is,
     *  and whether the premise reaches its bound. */
    private record Found(ExactRatio left, boolean reaches, int place) {

        boolean tighterThan(Found other) {
            int order = left.compareTo(other.left);
            return order < 0 || (order == 0 && !reaches && other.reaches);
        }
    }

    /**
     * What a form comes to by the one premise that bounds it highest, or by none where the cut is
     * null, or not read where the exact arithmetic could not hold a step.
     */
    record Highest(ExactCut cut, int place, boolean unread) {

        static final Highest UNREAD = new Highest(null, -1, true);
    }

    private final ExactCut mostX;
    private final ExactCut leastX;
    private final ExactCut mostJ;
    private final ExactCut leastJ;
    private final ExactCut aboveXOverJ;
    private final ExactCut aboveJOverX;

    private Orthant mostMost;
    private Orthant mostLeast;
    private Orthant leastMost;
    private Orthant leastLeast;

    /** The premises at one weight of x, by the weight of j. */
    private final Map<ExactRatio, Strip> atXBelowJ = new TreeMap<>();
    private final Map<ExactRatio, Strip> atXAboveJ = new TreeMap<>();
    private final Map<ExactRatio, Strip> atJBelowX = new TreeMap<>();
    private final Map<ExactRatio, Strip> atJAboveX = new TreeMap<>();
    private final Map<ExactRatio, Map<ExactRatio, Found>> same = new TreeMap<>();
    private final Map<ExactRatio, Strip> bySumBelow = new TreeMap<>();
    private final Map<ExactRatio, Strip> bySumAbove = new TreeMap<>();

    /** Whether the exact arithmetic could not hold a step: what came of this is then not read. */
    private boolean unheld;

    /**
     * One premise: {@code gx·x + gj·j <= bound}.
     *
     * @param place which premise of the round it is
     */
    record Premise(ExactRatio gx, ExactRatio gj, ExactCut bound, int place) {}

    private ReachIndex(Premise[] held, ExactCut mostX, ExactCut leastX, ExactCut mostJ,
                       ExactCut leastJ, ExactCut aboveXOverJ, ExactCut aboveJOverX) {
        List<Premise> premises = Arrays.asList(held);
        this.mostX = mostX;
        this.leastX = leastX;
        this.mostJ = mostJ;
        this.leastJ = leastJ;
        this.aboveXOverJ = aboveXOverJ;
        this.aboveJOverX = aboveJOverX;
        STEPS.add(premises.size());
        if (mostX != null && mostJ != null) {
            mostMost = orthant(premises, false, false, mostX, mostJ);
        }
        if (mostX != null && leastJ != null) {
            mostLeast = orthant(premises, false, true, mostX, leastJ);
        }
        if (leastX != null && mostJ != null) {
            leastMost = orthant(premises, true, false, leastX, mostJ);
        }
        if (leastX != null && leastJ != null) {
            leastLeast = orthant(premises, true, true, leastX, leastJ);
        }
        Map<ExactRatio, List<Premise>> byX = new TreeMap<>();
        Map<ExactRatio, List<Premise>> byJ = new TreeMap<>();
        Map<ExactRatio, List<Premise>> bySum = new TreeMap<>();
        for (Premise each : premises) {
            byX.computeIfAbsent(each.gx(), _ -> new ArrayList<>()).add(each);
            byJ.computeIfAbsent(each.gj(), _ -> new ArrayList<>()).add(each);
            bySum.computeIfAbsent(sum(each.gx(), each.gj()), _ -> new ArrayList<>()).add(each);
            Found itself = new Found(each.bound().at(), each.bound().inclusive(), each.place());
            same.computeIfAbsent(each.gx(), _ -> new TreeMap<>())
                    .merge(each.gj(), itself, ReachIndex::lower);
        }
        byX.forEach((weight, group) -> {
            if (mostJ != null) {
                atXBelowJ.put(weight, strip(group, true, each -> leftOf(each, null, mostJ)));
            }
            if (leastJ != null) {
                atXAboveJ.put(weight, strip(group, true, each -> leftOf(each, null, leastJ)));
            }
        });
        byJ.forEach((weight, group) -> {
            if (mostX != null) {
                atJBelowX.put(weight, strip(group, false, each -> leftOf(each, mostX, null)));
            }
            if (leastX != null) {
                atJAboveX.put(weight, strip(group, false, each -> leftOf(each, leastX, null)));
            }
        });
        bySum.forEach((weight, group) -> {
            if (aboveXOverJ != null) {
                bySumBelow.put(weight, strip(group, false, each -> new Found(
                        sum(each.bound().at(), product(each.gx(), aboveXOverJ.at()).negated()),
                        each.bound().inclusive(), each.place())));
            }
            if (aboveJOverX != null) {
                bySumAbove.put(weight, strip(group, false, each -> new Found(
                        sum(each.bound().at(), product(each.gx(), aboveJOverX.at())),
                        each.bound().inclusive(), each.place())));
            }
        });
    }

    /**
     * The index of {@code premises} read against {@code ends} and {@code differences}, or null
     * where the arithmetic could not hold what it is made of.
     *
     * <p>Held as an array of premises in the order of the rules, and what an index answers does not
     * turn on that order: it is a lowest over premises, told apart by the value and whether it is
     * reached and by nothing else, and each step it takes is one product or one sum of fixed terms.
     */
    static <A> ReachIndex over(Premise[] premises, Box<A> ends, A x, A j,
                               DifferenceBounds<A> differences) {
        ReachIndex out = new ReachIndex(premises, ends.mostOf(x), ends.leastOf(x),
                ends.mostOf(j), ends.leastOf(j), differences.differenceBound(x, j),
                differences.differenceBound(j, x));
        return out.unheld ? null : out;
    }

    /** The highest the form of weights {@code (cx, cj)} comes to by one premise. */
    Highest highest(ExactRatio cx, ExactRatio cj) {
        STEPS.increment();
        unheld = false;
        Map<ExactRatio, Found> row = same.get(cx);
        Found itself = row == null ? null : row.get(cj);
        ExactCut cut = null;
        int place = -1;
        if (itself != null) {
            cut = new ExactCut(itself.left(), itself.reaches());
            place = itself.place();
        }
        Held held = new Held(cut, place);
        held = held.with(mostMost == null ? null : mostMost.below(cx, cj), cx, mostX, cj, mostJ);
        held = held.with(mostLeast == null ? null : mostLeast.below(cx, cj.negated()), cx, mostX,
                cj, leastJ);
        held = held.with(leastMost == null ? null : leastMost.below(cx.negated(), cj), cx, leastX,
                cj, mostJ);
        held = held.with(leastLeast == null ? null
                : leastLeast.below(cx.negated(), cj.negated()), cx, leastX, cj, leastJ);
        Strip strip = atXBelowJ.get(cx);
        held = held.with(strip == null ? null : strip.below(cj), null, null, cj, mostJ);
        strip = atXAboveJ.get(cx);
        held = held.with(strip == null ? null : strip.above(cj), null, null, cj, leastJ);
        strip = atJBelowX.get(cj);
        held = held.with(strip == null ? null : strip.below(cx), cx, mostX, null, null);
        strip = atJAboveX.get(cj);
        held = held.with(strip == null ? null : strip.above(cx), cx, leastX, null, null);
        ExactRatio weights = sum(cx, cj);
        strip = bySumBelow.get(weights);
        if (strip != null) {
            Found found = strip.below(cx);
            if (found != null) {
                held = held.with(new ExactCut(sum(product(cx, aboveXOverJ.at()), found.left()),
                        found.reaches() && aboveXOverJ.inclusive()), found.place());
            }
        }
        strip = bySumAbove.get(weights);
        if (strip != null) {
            Found found = strip.above(cx);
            if (found != null) {
                held = held.with(new ExactCut(sum(product(cx, aboveJOverX.at()).negated(),
                        found.left()), found.reaches() && aboveJOverX.inclusive()), found.place());
            }
        }
        return unheld ? Highest.UNREAD : new Highest(held.cut(), held.place(), false);
    }

    /** The tighter cut so far, and the premise it is of. */
    private final class Held {
        private final ExactCut cut;
        private final int place;

        Held(ExactCut cut, int place) {
            this.cut = cut;
            this.place = place;
        }

        ExactCut cut() {
            return cut;
        }

        int place() {
            return place;
        }

        Held with(ExactCut other, int otherPlace) {
            if (other == null) {
                return this;
            }
            if (cut == null) {
                return new Held(other, otherPlace);
            }
            int order = other.at().compareTo(cut.at());
            boolean tighter = order < 0 || (order == 0 && cut.inclusive() && !other.inclusive());
            return tighter ? new Held(other, otherPlace) : this;
        }

        /** With what {@code found} leaves of the form once the form's own terms at the ends
         *  {@code ex} and {@code ej} are put back on it. */
        Held with(Found found, ExactRatio cx, ExactCut ex, ExactRatio cj, ExactCut ej) {
            if (found == null) {
                return this;
            }
            ExactRatio at = found.left();
            boolean reaches = found.reaches();
            if (ex != null) {
                at = sum(at, product(cx, ex.at()));
                reaches &= ex.inclusive();
            }
            if (ej != null) {
                at = sum(at, product(cj, ej.at()));
                reaches &= ej.inclusive();
            }
            return with(new ExactCut(at, reaches), found.place());
        }
    }

    private ExactRatio product(ExactRatio a, ExactRatio b) {
        ExactRatio out = a.times(b).orNull();
        if (out == null) {
            unheld = true;
            return ExactRatio.ZERO;
        }
        return out;
    }

    private ExactRatio sum(ExactRatio a, ExactRatio b) {
        ExactRatio out = a.plus(b).orNull();
        if (out == null) {
            unheld = true;
            return ExactRatio.ZERO;
        }
        return out;
    }

    /** {@code bound - gx·ex - gj·ej}, an end that is null being a term that is not there. */
    private Found leftOf(Premise premise, ExactCut ex, ExactCut ej) {
        ExactRatio left = premise.bound().at();
        if (ex != null) {
            left = sum(left, product(premise.gx(), ex.at()).negated());
        }
        if (ej != null) {
            left = sum(left, product(premise.gj(), ej.at()).negated());
        }
        return new Found(left, premise.bound().inclusive(), premise.place());
    }

    private static Found lower(Found a, Found b) {
        return b.tighterThan(a) ? b : a;
    }

    // --- a tree over one weight, each node sorted by the other ---------------------------------------

    private interface Reading {
        Found of(Premise premise);
    }

    private Orthant orthant(List<Premise> premises, boolean xAbove, boolean jAbove, ExactCut ex,
                            ExactCut ej) {
        List<ExactRatio[]> keys = new ArrayList<>(premises.size());
        List<Found> founds = new ArrayList<>(premises.size());
        for (Premise each : premises) {
            keys.add(new ExactRatio[] {xAbove ? each.gx().negated() : each.gx(),
                    jAbove ? each.gj().negated() : each.gj()});
            founds.add(leftOf(each, ex, ej));
        }
        return new Orthant(keys, founds);
    }

    private static final class Node {
        private int from;
        private int to;
        private Node left;
        private Node right;
        private ExactRatio[] bySecond;
        private Found[] lowest;
    }

    /** The lowest of what premises leave with both weights under a form's, by both weights. */
    private static final class Orthant {

        private final ExactRatio[] first;
        private final Node root;

        Orthant(List<ExactRatio[]> keys, List<Found> founds) {
            Integer[] order = new Integer[keys.size()];
            for (int at = 0; at < order.length; at++) {
                order[at] = at;
            }
            Arrays.sort(order, Comparator.comparing(at -> keys.get(at)[0]));
            first = new ExactRatio[order.length];
            ExactRatio[] second = new ExactRatio[order.length];
            Found[] held = new Found[order.length];
            for (int at = 0; at < order.length; at++) {
                first[at] = keys.get(order[at])[0];
                second[at] = keys.get(order[at])[1];
                held[at] = founds.get(order[at]);
            }
            root = order.length == 0 ? null : build(0, order.length, second, held);
        }

        private static Node build(int from, int to, ExactRatio[] second, Found[] held) {
            Node node = new Node();
            node.from = from;
            node.to = to;
            Integer[] order = new Integer[to - from];
            for (int at = 0; at < order.length; at++) {
                order[at] = from + at;
            }
            Arrays.sort(order, Comparator.comparing(at -> second[at]));
            node.bySecond = new ExactRatio[order.length];
            node.lowest = new Found[order.length];
            Found running = null;
            for (int at = 0; at < order.length; at++) {
                node.bySecond[at] = second[order[at]];
                running = running == null ? held[order[at]] : lower(running, held[order[at]]);
                node.lowest[at] = running;
            }
            if (to - from > 1) {
                int middle = (from + to) >>> 1;
                node.left = build(from, middle, second, held);
                node.right = build(middle, to, second, held);
            }
            return node;
        }

        /** The lowest over the premises whose first weight is below {@code first} and second
         *  below {@code second}. */
        Found below(ExactRatio firstWeight, ExactRatio secondWeight) {
            if (root == null) {
                return null;
            }
            return below(root, countBelow(first, firstWeight), secondWeight);
        }

        private static Found below(Node node, int count, ExactRatio secondWeight) {
            if (node.from >= count) {
                return null;
            }
            if (node.to <= count) {
                int under = countBelow(node.bySecond, secondWeight);
                return under == 0 ? null : node.lowest[under - 1];
            }
            return lower(below(node.left, count, secondWeight),
                    below(node.right, count, secondWeight));
        }

        private static Found lower(Found a, Found b) {
            return a == null ? b : b == null ? a : b.tighterThan(a) ? b : a;
        }
    }

    private static int countBelow(ExactRatio[] sorted, ExactRatio weight) {
        int from = 0;
        int to = sorted.length;
        while (from < to) {
            int middle = (from + to) >>> 1;
            if (sorted[middle].compareTo(weight) < 0) {
                from = middle + 1;
            } else {
                to = middle;
            }
        }
        return from;
    }

    private static int firstAbove(ExactRatio[] sorted, ExactRatio weight) {
        int from = 0;
        int to = sorted.length;
        while (from < to) {
            int middle = (from + to) >>> 1;
            if (sorted[middle].compareTo(weight) <= 0) {
                from = middle + 1;
            } else {
                to = middle;
            }
        }
        return from;
    }

    /** Premises sharing one weight, by the other, with the lowest at or before each and at or after
     *  each. */
    private static final class Strip {

        private final ExactRatio[] weights;
        private final Found[] before;
        private final Found[] after;

        Strip(List<ExactRatio> weights, List<Found> founds) {
            Integer[] order = new Integer[weights.size()];
            for (int at = 0; at < order.length; at++) {
                order[at] = at;
            }
            Arrays.sort(order, Comparator.comparing(weights::get));
            this.weights = new ExactRatio[order.length];
            before = new Found[order.length];
            after = new Found[order.length];
            Found running = null;
            for (int at = 0; at < order.length; at++) {
                this.weights[at] = weights.get(order[at]);
                Found found = founds.get(order[at]);
                running = running == null ? found : lower(running, found);
                before[at] = running;
            }
            running = null;
            for (int at = order.length - 1; at >= 0; at--) {
                Found found = founds.get(order[at]);
                running = running == null ? found : lower(running, found);
                after[at] = running;
            }
        }

        Found below(ExactRatio weight) {
            int count = countBelow(weights, weight);
            return count == 0 ? null : before[count - 1];
        }

        Found above(ExactRatio weight) {
            int at = firstAbove(weights, weight);
            return at >= weights.length ? null : after[at];
        }
    }

    private static Strip strip(List<Premise> group, boolean byJ, Reading reading) {
        List<ExactRatio> weights = new ArrayList<>(group.size());
        List<Found> founds = new ArrayList<>(group.size());
        for (Premise each : group) {
            weights.add(byJ ? each.gj() : each.gx());
            founds.add(reading.of(each));
        }
        return new Strip(weights, founds);
    }

}
