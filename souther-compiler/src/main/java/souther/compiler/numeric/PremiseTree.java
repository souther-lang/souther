package souther.compiler.numeric;

import java.util.Arrays;
import java.util.concurrent.atomic.LongAdder;

/**
 * The premises of a round held so that the lowest bound any one of them gives a form is found
 * without reading each of them.
 *
 * <p>A premise {@code g <= b} leaves a form {@code f} at most {@code b + Σ (f - g)·E}, where {@code E}
 * is, for each position, the end its weight in {@code f - g} runs it up to: the upper end where the
 * weight is positive and the lower where it is negative ({@link FormReach#fromTheEndsWithout}). That
 * is a distance from {@code f} to {@code g} which has no direction to it and grows with every
 * position the two differ in, and what is asked is the premise that leaves the form lowest, so a
 * premise far from the form in any position cannot be it.
 *
 * <p>So the premises are held in a tree of boxes, and a box says the lowest anything in it can leave
 * the form: the lowest bound of any premise in it, and the least each position can add given the
 * weights the box holds. A box that cannot leave the form lower than what is held already is not
 * read into. The tree is made of the premises' weights and bounds alone, so it does not turn on the
 * ends, which are what each box is read against.
 *
 * <p>The closed differences are a second route to a bound: a premise whose residual weighs two
 * positions by one amount and its negation is bounded by that amount of the difference between them,
 * which can be lower than the ends bound it. Such a premise agrees with the form in every other
 * position and in the sum of the two, so a box that holds none of that cannot leave the form a bound
 * that way. A box's floor is the lower of the two routes.
 *
 * <p><b>The tree chooses and does not answer.</b> A floor is worked out in {@code double}s, with room
 * for what that costs it, and is never above what a premise in the box leaves the form: a box is
 * passed over only where its floor is above what has been found. What a premise leaves the form is
 * read as every premise is read ({@link FormReach#fromTheEndsWithout}), so the exact arithmetic
 * that holds a sum in one order of adding and not another is read as it always was. A floor that is
 * not a number, because a number is beyond what a {@code double} holds, passes over nothing.
 */
final class PremiseTree {

    /** How many boxes have been looked at and premises read, for a test holding what a question
     *  costs to the premises and not to the premises and questions together: a shape and not a
     *  speed. */
    private static final LongAdder STEPS = new LongAdder();

    static long steps() {
        return STEPS.sum();
    }

    /** How many premises a box holds before it is split. */
    private static final int LEAF = 4;

    /**
     * What a floor is lowered by, as a share of the sizes of the terms it is made of.
     *
     * <p>Every number a floor starts from is a {@link ExactRatio#approximately} one, so zero or from
     * {@code 2^-200} to {@code 2^200} and off by {@link ExactRatio#APPROXIMATELY_OFF}, or not a
     * number and a floor that is not a number, which passes over nothing. What a floor does with
     * them — subtract, multiply, add, at most eight positions' worth — then never overflows or
     * falls below the smallest normal number, so each operation is off by half a unit in the last
     * place of its result and no more. Each term is off by under {@code 6e-15} of its size, and
     * this is more than ten times that.
     *
     * <p>A floor says one of three things: a number that no premise of the box leaves the form
     * below, positive infinity where none leaves it any, and not a number where it cannot be said.
     */
    private static final double ROOM = 1e-13;

    /** The sum of two weights, worked out exactly before it is a {@code double}: the weights are
     *  each rounded, and a sum of them that cancels is off by more than its own size. */
    private static double sumOf(ExactRatio one, ExactRatio other) {
        ExactRatio sum = one.plus(other).orNull();
        return sum == null ? Double.NaN : sum.approximately();
    }

    /**
     * One premise.
     *
     * @param weights what it weighs each position by, nought where it does not name it
     * @param bound   what it is bounded by
     * @param place   which premise of the round it is
     */
    record Premise(ExactRatio[] weights, ExactCut bound, int place) {}

    /**
     * Two positions whose closed differences bound some residual lower than their ends do.
     *
     * @param aboveOverBelow the bound on {@code above - below}, or null
     * @param belowOverAbove the bound on {@code below - above}, or null
     */
    record Pair(int above, int below, ExactCut aboveOverBelow, ExactCut belowOverAbove) {}

    /** What a premise leaves a form once the form's terms are taken off it, read as every premise
     *  is read, or null where nothing is left to bound. */
    interface Reading {
        ExactCut leftBy(int place);
    }

    /** A premise as the tree holds it. */
    private record Point(double[] weights, double[] sums, double bound, ExactCut exactBound,
                         int place) {}

    /** What a box holds the premises in it to. */
    private static final class Node {
        private double[] least;
        private double[] most;
        private double[] sumLeast;
        private double[] sumMost;
        private double lowestBound;
        private Node below;
        private Node above;
        private Point[] held;
    }

    /** For each position, the end a weight above nought reads it at and the one below, and whether
     *  the position has each. */
    private final double[] up;
    private final double[] down;
    private final boolean[] hasUp;
    private final boolean[] hasDown;

    /** For each position, the size of its ends. */
    private final double[] endSize;

    private final int[] above;
    private final int[] below;
    private final double[] aboveOverBelow;
    private final double[] belowOverAbove;
    private final boolean[] hasAboveOverBelow;
    private final boolean[] hasBelowOverAbove;
    private final Node root;

    private PremiseTree(ExactCut[] ups, ExactCut[] downs, Pair[] pairs, Node root) {
        int positions = ups.length;
        up = new double[positions];
        down = new double[positions];
        hasUp = new boolean[positions];
        hasDown = new boolean[positions];
        endSize = new double[positions];
        for (int position = 0; position < positions; position++) {
            hasUp[position] = ups[position] != null;
            hasDown[position] = downs[position] != null;
            up[position] = hasUp[position] ? ups[position].at().approximately() : 0.0;
            down[position] = hasDown[position] ? downs[position].at().approximately() : 0.0;
            endSize[position] = Math.max(Math.abs(up[position]), Math.abs(down[position]));
        }
        above = new int[pairs.length];
        below = new int[pairs.length];
        aboveOverBelow = new double[pairs.length];
        belowOverAbove = new double[pairs.length];
        hasAboveOverBelow = new boolean[pairs.length];
        hasBelowOverAbove = new boolean[pairs.length];
        for (int pair = 0; pair < pairs.length; pair++) {
            above[pair] = pairs[pair].above();
            below[pair] = pairs[pair].below();
            hasAboveOverBelow[pair] = pairs[pair].aboveOverBelow() != null;
            hasBelowOverAbove[pair] = pairs[pair].belowOverAbove() != null;
            aboveOverBelow[pair] = hasAboveOverBelow[pair]
                    ? pairs[pair].aboveOverBelow().at().approximately() : 0.0;
            belowOverAbove[pair] = hasBelowOverAbove[pair]
                    ? pairs[pair].belowOverAbove().at().approximately() : 0.0;
        }
        this.root = root;
    }

    /**
     * The tree of {@code premises}, or null where a weight or a bound of one is beyond what a
     * {@code double} holds.
     *
     * @param up    for each position, the end a weight above nought reads it at, or null
     * @param down  for each position, the end a weight below nought reads it at, or null
     * @param pairs the pairs of positions a difference bounds a residual lower for
     */
    static PremiseTree over(Premise[] premises, ExactCut[] up, ExactCut[] down, Pair[] pairs) {
        Point[] points = new Point[premises.length];
        for (int at = 0; at < points.length; at++) {
            Premise each = premises[at];
            double[] weights = new double[up.length];
            for (int position = 0; position < weights.length; position++) {
                weights[position] = each.weights()[position].approximately();
            }
            double[] sums = new double[pairs.length];
            for (int pair = 0; pair < pairs.length; pair++) {
                sums[pair] = sumOf(each.weights()[pairs[pair].above()],
                        each.weights()[pairs[pair].below()]);
            }
            double bound = each.bound().at().approximately();
            if (Double.isNaN(bound) || containsNaN(weights) || containsNaN(sums)) {
                return null;
            }
            points[at] = new Point(weights, sums, bound, each.bound(), each.place());
        }
        return new PremiseTree(up, down, pairs, build(points, 0, points.length, 0, up.length,
                pairs.length));
    }

    private static boolean containsNaN(double[] values) {
        for (double each : values) {
            if (Double.isNaN(each)) {
                return true;
            }
        }
        return false;
    }

    private static Node build(Point[] points, int from, int to, int depth, int dimensions,
                              int pairCount) {
        STEPS.add(to - from);
        Node node = new Node();
        node.least = new double[dimensions];
        node.most = new double[dimensions];
        node.sumLeast = new double[pairCount];
        node.sumMost = new double[pairCount];
        Arrays.fill(node.least, Double.POSITIVE_INFINITY);
        Arrays.fill(node.most, Double.NEGATIVE_INFINITY);
        Arrays.fill(node.sumLeast, Double.POSITIVE_INFINITY);
        Arrays.fill(node.sumMost, Double.NEGATIVE_INFINITY);
        node.lowestBound = Double.POSITIVE_INFINITY;
        for (int at = from; at < to; at++) {
            Point each = points[at];
            for (int dimension = 0; dimension < dimensions; dimension++) {
                node.least[dimension] = Math.min(node.least[dimension], each.weights()[dimension]);
                node.most[dimension] = Math.max(node.most[dimension], each.weights()[dimension]);
            }
            for (int pair = 0; pair < pairCount; pair++) {
                node.sumLeast[pair] = Math.min(node.sumLeast[pair], each.sums()[pair]);
                node.sumMost[pair] = Math.max(node.sumMost[pair], each.sums()[pair]);
            }
            node.lowestBound = Math.min(node.lowestBound, each.bound());
        }
        int split = -1;
        for (int step = 0; step < dimensions && split < 0; step++) {
            int dimension = (depth + step) % dimensions;
            if (node.least[dimension] < node.most[dimension]) {
                split = dimension;
            }
        }
        if (to - from <= LEAF || split < 0) {
            node.held = Arrays.copyOfRange(points, from, to);
            return node;
        }
        int along = split;
        Arrays.sort(points, from, to,
                (one, other) -> Double.compare(one.weights()[along], other.weights()[along]));
        int middle = (from + to) >>> 1;
        node.below = build(points, from, middle, depth + 1, dimensions, pairCount);
        node.above = build(points, middle, to, depth + 1, dimensions, pairCount);
        return node;
    }

    /**
     * {@code best} tightened by every premise's bound on {@code form} that is not one of
     * {@code left}.
     *
     * @param form     what the form weighs each position by
     * @param constant what the form adds
     * @param best     what is held already, or null for no bound
     * @param left     the places of the premises not to read
     */
    ExactCut lowest(ExactRatio[] form, ExactRatio constant, ExactCut best, int[] left,
                    Reading reading) {
        return new Query(form, constant, best, left, reading).search(root);
    }

    private final class Query {

        private final double[] form;
        private final double constant;
        private final int[] left;
        private final Reading reading;

        /** What the form weighs each pair of positions by together. */
        private final double[] formSums;

        /** The lowest bound found, and the most it can be taken to be in a floor's terms: positive
         *  infinity where there is none. */
        private ExactCut best;
        private double bestAt;

        Query(ExactRatio[] weights, ExactRatio constant, ExactCut best, int[] left,
              Reading reading) {
            form = new double[weights.length];
            for (int position = 0; position < form.length; position++) {
                form[position] = weights[position].approximately();
            }
            this.constant = constant.approximately();
            this.left = left;
            this.reading = reading;
            formSums = new double[above.length];
            for (int pair = 0; pair < above.length; pair++) {
                formSums[pair] = sumOf(weights[above[pair]], weights[below[pair]]);
            }
            found(best);
        }

        private void found(ExactCut cut) {
            best = cut;
            bestAt = cut == null ? Double.POSITIVE_INFINITY : cut.at().approximately();
        }

        ExactCut search(Node root) {
            walk(root);
            return best;
        }

        private void walk(Node node) {
            STEPS.increment();
            if (node.held != null) {
                walkAmong(node.held);
                return;
            }
            // The side with the lower floor first: what it leaves the form is what the other side
            // is held to, so the other is often not read into at all.
            double lowFloor = floorOf(node.below);
            double highFloor = floorOf(node.above);
            Node first = node.below;
            Node second = node.above;
            if (stands(highFloor, lowFloor)) {
                first = node.above;
                second = node.below;
                double swapped = lowFloor;
                lowFloor = highFloor;
                highFloor = swapped;
            }
            if (canBeat(lowFloor)) {
                walk(first);
            }
            if (canBeat(highFloor)) {
                walk(second);
            }
        }

        /** The premises of one box, the one with the lowest floor read first: what it leaves the
         *  form is what the rest are held to, and most of them can then not leave it lower. */
        private void walkAmong(Point[] held) {
            double[] floors = new double[held.length];
            for (int at = 0; at < held.length; at++) {
                Point each = held[at];
                floors[at] = isLeft(each.place()) ? Double.POSITIVE_INFINITY : floorOf(each.weights(),
                        each.weights(), each.sums(), each.sums(), each.bound());
            }
            for (int taken = 0; taken < held.length; taken++) {
                int next = -1;
                for (int at = 0; at < held.length; at++) {
                    if (floors[at] != Double.POSITIVE_INFINITY
                            && (next < 0 || stands(floors[at], floors[next]))) {
                        next = at;
                    }
                }
                if (next < 0) {
                    return;
                }
                double floor = floors[next];
                floors[next] = Double.POSITIVE_INFINITY;
                if (canBeat(floor)) {
                    STEPS.increment();
                    ExactCut residual = reading.leftBy(held[next].place());
                    if (residual != null) {
                        found(ExactCut.tighterUpper(best, new ExactCut(residual.at(),
                                residual.inclusive() && held[next].exactBound().inclusive())));
                    }
                }
            }
        }

        /** Whether the floor {@code one} stands below {@code other}, one that is not a number
         *  standing below any. */
        private boolean stands(double one, double other) {
            return Double.isNaN(one) ? !Double.isNaN(other) : one < other;
        }

        private boolean isLeft(int place) {
            for (int each : left) {
                if (each == place) {
                    return true;
                }
            }
            return false;
        }

        private double floorOf(Node node) {
            return floorOf(node.least, node.most, node.sumLeast, node.sumMost, node.lowestBound);
        }

        /** Whether anything a floor stands for could leave the form at or below what is found. */
        private boolean canBeat(double floor) {
            if (floor == Double.POSITIVE_INFINITY) {
                return false;
            }
            return Double.isNaN(floor) || Double.isNaN(bestAt)
                    || floor <= bestAt + ROOM * Math.abs(bestAt);
        }

        /**
         * The lowest bound the premises in a box can leave the form, less room for the arithmetic: the
         * lower of what the ends leave it and what the closed differences do, each from the weights
         * the box holds. Positive infinity where none of them leaves it any, and not a number where
         * it cannot be said.
         */
        private double floorOf(double[] least, double[] most, double[] sumLeast, double[] sumMost,
                               double lowestBound) {
            STEPS.increment();
            double floor = rangesFloor(lowestBound, least, most);
            for (int pair = 0; pair < above.length; pair++) {
                floor = Math.min(floor, differenceFloor(pair, lowestBound, least, most,
                        sumLeast[pair], sumMost[pair]));
            }
            return floor;
        }

        private double rangesFloor(double lowestBound, double[] least, double[] most) {
            double total = lowestBound + constant;
            double size = Math.abs(lowestBound) + Math.abs(constant);
            for (int position = 0; position < form.length; position++) {
                double term = termsFloor(position, least[position], most[position]);
                if (term == Double.POSITIVE_INFINITY) {
                    return Double.POSITIVE_INFINITY;
                }
                total += term;
                size += (Math.abs(form[position])
                        + Math.max(Math.abs(least[position]), Math.abs(most[position])))
                        * endSize[position];
            }
            return total - ROOM * size;
        }

        /**
         * The lowest term the form's weight at {@code position}, against the weights from
         * {@code least} to {@code most}, can come to: positive infinity where no weight in between
         * has an end to run up to.
         *
         * <p>The weights are doubles that stand for exact ones, so what is left of the form's weight
         * once the box's is taken off is an interval a little wider than the one the doubles give,
         * and a term is no more than a sign away from the one beside it only where the interval is
         * on one side of nought.
         */
        private double termsFloor(int position, double least, double most) {
            double weight = form[position];
            double slack = ROOM * (Math.abs(weight) + Math.max(Math.abs(least), Math.abs(most)));
            double low = weight - most - slack;
            double high = weight - least + slack;
            double lowest = Math.min(termAt(position, low), termAt(position, high));
            return low < 0 && high > 0 ? Math.min(lowest, 0.0) : lowest;
        }

        private double termAt(int position, double weight) {
            if (Double.isNaN(weight)) {
                return Double.NaN;
            }
            if (weight > 0) {
                return hasUp[position] ? weight * up[position] : Double.POSITIVE_INFINITY;
            }
            if (weight < 0) {
                return hasDown[position] ? weight * down[position] : Double.POSITIVE_INFINITY;
            }
            return 0.0;
        }

        /**
         * What a pair's closed difference leaves the form at the lowest, for the premises of a box
         * that agree with the form in every other position and in the sum of the two: positive
         * infinity where none of them can.
         */
        private double differenceFloor(int pair, double lowestBound, double[] least, double[] most,
                                       double sumLeast, double sumMost) {
            int upper = above[pair];
            int lower = below[pair];
            double together = formSums[pair];
            double room = ROOM * (Math.abs(form[upper]) + Math.abs(form[lower])
                    + Math.max(Math.abs(sumLeast), Math.abs(sumMost)));
            if (together < sumLeast - room || together > sumMost + room) {
                return Double.POSITIVE_INFINITY;
            }
            for (int position = 0; position < form.length; position++) {
                double within = ROOM * (Math.abs(form[position])
                        + Math.max(Math.abs(least[position]), Math.abs(most[position])));
                if (position != upper && position != lower && (form[position] < least[position]
                        - within || form[position] > most[position] + within)) {
                    return Double.POSITIVE_INFINITY;
                }
            }
            double slack = ROOM * (Math.abs(form[upper])
                    + Math.max(Math.abs(least[upper]), Math.abs(most[upper])));
            double low = form[upper] - most[upper] - slack;
            double high = form[upper] - least[upper] + slack;
            double lowest = Math.min(differenceTerm(pair, low), differenceTerm(pair, high));
            if (low < 0 && high > 0) {
                lowest = Math.min(lowest, 0.0);
            }
            if (lowest == Double.POSITIVE_INFINITY) {
                return lowest;
            }
            double size = Math.abs(lowestBound) + Math.abs(constant) + (Math.abs(form[upper])
                    + Math.max(Math.abs(least[upper]), Math.abs(most[upper])))
                    * Math.max(Math.abs(aboveOverBelow[pair]), Math.abs(belowOverAbove[pair]));
            return lowestBound + constant + lowest - ROOM * size;
        }

        /** What a weight on the first of the pair and its negation on the second comes to by the
         *  closed differences. */
        private double differenceTerm(int pair, double weight) {
            if (Double.isNaN(weight)) {
                return Double.NaN;
            }
            if (weight > 0) {
                return hasAboveOverBelow[pair] ? weight * aboveOverBelow[pair]
                        : Double.POSITIVE_INFINITY;
            }
            if (weight < 0) {
                return hasBelowOverAbove[pair] ? -weight * belowOverAbove[pair]
                        : Double.POSITIVE_INFINITY;
            }
            return 0.0;
        }
    }
}
