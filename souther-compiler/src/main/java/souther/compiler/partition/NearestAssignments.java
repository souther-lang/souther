package souther.compiler.partition;

import java.util.Arrays;

/**
 * The assignments over one origin's base that move some of the positions a row is not about, at
 * one distance from the origin, handed over one at a time in the order a search asks for them.
 *
 * <p>Distance is where an assignment does not stand where the origin does ({@link Delta}), which
 * is not how many positions were moved: the base the walk starts from already differs from the
 * origin at the positions the demand settled, and a position moved back to where the origin
 * stands is a move that brings the assignment nearer. A walk by how many positions it moved
 * would hand over a nearer assignment after a farther one.
 *
 * <p>So the distance is the axis the walk is asked along, and for one distance the assignments
 * come in the order: fewer positions moved first; the moved positions as combinations of the
 * positions in their own order, earliest first; and the classes of one combination with the first
 * position slowest. Which assignment comes first decides which row is offered, so two runs of one
 * model offer the same rows.
 *
 * <p>Nothing is held. A combination is chosen, its classes are walked in place, and each
 * assignment is handed to the visitor the moment it stands, so a visitor that stops after the first
 * leaves the rest unwalked. A moved position changes the distance by a number its class decides
 * and no other position's does, so the least and the most the positions still to move can change
 * it by bound what is reachable, and a combination or a class the target distance is out of reach
 * of is not walked.
 */
final class NearestAssignments {

    /** What the positions standing together allow, kept as positions are moved. */
    interface Together {

        /** Moves {@code axis} from the class {@code from} to the class {@code to}. */
        void move(int axis, int from, int to);

        /** Whether the classes standing can all stand in one value. */
        boolean holds();
    }

    /** Whether a part of the walk is one the visitor would pass over whatever is decided below. */
    interface Pruning {

        /**
         * Whether, deciding the steps one after another, nothing below the steps {@code from} to
         * {@code to} (each counted as the number of steps decided so far) is anything but left out,
         * with the classes in {@code where}.
         */
        boolean leavesOut(int[] where, int from, int to);
    }

    /** Takes the assignments one at a time. */
    interface Visitor {

        /** Whether the walk goes on after {@code where}, which is valid only for this call. */
        boolean goesOn(int[] where);
    }

    /**
     * What the walk is allowed to look at, across every walk that shares it.
     *
     * <p>A look is a combination of positions chosen or a class tried at a moved position, whether
     * or not anything stands at the end of it: a walk whose every assignment the visitor passes
     * over for nothing is still work, and the visitor's own budget never sees it.
     */
    static final class Looks {

        private long left;

        Looks(long most) {
            this.left = most;
        }

        /** Takes one look, and says whether there was one left to take. */
        boolean take() {
            if (left == 0) {
                return false;
            }
            left--;
            return true;
        }

        /** How many looks are left to take. */
        long left() {
            return left;
        }
    }

    /** What stopped a walk. */
    enum Ended {

        /** Every assignment at the distance was handed over. */
        EXHAUSTED,

        /** The visitor asked for no more. */
        DECLINED,

        /** The looks ran out in front of an assignment. */
        OUT_OF_LOOKS
    }

    private static final int UNREACHABLE = Integer.MAX_VALUE / 4;

    private final int[] stands;
    private final int[] base;
    private final int[] steps;
    private final int[] classes;
    private final int baseDistance;
    /** The least and the most moving the position at a step changes the distance by. */
    private final int[] least;
    private final int[] most;
    /** The least and the most moving that many positions changes the distance by. */
    private final int[] leastOfMany;
    private final int[] mostOfMany;

    /**
     * @param stands  where the origin stands at every position
     * @param base    where the walk starts, at every position
     * @param steps   the positions that may be moved, in the positions' own order
     * @param classes how many classes each position has
     */
    NearestAssignments(int[] stands, int[] base, int[] steps, int[] classes) {
        this.stands = stands;
        this.base = base;
        this.steps = steps;
        this.classes = classes;
        this.baseDistance = Delta.between(stands, base).size();
        least = new int[steps.length];
        most = new int[steps.length];
        int[] lows = new int[steps.length];
        int[] highs = new int[steps.length];
        int movable = 0;
        for (int j = 0; j < steps.length; j++) {
            int axis = steps[j];
            int low = UNREACHABLE;
            int high = -UNREACHABLE;
            for (int c = 0; c < classes[axis]; c++) {
                if (c != base[axis]) {
                    low = Math.min(low, change(axis, c));
                    high = Math.max(high, change(axis, c));
                }
            }
            least[j] = low;
            most[j] = high;
            if (low != UNREACHABLE) {
                lows[movable] = low;
                highs[movable] = high;
                movable++;
            }
        }
        Arrays.sort(lows, 0, movable);
        Arrays.sort(highs, 0, movable);
        leastOfMany = new int[steps.length + 1];
        mostOfMany = new int[steps.length + 1];
        Arrays.fill(leastOfMany, UNREACHABLE);
        Arrays.fill(mostOfMany, -UNREACHABLE);
        leastOfMany[0] = 0;
        mostOfMany[0] = 0;
        for (int m = 1; m <= movable; m++) {
            leastOfMany[m] = leastOfMany[m - 1] + lows[m - 1];
            mostOfMany[m] = mostOfMany[m - 1] + highs[movable - m];
        }
    }

    /** How far moving {@code axis} to the class {@code to} changes the distance from the origin. */
    private int change(int axis, int to) {
        return (to != stands[axis] ? 1 : 0) - (base[axis] != stands[axis] ? 1 : 0);
    }

    /** The nearest an assignment of this walk is to the origin. */
    int nearest() {
        int out = UNREACHABLE;
        for (int m = 0; m < leastOfMany.length; m++) {
            if (leastOfMany[m] != UNREACHABLE) {
                out = Math.min(out, baseDistance + leastOfMany[m]);
            }
        }
        return Math.max(out, 0);
    }

    /** The farthest an assignment of this walk is from the origin. */
    int farthest() {
        int out = 0;
        for (int m = 0; m < mostOfMany.length; m++) {
            if (mostOfMany[m] != -UNREACHABLE) {
                out = Math.max(out, baseDistance + mostOfMany[m]);
            }
        }
        return out;
    }

    /**
     * Hands every assignment {@code distance} from the origin to {@code visitor}, in order.
     *
     * @return why the walk ended: every assignment was handed over, the visitor asked for no more,
     *         or the looks ran out
     */
    Ended visitAt(int distance, Together together, Pruning pruning, Looks looks, Visitor visitor) {
        int target = distance - baseDistance;
        int[] where = base.clone();
        for (int moves = 0; moves < leastOfMany.length; moves++) {
            if (leastOfMany[moves] == UNREACHABLE || target < leastOfMany[moves]
                    || target > mostOfMany[moves]) {
                continue;
            }
            Walk walk = new Walk(together, pruning, looks, visitor, where, target, new int[moves]);
            if (walk.choose(0, 0)) {
                return walk.ended;
            }
        }
        return Ended.EXHAUSTED;
    }

    /** One combination size's walk: the positions chosen so far, and the classes in place. */
    private final class Walk {

        private final Together together;
        private final Pruning pruning;
        private final Looks looks;
        private final Visitor visitor;
        private final int[] where;
        private final int target;
        private final int[] chosen;
        /** What the positions chosen from a depth on can change the distance by, least and most. */
        private final int[] restLeast;
        private final int[] restMost;
        /** Why the walk stopped, once it has. */
        private Ended ended = Ended.EXHAUSTED;

        Walk(Together together, Pruning pruning, Looks looks, Visitor visitor, int[] where,
             int target, int[] chosen) {
            this.together = together;
            this.pruning = pruning;
            this.looks = looks;
            this.visitor = visitor;
            this.where = where;
            this.target = target;
            this.chosen = chosen;
            this.restLeast = new int[chosen.length + 1];
            this.restMost = new int[chosen.length + 1];
        }

        /** Chooses the positions from the step {@code from} on, {@code count} chosen already. */
        boolean choose(int from, int count) {
            if (count == chosen.length) {
                if (!looks.take()) {
                    ended = Ended.OUT_OF_LOOKS;
                    return true;
                }
                return reachable() && classesOf(0, 0, 0);
            }
            for (int step = from; step <= steps.length - (chosen.length - count); step++) {
                chosen[count] = step;
                if (choose(step + 1, count + 1)) {
                    return true;
                }
            }
            return false;
        }

        /** Whether the chosen positions can reach the target at all. */
        private boolean reachable() {
            restLeast[chosen.length] = 0;
            restMost[chosen.length] = 0;
            for (int k = chosen.length - 1; k >= 0; k--) {
                if (least[chosen[k]] == UNREACHABLE) {
                    return false;
                }
                restLeast[k] = restLeast[k + 1] + least[chosen[k]];
                restMost[k] = restMost[k + 1] + most[chosen[k]];
            }
            return restLeast[0] <= target && target <= restMost[0];
        }

        /**
         * The classes of the chosen position at depth {@code k}, and below it, with the distance
         * changed by {@code changed} so far.
         *
         * @param decided how many steps are decided so far, which is where a stretch of positions
         *                left where they stand starts
         */
        private boolean classesOf(int k, int decided, int changed) {
            int until = k < chosen.length ? chosen[k] : steps.length;
            if (pruning.leavesOut(where, decided, until)) {
                return false;
            }
            if (k == chosen.length) {
                if (visitor.goesOn(where)) {
                    return false;
                }
                ended = Ended.DECLINED;
                return true;
            }
            int axis = steps[chosen[k]];
            int stood = where[axis];
            int at = stood;
            for (int c = 0; c < classes[axis]; c++) {
                if (c == stood) {
                    continue;
                }
                int now = changed + change(axis, c);
                if (target - now < restLeast[k + 1] || target - now > restMost[k + 1]) {
                    continue;
                }
                if (!looks.take()) {
                    ended = Ended.OUT_OF_LOOKS;
                    return true;
                }
                together.move(axis, at, c);
                at = c;
                where[axis] = c;
                if (together.holds() && classesOf(k + 1, chosen[k] + 1, now)) {
                    return true;
                }
            }
            together.move(axis, at, stood);
            where[axis] = stood;
            return false;
        }
    }
}
