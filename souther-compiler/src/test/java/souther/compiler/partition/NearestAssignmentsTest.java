package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The assignments a walk hands over, nearest first, are the ones the contract names in the order
 * it names, whatever the positions and the classes: held against the whole space, listed and
 * sorted by the contract's own key, on models small enough to list.
 *
 * <p>And handed over one at a time: a walk whose visitor stops leaves the rest of the space
 * unwalked, which the looks it spends say directly.
 */
class NearestAssignmentsTest {

    private static final int NOT_HERE = -1;

    /** Two classes that leave each other no room, at two positions. */
    private record Clash(int one, int here, int other, int there) {

        boolean holdsIn(int[] where) {
            return where[one] == here && where[other] == there;
        }
    }

    /** What a model of positions, classes, an origin and a base stands for. */
    private record Model(int[] stands, int[] base, int[] steps, int[] classes, List<Clash> clashes,
                         int leftOutAxis, int leftOutClass) {

        boolean allows(int[] where) {
            for (Clash clash : clashes) {
                if (clash.holdsIn(where)) {
                    return false;
                }
            }
            return true;
        }

        boolean leavesOut(int[] where) {
            return leftOutAxis >= 0 && where[leftOutAxis] == leftOutClass;
        }

        NearestAssignments walk() {
            return new NearestAssignments(stands, base, steps, classes);
        }

        NearestAssignments.Together together() {
            int[] standing = base.clone();
            return new NearestAssignments.Together() {

                @Override
                public void move(int axis, int from, int to) {
                    standing[axis] = to;
                }

                @Override
                public boolean holds() {
                    return allows(standing);
                }
            };
        }

        NearestAssignments.Pruning pruning() {
            return (where, from, to) -> {
                // Decided at a step once the walk has passed it: what a pruning may look at.
                for (int filled = from; filled <= to; filled++) {
                    if (leftOutAxis >= 0 && where[leftOutAxis] == leftOutClass
                            && decided(leftOutAxis, filled)) {
                        return true;
                    }
                }
                return false;
            };
        }

        private boolean decided(int axis, int filled) {
            for (int j = 0; j < steps.length; j++) {
                if (steps[j] == axis) {
                    return j < filled;
                }
            }
            return true;
        }

        int distance(int[] where) {
            return Delta.between(stands, where).size();
        }
    }

    private static Model random(Random random, boolean withClashes, boolean withPruning) {
        int axes = 2 + random.nextInt(4);
        int[] classes = new int[axes];
        int[] stands = new int[axes];
        int[] base = new int[axes];
        List<Integer> movable = new ArrayList<>();
        for (int i = 0; i < axes; i++) {
            classes[i] = 1 + random.nextInt(4);
            stands[i] = random.nextInt(5) == 0 ? NOT_HERE : random.nextInt(classes[i]);
            base[i] = random.nextInt(8) == 0 ? NOT_HERE
                    : random.nextBoolean() || stands[i] == NOT_HERE ? random.nextInt(classes[i])
                    : stands[i];
            if (base[i] != NOT_HERE && random.nextInt(4) != 0) {
                movable.add(i);
            }
        }
        List<Clash> clashes = new ArrayList<>();
        for (int i = 0; withClashes && i < axes; i++) {
            if (random.nextBoolean()) {
                int other = random.nextInt(axes);
                if (other != i) {
                    clashes.add(new Clash(i, random.nextInt(classes[i]), other,
                            random.nextInt(classes[other])));
                }
            }
        }
        int leftOut = withPruning ? random.nextInt(axes) : -1;
        return new Model(stands, base, movable.stream().mapToInt(Integer::intValue).toArray(),
                classes, clashes, leftOut, leftOut < 0 ? 0 : random.nextInt(classes[leftOut]));
    }

    /** One assignment the contract lists, and the key it is ordered by. */
    private record Listed(int[] where, int distance, int moves, int[] positions) {}

    /**
     * Every assignment the contract admits, by listing the whole space: a subset of the movable
     * positions, each moved to a class it does not stand at, every prefix of the moves standing
     * together beside the base that follows, and nothing the pruning leaves out.
     */
    private static List<Listed> listed(Model model) {
        List<Listed> out = new ArrayList<>();
        int n = model.steps().length;
        for (int mask = 0; mask < 1 << n; mask++) {
            List<Integer> positions = new ArrayList<>();
            for (int j = 0; j < n; j++) {
                if ((mask & 1 << j) != 0) {
                    positions.add(model.steps()[j]);
                }
            }
            fill(model, positions, 0, model.base().clone(), mask, out);
        }
        out.sort(Comparator.<Listed>comparingInt(Listed::distance)
                .thenComparingInt(Listed::moves)
                .thenComparing(Listed::positions, Arrays::compare)
                .thenComparing((one, other) -> {
                    for (int axis : one.positions()) {
                        int compared = Integer.compare(one.where()[axis], other.where()[axis]);
                        if (compared != 0) {
                            return compared;
                        }
                    }
                    return 0;
                }));
        return out;
    }

    private static void fill(Model model, List<Integer> positions, int k, int[] where, int mask,
                             List<Listed> out) {
        if (!model.allows(where) && k > 0) {
            return;
        }
        if (k == positions.size()) {
            if (!model.leavesOut(where)) {
                out.add(new Listed(where.clone(), model.distance(where), positions.size(),
                        positions.stream().mapToInt(Integer::intValue).toArray()));
            }
            return;
        }
        int axis = positions.get(k);
        int stood = where[axis];
        for (int c = 0; c < model.classes()[axis]; c++) {
            if (c == stood) {
                continue;
            }
            where[axis] = c;
            fill(model, positions, k + 1, where, mask, out);
        }
        where[axis] = stood;
    }

    private static List<int[]> walked(Model model) {
        NearestAssignments walk = model.walk();
        List<int[]> out = new ArrayList<>();
        for (int distance = 0; distance <= walk.farthest() + 1; distance++) {
            NearestAssignments.Ended ended = walk.visitAt(distance, model.together(),
                    model.pruning(), new NearestAssignments.Looks(Long.MAX_VALUE), where -> {
                        out.add(where.clone());
                        return true;
                    });
            assertEquals(NearestAssignments.Ended.EXHAUSTED, ended);
        }
        return out;
    }

    @Test
    void theAssignmentsComeInTheOrderTheContractNamesOnEveryModel() {
        Random random = new Random(2722);
        int withMore = 0;
        for (int round = 0; round < 3000; round++) {
            Model model = random(random, round % 3 != 0, round % 2 == 0);
            List<int[]> expected = listed(model).stream().map(Listed::where).toList();
            List<int[]> actual = walked(model);
            assertEquals(expected.stream().map(Arrays::toString).toList(),
                    actual.stream().map(Arrays::toString).toList(), "round " + round);
            withMore += expected.size() > 1 ? 1 : 0;
        }
        assertTrue(withMore > 1000, "the models had something to order");
    }

    /**
     * A position moved back to where the origin stands brings the assignment nearer, so fewer
     * positions moved is not nearer: the walk hands over by distance, and a nearer assignment is
     * never behind a farther one.
     */
    @Test
    void aMoveBackToTheOriginIsNearerThanTheBaseItLeft() {
        // The base differs from the origin at both positions; moving either back is one move and
        // brings the assignment one nearer.
        Model model = new Model(new int[] {0, 0, 0}, new int[] {1, 1, 0}, new int[] {0, 1},
                new int[] {2, 2, 2}, List.of(), -1, 0);
        List<Integer> distances = new ArrayList<>();
        List<Integer> moves = new ArrayList<>();
        for (Listed each : listed(model)) {
            distances.add(each.distance());
            moves.add(each.moves());
        }
        assertEquals(distances.stream().sorted().toList(), distances);
        assertTrue(moves.getFirst() > 0, "the nearest assignment moves a position: " + moves);
        assertEquals(listed(model).stream().map(l -> Arrays.toString(l.where())).toList(),
                walked(model).stream().map(Arrays::toString).toList());
    }

    @Test
    void aVisitorThatStopsAtTheFirstLeavesTheRestUnwalked() {
        int[] classes = new int[14];
        Arrays.fill(classes, 141);
        int[] steps = new int[14];
        for (int i = 0; i < steps.length; i++) {
            steps[i] = i;
        }
        int[] zeros = new int[14];
        NearestAssignments walk = new NearestAssignments(zeros, zeros, steps, classes);
        NearestAssignments.Looks looks = new NearestAssignments.Looks(1_000_000L);
        int[] seen = {0};
        NearestAssignments.Ended ended = walk.visitAt(3, together(14), (_, _, _) -> false, looks,
                where -> {
                    seen[0]++;
                    return false;
                });
        assertEquals(NearestAssignments.Ended.DECLINED, ended);
        assertEquals(1, seen[0]);
        assertTrue(looks.left() > 999_000L, "three classes were looked at: " + looks.left());
    }

    @Test
    void aVisitorThatStopsInTheMiddleAndAtTheEndStopsThere() {
        Model model = random(new Random(7), false, false);
        List<int[]> all = walked(model);
        assertTrue(all.size() >= 3, "something to stop in the middle of");
        for (int stopAt : new int[] {0, all.size() / 2, all.size() - 1}) {
            List<int[]> seen = new ArrayList<>();
            NearestAssignments walk = model.walk();
            NearestAssignments.Ended last = NearestAssignments.Ended.EXHAUSTED;
            for (int distance = 0; distance <= walk.farthest() + 1
                    && last == NearestAssignments.Ended.EXHAUSTED; distance++) {
                last = walk.visitAt(distance, model.together(), model.pruning(),
                        new NearestAssignments.Looks(Long.MAX_VALUE), where -> {
                            seen.add(where.clone());
                            return seen.size() <= stopAt;
                        });
            }
            assertEquals(stopAt + 1, seen.size(), "stopped at " + stopAt);
            assertEquals(NearestAssignments.Ended.DECLINED, last);
            assertEquals(Arrays.toString(all.get(stopAt)), Arrays.toString(seen.get(stopAt)));
        }
    }

    @Test
    void lookAtMostAsManyAsTheLooksAllowAndSayThatTheyRanOut() {
        int[] classes = {141, 141, 141, 141, 141, 141};
        int[] steps = {0, 1, 2, 3, 4, 5};
        int[] zeros = new int[6];
        NearestAssignments walk = new NearestAssignments(zeros, zeros, steps, classes);
        NearestAssignments.Looks looks = new NearestAssignments.Looks(1000);
        int[] seen = {0};
        NearestAssignments.Ended ended = walk.visitAt(3, together(6), (_, _, _) -> false, looks,
                where -> {
                    seen[0]++;
                    return true;
                });
        assertEquals(NearestAssignments.Ended.OUT_OF_LOOKS, ended);
        assertTrue(looks.spent());
        assertTrue(seen[0] <= 1000, "an assignment is at least a look: " + seen[0]);
    }

    @Test
    void aWalkThatHasEverythingIsExhaustedAndNotOutOfLooks() {
        Model model = new Model(new int[] {0, 0}, new int[] {0, 0}, new int[] {0, 1},
                new int[] {2, 2}, List.of(), -1, 0);
        NearestAssignments.Looks looks = new NearestAssignments.Looks(100);
        List<int[]> seen = new ArrayList<>();
        for (int distance = 0; distance <= 2; distance++) {
            assertEquals(NearestAssignments.Ended.EXHAUSTED, model.walk().visitAt(distance,
                    model.together(), model.pruning(), looks, where -> {
                        seen.add(where.clone());
                        return true;
                    }));
        }
        assertEquals(4, seen.size());
        assertTrue(!looks.spent());
    }

    private static NearestAssignments.Together together(int axes) {
        int[] standing = new int[axes];
        return new NearestAssignments.Together() {

            @Override
            public void move(int axis, int from, int to) {
                standing[axis] = to;
            }

            @Override
            public boolean holds() {
                return true;
            }
        };
    }
}
