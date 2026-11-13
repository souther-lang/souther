package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;
import souther.test.Growth;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Random;
import java.util.SequencedMap;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * What the difference closure holds is what shortest paths over every position leave, with nought
 * one more position, and a chain of rules is closed in the square of its length.
 *
 * <p>The paths are worked out here the plain way: every pair of positions, every position through
 * which a path may go, one after another. Strictness travels with the sum, so rules are drawn both
 * ways, over positions that fill so that a strict bound stays strict. A system whose paths come
 * back to a position below nought, or to nought without reaching it, holds nothing, and holds
 * nothing in the closure too; otherwise every difference, and every position's bound on either
 * side, is what the paths say.
 */
class TheDifferenceClosureIsTheShortestPathsOverEveryPositionTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c", "d", "e", "f", "g");
    private static final Function<String, Granularity> FILLING = _ -> Granularity.DENSE;
    private static final List<String> RELATIONS = List.of("<=", "<", ">=", ">");

    /** The rules as text, and what they state as {@code paths[from][to]}: the tightest bound on
     *  {@code from - to}, with nought the position after the last. */
    private record Drawn(List<Written> rules, ExactCut[][] paths) {}

    private static Drawn draw(Random random, int positions) {
        int nought = positions;
        List<Written> rules = new ArrayList<>();
        ExactCut[][] paths = new ExactCut[positions + 1][positions + 1];
        int count = 1 + random.nextInt(2 * positions + 2);
        for (int at = 0; at < count; at++) {
            int x = random.nextInt(positions);
            int y = random.nextInt(positions + 1);
            if (y == x) {
                continue;
            }
            int n = random.nextInt(9) - 4;
            int relation = random.nextInt(4);
            boolean strict = relation == 1 || relation == 3;
            boolean atMost = relation < 2;
            String left = POSITIONS.get(x);
            rules.add(rule(y == nought ? left + " " + RELATIONS.get(relation) + " " + n
                    : left + " - " + POSITIONS.get(y) + " " + RELATIONS.get(relation) + " " + n));
            int from = atMost ? x : y;
            int to = atMost ? y : x;
            ExactRatio bound = ExactRatio.of(atMost ? n : -n);
            paths[from][to] = ExactCut.tighterUpper(paths[from][to],
                    strict ? ExactCut.exclusive(bound) : ExactCut.inclusive(bound));
        }
        return new Drawn(rules, paths);
    }

    /** Every pair through every position, one position after another. */
    private static void closeOverEveryPosition(ExactCut[][] paths) {
        for (int through = 0; through < paths.length; through++) {
            for (int from = 0; from < paths.length; from++) {
                for (int to = 0; to < paths.length; to++) {
                    if (paths[from][through] != null && paths[through][to] != null) {
                        ExactCut by = ExactCut.meetingBoth(paths[from][through],
                                paths[through][to]).orNull();
                        paths[from][to] = ExactCut.tighterUpper(paths[from][to], by);
                    }
                }
            }
        }
    }

    private static boolean someCycleSumsBelowNought(ExactCut[][] paths) {
        for (int at = 0; at < paths.length; at++) {
            ExactCut cycle = paths[at][at];
            if (cycle != null && (cycle.at().signum() < 0
                    || (cycle.at().isZero() && !cycle.inclusive()))) {
                return true;
            }
        }
        return false;
    }

    @Test
    void everyPairIsWhatShortestPathsLeave() {
        Random random = new Random(3167);
        int compared = 0;
        int empty = 0;
        for (int round = 0; round < 2000; round++) {
            int positions = 2 + random.nextInt(6);
            int nought = positions;
            Drawn drawn = draw(random, positions);
            ExactCut[][] paths = drawn.paths();
            closeOverEveryPosition(paths);
            DifferenceBounds<String> closed = DifferenceBounds.over(
                    statedOnly(drawn.rules(), FILLING), CanonicalOrder.asTheyAreSpelled());
            boolean nothing = someCycleSumsBelowNought(paths);
            assertEquals(nothing, closed.holdsNothing(), drawn.rules().toString());
            if (nothing) {
                empty++;
                continue;
            }
            compared++;
            for (int a = 0; a < positions; a++) {
                String atom = POSITIONS.get(a);
                if (!closed.positions().contains(atom)) {
                    continue;
                }
                assertEquals(paths[a][nought], closed.upperBoundOf(atom),
                        "above " + atom + " in " + drawn.rules());
                ExactCut under = paths[nought][a];
                assertEquals(under == null ? null
                                : new ExactCut(under.at().negated(), under.inclusive()),
                        closed.lowerBoundOf(atom), "below " + atom + " in " + drawn.rules());
                for (int b = 0; b < positions; b++) {
                    String other = POSITIONS.get(b);
                    if (a != b && closed.positions().contains(other)) {
                        assertEquals(paths[a][b], closed.differenceBound(atom, other),
                                atom + " - " + other + " in " + drawn.rules());
                    }
                }
            }
        }
        assertTrue(compared > 300 && empty > 100, "compared " + compared + ", empty " + empty);
    }

    /** Each position at most one above the next and two below it, the first held at most five and
     *  the last at least nought. */
    private static List<AffineConstraint<String>> chain(int n) {
        List<Written> rules = new ArrayList<>();
        for (int at = 0; at + 1 < n; at++) {
            rules.add(rule(name(at) + " - " + name(at + 1) + " <= 1"));
            rules.add(rule(name(at + 1) + " - " + name(at) + " <= 2"));
        }
        rules.add(rule(name(0) + " <= 5"));
        rules.add(rule(name(n - 1) + " >= 0"));
        return statedOnly(rules, FILLING);
    }

    /** A position's name in letters, which is all a rule written as text names one with. */
    private static String name(int at) {
        StringBuilder out = new StringBuilder();
        int rest = at;
        do {
            out.append((char) ('a' + rest % 26));
            rest /= 26;
        } while (rest > 0);
        return out.reverse().toString();
    }

    @Test
    void aChainIsClosedInTheSquareOfItsLength() {
        SequencedMap<Integer, Long> hops = new LinkedHashMap<>();
        for (int n : new int[] {30, 60, 120}) {
            long[] counting = {0};
            DifferenceBounds.COUNTING_HOPS = counting;
            try {
                DifferenceBounds.over(chain(n), CanonicalOrder.asTheyAreSpelled());
            } finally {
                DifferenceBounds.COUNTING_HOPS = null;
            }
            hops.put(n, counting[0]);
        }
        // Twice the length is four times the paths, where closing through every position in turn
        // is eight times the hops.
        Growth.eachAtMost(hops, 5, 1);
    }

    @Test
    void aChainBoundsEachPositionByTheOnesAlongIt() {
        DifferenceBounds<String> closed =
                DifferenceBounds.over(chain(40), CanonicalOrder.asTheyAreSpelled());
        // The first is at most 5 and each next is at most two above the one before it, so the last
        // is at most 5 + 2·39. The last is at least nought and the first is at most two below each
        // next, so the first is at least -2·39.
        assertEquals(ExactCut.inclusive(ExactRatio.of(5)), closed.upperBoundOf(name(0)));
        assertEquals(ExactCut.inclusive(ExactRatio.of(5 + 2 * 39)), closed.upperBoundOf(name(39)));
        assertEquals(ExactCut.inclusive(ExactRatio.of(-2 * 39)), closed.lowerBoundOf(name(0)));
    }
}
