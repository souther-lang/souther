package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.LengthsPastTheWay.Lengths;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import net.unit8.notation199x.pattern.Meter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lengths of some runs are the lengths of any of them, asked of every length up to a few more
 * than the runs reach: what they hold, what they leave out, the lengths two of them share, and the
 * strings of the lengths. A brute-force walk over the lengths is the oracle, and the sets of runs
 * are every choice of up to three from a few that touch, overlap and lie apart.
 */
class LengthRunsAreTheLengthsOfTheirRunsTest {

    private static final int REACH = 16;

    private static final List<Lengths> SOME = List.of(
            run(0, 2), run(3, 3), run(5, 6), run(6, 9), run(11, 11), run(14, null), run(1, 0));

    private static Lengths run(int least, Integer most) {
        return new Lengths(BigInteger.valueOf(least),
                most == null ? null : BigInteger.valueOf(most));
    }

    /** Every list of at most three of {@link #SOME}, in every order. */
    private static List<List<Lengths>> everyChoice() {
        List<List<Lengths>> out = new ArrayList<>();
        out.add(List.of());
        for (Lengths a : SOME) {
            out.add(List.of(a));
            for (Lengths b : SOME) {
                out.add(List.of(a, b));
                for (Lengths c : SOME) {
                    out.add(List.of(a, b, c));
                }
            }
        }
        return out;
    }

    private static boolean holds(LengthRuns runs, int length) {
        return runs.runs().stream().anyMatch(each -> each.holds(BigInteger.valueOf(length),
                BigInteger.valueOf(length)));
    }

    private static boolean anyHolds(List<Lengths> runs, int length) {
        return runs.stream().anyMatch(each -> each.holds(BigInteger.valueOf(length),
                BigInteger.valueOf(length)));
    }

    @Test
    void theRunsHoldTheLengthsOfAnyOfTheRunsTheyWereMadeOf() {
        for (List<Lengths> made : everyChoice()) {
            LengthRuns runs = LengthRuns.ofAll(made);
            for (int length = 0; length <= REACH; length++) {
                assertEquals(anyHolds(made, length), holds(runs, length), made + " at " + length);
            }
        }
    }

    @Test
    void theyAreKeptLowestFirstAndApartSoThatTheSameLengthsAreOneValue() {
        for (List<Lengths> made : everyChoice()) {
            LengthRuns runs = LengthRuns.ofAll(made);
            for (int each = 1; each < runs.runs().size(); each++) {
                assertTrue(runs.runs().get(each - 1).most().add(BigInteger.ONE)
                        .compareTo(runs.runs().get(each).least()) < 0, made.toString());
            }
            List<Lengths> turned = new ArrayList<>(made).reversed();
            assertEquals(runs, LengthRuns.ofAll(turned), made.toString());
        }
    }

    @Test
    void theLengthsOfTwoAreTheLengthsBothHold() {
        List<List<Lengths>> choices = everyChoice().stream().filter(c -> c.size() <= 2).toList();
        for (List<Lengths> one : choices) {
            for (List<Lengths> other : choices) {
                LengthRuns both = LengthRuns.ofAll(one).and(LengthRuns.ofAll(other));
                for (int length = 0; length <= REACH; length++) {
                    assertEquals(anyHolds(one, length) && anyHolds(other, length),
                            holds(both, length), one + " and " + other + " at " + length);
                }
            }
        }
    }

    @Test
    void whatIsOutsideIsEveryLengthTheyDoNotHold() {
        for (List<Lengths> made : everyChoice()) {
            LengthRuns runs = LengthRuns.ofAll(made);
            for (int length = 0; length <= REACH; length++) {
                int at = length;
                boolean outside = runs.outside().stream().anyMatch(piece ->
                        piece.shortest() <= at && (piece.longest() == null || at <= piece.longest()));
                assertEquals(!holds(runs, length), outside, made + " at " + length);
            }
        }
    }

    @Test
    void theStringsAreTheStringsOfTheLengthsHeld() {
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        for (List<Lengths> made : everyChoice()) {
            LengthRuns runs = LengthRuns.ofAll(made);
            PatternPlan inside = runs.strings();
            PatternPlan outside = runs.stringsOutside();
            if (runs.isEmpty()) {
                assertEquals(null, inside, made.toString());
                continue;
            }
            Language in = inside.compile(meter);
            Language out = outside == null ? null : outside.compile(meter);
            for (int length = 0; length <= REACH; length++) {
                String text = "a".repeat(length);
                assertEquals(holds(runs, length), in.has(text), made + " at " + length);
                if (out != null) {
                    assertEquals(!holds(runs, length), out.has(text), made + " out at " + length);
                }
            }
        }
    }

    @Test
    void theSameLengthsAreOneValueHoweverTheyWereMade() {
        assertEquals(LengthRuns.of(run(2, 5)),
                LengthRuns.ofAll(List.of(run(4, 5), run(2, 3))), "touching runs are one run");
        assertEquals(LengthRuns.of(run(2, 5)),
                LengthRuns.ofAll(List.of(run(2, 5), run(3, 4))), "a run inside another is lost");
        assertEquals(LengthRuns.ofAll(List.of(run(2, 3), run(6, 7))),
                LengthRuns.ofAll(List.of(run(6, 7), run(2, 3))), "the order they come in is none");
        assertEquals(LengthRuns.NONE, LengthRuns.ofAll(List.of()));
        assertEquals(LengthRuns.NONE, LengthRuns.of(new Lengths(BigInteger.ONE, BigInteger.ZERO)));
    }

    @Test
    void theValuesOfTheRunsAreTheValuesOfEachRunAtItsLengths() {
        LengthRuns runs = LengthRuns.ofAll(List.of(run(0, 6), run(8, 10)));
        List<ValuesWithin> over = runs.over(ValueSet.ANY);
        assertEquals(2, over.size());
        assertEquals(7L, over.getLast().shortest() - 1);
        IntPredicate has = length -> runs.ofValues(ValueSet.ANY)
                .has(souther.compiler.values.Value.text("a".repeat(length)));
        assertTrue(has.test(6));
        assertTrue(!has.test(7));
        assertTrue(has.test(8));
    }
}
