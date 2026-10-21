package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line of a count of statements is a statement of the count, and it decides where the other
 * statements come to a number the count admits with the line holding and not with it failing, or
 * the other way round: one case for each such number, and not one for each set of the others that
 * comes to it.
 *
 * <p>A row on each side of the line is in the same case only where the others come to the same
 * number on both sides, which is what a case saying how many of them hold asks of a row.
 */
class WhereALineOfACountDecidesWhereTheOthersComeToTheNumbersAroundItTest {

    /** {@code x<at> > 0}, held. */
    private static Proposition.Compared positive(int at) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("w").then("x%02d".formatted(at)))),
                        ExactRatio.ONE)), Rel.GT), true);
    }

    private static List<Proposition> positives(int n) {
        List<Proposition> out = new ArrayList<>();
        for (int at = 0; at < n; at++) {
            out.add(positive(at));
        }
        return out;
    }

    private static Proposition count(List<Proposition> statements, int... admitted) {
        return Proposition.SoManyHold.counting(statements,
                statements.stream().map(_ -> 1).toList(),
                IntStream.of(admitted).boxed().toList());
    }

    /**
     * Exactly {@code k} of {@code n} values above nought: every value is a line, and it decides
     * where the other {@code n - 1} come to {@code k - 1} (the line then moves the count into
     * {@code k}) or to {@code k} (and out of it). The counts either side of the figure a count
     * was once written out at, and one past every figure, come to the same two cases a line.
     */
    @Test
    void everyLineIsTwoCasesWhateverHowManySetsOfTheOthersComeToThem() {
        for (int[] nk : new int[][] {{8, 4}, {10, 5}, {11, 5}, {13, 6}, {20, 10}}) {
            int n = nk[0];
            int k = nk[1];
            List<Proposition> values = positives(n);
            Proposition stated = count(values, k);
            assertTrue(stated instanceof Proposition.SoManyHold, () -> "held as a count: " + stated);

            List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);

            assertEquals(n, lines.size(), () -> n + "," + k + ": a line for each value");
            for (WhereEachLineDecides.Decides line : lines) {
                List<Proposition> others = new ArrayList<>(values);
                others.removeIf(each -> each.key().equals(line.line().key()));
                assertEquals(List.of(count(others, k - 1), count(others, k)),
                        line.cases().stream().map(DecidingCase::condition).toList(),
                        () -> n + "," + k + ": " + line.line());
                assertTrue(line.cases().stream().allMatch(DecidingCase::saidAlone),
                        () -> n + "," + k + ": each case stands for itself");
            }
        }
    }

    /**
     * Fewer than {@code k} is the denial of {@code k} or more, and the line decides at the one
     * number where the count crosses the bound: a count admitting everything from {@code k} up is
     * one case a line.
     */
    @Test
    void aCountAdmittingEveryNumberFromSomeNumberUpDecidesAtTheOneNumberBelowIt() {
        List<Proposition> values = positives(12);
        Proposition stated = count(values, 7, 8, 9, 10, 11, 12);

        for (WhereEachLineDecides.Decides line : WhereEachLineDecides.in(stated)) {
            List<Proposition> others = new ArrayList<>(values);
            others.removeIf(each -> each.key().equals(line.line().key()));
            assertEquals(List.of(count(others, 6)),
                    line.cases().stream().map(DecidingCase::condition).toList(),
                    () -> "" + line.line());
        }
    }

    /**
     * A statement written twice is one statement weighed twice, and crossing its line moves both:
     * the line decides where the others come to the numbers two below and at the count.
     */
    @Test
    void aStatementWrittenTwiceMovesTheCountByTwoAcrossItsLine() {
        List<Proposition> others = positives(12).subList(1, 12);
        List<Proposition> all = new ArrayList<>(others);
        all.add(positive(0));
        List<Integer> weights = new ArrayList<>(others.stream().map(_ -> 1).toList());
        weights.add(2);
        Proposition stated = Proposition.SoManyHold.counting(all, weights, List.of(6));

        WhereEachLineDecides.Decides doubled = WhereEachLineDecides.in(stated).stream()
                .filter(line -> line.line().key().equals(positive(0).key())).findFirst()
                .orElseThrow();

        assertEquals(List.of(count(others, 4), count(others, 6)),
                doubled.cases().stream().map(DecidingCase::condition).toList());
    }
}
