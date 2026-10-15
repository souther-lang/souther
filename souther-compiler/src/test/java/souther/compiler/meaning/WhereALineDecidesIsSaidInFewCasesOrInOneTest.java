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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line decides is said as cases while there are few of them, and as one case — the
 * statement with the line held against the statement with it failing — once there would be more.
 *
 * <p>A line held together with a choice of an even number of other parts holding decides exactly
 * where an even number of them hold, which is a case for every such way: sixteen of five parts, and
 * thirty-two of six. The first is said case by case; the second is past what is said that way, and
 * the cases are not all worked out before that is noticed.
 */
class WhereALineDecidesIsSaidInFewCasesOrInOneTest {

    private static final Proposition.Compared LINE = new Proposition.Compared(
            new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                    Map.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x"))),
                            ExactRatio.ONE)), Rel.GT), true);

    @Test
    void sixteenCasesAreSaidOneByOne() {
        List<Proposition> cases = casesOf(5);
        assertEquals(16, cases.size(), () -> "a case for each even way of five: " + cases);
        assertTrue(cases.stream().allMatch(each -> each instanceof Proposition.All all
                        && all.parts().size() == 5),
                () -> "each of them the five parts, held or failing: " + cases);
    }

    @Test
    void moreCasesThanThatAreSaidAsOne() {
        List<Proposition> cases = casesOf(6);
        assertEquals(1, cases.size(), () -> "one case: " + cases);
        assertInstanceOf(Proposition.Any.class, cases.getFirst(),
                "the statement held against itself across the line, which is one of two things");
    }

    /** Where {@link #LINE} decides, held together with an even number of {@code parts} truths. */
    private static List<Proposition> casesOf(int parts) {
        List<Proposition> truths = new ArrayList<>();
        for (int i = 0; i < parts; i++) {
            truths.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + i)),
                    true));
        }
        List<Proposition> even = new ArrayList<>();
        for (int ways = 0; ways < 1 << parts; ways++) {
            if (Integer.bitCount(ways) % 2 != 0) {
                continue;
            }
            List<Proposition> each = new ArrayList<>();
            for (int i = 0; i < parts; i++) {
                each.add((ways >> i & 1) == 1 ? truths.get(i) : truths.get(i).denied());
            }
            even.add(Proposition.all(each));
        }
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(
                Proposition.all(List.of(LINE, Proposition.any(even))));
        assertEquals(1, lines.size(), () -> "one relation is a line: " + lines);
        return lines.getFirst().cases();
    }
}
