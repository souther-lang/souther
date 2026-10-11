package souther.compiler.meaning;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * How many of some statements hold, held against a number, is which of them hold: a choice for each
 * that puts the number where the comparison does.
 *
 * <p>What a closure states of each value a container was written with is one statement per value,
 * and {@code List.filter(x -> x > 0, [a, a])} holds two of one statement. So two of them is that
 * statement, and one of them is nothing a row can be: the same value meets it twice or not at all.
 */
class HowManyOfSomeStatementsHoldIsWhichOfThemDoTest {

    /** How many choices of which statements hold a comparison here is written out as. */
    private static final long CHOICES = 256;

    private static final Proposition P =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("p")), true);

    private static final Proposition Q =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("q")), true);

    @Test
    void twoOfOneStatementWrittenTwiceIsThatStatement() {
        assertEquals(P, howMany(List.of(P, P), Rel.EQ, 2));
    }

    @Test
    void oneOfOneStatementWrittenTwiceIsNoRow() {
        assertEquals(new Proposition.Always(false), howMany(List.of(P, P), Rel.EQ, 1));
    }

    @Test
    void oneOfTwoIsEitherOfThemAndNotBoth() {
        assertEquals(Proposition.any(List.of(
                        Proposition.all(List.of(P, Q.denied())),
                        Proposition.all(List.of(P.denied(), Q)))),
                howMany(List.of(P, Q), Rel.EQ, 1));
    }

    /** At least one holding is one of them holding, whatever the other does: a fewest set that
     *  comes to the number, and nothing said of the rest. */
    @Test
    void atLeastOneOfTwoIsEitherOfThem() {
        assertEquals(Proposition.any(List.of(P, Q)), howMany(List.of(P, Q), Rel.GE, 1));
    }

    /** At most one holding is the denial of both holding: one of them failing, whatever the other
     *  does. */
    @Test
    void atMostOneOfTwoIsEitherOfThemFailing() {
        assertEquals(Proposition.any(List.of(P.denied(), Q.denied())),
                Proposition.compared(relation(List.of(P, Q), Rel.GE, 2), false, CHOICES));
    }

    @Test
    void denyingTheComparisonDeniesWhichOfThemHold() {
        assertEquals(P.denied(),
                Proposition.compared(relation(List.of(P, P), Rel.EQ, 2), false, CHOICES));
    }

    /** A statement written twice weighs two: two of three writings is it alone or the other with
     *  it failing — never the other alone. */
    @Test
    void aStatementWrittenTwiceWeighsTwo() {
        assertEquals(Proposition.all(List.of(P, Q.denied())),
                howMany(List.of(P, P, Q), Rel.EQ, 2));
    }

    /**
     * Exactly one of many is one choice for each of them, and not one for each way they could all
     * come out — which is what lets a count over as many values as a reading allows readings be
     * read at all.
     */
    @Test
    void exactlyOneOfManyIsOneChoiceForEach() {
        assertEquals(18, Proposition.choicesIn(relation(distinct(18), Rel.EQ, 1), 256));
        assertEquals(257, Proposition.choicesIn(relation(distinct(18), Rel.EQ, 9), 256));
    }

    /** More choices than a figure handed in are not written out, and nothing is said in their
     *  place. */
    @Test
    void moreChoicesThanAreMadeAreNotWrittenOut() {
        Relation half = relation(distinct(18), Rel.EQ, 9);

        assertNull(Proposition.compared(half, true, CHOICES));
    }

    /** A count of statements compared with no figure in hand is refused rather than written out
     *  however many choices it comes to. */
    @Test
    void aCountComparedWithNoFigureIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> Proposition.compared(relation(distinct(18), Rel.EQ, 9), true));
    }

    /**
     * A count no choice comes to is no choice, found without looking at any: forty statements each
     * written twice come to an even number however many hold, and every set of fewer than twenty
     * of them comes short of thirty-nine.
     */
    @Test
    @Timeout(value = 10, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void aCountNoChoiceComesToIsNoChoiceFoundWithoutLookingAtAny() {
        List<Proposition> twice = new ArrayList<>();
        for (Proposition one : distinct(40)) {
            twice.add(one);
            twice.add(one);
        }
        Relation odd = relation(twice, Rel.EQ, 39);

        assertEquals(0, Proposition.choicesIn(odd, 256));
        assertEquals(new Proposition.Always(false), Proposition.compared(odd, true, CHOICES));
    }

    /** {@code count} statements, each about a position of its own. */
    private static List<Proposition> distinct(int count) {
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + i)), true));
        }
        return out;
    }

    /** {@code #each - against} standing to nought as {@code rel} says. */
    private static Proposition howMany(List<Proposition> each, Rel rel, long against) {
        return Proposition.compared(relation(each, rel, against), true, CHOICES);
    }

    private static Relation relation(List<Proposition> each, Rel rel, long against) {
        return new Relation.Affine(new LinearForm<>(ExactRatio.of(-against),
                Map.of(new Quantity.HowManyHold(each), ExactRatio.ONE)), rel);
    }
}
