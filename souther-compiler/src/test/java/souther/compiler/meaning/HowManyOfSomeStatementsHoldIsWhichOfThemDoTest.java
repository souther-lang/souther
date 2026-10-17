package souther.compiler.meaning;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many of some statements hold, held against a number, is which of them hold: a choice for each
 * that puts the number where the comparison does — written out where the choices are few enough to
 * be a part of what a step states, and otherwise held as the statements and the counts admitted.
 *
 * <p>What a closure states of each value a container was written with is one statement per value,
 * and {@code List.filter(x -> x > 0, [a, a])} holds two of one statement. So two of them is that
 * statement, and one of them is nothing a row can be: the same value meets it twice or not at all.
 */
class HowManyOfSomeStatementsHoldIsWhichOfThemDoTest {

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
                Proposition.compared(relation(List.of(P, Q), Rel.GE, 2), false));
    }

    @Test
    void denyingTheComparisonDeniesWhichOfThemHold() {
        assertEquals(P.denied(), Proposition.compared(relation(List.of(P, P), Rel.EQ, 2), false));
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
     * come out: written out, as long as the choices come to no more parts than a step is concluded
     * with.
     */
    @Test
    void exactlyOneOfManyIsOneChoiceForEach() {
        List<Proposition> each = distinct(18);
        assertEquals(exactlyOneOf(each), howMany(each, Rel.EQ, 1));
    }

    /**
     * Exactly one of more, whose choices each name every statement, comes to more parts written
     * out than a step is concluded with, and is held as the count: each statement once, and the
     * one count it admits. Its choices are still what it states, for a reader that asks for them.
     */
    @Test
    void aCountWhoseChoicesComeToMorePartsIsHeldAsTheCount() {
        List<Proposition> each = distinct(70);
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(each, Rel.EQ, 1));

        assertEquals(each.stream().sorted((a, b) -> a.key().compareTo(b.key())).toList(),
                held.statements());
        assertEquals(List.of(1), held.admitted());
        assertTrue(held.weights().stream().allMatch(weight -> weight == 1), held::toString);
        assertEquals(exactlyOneOf(each), held.choices());
    }

    /** Half of eighteen is more choices than are written out, and is held as the count too. */
    @Test
    void moreChoicesThanAreWrittenOutAreHeldAsTheCount() {
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(18), Rel.EQ, 9));

        assertEquals(List.of(9), held.admitted());
    }

    /**
     * A count held as the count is denied as the other counts: no statement is denied and no choice
     * is made, so the denial of a count past what is written out is as small as the count.
     */
    @Test
    void aCountHeldAsTheCountIsDeniedAsTheOtherCounts() {
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(70), Rel.EQ, 1));
        Proposition.SoManyHold denied = assertInstanceOf(Proposition.SoManyHold.class,
                held.denied());

        assertEquals(held.statements(), denied.statements());
        List<Integer> others = new ArrayList<>();
        others.add(0);
        for (int count = 2; count <= 70; count++) {
            others.add(count);
        }
        assertEquals(others, denied.admitted());
        assertEquals(held, denied.denied());
        assertEquals(denied, Proposition.compared(relation(distinct(70), Rel.EQ, 1), false));
    }

    /**
     * Choices more than one condition is read in, or that come to more parts than a reader of
     * them is handed, are handed to none, and which of the two is what the reader is told.
     *
     * <p>Half of eighteen is past how many; exactly one of two hundred and fifty-six is as many
     * choices as one condition is read in, each naming every statement, and past the parts.
     */
    @Test
    void choicesPastWhatAReaderIsHandedAreHandedToNone() {
        Proposition.SoManyHold half = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(18), Rel.EQ, 9));
        assertNull(half.choices());
        assertEquals(CompositionBudget.READINGS_OF_ONE_CONDITION, half.choicesStoppedAt());

        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        Proposition.SoManyHold one = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(most), Rel.EQ, 1));
        assertNull(one.choices());
        assertEquals(CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO,
                one.choicesStoppedAt());
        assertEquals(CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO.figure(),
                new WhyNotTaken.MoreChoicesThanAreWrittenOut(one.choicesStoppedAt()).figure()
                        .orElseThrow());

        Proposition.SoManyHold fewer = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(distinct(70), Rel.EQ, 1));
        assertEquals(exactlyOneOf(distinct(70)), fewer.choices());
        assertNull(fewer.choicesStoppedAt());
    }

    /**
     * A count whose statements a reader makes again is the same count of what they came to, two
     * that came out one statement being that one weighed as both were — and written out where that
     * is few enough choices.
     */
    @Test
    void aCountMadeAgainWeighsTwoStatementsThatCameOutOneAsBoth() {
        List<Proposition> each = distinct(70);
        Proposition.SoManyHold held = assertInstanceOf(Proposition.SoManyHold.class,
                howMany(each, Rel.EQ, 1));
        List<Proposition> remade = new ArrayList<>();
        for (int at = 0; at < held.statements().size(); at++) {
            remade.add(at < 69 ? P : Q);
        }

        // P weighs sixty-nine, so one holding is Q holding with P failing.
        assertEquals(Proposition.all(List.of(P.denied(), Q)), held.over(remade));
        assertEquals(howMany(remade, Rel.EQ, 1), held.over(remade));
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

        assertEquals(new Proposition.Always(false), howMany(twice, Rel.EQ, 39));
    }

    /** {@code count} statements, each about a position of its own. */
    private static List<Proposition> distinct(int count) {
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + i)), true));
        }
        return out;
    }

    /** Some one of {@code each} holding and every other failing, written out by hand. */
    private static Proposition exactlyOneOf(List<Proposition> each) {
        List<Proposition> choices = new ArrayList<>();
        for (Proposition holding : each) {
            List<Proposition> parts = new ArrayList<>();
            for (Proposition one : each) {
                parts.add(one == holding ? one : one.denied());
            }
            choices.add(Proposition.all(parts));
        }
        return Proposition.any(choices);
    }

    /** {@code #each - against} standing to nought as {@code rel} says. */
    private static Proposition howMany(List<Proposition> each, Rel rel, long against) {
        return Proposition.compared(relation(each, rel, against), true);
    }

    private static Relation relation(List<Proposition> each, Rel rel, long against) {
        return new Relation.Affine(new LinearForm<>(ExactRatio.of(-against),
                Map.of(new Quantity.HowManyHold(each), ExactRatio.ONE)), rel);
    }
}
