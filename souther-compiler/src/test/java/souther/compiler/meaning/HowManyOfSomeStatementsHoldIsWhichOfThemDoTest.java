package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many of some statements hold, held against a number, is which of them hold: a choice for each
 * that puts the number where the comparison does.
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
     * come out — which is what lets a count over as many values as a reading allows readings be
     * read at all.
     */
    @Test
    void exactlyOneOfManyIsOneChoiceForEach() {
        List<Proposition> many = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            many.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + i)), true));
        }

        assertEquals(18, Proposition.choicesIn(relation(many, Rel.EQ, 1), 256));
        assertEquals(257, Proposition.choicesIn(relation(many, Rel.EQ, 9), 256));
    }

    /** More choices than the reading that counted them makes is kept as the relation. */
    @Test
    void moreChoicesThanAreMadeAreNotWrittenOut() {
        List<Proposition> many = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            many.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + i)), true));
        }
        Relation half = relation(many, Rel.EQ, 9);

        assertEquals(new Proposition.Compared(half, true), Proposition.compared(half, true));
    }

    /** {@code #each - against} standing to nought as {@code rel} says. */
    private static Proposition howMany(List<Proposition> each, Rel rel, long against) {
        return Proposition.compared(relation(each, rel, against), true);
    }

    private static Relation relation(List<Proposition> each, Rel rel, long against) {
        return new Relation.Affine(new LinearForm<>(ExactRatio.of(-against),
                Map.of(new Quantity.HowManyHold(each, 256), ExactRatio.ONE)), rel);
    }
}
