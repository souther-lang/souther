package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

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

    @Test
    void atLeastOneOfTwoIsAnyChoiceWithOneHolding() {
        assertEquals(Proposition.any(List.of(
                        Proposition.all(List.of(P, Q)),
                        Proposition.all(List.of(P, Q.denied())),
                        Proposition.all(List.of(P.denied(), Q)))),
                howMany(List.of(P, Q), Rel.GE, 1));
    }

    @Test
    void denyingTheComparisonDeniesWhichOfThemHold() {
        assertEquals(P.denied(), Proposition.compared(relation(List.of(P, P), Rel.EQ, 2), false));
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
