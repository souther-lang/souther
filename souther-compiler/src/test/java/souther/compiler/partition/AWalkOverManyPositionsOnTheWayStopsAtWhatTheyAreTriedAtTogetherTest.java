package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk placing the numbers of one question on the way tries each position at a bounded number of
 * values under every value of the positions before it, and so is held besides to how many values
 * its positions are tried at together: past that it stops, and says the figure.
 *
 * <p>Held by a question nothing answers: whole numbers nothing narrows, and a composer that
 * refuses every assignment it is offered, so the walk goes on until something stops it. Over five
 * positions the values each is tried at come, multiplied, to far more than the figure; over two
 * they do not, and the walk ends at the values each position is tried at without reaching it.
 */
class AWalkOverManyPositionsOnTheWayStopsAtWhatTheyAreTriedAtTogetherTest {

    private static final CompositionBudget TOGETHER =
            CompositionBudget.VALUES_THE_POSITIONS_ON_THE_WAY_ARE_TRIED_AT;

    private static final int EACH =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /** What a walk over {@code positions} whole numbers met, every assignment refused, and how
     *  many assignments it was offered. */
    private record Walked(NumericWitness.Standing standing, int offered) {}

    private static Walked walked(int positions) {
        return walked(positions, null);
    }

    /** The same, held to every residue of the positions' sum by {@code divisor}, where there is
     *  one. */
    private static Walked walked(int positions, BigInteger divisor) {
        List<String> names = new ArrayList<>();
        for (int i = 0; i < positions; i++) {
            names.add("n" + i);
        }
        Quantities quantities = quantities(names);
        List<NumericTerm.FromOnePosition> terms = new ArrayList<>();
        for (String name : names) {
            terms.add(new NumericTerm.ValueOf(TermPath.of(name)));
        }
        int[] offered = {0};
        NumericWitness.Composing refusingAll = _ -> {
            offered[0]++;
            return new NumericWitness.Composed.NotBuilt(CompositionShortfall.NONE);
        };
        Function<NumericTerm, Carrier> on = each -> quantities.ordersOf(each).answered();
        if (divisor == null) {
            return new Walked(NumericWitness.of(quantities.region(), terms, on,
                    NothingTheDeclarationsNarrow.LOOKING, refusingAll), offered[0]);
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        terms.forEach(term -> coefs.put(term, ExactRatio.ONE));
        List<NumericWitness.Congruent> congruents = new ArrayList<>();
        for (BigInteger r = BigInteger.ZERO; r.compareTo(divisor) < 0; r = r.add(BigInteger.ONE)) {
            congruents.add(new NumericWitness.Congruent(
                    new LinearForm<>(ExactRatio.ZERO, coefs), divisor, r));
        }
        return new Walked(NumericWitness.of(quantities.region(), terms, on,
                NothingTheDeclarationsNarrow.LOOKING, refusingAll, congruents), offered[0]);
    }

    /**
     * Asked under several congruences, the question is one question: the values tried under
     * each are counted together, so asking it seven ways tries no more than asking it once.
     */
    @Test
    void theCongruencesOfOneQuestionAreTriedUnderOneFigure() {
        Walked seven = walked(5, BigInteger.valueOf(7));

        NumericWitness.Standing.NotFound notFound =
                assertInstanceOf(NumericWitness.Standing.NotFound.class, seven.standing());
        assertTrue(notFound.met().figures().contains(TOGETHER), () -> notFound.met().toString());
        assertTrue(seven.offered() <= TOGETHER.maximum(),
                () -> "offered under one figure for all seven: " + seven.offered());
    }

    /**
     * And the congruences left once the figure is spent are not walked, and are said as left at
     * it. Over one position each congruence is tried at the values a position is tried at and no
     * more, so the figure is spent at the end of a walk that was refused nothing, and what says
     * it is the congruences left after it.
     */
    @Test
    void theCongruencesLeftOnceTheFigureIsSpentAreSaidAsLeftAtIt() {
        assertEquals(0, TOGETHER.maximum() % EACH, "the figure is spent at the end of a walk");
        Walked one = walked(1, BigInteger.valueOf(100));

        NumericWitness.Standing.NotFound notFound =
                assertInstanceOf(NumericWitness.Standing.NotFound.class, one.standing());
        assertTrue(notFound.met().figures().contains(TOGETHER), () -> notFound.met().toString());
        assertEquals(TOGETHER.maximum(), one.offered(), "every value the figure lets, and no more");
    }

    @Test
    void aWalkOverMorePositionsThanTheFigureLetsStopsAtItAndSaysSo() {
        assertTrue(Math.pow(EACH, 5) > TOGETHER.maximum(), "five positions are past the figure");
        Walked five = walked(5);

        NumericWitness.Standing.NotFound notFound =
                assertInstanceOf(NumericWitness.Standing.NotFound.class, five.standing());
        assertTrue(notFound.met().figures().contains(TOGETHER), () -> "says the figure: "
                + notFound.met());
        assertTrue(five.offered() > 0 && five.offered() <= TOGETHER.maximum(),
                () -> "offers no more than it tries: " + five.offered());
    }

    @Test
    void aWalkOverFewerReachesTheEndOfEachPositionWithoutTheFigure() {
        assertTrue(EACH + EACH * EACH < TOGETHER.maximum(), "two positions are within it");
        Walked two = walked(2);

        NumericWitness.Standing.NotFound notFound =
                assertInstanceOf(NumericWitness.Standing.NotFound.class, two.standing());
        assertFalse(notFound.met().figures().contains(TOGETHER), () -> notFound.met().toString());
        assertEquals(EACH * EACH, two.offered(), "every value of each under every value of the other");
    }

    private static Quantities quantities(List<String> names) {
        StringBuilder parameters = new StringBuilder();
        for (String name : names) {
            parameters.append(parameters.isEmpty() ? "" : ", ").append(name).append(": Int");
        }
        Compilation compilation = ACompiledModel.answered("""
                module example.many

                data Ok = { v: Int }

                behavior f : (%s) -> Ok
                    constructs Ok

                let f (%s) = Ok { v = 1 }
                """.formatted(parameters, String.join(", ", names)));
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        return inputs.quantities(rules);
    }
}
