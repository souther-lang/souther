package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.rule;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

/**
 * A basis is made from the basis of the rules before only where the rules before were closed as the
 * rules now are: with the same spacing of every position they weigh, and walked in the same order.
 *
 * <p>The rules being the very ones is not that. What a basis is rests on every position of its
 * rules being whole-numbered and on the places of the first prefix, which the order sorts; the
 * rules added say nothing of either for the positions they do not name, so a spacing or an order
 * that changed for those is a closure that is made over again.
 */
class AClosureMadeFromTheClosureBeforeIsMadeUnderTheSameSpacingAndOrderTest {

    private static final Function<String, Granularity> WHOLE = _ -> Granularity.DISCRETE;

    /** {@code a} fills, the others are whole. */
    private static Granularity aFills(String position) {
        return position.equals("a") ? Granularity.DENSE : Granularity.DISCRETE;
    }

    private static List<AffineConstraint<String>> read(List<Written> written,
                                                       Function<String, Granularity> spacing) {
        return RulesAsWritten.statedOnly(written, spacing);
    }

    private static List<Written> aChainOver(String... atoms) {
        List<Written> out = new ArrayList<>();
        for (String atom : atoms) {
            out.add(rule(atom + " >= 0"));
            out.add(rule(atom + " <= 9"));
        }
        out.add(rule(atoms[0] + " + " + atoms[1] + " <= 10"));
        out.add(rule(atoms[0] + " + " + atoms[1] + " + " + atoms[2] + " <= 12"));
        return out;
    }

    private static PrefixBasis.Highest sumOf(ClosedState<String> state, String... atoms) {
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        for (String atom : atoms) {
            sum.put(atom, ExactRatio.ONE);
        }
        return state.highestInBasis(sum, ExactRatio.ZERO);
    }

    @Test
    void aPositionThatFillsWhereItWasWholeIsAClosureMadeOverAgain() {
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        List<AffineConstraint<String>> before = read(aChainOver("a", "b", "c"), WHOLE);
        ClosedStates kept = ClosedStates.kept();
        ClosedStates.Parted<String> parent = kept.of(before, WHOLE::apply, order, null);
        assertTrue(sumOf(parent.state(), "a", "b") instanceof PrefixBasis.Highest.Within,
                "the rules before are closed in a basis, which is what follows from them");

        List<AffineConstraint<String>> after = new ArrayList<>(before);
        after.addAll(read(List.of(rule("b <= 5")), WHOLE));
        ClosedState<String> alone = ClosedState.closedTogether(after,
                AClosureMadeFromTheClosureBeforeIsMadeUnderTheSameSpacingAndOrderTest::aFills, order);
        ClosedState<String> followed = kept.of(after,
                AClosureMadeFromTheClosureBeforeIsMadeUnderTheSameSpacingAndOrderTest::aFills, order,
                parent).state();

        assertEquals(sumOf(alone, "a", "b").getClass(), sumOf(followed, "a", "b").getClass(),
                "a basis is chosen for the rules as they are spaced now, and not as they were");
        assertSame(PrefixBasis.Highest.NOT_ANSWERED, sumOf(followed, "a", "b"));
    }

    /** Rules that are no chain, closed by rounds, whose work the next closure is worked from. */
    @Test
    void theWorkOfTheRoundsIsNotTakenAcrossAChangeOfSpacingEither() {
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        List<Written> written = List.of(rule("2a - b >= 1"), rule("b - c <= 0"), rule("c <= 7"),
                rule("a >= -3"), rule("2a + 3b - c <= 9"), rule("b >= -4"));
        List<AffineConstraint<String>> before = read(written, WHOLE);
        ClosedStates kept = ClosedStates.kept();
        ClosedStates.Parted<String> parent = kept.of(before, WHOLE::apply, order, null);
        List<AffineConstraint<String>> after = new ArrayList<>(before);
        after.addAll(read(List.of(rule("c >= 2")), WHOLE));
        ClosedState<String> alone = ClosedState.closedTogether(after,
                AClosureMadeFromTheClosureBeforeIsMadeUnderTheSameSpacingAndOrderTest::aFills, order);
        ClosedState<String> followed = kept.of(after,
                AClosureMadeFromTheClosureBeforeIsMadeUnderTheSameSpacingAndOrderTest::aFills, order,
                parent).state();
        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(alone),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(followed));
    }

    @Test
    void anOrderThatPutsThePositionsElsewhereIsAClosureMadeOverAgain() {
        CanonicalOrder<String> spelled = CanonicalOrder.asTheyAreSpelled();
        CanonicalOrder<String> reversed = (one, other) -> other.compareTo(one);
        List<AffineConstraint<String>> before = read(aChainOver("a", "b", "c"), WHOLE);
        ClosedStates kept = ClosedStates.kept();
        ClosedStates.Parted<String> parent = kept.of(before, WHOLE::apply, spelled, null);

        List<AffineConstraint<String>> after = new ArrayList<>(before);
        after.addAll(read(List.of(rule("c <= 5")), WHOLE));
        ClosedState<String> alone = ClosedState.closedTogether(after, WHOLE::apply, reversed);
        ClosedState<String> followed = kept.of(after, WHOLE::apply, reversed, parent).state();

        for (String[] atoms : new String[][] {{"a"}, {"b"}, {"c"}, {"a", "b"}, {"b", "c"},
                {"a", "b", "c"}}) {
            assertEquals(sumOf(alone, atoms), sumOf(followed, atoms),
                    "what is left of " + String.join(" + ", atoms) + " is not what the order makes it");
        }
        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(alone),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(followed));
    }
}
