package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.CoverageOrigin;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which values reach one arm of a guard, which is not which side of the line its value belongs to.
 *
 * <p>A {@link Threshold} answers the second, and that is what decides where one class ends and the
 * next begins. It cannot answer the first: {@code x <= c} and {@code x > c} both put {@code c} on the
 * low side and their {@code then} arms are opposite halves of the line. So the arms are read off the
 * operator where it is still known, and a measure that recovered them from a threshold would have
 * counted the wrong arm.
 */
class AGuardsArmsAreNotItsThresholdTest {

    private static GuardThresholds.Guards read(String condition) {
        String source = """
                module example.guarded

                data Count = Int
                    invariant range = value >= 0 && value <= 10

                data Low
                data High

                behavior pick : (n: Count) -> Low | High
                    constructs Low, High

                let pick (n) =
                    if CONDITION
                        then High
                        else Low
                """.replace("CONDITION", condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + condition);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("pick")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("pick");
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies());
        return GuardThresholds.of("pick", body, plan,
                spec.params().stream().map(Hir.Param::name).toList(), symbols);
    }

    /** The arm taken when the condition holds, which the plan numbers first. */
    private static GuardEdge thenArm(GuardThresholds.Guards guards) {
        int site = guards.edges().get(0).guard().siteIndexThen();
        return guards.edges().stream().filter(e -> e.site() == site).findFirst().orElseThrow();
    }

    private static GuardEdge elseArm(GuardThresholds.Guards guards) {
        int site = guards.edges().get(0).guard().siteIndexElse();
        return guards.edges().stream().filter(e -> e.site() == site).findFirst().orElseThrow();
    }

    private static String shown(GuardEdge edge) {
        return (edge.low() == null ? "(-inf" : (edge.lowInclusive() ? "[" : "(") + edge.low())
                + ", " + (edge.high() == null ? "+inf)"
                        : edge.high() + (edge.highInclusive() ? "]" : ")"));
    }

    @Test
    void thereAreTwoArmsAndBothAreRead() {
        GuardThresholds.Guards guards = read("n.value <= 5");

        assertEquals(1, guards.thresholds().size(), () -> "one line: " + guards.thresholds());
        assertEquals(2, guards.edges().size(), () -> "and two arms of it: " + guards.edges());
        assertEquals("n", thenArm(guards).path().toString());
    }

    /**
     * The finding this test exists for.
     *
     * <p>Both operators put 5 on the low side, so a threshold cannot tell them apart. Their arms are
     * the two halves of the line the other way round, and anything reading the arms off
     * {@code valueBelongsBelow} would have taken one for the other.
     */
    @Test
    void twoOperatorsAgreeAboutTheValueAndTakeOppositeArms() {
        GuardThresholds.Guards atOrBelow = read("n.value <= 5");
        GuardThresholds.Guards above = read("n.value > 5");

        assertTrue(atOrBelow.thresholds().get(0).valueBelongsBelow(),
                "`x <= 5` puts 5 on the low side");
        assertTrue(above.thresholds().get(0).valueBelongsBelow(),
                "and so does `x > 5`");

        assertEquals("(-inf, 5]", shown(thenArm(atOrBelow)));
        assertEquals("(5, +inf)", shown(thenArm(above)));
        assertEquals(shown(thenArm(atOrBelow)), shown(elseArm(above)),
                "the arms are the same two halves, swapped");
        assertEquals(shown(thenArm(above)), shown(elseArm(atOrBelow)));
    }

    @Test
    void theOtherTwoOperatorsPutTheValueHighAndAlsoTakeOppositeArms() {
        GuardThresholds.Guards below = read("n.value < 5");
        GuardThresholds.Guards atOrAbove = read("n.value >= 5");

        assertFalse(below.thresholds().get(0).valueBelongsBelow(),
                "`x < 5` puts 5 on the high side");
        assertFalse(atOrAbove.thresholds().get(0).valueBelongsBelow(),
                "and so does `x >= 5`");

        assertEquals("(-inf, 5)", shown(thenArm(below)));
        assertEquals("[5, +inf)", shown(thenArm(atOrAbove)));
        assertEquals(shown(thenArm(below)), shown(elseArm(atOrAbove)));
        assertEquals(shown(thenArm(atOrAbove)), shown(elseArm(below)));
    }

    /** A comparison written the other way round says what the first one says, arms included. */
    @Test
    void aMirroredComparisonHasTheSameArms() {
        assertEquals(shown(thenArm(read("n.value <= 5"))), shown(thenArm(read("5 >= n.value"))));
        assertEquals(shown(elseArm(read("n.value <= 5"))), shown(elseArm(read("5 >= n.value"))));
    }

    // --- what the bounds prove about an arm --------------------------------------------------------

    private static final CoverageSites.GuardRef ONE_GUARD =
            new CoverageSites.GuardRef("pick", CoverageOrigin.written("t", 0), 0, 1, null);

    private static GuardEdge above(long value, boolean inclusive) {
        return GuardEdge.above(ONE_GUARD, 0, new NumericTerm.ValueOf(TermPath.of("n")),
                Count.of(value), inclusive);
    }

    private static GuardEdge below(long value, boolean inclusive) {
        return GuardEdge.below(ONE_GUARD, 1, new NumericTerm.ValueOf(TermPath.of("n")),
                Count.of(value), inclusive);
    }

    private static NumericDomain.Bounds holds(Long min, Long max) {
        return new NumericDomain.Bounds(
                min == null ? null : Endpoint.inclusive(Count.of(min)),
                max == null ? null : Endpoint.inclusive(Count.of(max)));
    }

    @Test
    void anArmBeyondWhatThePositionHoldsIsProvenUnreachable() {
        assertTrue(above(50, true).provenDisjoint(holds(0L, 10L)),
                "nothing at or above 50 is a value of [0, 10]");
        assertTrue(below(-1, true).provenDisjoint(holds(0L, 10L)));
    }

    @Test
    void anArmThatMeetsThemIsNotProven() {
        assertFalse(above(10, true).provenDisjoint(holds(0L, 10L)),
                "10 is a value of [0, 10], so this arm is not ruled out");
        assertFalse(above(5, true).provenDisjoint(holds(0L, 10L)));
        assertFalse(below(0, true).provenDisjoint(holds(0L, 10L)));
    }

    /** The edge that touches the end without including it. Read as closed it would be called
     * reachable, and the arm behind it would stay in a denominator nothing can fill. */
    @Test
    void anArmOpenAtTheEndItTouchesIsProvenUnreachable() {
        assertTrue(above(10, false).provenDisjoint(holds(0L, 10L)),
                "there is no value of [0, 10] above 10");
        assertTrue(below(0, false).provenDisjoint(holds(0L, 10L)));
    }

    /**
     * The position's own end is open at the value the arm starts at.
     *
     * <p>Two half-lines meeting at one number share it only where both hold it, and either side can
     * be the one that does not. A rule that reaches an end without including it — `low < high` over
     * decimals leaves `low` short of the top of its type — leaves the arm at that number nothing to
     * be taken by, however the arm itself is written.
     */
    @Test
    void anArmAtAnEndThePositionDoesNotReachIsProvenUnreachable() {
        NumericDomain.Bounds under = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(BigDecimal.ZERO)), Endpoint.exclusive(Count.of(BigDecimal.TEN)));
        NumericDomain.Bounds over = new NumericDomain.Bounds(
                Endpoint.exclusive(Count.of(BigDecimal.ZERO)), Endpoint.inclusive(Count.of(BigDecimal.TEN)));

        assertTrue(above(10, true).provenDisjoint(under), "no value of [0, 10) is 10 or above");
        assertTrue(below(0, true).provenDisjoint(over), "and none of (0, 10] is 0 or below");
        assertFalse(above(10, true).provenDisjoint(over), "10 is a value of (0, 10]");
        assertFalse(below(0, true).provenDisjoint(under), "and 0 is one of [0, 10)");
    }

    /** Nothing is proven where nothing is known. An unbounded position rules out no arm, and neither
     * does a position nobody bounded in the direction the arm goes. */
    @Test
    void nothingIsProvenWhereThePositionIsUnbounded() {
        assertFalse(above(50, true).provenDisjoint(null));
        assertFalse(above(50, true).provenDisjoint(holds(0L, null)));
        assertFalse(below(-1, true).provenDisjoint(holds(null, 10L)));
    }

    @Test
    void reachabilityNamesTheArmsItProvesAndNoOthers() {
        List<GuardEdge> edges = List.of(above(50, true), below(50, false));
        GuardReachability reach = GuardReachability.of(edges,
                Map.of(new NumericTerm.ValueOf(TermPath.of("n")), holds(0L, 10L)));

        assertTrue(reach.provenUnreachable(0), "the arm above 50 is unreachable");
        assertFalse(reach.provenUnreachable(1), "the arm below it is the whole of the range");
        assertEquals(java.util.Set.of(0), reach.unreachableSites());
    }

    @Test
    void aPositionWithNoBoundsProvesNothingAboutEitherArm() {
        GuardReachability reach = GuardReachability.of(
                List.of(above(50, true), below(50, false)), Map.of());

        assertTrue(reach.isEmpty(), () -> "proved " + reach.unreachableSites());
    }
}
