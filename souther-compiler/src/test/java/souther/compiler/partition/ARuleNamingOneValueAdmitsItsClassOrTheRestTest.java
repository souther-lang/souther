package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.Factor;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.Outcome;
import souther.compiler.reading.WayIn;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A decision on a rule that names one value admits that value's class, or every class but it.
 *
 * <p>An equality has no side its values are true on, so the decision is not placed the way a cut
 * is. What it tells apart is the value from the rest, and the axis says so with a class holding the
 * value and nothing else: the decision admits that class where it wants the rule to hold at the
 * value, and the others where it wants it not to. An equality held and an inequality broken both
 * want the first.
 *
 * <p>Only where the class is that one value. Where the value sits inside a class with others, the
 * rule cuts through the class, and no set of classes is what the decision admits.
 */
class ARuleNamingOneValueAdmitsItsClassOrTheRestTest {

    @Test
    void anEqualityHeldAdmitsTheValueAndBrokenAdmitsTheRest() {
        assertEquals(Map.of(true, List.of("= 3"), false, List.of("/= 3")),
                admittedOn("x == 3"));
    }

    @Test
    void anInequalityHeldAdmitsTheRestAndBrokenAdmitsTheValue() {
        assertEquals(Map.of(true, List.of("/= 3"), false, List.of("= 3")),
                admittedOn("x /= 3"));
    }

    /**
     * A value singled out beside a line is a class of its own, and the decision admits it or the
     * rest as it does where equalities alone divide the position.
     *
     * <p>The cut at ten makes the runs, and three is taken out of the one below it: the classes
     * are three, the run below ten without it, and the run from ten up. The rest is both of the
     * others, because the rule naming three holds at none of their values.
     */
    @Test
    void aValueBesideALineIsAClassTheDecisionAdmits() {
        assertEquals(Map.of(true, List.of("= 3"),
                        false, List.of("x < 10 and x /= 3", "10 <= x")),
                admittedOn("x == 3 || x >= 10"));
    }

    /** What a way that placed no cell is written as, apart from a cell admitting no class. */
    private static final List<String> PLACED_NOTHING = List.of("(placed nothing)");

    /** What each way of the rule naming one value admits on {@code x}'s axis, under
     *  {@code guard}. */
    private static Map<Boolean, List<String>> admittedOn(String guard) {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Low
                data High

                behavior pick : (x: Int) -> Low | High
                let pick (x) = if %s then High else Low
                """.formatted(guard), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        CoverageRead.Read read =
                compilation.db().ask(new Adequacy.Meets("probe")).value().get("pick");
        MeasuredInput.MeasuredAxes measured = MeasuredInput.of("pick",
                compilation.db().ask(new Adequacy.Inputs("probe")).value().get("pick")
                        .reading(RuleReadings.of(compilation, "probe")),
                compilation.db().ask(new Adequacy.Divided("probe", "pick")).value()).axes();
        List<Axis> axes = measured.axes();
        assertNotNull(read, () -> "the model compiles: " + compilation.errors());
        Map<Boolean, List<String>> out = new LinkedHashMap<>();
        for (souther.compiler.reading.Condition.Side side : sides(read)) {
            int axis = axisOf(axes, side);
            if (!namesOneValue(side, axes.get(axis))) {
                continue;
            }
            InteractionCells.Cell cell = InteractionCells.admittedBy(side, measured);
            if (cell == null) {
                out.put(side.held(), PLACED_NOTHING);
                continue;
            }
            List<String> classes = new ArrayList<>();
            for (int c = 0; c < axes.get(axis).classes().size(); c++) {
                if (cell.allowed()[axis][c]) {
                    classes.add(axes.get(axis).classes().get(c).label());
                }
            }
            out.put(side.held(), classes);
        }
        return out;
    }

    /** Whether {@code side} is a way out of a rule that drew a line on {@code axis} naming one
     *  value, asked of the line and not of how the rule was spelled. */
    private static boolean namesOneValue(souther.compiler.reading.Condition.Side side, Axis axis) {
        ModelOccurrence states = ModelOccurrence.statedAt(side.statedAt()).orElse(null);
        for (Cut cut : axis.cuts()) {
            for (LineOrigin origin : cut.origins()) {
                if (origin instanceof LineOrigin.ComparisonOrigin guard
                        && guard.read().states().equals(states)
                        && guard.facts().claim() instanceof ComparisonClaim.Singled) {
                    return true;
                }
            }
        }
        return false;
    }

    private static int axisOf(List<Axis> axes, souther.compiler.reading.Condition.Side side) {
        for (int i = 0; i < axes.size(); i++) {
            if (axes.get(i).term().equals(side.at())) {
                return i;
            }
        }
        throw new AssertionError("no axis measures " + side.at());
    }

    /** Every decision on a comparison the read holds, on the ways into the body and where values
     *  meet. */
    private static List<souther.compiler.reading.Condition.Side> sides(CoverageRead.Read read) {
        List<souther.compiler.reading.Condition.Side> out = new ArrayList<>();
        for (WayIn way : read.taken()) {
            way.decisions().forEach(decision -> sideOf(decision, out));
        }
        for (Interaction each : read.interactions()) {
            each.reach().forEach(decision -> sideOf(decision, out));
            for (Factor factor : each.factors()) {
                for (Outcome outcome : factor.outcomes()) {
                    outcome.holds().forEach(decision -> sideOf(decision, out));
                }
            }
        }
        return out;
    }

    private static void sideOf(Decision decision,
                               List<souther.compiler.reading.Condition.Side> out) {
        if (decision.constrains() instanceof souther.compiler.reading.Condition.Side side
                && !out.contains(side)) {
            out.add(side);
        }
    }
}
