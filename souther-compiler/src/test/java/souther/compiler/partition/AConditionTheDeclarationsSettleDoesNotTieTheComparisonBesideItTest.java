package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison that every row the declarations leave meets keeps no row off the comparison after
 * it, so the one after it is read as it is read alone.
 *
 * <p>{@code eaches >= 0} and {@code pack >= 1} make {@code eaches + pack > 0} true wherever the
 * declarations hold. Kept as a statement of the way to {@code eaches < pack}, it tied the two
 * numbers to one another and no value of either was shown to be reached whatever the other held.
 *
 * <p>Read is what the report's {@code notRead} says of every place: that the rule relates two
 * values and divides none, which asks nothing of the model, and no more.
 */
class AConditionTheDeclarationsSettleDoesNotTieTheComparisonBesideItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();
    private static final String READ = "rule_relating_two_values";
    private static final String NOT_SHOWN_TO_REACH = "relation_not_shown_to_reach_every_value";
    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";
    private static final String BOUND = "    invariant value <= 1000";

    @Test
    void aSumTheDeclarationsKeepAboveNoughtLeavesTheComparisonAfterItRead() {
        JsonNode report = reportOf(BOUND,
                "eaches.value + pack.value > 0 && eaches.value < pack.value", "0", "24");
        assertEquals(List.of(READ), reasonsNotRead(report), report::toString);
        assertEquals(List.of(), stopsOf(report), report::toString);
    }

    /**
     * The condition comes from a division here. Every reason said is a fact about the model, the
     * words of a rule that was read to the end, and none is a shortfall of the compiler's.
     */
    @Test
    void aQuotientRoundedTowardNoughtAndHeldAtNoughtIsRead() {
        JsonNode report = reportOf("",
                "Rational.toInt(DOWN, eaches.value / pack.value) == 0", "0", "24");
        assertEquals(List.of("rule_cuts_outside_what_the_quantity_holds",
                "rule_never_turns_on_this_line", READ), reasonsNotRead(report), report::toString);
    }

    /**
     * What the sum may stop a run at is said where the sum is. The values at which it stops are
     * not reached, and that is what the place after it is not shown for: no relation is blamed.
     */
    @Test
    void whereTheSumMayStopARunTheStopIsKeptAndTheRelationIsNotBlamedForIt() {
        JsonNode report = reportOf("",
                "eaches.value + pack.value > 0 && eaches.value < pack.value", "0", "24");
        assertEquals(List.of("eaches + pack at least 9223372036854775808"), stopsOf(report),
                report::toString);
        List<String> reasons = reasonsNotRead(report);
        assertTrue(reasons.contains(NOT_SHOWN_REACHED), report::toString);
        assertFalse(reasons.contains(NOT_SHOWN_TO_REACH), report::toString);
    }

    /**
     * {@code eaches >= pack} keeps rows off {@code eaches < 2 * pack}, so it is a statement of the
     * way and ties the two: the comparison after it is read alone as {@code eaches < 2 * pack} is,
     * which would say of every value of {@code eaches} what only some rows hold.
     */
    @Test
    void aConditionTheDeclarationsDoNotSettleStillTiesTheComparisonAfterIt() {
        JsonNode report = reportOf("",
                "eaches.value >= pack.value && eaches.value < 2 * pack.value", "12", "0");
        assertTrue(reasonsNotRead(report).contains(NOT_SHOWN_TO_REACH), report::toString);
    }

    /** The reasons of the places not read, each as many times as it is said. */
    private static List<String> reasonsNotRead(JsonNode report) {
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.get("modules").get(0).get("behaviors").get(0)
                .get("partition").get("notRead")) {
            out.add(each.get("reason").asString());
        }
        return out.stream().distinct().sorted().toList();
    }

    /** What every run stops in, as {@code operation at least number}, wherever the report says. */
    private static List<String> stopsOf(JsonNode report) {
        List<String> out = new ArrayList<>();
        for (JsonNode every : report.findValues("everyRunStops")) {
            for (JsonNode stop : every) {
                for (JsonNode where : stop.get("where")) {
                    out.add(stop.get("operation").asString() + " at least "
                            + where.get("least").asString());
                }
            }
        }
        return out;
    }

    /**
     * The adequacy report of a behavior that guards on {@code guard}, over numbers each held by
     * {@code bound} as well as by what they declare. The examples take each side of the guard, at
     * {@code whole} and {@code part} eaches of a pack of twelve.
     */
    private static JsonNode reportOf(String bound, String guard, String whole, String part) {
        Compilation compilation = Compilation.ofSource("""
                module m1

                data Eaches = Int
                    invariant value >= 0
                %1$s
                data PackSize = Int
                    invariant value >= 1
                %1$s
                data Whole = { n: Int }
                data Part = { left: Int }

                behavior split : (eaches: Eaches, pack: PackSize) -> Whole | Part

                let split (eaches, pack) = {
                    guard %2$s else Part { left = 1 }
                    Whole { n = 1 }
                }

                example split
                    | "a" : (Eaches(%3$s), PackSize(12)) -> Whole { n = 1 }
                    | "b" : (Eaches(%4$s), PackSize(12)) -> Part { left = 1 }
                """.formatted(bound, guard, whole, part), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }
}
