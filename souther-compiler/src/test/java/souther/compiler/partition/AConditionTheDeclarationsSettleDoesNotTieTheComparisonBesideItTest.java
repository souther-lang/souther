package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison that every row the declarations leave meets keeps no row off the comparison after
 * it, so the one after it is read as it is read alone.
 *
 * <p>{@code eaches >= 0} and {@code pack >= 1} make {@code eaches + pack > 0} true wherever the
 * declarations hold. Kept as a statement of the way to {@code eaches < pack}, it tied the two
 * numbers to one another and no value of either was shown to be reached whatever the other held.
 */
class AConditionTheDeclarationsSettleDoesNotTieTheComparisonBesideItTest {

    private static final String NOT_SHOWN_TO_REACH =
            "relates the value here to another value not shown to reach every value here";
    private static final String MAY_STOP = "may stop a run";

    @Test
    void aSumTheDeclarationsKeepAboveNoughtLeavesTheComparisonAfterItRead() {
        String report = reportOf("PackSize", "    invariant value <= 1000",
                "eaches.value + pack.value > 0 && eaches.value < pack.value", "0", "24");
        assertFalse(report.contains(NOT_SHOWN_TO_REACH), report);
        assertFalse(report.contains(MAY_STOP), report);
    }

    /** The same two lines, met through a quotient: the condition comes from a division. */
    @Test
    void aQuotientRoundedTowardNoughtAndHeldAtNoughtIsRead() {
        String report = reportOf("PackSize", "",
                "Rational.toInt(DOWN, eaches.value / pack.value) == 0", "0", "24");
        assertFalse(report.contains(NOT_SHOWN_TO_REACH), report);
    }

    /**
     * What the sum may stop a run at is said where the sum is, and is no part of what the
     * declarations settle: the values at which it stops are not reached.
     */
    @Test
    void whereTheSumMayStopARunTheStopIsSaidAndNoRelationIsBlamedForIt() {
        String report = reportOf("PackSize", "",
                "eaches.value + pack.value > 0 && eaches.value < pack.value", "0", "24");
        assertTrue(report.contains(MAY_STOP), report);
        assertFalse(report.contains(NOT_SHOWN_TO_REACH), report);
    }

    /** Nothing leaves the sum above nought here, so the comparison after it is still tied to it. */
    @Test
    void aSumTheDeclarationsDoNotKeepAboveNoughtStillTiesTheComparisonAfterIt() {
        String report = reportOf("Int", "", "eaches.value + pack > 0 && eaches.value < pack",
                "0", "24");
        assertTrue(report.contains(NOT_SHOWN_TO_REACH), report);
    }

    /**
     * The adequacy report of a behavior that guards on {@code guard}, over numbers each held by
     * {@code bound} as well as by what they declare.
     */
    private static String reportOf(String packType, String bound, String guard, String whole,
                                   String part) {
        String pack = packType.equals("Int") ? "12" : "PackSize(12)";
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

                behavior split : (eaches: Eaches, pack: %2$s) -> Whole | Part

                let split (eaches, pack) = {
                    guard %3$s else Part { left = 1 }
                    Whole { n = 1 }
                }

                example split
                    | "a" : (Eaches(%4$s), %6$s) -> Whole { n = 1 }
                    | "b" : (Eaches(%5$s), %6$s) -> Part { left = 1 }
                """.formatted(bound, packType, guard, whole, part, pack), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
