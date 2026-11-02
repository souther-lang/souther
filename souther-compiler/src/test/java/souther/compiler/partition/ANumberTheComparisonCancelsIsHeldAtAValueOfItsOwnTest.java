package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number the comparison cancels out of the form is still worked out by the program, and a row
 * that holds it large stops there. The relation is shown to reach every value of its sides where
 * the cancelled number can be held at a value of its own, one the declarations leave it nearest
 * nought, and a row is built at it.
 *
 * <p>In {@code base + commuting >= commuting + social} the relation is {@code base >= social}
 * and {@code commuting} is no side of it, but {@code base + commuting} and
 * {@code commuting + social} are worked out all the same.
 */
class ANumberTheComparisonCancelsIsHeldAtAValueOfItsOwnTest {

    private static Compilation measured(String commutingRule, String comparison) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Yen = Int
                    invariant value >= 0

                data M = { base: Yen, commuting: Yen, other: Yen }
                    invariant base.value >= 0
                    %s

                behavior f : (m: M, social: Int) -> Bool
                let f (m, social) = %s
                """.formatted(commutingRule, comparison), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static final String CANCELLED =
            "m.base.value + m.commuting.value >= m.commuting.value + social";

    private static boolean notShown(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE))
                .contains("relation_not_shown_to_reach_every_value");
    }

    private static String offered(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
    }

    @Test
    void theRelationIsShownWhereTheCancelledNumberIsHeldAtNought() {
        Compilation compilation = measured("invariant commuting.value >= 0", CANCELLED);

        assertFalse(notShown(compilation), () -> offered(compilation));
    }

    @Test
    void theRelationIsShownWhereTheCancelledNumberCannotBeNought() {
        Compilation compilation = measured("invariant commuting.value >= 5", CANCELLED);

        assertFalse(notShown(compilation), () -> offered(compilation));
        assertTrue(offered(compilation).contains("commuting = Yen(5)"), () -> offered(compilation));
        assertFalse(offered(compilation).contains("commuting = Yen(0)"),
                () -> offered(compilation));
    }

    @Test
    void aRowIsBuiltOnEachSideOfTheLineAtTheHeldValue() {
        Compilation compilation = measured("invariant commuting.value >= 5", CANCELLED);
        String rows = offered(compilation);

        assertTrue(rows.contains("base = Yen(1), commuting = Yen(5)") && rows.contains(", 0)"),
                () -> "a row where the relation holds: " + rows);
        assertTrue(rows.contains("base = Yen(0), commuting = Yen(5)") && rows.contains(", 2)"),
                () -> "a row where it fails: " + rows);
    }

    @Test
    void aNumberTiedToASideByARuleIsNotHeldApart() {
        Compilation compilation = measured("invariant commuting.value == base.value", CANCELLED);

        assertTrue(notShown(compilation), () -> offered(compilation));
    }

    @Test
    void aNumberTheDeclarationsLeaveNoValueNearNoughtIsNotHeldWhereTheOperationsStop() {
        Compilation compilation = measured(
                "invariant commuting.value >= 9223372036854775807", CANCELLED);

        assertTrue(notShown(compilation), () -> offered(compilation));
    }
}
