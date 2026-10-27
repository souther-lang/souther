package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A weight is a fault of the computation, which every threshold of its table reads, so a value cut
 * at several places owes it once and not again beside each threshold.
 */
class AWeightOfADerivedValueCutAtSeveralPlacesIsOwedOnceTest {

    private static final String SIX_ROWS = """
            module example.it
            data Row = { grade: Int, lowerBound: Int }
            data Yen = Int
                invariant value >= 0
            data Rem = { base: Yen, extra: Yen }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)
            behavior g : (r: Rem) -> Int
            let g (r) = gradeOf(r.base.value + r.extra.value)
            example g
                | "ON 100 in base"   : (Rem { base = Yen(100), extra = Yen(0) }) -> 2
                | "OFF 100 in base"  : (Rem { base = Yen(99), extra = Yen(0) }) -> 1
                | "IN in base"       : (Rem { base = Yen(150), extra = Yen(0) }) -> 2
                | "OUT in base"      : (Rem { base = Yen(50), extra = Yen(0) }) -> 1
                | "ON 200 in extra"  : (Rem { base = Yen(0), extra = Yen(200) }) -> 3
                | "OFF 200 in extra" : (Rem { base = Yen(0), extra = Yen(199) }) -> 2
            """;

    @Test
    void aBorderIsNotHeldAgainstALineThatOnlyWeighsAPositionDifferently() {
        String report = reportOf(SIX_ROWS);
        assertFalse(report.contains("no row tells"), report);
    }

    /** The weights stay owed to the computation, so a position no row weighs is still said. */
    @Test
    void aWeightNoRowFixesIsStillOwedAndSaidOnce() {
        String report = reportOf(SIX_ROWS.replace("""
                    | "ON 200 in extra"  : (Rem { base = Yen(0), extra = Yen(200) }) -> 3
                    | "OFF 200 in extra" : (Rem { base = Yen(0), extra = Yen(199) }) -> 2
                """, ""));
        assertTrue(report.contains("no row fixes how `r.extra` weighs"), report);
        assertFalse(report.contains("no row tells"), report);
    }

    /** A value cut at one place has no computation shared by thresholds, so its border keeps the
     *  lines beside it. */
    @Test
    void aValueCutAtOnePlaceKeepsTheLinesBesideItsBorder() {
        String report = reportOf(SIX_ROWS
                .replace("""
                                         Row { grade = 3, lowerBound = 200 } ]""", " ]")
                .replace("Row { grade = 2, lowerBound = 100 },", "Row { grade = 2, lowerBound = 100 }")
                .replaceAll("(?m)^ *\\| \"(ON|OFF) 200.*\\n", ""));
        assertTrue(report.contains("no row tells"), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
