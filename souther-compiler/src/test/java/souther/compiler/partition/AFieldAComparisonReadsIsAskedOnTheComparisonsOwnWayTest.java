package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A closure making a record of each element works out every field of it on every application,
 * and a comparison reading one field is reached past what the others work out. So whether that
 * comparison is read is what its own field and the run to it say, and not which fields another
 * comparison of the same body reads: {@code nominal}, a date moved past the end of the calendar
 * for some {@code from}, keeps the comparison of {@code landed} from being shown reached at every
 * value whether or not {@code nominal} is compared too.
 */
class AFieldAComparisonReadsIsAskedOnTheComparisonsOwnWayTest {

    private static final String READ = "it relates the value here to another value rather than"
            + " dividing the values here";

    @Test
    void aFieldTheComparisonDoesNotReadStopsTheRunAlikeWhereverElseItIsRead() {
        assertEquals(List.of(READ), saidOfTheComparisonOfLanded("from", "v.landed == d"));
        String moved = "Date.addDays(n, from)";
        List<String> alone = saidOfTheComparisonOfLanded(moved, "v.landed == d");
        assertFalse(alone.contains(READ), alone::toString);
        assertEquals(alone, saidOfTheComparisonOfLanded(moved, "v.landed == d || v.nominal == d"));
    }

    /** What the report says of {@code from} at the comparison of {@code landed}, which is the
     *  first one the closure writes. */
    private static List<String> saidOfTheComparisonOfLanded(String nominal, String compared) {
        String model = """
                module probe

                data V = { landed: Date, nominal: Date }

                behavior f : (from: Date, d: Date, days: Int) -> Bool
                let f (from, d, days) =
                    List.rangeInclusive(0, days)
                        |> List.map(n -> V { landed = from, nominal = %s })
                        |> List.any(v -> %s)
                """.formatted(nominal, compared);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("comparison@9:35") && line.endsWith("about `from`"))
                .map(line -> line.substring(line.indexOf("— ") + 2, line.lastIndexOf(", about")))
                .toList();
    }
}
