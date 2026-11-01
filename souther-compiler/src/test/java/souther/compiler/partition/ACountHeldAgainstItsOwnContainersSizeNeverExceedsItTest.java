package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many elements of a container meet a statement, less how many the container holds, is never
 * above nought, so a point of the border above it is excluded and not left to a search.
 *
 * <p>The count is of elements the container holds, and the size taken from it is that container's
 * own. Taken from another container's size, nothing bounds the difference above, and the points
 * there stay owed.
 */
class ACountHeldAgainstItsOwnContainersSizeNeverExceedsItTest {

    private static String model(String against) {
        return """
                module probe.count exposing ( check, Deal, Code, Table, Ok, Short )

                data Code = String
                    invariant String.matches("[A-Z]{3}", value)

                data Deal = { currency: Code }

                data Table = { rates: Map<Code, Int> }

                data Ok
                data Short

                behavior check : (deals: List<Deal>, others: List<Deal>, table: Table) -> Ok | Short

                let check (deals, others, table) = {
                    let priced = List.filterMap(d -> Map.get(d.currency, table.rates), deals)
                    if List.length(priced) == List.length(%s) then Ok else Short
                }

                let usd = Deal { currency = Code("USD") }
                let eur = Deal { currency = Code("EUR") }
                let known = Table { rates = Map.fromList([ (Code("USD"), 1) ]) }

                example check
                    | "all priced" : ([ usd ], [ usd ], known) -> Ok
                    | "none" : ([ ], [ ], known) -> Ok
                    | "one missing" : ([ usd, eur ], [ usd, eur ], known) -> Short
                """.formatted(against);
    }

    @Test
    void aCountLessItsOwnContainersSizeOwesNoPointAboveTheLine() {
        String said = report(model("deals"));

        assertTrue(said.contains("no OFF point above the line is owed at #deals"), said);
        assertTrue(said.contains("no OUT point above the line is owed at #deals"), said);
        assertFalse(said.contains("nothing could show a row can be written at the OFF point"),
                said);
        assertFalse(said.contains("nothing could show a row can be written at the OUT point"),
                said);
    }

    @Test
    void aCountLessAnotherContainersSizeStillOwesThem() {
        String said = report(model("others"));

        assertFalse(said.contains("above the line is owed"), said);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
