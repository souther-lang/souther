package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container a row is asked to hold so many of, where the way to the line narrows its elements to
 * one case, holds that many elements of the case.
 *
 * <p>Inside {@code List.filter(o -> isReview(o) && ..., opps)} the lookup reads the account of an
 * element of {@code Review}, and the map is composed after the list, holding an entry for that
 * account or none. Asked only that the list hold one, the list was written whole as one element of
 * whichever case comes first, and there was no account of a {@code Review} to file the entry
 * under. The control is the same model with {@code Review} declared first.
 */
class AContainerAskedHowManyItHoldsIsBuiltUnderTheCaseItsElementsAreTest {

    private static String model(String cases) {
        return """
                module p
                data Common = { accountId: String, amount: Int }
                data Review = { ...Common, floor: Int }
                data Closing = { ...Common }
                data Prospect = { ...Common }
                data Opp = %s
                let isReview (o: Opp): Bool =
                    match o with
                        | Review -> true
                        | Closing -> false
                        | Prospect -> false
                behavior f : (opps: List<Opp>, m: Map<String, Int>, after: Int) -> Int
                let f (opps, m, after) = List.length(List.filter(o -> isReview(o)
                    && Option.withDefault(0, Map.get(o.accountId, m)) >= after, opps))
                """.formatted(cases);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Every point is offered a row, whichever case is declared first, and every row offered for
     *  a line read under the narrowing holds a {@code Review}. */
    @Test
    void everyPointIsOfferedARowOfTheCaseTheWayNarrowsTo() {
        for (String cases : List.of("Prospect | Closing | Review", "Review | Closing | Prospect")) {
            Compilation compilation = measured(model(cases));
            Generator.GenerationResult offered = OfferedAtTheLines.of(compilation, "p", "f");

            assertEquals(List.of(), offered.unresolved(), () -> report(compilation));
            assertFalse(report(compilation).contains("nothing could show a row can be written"),
                    () -> report(compilation));
            for (Generator.GeneratedRow row : offered.rows()) {
                String opps = row.inputs().getFirst().text();
                assertTrue(opps.contains("Review {"), opps);
            }
        }
    }

    /**
     * A container asked for what its elements add up to is written as the elements adding up to
     * it, which a count of them alone would lose: only a container asked for how many it holds and
     * nothing else is asked for that many instead of the value.
     */
    @Test
    void aContainerAskedForWhatItsElementsAddUpToKeepsThem() {
        Compilation compilation = measured("""
                module p
                data Common = { accountId: String, amount: Int }
                data Review = { ...Common, floor: Int }
                data Closing = { ...Common }
                data Prospect = { ...Common }
                data Opp = Prospect | Closing | Review
                let isReview (o: Opp): Bool =
                    match o with
                        | Review -> true
                        | Closing -> false
                        | Prospect -> false
                behavior f : (opps: List<Opp>, m: Map<String, Int>, after: Int) -> Int
                let f (opps, m, after) = {
                    guard List.sum(List.map(o -> o.amount, opps)) >= 10 else 0
                    List.length(List.filter(o -> isReview(o)
                        && Option.withDefault(0, Map.get(o.accountId, m)) >= after, opps))
                }
                """);

        String report = report(compilation);
        assertFalse(report.contains("nothing could show a row can be written"), report);
    }
}
