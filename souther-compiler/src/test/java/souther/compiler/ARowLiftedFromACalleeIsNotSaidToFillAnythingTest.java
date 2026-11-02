package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row lifted from a callee is offered to try an input. The block counts and marks the rows that
 * fill something and the rows that only try, and a block of the second kind alone does not say it
 * fills what nothing covers.
 */
class ARowLiftedFromACalleeIsNotSaidToFillAnythingTest {

    private static final String CALLEE = """
            module m

            data N = Int
                invariant value >= 0 && value <= 9

            behavior p : (n: N) -> Int

            let p (n) = n.value * 2

            example p
                | (N(0)) -> 0
                | (N(9)) -> 18
                | (N(3)) -> 6
                | (N(7)) -> 14

            """;

    private static final String SATISFIED = CALLEE + """
            behavior q : (xs: List<N>) -> Int

            let q (xs) = List.fold((acc, n) -> acc + p(n), 0, xs)

            example q
                | ([]) -> 0
                | ([N(1), N(2)]) -> 6
            """;

    private static final String WITH_A_GAP = CALLEE + """
            behavior q : (xs: List<N>) -> Int

            let q (xs) = List.fold((acc, n) -> acc + p(n), 0, xs)

            example q
                | ([N(1), N(2)]) -> 6
            """;

    @Test
    void rowsThatFillNothingAreSuggestionsAndSaySo() {
        Offered offered = offeredFor(SATISFIED);
        Offering offering = offered.offering();
        assertEquals(offering.count(), offering.suggestionCount());
        String text = offered.text();
        assertFalse(text.contains("to fill what nothing covers"), text);
        assertTrue(text.contains("4 optional rows"), text);
        assertEquals(4, text.lines()
                .filter(line -> line.equals("// suggested input; no uncovered obligation"))
                .count(), text);
    }

    @Test
    void rowsThatFillSomethingAreCountedApartFromTheSuggestions() {
        Offered offered = offeredFor(WITH_A_GAP);
        Offering offering = offered.offering();
        String text = offered.text();
        assertTrue(offering.suggestionCount() < offering.count(),
                "a row is proposed for the empty list: " + text);
        int owed = offering.count() - offering.suggestionCount();
        assertTrue(text.contains("// " + owed + (owed == 1 ? " row" : " rows")
                + " to fill what nothing covers."), text);
        assertEquals(offering.suggestionCount(), text.lines()
                .filter(line -> line.equals("// suggested input; no uncovered obligation"))
                .count(), text);
    }

    /** What is offered for a model, with the block written from it. */
    private record Offered(Offering offering, String text) {
    }

    private static Offered offeredFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList());
        Offering offering = Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m"));
        return new Offered(offering, GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text());
    }
}
