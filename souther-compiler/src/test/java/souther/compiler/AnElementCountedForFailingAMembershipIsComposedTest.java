package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A guard over how many elements of a container fail to be a key of a map is composed as one over
 * how many are.
 *
 * <p>An element meets "no key of the rates is its currency" two ways as the reading states it:
 * that no key is, or that the rates hold none. The second is the first met by a map holding none,
 * so it is no other way, and an element that meets the statement one way is one a row is handed the
 * rates for. Read as two ways, nothing was handed on, and a count of the elements whose currency
 * the rates do not rate was a count no row was composed for, where a count of those it does rate
 * was.
 */
class AnElementCountedForFailingAMembershipIsComposedTest {

    private static final String DEALS = """
            module probe

            data Deal = { currency: String, amount: Decimal }
            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (deals: List<Deal>, rates: Map<String, Decimal>) -> Priced | Unpriced
                constructs Priced, Unpriced

            let named (deals, rates) = {
                guard GUARD
                    else Unpriced { n = 0 }
                Priced { n = 1 }
            }
            """;

    private static final String UNPRICED = "List.length(List.filter(d -> "
            + "Bool.not(Map.containsKey(d.currency, rates)), deals))";

    private static final String PRICED = "List.length(List.filter(d -> "
            + "Map.containsKey(d.currency, rates), deals))";

    @Test
    void exactlyOneElementFailingAMembershipIsComposed() {
        assertEquals(List.of(), whatNothingCouldShow(UNPRICED + " == 1"));
    }

    @Test
    void exactlyTwoElementsFailingAMembershipAreComposed() {
        assertEquals(List.of(), whatNothingCouldShow(UNPRICED + " == 2"));
    }

    @Test
    void exactlyOneElementMeetingAMembershipIsComposed() {
        assertEquals(List.of(), whatNothingCouldShow(PRICED + " == 1"));
    }

    /** The points nothing could show a row can be written at. */
    private static List<String> whatNothingCouldShow(String guard) {
        Compilation compilation = Compilation.ofSource(DEALS.replace("GUARD", guard), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> found = new ArrayList<>();
        for (String line : page.split("\n")) {
            if (line.contains("nothing could show a row can be written at")) {
                found.add(line.trim());
            }
        }
        return found;
    }
}
