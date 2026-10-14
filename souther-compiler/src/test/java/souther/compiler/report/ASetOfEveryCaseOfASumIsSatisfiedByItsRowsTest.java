package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fee over a set of a sum's cases, with a row at every size the set can hold, is satisfied.
 *
 * <p>The set holds at most as many as the sum has cases, so the sizes past that are no points of
 * the border, and nothing is left for a search to find or for a reader to be told to widen.
 */
class ASetOfEveryCaseOfASumIsSatisfiedByItsRowsTest {

    private static final String MODEL = """
            module probe.fee

            data Service = Insurance | Support | Security
            data Yen = Int

            behavior optionFee : (picked: Set<Service>) -> Yen
                constructs Yen

            let optionFee (picked) =
                if Set.size(picked) == 3 then Yen(1000) else Yen(Set.size(picked) * 400)

            example optionFee
                | "none"  : ([]) -> Yen(0)
                | "one"   : ([Insurance]) -> Yen(400)
                | "two"   : ([Insurance, Support]) -> Yen(800)
                | "three" : ([Insurance, Support, Security]) -> Yen(1000)
            """;

    @Test
    void theFeeIsSatisfiedAndNothingKeepsItOpen() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        String human = report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(), human);
        assertTrue(report.adequacyGaps().isEmpty(), human);
        assertTrue(report.whatKeepsTheVerdictOpen().isEmpty(), human);
    }
}
