package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code Bool} every case of a sum spreads, read on the way to a line, is a value a row writes
 * under whichever case it is.
 *
 * <p>The way to {@code r.q.amount > 50} asks {@code r.q.urgent} to be true, and {@code r.q.urgent}
 * is no position: it stands at {@code r.q@A.urgent} or at {@code r.q@B.urgent}. A row composed for
 * the line writes the truth where the case it is written as holds it, the same as the number.
 */
class ABoolTheCasesShareIsWrittenUnderTheCaseTheRowIsTest {

    private static final String MODEL = """
            module probe.truth

            data Common = { urgent: Bool, amount: Int }
                invariant amount >= 0 && amount <= 100
            data A = { ...Common, a: Int }
            data B = { ...Common, b: Int }
            data Q = A | B
            data Req = { q: Q }

            behavior fee : (r: Req) -> Int
            let fee (r) =
                if r.q.urgent then
                    if r.q.amount > 50 then 2 else 1
                else 0
            """;

    /** Every rule behind the truth is composed, and none waits on a case nobody chose. */
    @Test
    void aRowThroughTheTruthIsComposed() {
        Compilation c = measured();
        String human = AdequacyReport.of(c).human(SourceRendering.namedByIdentity(c.texts()));
        assertFalse(human.contains("nothing said which of them the value under it is"), human);
    }

    /** The truth is written where the case the row is written as holds it. */
    @Test
    void theTruthStandsUnderTheCaseTheRowIs() {
        Compilation c = measured();
        String block = GeneratedRows.of(
                Adequacy.offeredFor(c.db(), OfferingRequest.overTheModule("probe.truth")),
                Map.of(), SourceRendering.namedByIdentity(c.texts()), c.db()).text();
        assertTrue(block.contains("urgent = true, amount = 51"),
                () -> "a row at the line is written with the truth the way asks:\n" + block);
    }

    private static Compilation measured() {
        Compilation c = Measured.ONCE;
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().said()).toList(),
                "the model is measured");
        return c;
    }

    /** The model measured once: both questions here read the one measurement. */
    private static final class Measured {

        static final Compilation ONCE = measure();

        private static Compilation measure() {
            Compilation c = Compilation.ofSource(MODEL, "Main");
            c.measure(Adequacy.Asked.fullReport());
            c.answerEverything();
            return c;
        }
    }
}
