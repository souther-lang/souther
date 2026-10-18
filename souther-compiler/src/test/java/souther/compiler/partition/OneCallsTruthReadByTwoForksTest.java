package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One call's answer, held in a name and read by the conditions of two forks, is one construct of
 * the model asked twice, and measuring the model is not refused for it.
 */
class OneCallsTruthReadByTwoForksTest {

    private static final String MODEL = """
            module probe

            data Sign = Positive | Negative
            data Result = { body: String, sign: Sign }

            behavior parse : (text: String) -> Result
            let parse (text) = {
                let minus = String.startsWith("-", text)
                Result {
                    body = if minus then "negative" else text,
                    sign = if minus then Negative else Positive
                }
            }
            """;

    @Test
    void aModelIsMeasuredWhoseTwoForksReadOneCallsAnswer() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = assertDoesNotThrow(() -> AdequacyReport.of(compilation));
        assertEquals(List.of("parse"), report.modules().getFirst().behaviors().stream()
                .map(AdequacyReport.BehaviorReport::name).toList());
    }
}
