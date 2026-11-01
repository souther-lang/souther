package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The value of a case an arm opens is read beside the sum it is added to as a plain input is,
 * when the region of the way is rebuilt without the statement a row at the line of the second
 * comparison meets.
 *
 * <p>Held here: that the second of two comparisons of one sum is read with the value an input
 * and with it the value of a case, whatever the guard that narrows it.
 */
class ACaseAnArmOpensIsReadAsAPlainInputIsWhenAStatementIsTakenAwayTest {

    private static final String SCORES = """
            module m

            data Score = Int
                invariant value >= 0 && value <= 50

            data Points = Int
                invariant value >= 0 && value <= 12
            """;

    private static final String SUMS = """
            else if a.value + b.value > 50 then 1
            else if a.value + b.value < 50 then 2
            else 3""";

    private static String viaTheCase(String guard) {
        return SCORES + """

                data Result = Points | Fault

                behavior f : (a: Score, r: Result) -> Int

                let f (a, r) =
                    match r with
                        | Fault -> 0
                        | Points as b ->
                %s
                """.formatted((guard + "\n" + SUMS).indent(12).stripTrailing());
    }

    private static String viaTheInput(String guard) {
        return SCORES + """

                behavior f : (a: Score, b: Points) -> Int

                let f (a, b) =
                %s
                """.formatted((guard + "\n" + SUMS).indent(4).stripTrailing());
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The guard that makes a hole in the value and the one that bounds it are read alike. */
    @Test
    void theValueOfTheCaseIsReadWhateverTheGuardOnItIs() {
        for (String guard : List.of("if b.value == 0 then 0", "if b.value < 1 then 0",
                "if b.value == 12 then 0", "if b.value < 3 then 0", "if b.value > 3 then 0")) {
            String viaCase = report(viaTheCase(guard));
            String viaInput = report(viaTheInput(guard));
            assertTrue(viaInput.contains("measurement: complete"), guard + "\n" + viaInput);
            assertFalse(viaCase.contains("not read: comparison"), guard + "\n" + viaCase);
            assertTrue(viaCase.contains("measurement: complete"), guard + "\n" + viaCase);
        }
    }
}
