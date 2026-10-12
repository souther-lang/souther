package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an application of an operation the library writes in the language answers is one decision
 * of the model's, and what the operation's own code does on the way is no decision of it.
 *
 * <p>The analysis is given a copy of such an operation where it is applied, and the copy's code
 * forks and binds names of its own. A rule read off those would be about a name the operation
 * bound — a truth no run is recorded at — and no row could be seen to take it. The answer the
 * application gives is recorded, and is what a rule about it is seen at, as an operation the
 * language keeps standing is.
 */
class WhatALibraryOperationAnswersIsOneDecisionOfTheModelTest {

    private static final String THROUGH_THE_OPERATION = """
            module p
            data H = { flag: Option<Bool> }
            behavior f : (h: H) -> Bool
            let f (h) = Option.withDefault(false, h.flag)
            """;

    private static final String WRITTEN_OUT = """
            module p
            data H = { flag: Option<Bool> }
            behavior f : (h: H) -> Bool
            let f (h) =
                match h.flag with
                    | Some v -> v
                    | None -> false
            """;

    private static final String ROWS = """

            example f
                | "none" : (H { flag = None }) -> false
                | "true" : (H { flag = true }) -> true
                | "false" : (H { flag = false }) -> false
            """;

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

    private static String decisionLine(String report) {
        return report.lines().filter(line -> line.contains("decision ")).findFirst().orElse("");
    }

    @Test
    void aRowThroughEachAnswerIsSeenTakingItsRule() {
        Compilation compilation = measured(THROUGH_THE_OPERATION + ROWS);
        String report = report(compilation);

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                report);
        assertTrue(decisionLine(report).contains("rules 2   taken 2"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** The same rows measure the operation and the match written out the same way. */
    @Test
    void itIsMeasuredAsTheMatchWrittenOutIs() {
        String through = report(measured(THROUGH_THE_OPERATION + ROWS));
        String written = report(measured(WRITTEN_OUT + ROWS));

        assertEquals(decisionLine(written), decisionLine(through), through);
    }

    /** The rules are what the application answers, and nothing the operation bound. */
    @Test
    void theRulesAreWhatTheApplicationAnswers() {
        for (String model : List.of(THROUGH_THE_OPERATION, """
                module p
                behavior f : (k: String, m: Map<String, Bool>) -> Bool
                let f (k, m) = Map.get(k, m) |> Option.withDefault(false)
                """)) {
            String report = report(measured(model));

            assertTrue(decisionLine(report).contains("rules 2"), report);
            assertTrue(report.contains("answers true"), report);
            assertTrue(report.contains("answers false"), report);
            assertFalse(report.contains("no run through it is recorded at"), report);
        }
    }

    /** An application that answers true whatever it is handed is one rule, and none is read for
     *  the answer it never gives. */
    @Test
    void anAnswerNeverGivenIsNoRule() {
        String report = report(measured("""
                module p
                data H = { flag: Option<Bool> }
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(true, Option.map(v -> true, h.flag))
                """));

        assertTrue(decisionLine(report).contains("rules 1"), report);
        assertFalse(report.contains("answers false"), report);
    }
}
