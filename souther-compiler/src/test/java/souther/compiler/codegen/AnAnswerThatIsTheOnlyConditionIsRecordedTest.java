package souther.compiler.codegen;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body whose only condition is what an application of the language's operations answers — no
 * comparison and no arm of its own — is measured, and the answer each run gets is recorded.
 *
 * <p>The place the answer is recorded at is the one place the plan numbers in such a body. A build
 * that took the body for one with nothing to record would leave that place out of the code and be
 * refused for it.
 */
class AnAnswerThatIsTheOnlyConditionIsRecordedTest {

    /** A plan numbering nothing but where an application's answer is recorded has a place to
     *  record at, and no arm or comparison a row is owed for. */
    @Test
    void aPlanHoldingOnlyAnAnswerHasAPlaceToRecordAt() {
        Compilation compilation = Compilation.ofSource("""
                module p
                behavior f : (xs: List<Bool>) -> Bool
                let f (xs) = List.any(x -> x, xs)
                """, "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("p")).value();
        assertNotNull(checked, "the model compiles");
        CoverageSites.Plan plan = checked.plan();

        assertTrue(plan.sites().isEmpty(), () -> plan.sites().toString());
        assertEquals(1, plan.answers().size(), () -> plan.answers().toString());
        assertFalse(plan.hasNoProbes());
    }

    @ParameterizedTest
    @ValueSource(strings = {"List.any(x -> x, xs)", "List.all(x -> x, xs)",
            "List.any(x -> Bool.not(Bool.not(x)), xs)"})
    void eachWayTheAnswerComesOutIsTakenByTheRowThatGetsIt(String condition) {
        Compilation compilation = Compilation.ofSource("""
                module p
                behavior f : (xs: List<Bool>) -> Bool
                let f (xs) = %s

                example f
                    | "one of each" : ([true, false]) -> %s
                    | "none" : ([]) -> %s
                    | "only false" : ([false]) -> false
                    | "only true" : ([true]) -> true
                """.formatted(condition, !condition.startsWith("List.all"),
                condition.startsWith("List.all")), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                report);
        assertTrue(report.contains("decision    rules 2   taken 2"), report);
    }
}
