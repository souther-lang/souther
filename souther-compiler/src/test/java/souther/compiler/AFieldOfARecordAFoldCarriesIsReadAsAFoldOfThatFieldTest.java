package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.WhyAPlaceIsUndividedIsSaid;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field of the record a walk from a seed carries is a walk of its own, where the step gives it a
 * value that reads what was carried only as that field: its seed is the field's seed and its step
 * the field's value in the step.
 *
 * <p>So a comparison of a field that only adds draws the line the total of the same numbers draws,
 * and one of a field that counts the elements meeting something draws the count's, whatever the
 * other fields do. A field reading another field of what was carried is no walk of its own, and
 * is measured on its runs as a comparison over a number nothing reads is.
 */
class AFieldOfARecordAFoldCarriesIsReadAsAFoldOfThatFieldTest {

    private static final String STATE = """
            module m

            data State = { score: Int, misses: Int, zeros: Int }

            behavior state : (xs: List<Int>) -> State
            let state (xs) = List.fold((s, x) -> State {
                    score = s.score + x,
                    misses = if x == 0 then s.misses + 1 else 0,
                    zeros = if x == 0 then s.zeros + 1 else s.zeros
                }, State { score = 0, misses = 0, zeros = 0 }, xs)

            behavior out : (xs: List<Int>) -> Bool
            """;

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String out(String body) {
        return report(STATE + "let out (xs) = " + body + "\n");
    }

    private static String inline(String body) {
        return report("""
                module m

                data State = { score: Int, misses: Int, zeros: Int }

                behavior out : (xs: List<Int>) -> Bool
                let out (xs) = %s
                """.formatted(body));
    }

    private static final String FOLDED = "List.fold((s, x) -> State {"
            + " score = s.score + x,"
            + " misses = if x == 0 then s.misses + 1 else 0,"
            + " zeros = if x == 0 then s.zeros + 1 else s.zeros"
            + " }, State { score = 0, misses = 0, zeros = 0 }, xs)";

    private static final String ON_ITS_RUNS =
            WhyAPlaceIsUndividedIsSaid.of(UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS);

    @Test
    void aFieldThatOnlyAddsIsTheTotalOfWhatItAdds() {
        String report = inline(FOLDED + ".score >= 10");

        assertTrue(report.contains("read as out/List.sum(xs): = 10"), report);
        assertFalse(report.contains(ON_ITS_RUNS), report);
    }

    @Test
    void aFieldThatCountsIsTheCount() {
        String report = inline(FOLDED + ".zeros >= 3");

        assertTrue(report.contains("#xs [xs[*] == 0]"), report);
        assertFalse(report.contains(ON_ITS_RUNS), report);
    }

    /** A call of a behavior whose body is the walk is the walk. */
    @Test
    void throughACallAFieldIsReadAsWritten() {
        String score = out("state(xs).score >= 10");
        assertTrue(score.contains("read as out/List.sum(xs): = 10"), score);
        String zeros = out("state(xs).zeros >= 3");
        assertTrue(zeros.contains("#xs [xs[*] == 0]"), zeros);
    }

    /** A streak is no fold any form says, field or not: its runs place the rows. */
    @Test
    void aFieldThatStartsOverIsMeasuredOnItsRuns() {
        String report = out("state(xs).misses >= 3");

        assertTrue(report.contains(ON_ITS_RUNS), report);
        assertFalse(report.contains("not read: comparison"), report);
    }

    /**
     * A field whose step reads another field of what was carried is no walk of its own: read as
     * one, {@code s.zeros + x} would be a total of the elements, and it is the count before the
     * last element with that element added.
     */
    @Test
    void aFieldReadingAnotherIsNoWalkOfItsOwn() {
        String report = inline("List.fold((s, x) -> State {"
                + " score = s.zeros + x,"
                + " misses = s.misses,"
                + " zeros = if x == 0 then s.zeros + 1 else s.zeros"
                + " }, State { score = 0, misses = 0, zeros = 0 }, xs).score >= 10");

        assertFalse(report.contains("List.sum"), report);
        assertTrue(report.contains(ON_ITS_RUNS), report);
    }
}
