package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A line a helper draws is one line however many calls read it, and whether a row is seen
 * arriving where nothing showed an input is said of that one line.
 *
 * <p>{@code atLeast} is called on the entry {@code Map.get} finds in both arms of {@code flag}.
 * The rows reaching the first call rule the lines beside it out; the rows reaching the second hold
 * one threshold and leave them, and past the lookup nothing showed an input arriving. One reading
 * ruling a line out settles it for both: a row seen arriving at the other reading is no reason to
 * name it, and the two readings put together are not two answers.
 */
class ALineBesideOneIsNamedForTheLineAndNotForOneReadingOfItTest {

    private static final String MODEL = """
            module p
            let atLeast (a: Int, b: Int): Bool = a >= b
            behavior f : (by: Map<String, Int>, k: String, q: Int, flag: Bool) -> Int
            let f (by, k, q, flag) =
                match Map.get(k, by) with
                    | None -> 0
                    | Some got -> if flag then (if atLeast(got, q) then 1 else 2)
                        else (if atLeast(got, q) then 3 else 4)
            example f
                | "on" : ([("Q", 5)], "Q", 5, true) -> 1
                | "off" : ([("Q", 4)], "Q", 5, true) -> 2
                | "in" : ([("Q", 9)], "Q", 5, true) -> 1
                | "out" : ([("Q", 0)], "Q", 5, true) -> 2
                | "kept higher" : ([("Q", 7)], "Q", 7, true) -> 1
                | "kept lower" : ([("Q", 3)], "Q", 2, true) -> 1
                | "refused higher" : ([("Q", 10)], "Q", 12, true) -> 2
                | "refused lower" : ([("Q", -1)], "Q", 0, true) -> 2
                | "on, the other way" : ([("Q", 5)], "Q", 5, false) -> 3
                | "off, the other way" : ([("Q", 4)], "Q", 5, false) -> 4
                | "in, the other way" : ([("Q", 9)], "Q", 5, false) -> 3
                | "out, the other way" : ([("Q", 0)], "Q", 5, false) -> 4
                | "none" : ([], "Q", 5, true) -> 0
            """;

    /** The model is measured whole, and no line beside the helper's is named. */
    @Test
    void theRowsRulingTheLinesOutAtOneCallSettleThemForTheLine() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertFalse(report.contains("! no row tells"), report);
    }
}
