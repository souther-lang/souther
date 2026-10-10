package souther.compiler.partition;

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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the labels a text splits into at commas hold any once trimmed is whether the text holds a
 * code point that is neither whitespace nor a comma, and the line a rule on it draws is drawn on
 * that count of the text.
 *
 * <p>Held end to end: the rows the model is offered stand at the three points of that line, and
 * the rows the author writes are told apart by it, so a rule about the pieces of a string that
 * counted a comma as something a piece holds would put the one row it writes at the wrong point.
 */
class AStringSplitAtOneCodePointDrawsItsLineOnWhatTheStringHoldsTest {

    private static final String LABELS = """
            module example.labels

            let labelsOf (text: String): Set<String> =
                text
                    |> String.split(",")
                    |> Set.fromList
                    |> Set.map(piece -> piece |> String.trim |> String.lowercase)
                    |> Set.filter(piece -> Bool.not(String.isEmpty(piece)))

            behavior hasLabels : (text: String) -> Bool
            let hasLabels (text) = Set.size(labelsOf(text)) >= 1
            """;

    /** The model, offered no row: one at each of the three points of the line it draws. */
    @Test
    void theRowsOfferedStandAtTheThreePointsOfTheLine() {
        Compilation compilation = measured(LABELS);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.labels")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        assertTrue(offered.contains("3 rows to fill what nothing covers"), offered);
        assertTrue(offered.contains("(\" \")"), () -> "a text of whitespace alone: " + offered);
        assertTrue(offered.contains("(\"x\")"), () -> "a text of one code point: " + offered);
        assertTrue(offered.contains("(\"xx\")"), () -> "and of more: " + offered);
    }

    /**
     * A comma alone is no code point a label can be made of, so a row of it is at the point of
     * none; a letter is at the point of one. Read the other way — a comma counted — the row of a
     * comma would stand at the point of one, and the point of none would be owed a row.
     */
    @Test
    void aCommaAloneIsAtThePointOfNoneAndALetterAtThePointOfOne() {
        Compilation compilation = measured(LABELS + """

                example hasLabels
                    | "a comma alone" : (",") -> false
                    | "a letter" : ("x") -> true
                    | "more" : ("xx") -> true
                """);

        assertEquals(List.of(), compilation.errors(), "the rows hold");
        String report = AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("obligations 3/3"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** The texts a person would try, each as the run time answers. */
    @Test
    void theRowsAPersonWouldWriteHold() {
        Compilation compilation = measured(LABELS + """

                example hasLabels
                    | "labels" : ("Bug, bug , UI") -> true
                    | "blank and separator" : (" , ") -> false
                    | "only separators" : (",,,") -> false
                    | "padded" : ("  abc  ") -> true
                    | "ideographic blanks" : ("　,　") -> false
                    | "two" : ("a,b") -> true
                """);

        assertEquals(List.of(), compilation.errors(), "the rows hold");
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
