package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A location a rule measures twice is written once, with a value answering both numbers.
 *
 * <p>The hour of a time and its minute are two numbers of one location, so a row that stands where
 * a rule about one of them is drawn has to hold the other as well. Composed a number at a time, the
 * second value was written where the first already stood and the condition above the line went
 * unrepresented — and whether the row then arrived was settled by whether the value the line's own
 * edge happened to choose satisfied the condition that was dropped.
 *
 * <p><b>Read back, and not merely built.</b> Nothing below asserts what value was written. A row
 * offered at a point is read again after it is composed, and a row holding an hour that the guard
 * above the line sends elsewhere does not reach the point — so a page with no point left
 * unestablished is the statement that the value answers both numbers at once.
 *
 * <p><b>And only what one value can be built to answer.</b> Which numbers those are is the
 * realizer's, and a location asked for its own content beside a number taken of it is not among
 * them. The last model here holds that, so this does not read as a claim about every two numbers at
 * one location.
 */
class ALocationAskedForTwoNumbersIsWrittenOnceForBothTest {

    /** Two parts of one time: the line divides one of them and the way above bounds the other. */
    private static final String TWO_PARTS_OF_A_TIME = """
            module example.time

            data Yes = { v: Int }
            data No = { why: Int }

            behavior at : (t: Time) -> Yes | No
                constructs Yes
                constructs No

            let at (t) = {
                guard Time.hour(t) /= 0 else No { why = 0 }
                guard Time.minute(t) < 30 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /**
     * Two parts of one time compared with each other, which the item fixes both of.
     *
     * <p>Beside the one above and not a shape of it. There the item names one number and the way
     * above the line names the other, so the item fixes one location; here the item names both and
     * fixes one location twice. A limit about a value standing beside a second location of the same
     * item counts the locations — read as the numbers, this item is two and the row is refused for
     * a limit about something the model does not have here.
     */
    private static final String TWO_PARTS_COMPARED_WITH_EACH_OTHER = """
            module example.compared

            data Yes = { v: Int }
            data No = { why: Int }

            behavior at : (t: Time) -> Yes | No
                constructs Yes
                constructs No

            let at (t) = {
                guard Time.hour(t) < Time.minute(t) else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** The same of a date, which is the other family a value is built to have parts of. */
    private static final String TWO_PARTS_OF_A_DATE = """
            module example.date

            data Yes = { v: Int }
            data No = { why: Int }

            behavior on : (d: Date) -> Yes | No
                constructs Yes
                constructs No

            let on (d) = {
                guard Date.month(d) /= 1 else No { why = 0 }
                guard Date.day(d) < 15 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** One part alone, which is what the parts beside it being free looks like when nothing asks
     *  for them. */
    private static final String ONE_PART_OF_A_TIME = """
            module example.one

            data Yes = { v: Int }
            data No = { why: Int }

            behavior at : (t: Time) -> Yes | No
                constructs Yes
                constructs No

            let at (t) = {
                guard Time.minute(t) < 30 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /**
     * A location asked for its own content beside a number taken of it, which is not a pair one
     * value is built for.
     *
     * <p>The control, and it is still open. What a string is and how long it is do not leave each
     * other free the way the parts of a time do, so nothing composes the two together and the
     * condition above the line is still one the row was written without. Read as passing because
     * the models above pass, this test would be saying that any two numbers at a location compose.
     *
     * <p>And nothing else answers it either: the only string of no characters is the least one
     * there is, so no value stands below it and no second value put to this point would arrive.
     * Written at a length several strings have, the search finds one of them and the condition it
     * was composed without is met by accident — which says nothing about whether the two were
     * composed together.
     */
    private static final String A_MEASURE_AND_THE_VALUE_MEASURED = """
            module example.string

            data Yes = { v: Int }
            data No = { why: Int }

            behavior cmp : (a: String, b: String) -> Yes | No
                constructs Yes
                constructs No

            let cmp (a, b) = {
                guard String.length(b) < 1 else No { why = 0 }
                guard a < b else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    private static final String LEFT_OUT =
            "not every condition on the way to the line is one the row was composed against";

    /**
     * Nothing is left unestablished, which is the whole of it: every point of the line below, and
     * the rule of the body that takes both conditions.
     */
    @Test
    void bothNumbersAreAnsweredByTheOneValueTheRowWrites() {
        for (String model : List.of(TWO_PARTS_OF_A_TIME, TWO_PARTS_OF_A_DATE,
                TWO_PARTS_COMPARED_WITH_EACH_OTHER)) {
            List<String> open = whatNothingCouldShow(model);

            assertEquals(List.of(), open,
                    () -> "every point of this model has a row composed for it:\n" + model);
        }
    }

    /** And no condition on the way was left out, which is the reason those points came right. */
    @Test
    void theConditionAboveTheLineIsOneTheRowWasComposedAgainst() {
        for (String model : List.of(TWO_PARTS_OF_A_TIME, TWO_PARTS_OF_A_DATE)) {
            assertFalse(human(model).contains(LEFT_OUT),
                    () -> "the way to each line was used whole:\n" + human(model));
        }
    }

    /** One part alone composes as it did, so nothing above turns on there being two. */
    @Test
    void aLineOverOnePartIsUnchanged() {
        assertEquals(List.of(), whatNothingCouldShow(ONE_PART_OF_A_TIME));
    }


    /**
     * And a location whose two numbers no value answers together is still said to be one, which is
     * what keeps this from reading as a claim about any two numbers at a location.
     */
    @Test
    void aPairNoValueAnswersTogetherIsStillLeftOut() {
        String page = human(A_MEASURE_AND_THE_VALUE_MEASURED);

        assertTrue(page.contains("a condition on another number taken where this row is already"
                        + " being written for one"),
                () -> "nothing composes a string that is both as long as one rule says and where"
                        + " the other puts it: " + page);
        assertFalse(whatNothingCouldShow(A_MEASURE_AND_THE_VALUE_MEASURED).isEmpty(),
                "and the point it was composed without is still open");
    }

    /**
     * The points of the line that nothing could show a row can be written at.
     *
     * <p>The points and not the rules of the body. Whether a row composed for one rule took another
     * is a question about which rules the rows between them reach, and it is asked of a body rather
     * than of a location — a model here that has such a rule open has it open whether or not a
     * value was composed at each of its points.
     */
    private static List<String> whatNothingCouldShow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing could show a row can be written at the ")) {
                found.add(line.trim());
            }
        }
        return found;
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
