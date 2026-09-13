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
 * <p><b>Its own content among them.</b> What a string is and how long it is are two numbers of one
 * location as much as the parts of a time are, and a row is composed holding both: the value the
 * comparison puts the string at is one of however many have the length the rule leaves.
 *
 * <p><b>And only where a value answers both.</b> Which pairs those are is the model's and not this
 * compiler's — two rules can leave a location nothing at all — so the last model here is one whose
 * two numbers no value holds together, and this does not read as a claim that any two of them
 * compose.
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

    /**
     * A location asked for its own value and for a number taken of that value.
     *
     * <p>The comparison puts {@code b} at a place of the strings and the rule above it puts {@code
     * b} at a place of its lengths, which is one location measured at two numbers and is not two
     * locations. Composed for one of them at a time, the row was written at whatever the line's own
     * edge chose and arrived only where that value happened to meet the rule that was dropped.
     */
    private static final String A_VALUE_AND_A_NUMBER_TAKEN_OF_IT = """
            module example.string

            data Yes = { v: Int }
            data No = { why: Int }

            behavior cmp : (a: String, b: String) -> Yes | No
                constructs Yes
                constructs No

            let cmp (a, b) = {
                guard String.length(b) /= 1 else No { why = 0 }
                guard a < b else No { why = 1 }
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
     * The same two numbers of one location, where the rules leave no value that stands at the
     * point.
     *
     * <p>The control, and it is still open. A string and its length are written together in the
     * model above; what is different here is the model. A string whose length is below one is the
     * least string there is, so nothing stands below it for the comparison — and no value put to
     * this point arrives, however many of them it is put.
     *
     * <p>Which is what keeps the models above from reading as a claim about this compiler's reach.
     * A point is answered where a value answers it, and two numbers belonging to one location is
     * not a reason to write a row.
     */
    private static final String WHERE_NO_VALUE_STANDS_AT_THE_POINT = """
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
                TWO_PARTS_COMPARED_WITH_EACH_OTHER, A_VALUE_AND_A_NUMBER_TAKEN_OF_IT)) {
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
     * And a point no value of the model stands at is left open, whatever its numbers belong to.
     *
     * <p>What the models above establish is that a location measured twice is answered where a
     * value answers it. Read as a claim about the numbers rather than about the values, this would
     * say a row comes of two of them belonging to one location — and the row would be one a person
     * pastes and finds the point still uncovered.
     *
     * <p>The page says what the composer did as well, which is a separate answer: this one is
     * written for one number of the location and the rule about the other is a condition it was
     * composed without. Where a value stands at the point that is what the search goes on to find,
     * and here there is none.
     */
    @Test
    void aPointNoValueStandsAtIsStillLeftOpen() {
        String page = human(WHERE_NO_VALUE_STANDS_AT_THE_POINT);

        assertFalse(whatNothingCouldShow(WHERE_NO_VALUE_STANDS_AT_THE_POINT).isEmpty(),
                () -> "no string stands below the least one, so the point is open: " + page);
        assertTrue(page.contains("a condition on another number taken where this row is already"
                        + " being written for one"),
                () -> "and the row was composed for one number of the location: " + page);
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
