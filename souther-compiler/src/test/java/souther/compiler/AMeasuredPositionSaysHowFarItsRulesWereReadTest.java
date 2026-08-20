package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position the axes measure says how far its rules were read.
 *
 * <p>The classes beside a position mean one thing on a reading that ran to the end and another on
 * one that did not: a class arrived at from part of the rules is a value the model singled out, and
 * a rule that went unread may yet refuse it. The axis has carried that since it was measured, with
 * nothing reading it — so two classes were offered and neither surface said what they rested on.
 *
 * <p>Said apart from a position with no axis at all. Both are readings that did not finish, and
 * they are not the same thing to act on: reading the same sentence about a position with three
 * classes as about one with none says the numbers beside it are not to be believed.
 */
class AMeasuredPositionSaysHowFarItsRulesWereReadTest {

    /**
     * A position the axes measure whose rules were not read in full.
     *
     * <p>The option divides `i.assignee` into `None` and `Some`, so the position is measured. What
     * `Assignee` says about the value inside is behind the option, and this reading does not go
     * there.
     */
    private static final String MEASURED_IN_PART = """
            module o

            data Assignee = String
                invariant String.length(value) >= 1

            data Issue = { assignee: Assignee? }
            data Accepted = { at: Int }

            behavior classify : (i: Issue) -> Accepted
            """;

    /** The control: the same shape with nothing left unread. */
    private static final String READ_IN_FULL = """
            module u

            data Low
            data Accepted = { at: Int }

            behavior classify : (n: Int) -> Accepted | Low
                constructs Accepted

            let classify (n) = {
                guard n >= 60 else Low
                Accepted { at = n }
            }
            """;

    private static AdequacyReport reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static String humanOf(String source) {
        return reportOf(source).human(SourceNameResolver.identity());
    }

    private static JsonNode partitionOf(String source) {
        JsonNode document = JsonMapper.builder().build()
                .readTree(reportOf(source).json(SourceNameResolver.identity()));
        return document.get("modules").get(0).get("behaviors").get(0).get("partition");
    }

    @Test
    void aMeasuredPositionIsToldApartFromOneWithNoAxis() {
        JsonNode axis = partitionOf(MEASURED_IN_PART).get("axes").get(0);
        assertEquals("i.assignee", axis.get("path").asText());
        assertEquals(2, axis.get("classes").size(), axis.toString());
        assertEquals("partial", axis.get("read").get("extent").asText(),
                "the axis says that something about its position's rules is left standing");
        // Which of the two it is, and not only that there is one. Nothing here reached the rules
        // behind the option — which is not a rule this read and could not use, and saying so would
        // publish a cause this was not observed to have.
        assertTrue(axis.get("read").get("rulesNotReached").asBoolean(), axis.toString());
        assertFalse(axis.get("read").has("unanswered"),
                "there is no rule to name, because nothing was seen: " + axis);

        String human = humanOf(MEASURED_IN_PART);
        assertTrue(human.contains("rules not reached: i.assignee"),
                "a measured position says its rules were never reached, which a position with no"
                        + " axis does not: " + human);
        assertFalse(human.contains("not read: i.assignee"),
                "and is not said as one nothing divided: " + human);
    }

    /** Nothing is invented: a position whose rules were read in full gains no line either way. */
    @Test
    void aPositionWhoseRulesWereReadInFullGainsNoLine() {
        String human = humanOf(READ_IN_FULL);

        JsonNode read = partitionOf(READ_IN_FULL).get("axes").get(0).get("read");
        assertEquals("complete", read.get("extent").asText());
        assertFalse(read.has("rulesNotReached"), "nothing was left standing: " + read);
        assertFalse(read.has("unanswered"), "nothing was left standing: " + read);
    }
}
