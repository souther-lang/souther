package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element of a container that is a record is chosen by values for each of its fields, and a
 * field a statement compares with another input turns over at that input's value, so the field's
 * values are read with the input where it stands.
 */
class ARecordFieldEqualToAnInputIsChosenAgainstThatInputTest {

    @Test
    void aFieldComparedWithAnInputGetsValuesAroundThatInput() {
        Compilation compilation = measured("""
                module example.popular

                data Item = { label: String, weight: Int }

                behavior popular : (xs: List<Item>, label: String) -> Bool

                let popular (xs, label) =
                    List.length(List.filter(x -> x.label == label, xs)) >= 3
                """);
        assertFalse(report(compilation).contains("neither one of so many"),
                () -> report(compilation));
        List<Long> meeting = Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular"))
                .rowsByBehavior().getOrDefault("popular", List.of()).stream()
                .map(row -> meetingTheInput(row.inputs().stream()
                        .map(FixtureTemplate::text).toList()))
                .toList();
        assertTrue(meeting.contains(3L) && meeting.contains(2L), () -> "both sides: " + meeting);
        assertTrue(meeting.stream().anyMatch(each -> each > 3), () -> "past it: " + meeting);
        assertTrue(meeting.stream().anyMatch(each -> each < 2), () -> "short of it: " + meeting);
    }

    /** How many items of the list a row offers carry the label the row offers beside it. */
    private static long meetingTheInput(List<String> inputs) {
        Matcher label = LABEL.matcher(inputs.get(1));
        assertTrue(label.matches(), () -> "the label of an offered row: " + inputs);
        Matcher item = ITEM.matcher(inputs.getFirst());
        long meeting = 0;
        while (item.find()) {
            if (item.group(1).equals(label.group(1))) {
                meeting++;
            }
        }
        return meeting;
    }

    private static final Pattern LABEL = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"");

    private static final Pattern ITEM = Pattern.compile("label = \"((?:[^\"\\\\]|\\\\.)*)\"");

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
