package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a rule this read from end to end costs a measurement, which is nothing.
 *
 * <p>Four models differing by one clause, and the clause is the whole test. One draws a line; two
 * are read to the end and leave the positions no class of their own; one is written in a form
 * nothing here takes apart. The first three cost the measurement nothing and the fourth costs it
 * what a limit of this compiler costs, and the document has to say so — a rule read from end to end
 * reported as a question nobody answered tells an author to go and look at a clause that is doing
 * exactly what they wrote.
 *
 * <p>Asked of the document and of the sentence a person reads, because the two are written by
 * different code from the same evidence and this is the seam every round of #1029 and #1047 went
 * wrong at. The reason type told the two halves apart and the words underneath it did not.
 */
class ARuleReadToTheEndIsNotOneThisCouldNotReadTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One behavior, one record, and one clause written about a field it does not divide.
     *
     * <p>The behavior is deliberately about a different field. What the clause costs has to be read
     * off the clause rather than off anything the body does with it, and a body comparing the same
     * field would put a second reading over the first.
     */
    private static String model(String clause) {
        return """
                module m

                data Auto
                data Manual
                data Small
                data Large
                data Size = Small | Large

                data Box = { size: Size, name: String, lo: Int, hi: Int }
                %s

                behavior byBox : (b: Box) -> Auto | Manual
                let byBox (b) =
                    match b.size with
                        | Small -> Auto
                        | Large -> Manual

                example byBox
                    | "one" : (Box { size = Small, name = "n", lo = 1, hi = 2 }) -> Auto
                """.formatted(clause);
    }

    /** What one of these models came to, in the words both surfaces write it in. */
    private record Measured(String status, List<String> weakening, List<String> kinds,
                            String human) {

        boolean says(String word) {
            return human.contains(word);
        }
    }

    private static Measured of(String clause) {
        Compilation compilation = Compilation.ofSource(model(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        JsonNode document = JSON.readTree(report.json(SourceNameResolver.identity()));
        JsonNode behavior = document.get("modules").get(0).get("behaviors").get(0);
        List<String> weakening = new ArrayList<>();
        behavior.path("weakening").forEach(each -> weakening.add(each.asString()));
        List<String> kinds = new ArrayList<>();
        behavior.path("findings").forEach(each -> kinds.add(each.get("kind").asString()));
        return new Measured(behavior.get("status").asString(), weakening, kinds,
                report.human(SourceNameResolver.identity()));
    }

    /** A clause that draws a line, which is what the three below are read against. */
    @Test
    void aClauseThatDrawsALineIsMeasuredWhole() {
        Measured measured = of("    invariant lo >= 0");

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.weakening());
        assertTrue(measured.kinds().contains("boundary_unmet"), measured.kinds().toString());
        assertFalse(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }

    /**
     * A clause read to the end that relates two positions, which divides neither.
     *
     * <p>Nothing is missing: both sides were recognised, and what the clause says is not a set of
     * one position's values. The document says the position has no class from this rule and asks
     * nothing further of anybody.
     */
    @Test
    void aClauseRelatingTwoPositionsCostsTheMeasurementNothing() {
        Measured measured = of("    invariant lo <= hi");

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.weakening());
        assertTrue(measured.says("it relates two positions rather than dividing one"),
                measured.human());
        assertFalse(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }

    /**
     * A clause read to the end whose quantity the position does not appear in.
     *
     * <p>{@code lo - lo >= 0} holds of every row. It is read from end to end, and the sentence a
     * person is shown says so; the accounting beside it raises a question about which values may
     * stand at the position and nothing answers it, so a rule this compiler understood completely
     * comes out as one nobody accounted for and takes the measurement down to partial with it.
     *
     * <p><b>This is what #1047 is about, and these three assertions are what it moves.</b> They are
     * written against what this does today so that the change is visible as a change; the clause
     * above raises no question at all and this one has to come to the same place.
     */
    @Test
    void aClauseCuttingNothingIsStillCountedAsAQuestionNobodyAnswered() {
        Measured measured = of("    invariant lo - lo >= 0");

        assertTrue(measured.says("it was read to the end and cuts nothing this position appears in"),
                measured.human());

        assertEquals("partial", measured.status());
        assertEquals(List.of("question_unanswered"), measured.weakening());
        assertTrue(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }

    /**
     * And a clause nothing here takes apart, which is what a limit of this compiler looks like.
     *
     * <p>Here the question standing is the truth: what the clause says about the values was never
     * read, so what the position may hold is not known to have been read either. The three above
     * are what this one has to stay different from.
     */
    @Test
    void aClauseNothingReadsIsAQuestionNobodyAnswered() {
        Measured measured = of("    invariant String.length(name) <= 0 - 1");

        assertEquals("partial", measured.status());
        assertTrue(measured.weakening().contains("rule_unread"), measured.weakening().toString());
        assertTrue(measured.weakening().contains("question_unanswered"),
                measured.weakening().toString());
        assertTrue(measured.says("written in a form this compiler does not read"), measured.human());
        assertTrue(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }
}
