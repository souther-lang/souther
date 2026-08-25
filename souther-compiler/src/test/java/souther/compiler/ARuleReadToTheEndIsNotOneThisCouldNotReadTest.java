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
 *
 * <p>What these hold to, said once so that a later reader has it:
 *
 * <ul>
 *   <li>What a rule cuts outranks how it is spelled. Which positions a rule restricts is settled by
 *       the quantity its canonical form cuts, and the spelling answers only where there is no
 *       quantity to be had.</li>
 *   <li>A comparison whose positions cancel and whose residue holds of every row raises no
 *       coverage obligation. One whose positions cancel and whose residue holds of none admits
 *       nothing, which is the opposite, and raises what it always did.</li>
 *   <li>A rule read to the end that draws no line is never a question nobody answered.</li>
 *   <li>Every question nobody answered is one whose reading actually stopped, which
 *       {@code RuleAccounting.Unaccounted} takes only a stop for.</li>
 *   <li>One comparison may come to different answers from different readings without being two
 *       rules, and the document still writes one word for it
 *       ({@code OneRuleReadTwoWaysIsTwoAnswersAndOneWordTest}).</li>
 * </ul>
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
     * <p>{@code lo - lo >= 0} holds of every row, and the position it names cancels against itself.
     * It costs the measurement what the clause above costs it, which is nothing: no value anywhere
     * is admitted or refused, so there is no question about the values for anybody to answer.
     *
     * <p>The position is written twice, so a classification counting off the sides made it a rule
     * about {@code lo} raising the questions a rule about a position raises — which nothing could
     * answer, because the rule states neither of them. A clause this compiler read from end to end
     * came out as a question nobody had answered and took the measurement to partial with it.
     */
    @Test
    void aClauseCuttingNothingCostsTheMeasurementNothing() {
        Measured measured = of("    invariant lo - lo >= 0");

        assertTrue(measured.says("it was read to the end and cuts nothing this position appears in"),
                measured.human());

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.weakening());
        assertFalse(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }

    /**
     * The same clause under a different operator, which is the same rule about the model.
     *
     * <p>{@code lo - lo == 0} holds of every row exactly as {@code lo - lo >= 0} does. Which
     * operator an author wrote is no part of whether their rule states anything, so a fix that
     * turned on the operator would have left this one telling them that which values may stand at
     * {@code lo} is a question nothing answered.
     */
    @Test
    void whichOperatorIsWrittenDoesNotDecideIt() {
        Measured measured = of("    invariant lo - lo == 0");

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.weakening());
        assertFalse(measured.kinds().contains("rule_unaccounted"), measured.kinds().toString());
    }

    /**
     * And a clause whose positions cancel to something no row satisfies, which is the opposite.
     *
     * <p>{@code lo - lo >= 1} is {@code 0 >= 1}. The quantity it cuts is empty, exactly as the two
     * above, and the rule admits nothing rather than restricting nothing — so the questions it
     * raises are real ones and the rows that cannot be built are what a reader is shown. Read off
     * the empty quantity alone, this would have come out as a rule that states nothing.
     */
    @Test
    void aClauseNoRowSatisfiesIsNotOneThatRestrictsNothing() {
        Measured measured = of("    invariant lo - lo >= 1");

        assertEquals("partial", measured.status());
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
