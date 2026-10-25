package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An edge at a number taken of a string is proved writable only where the position's strings
 * reach every such number. A format can leave lengths out, a set of every string but a few can
 * leave out the one string of a length, and the line is drawn at a number the rules around the
 * format know nothing of — so the number may be one no string of the position has.
 */
class ANumberOfAStringIsProvedWrittenOnlyWhereTheStringsReachItTest {

    /** Strings no rule is written about reach every length. */
    private static final String ANY = """
            module example.any

            behavior f : (s: String) -> Int

            let f (s) =
                if String.length(s) >= 3 then 1 else 0
            """;

    /** The format has strings of length two and four, and none of length three, where the body
     *  draws its line. The number is first measured by the body. */
    private static final String GAPS = """
            module example.gaps

            data Code = String
                invariant String.matches("aa|aaaa", value)

            behavior f : (s: Code) -> Int

            let f (s) =
                if String.length(s.value) >= 3 then 1 else 0
            """;

    /** Every string but the empty one is a value, and none of them has length nought. */
    private static final String NOT_EMPTY = """
            module example.notempty

            data Named = String
                invariant value /= ""

            behavior f : (s: Named) -> Int

            let f (s) =
                if String.length(s.value) >= 1 then 1 else 0
            """;

    /** Every string starts with an a and a combining acute, which a String holds as one code
     *  point: the run the rule names has an end no value is. */
    private static final String MARKED = """
            module example.marked

            data Marked = String
                invariant String.matches("a\\\\x{301}[\\\\s\\\\S]*", value)

            behavior f : (s: Marked) -> Int

            let f (s) = 1
            """;

    /** The code points are bounded by a rule and the length is measured by the body. */
    private static final String ZERO_SUM = """
            module example.zerosum

            data Silent = String
                invariant List.sum(String.codePoints(value)) == 0

            behavior f : (s: Silent) -> Int

            let f (s) =
                if String.length(s.value) >= 3 then 1 else 0
            """;

    /** A rule the reading cannot take in refuses every string, and the format alone leaves them all. */
    private static final String UNREAD_REFUSES_ALL = """
            module example.unread

            data Nothing = String
                invariant String.reverse(value) /= String.reverse(value)

            behavior f : (s: Nothing) -> Int

            let f (s) =
                if String.length(s.value) >= 3 then 1 else 0
            """;

    /** No value of the element exists, and the empty list is a value of the input all the same. */
    private static final String NO_ELEMENT_EXISTS = """
            module example.noelement

            data Never = String
                invariant String.matches("a\\\\x{301}.*", value)

            data Holder = { items: List<Never>, n: Int }

            behavior f : (h: Holder) -> Int

            let f (h) =
                if h.n >= 10 then 1 else 0
            """;

    @Test
    void aLengthIsNotProvedWhereARuleBoundsTheCodePointsApart() {
        List<BorderAssessment.Point> points = owedPoints(ZERO_SUM, "example.zerosum");
        assertTrue(onNumberNamed(points, "3").findAny().isPresent(),
                "the body draws a line on the length: " + labels(points));
        assertFalse(provedAny(onNumberNamed(points, "3").toList()),
                "a string of three code points has a sum of more than nought");
    }

    @Test
    void nothingIsProvedOfAPositionWhoseRulesWereNotReadInFull() {
        List<BorderAssessment.Point> points = owedPoints(UNREAD_REFUSES_ALL, "example.unread");
        assertFalse(provedAny(points), "a rule not read may refuse every string the format leaves");
    }

    @Test
    void aPositionNoRowNeedsToHoldAValueIsNotWhatKeepsAnotherFromTheProof() {
        List<BorderAssessment.Point> points = owedPoints(NO_ELEMENT_EXISTS, "example.noelement");
        assertFalse(points.isEmpty(), "the body draws a line on n");
        assertTrue(provedAny(points), "the empty list is a value, so a row at the edge is written");
    }

    @Test
    void aStringNoRuleIsWrittenAboutReachesEveryLength() {
        List<BorderAssessment.Point> points = owedPoints(ANY, "example.any");
        assertFalse(points.isEmpty(), "the body draws a line on the length");
        assertTrue(provedAny(points), "the control: every length is a length of some string");
    }

    @Test
    void aFormatWithAGapInItsLengthsProvesNoEdgeTheBodyDrawsOnThem() {
        List<BorderAssessment.Point> points = owedPoints(GAPS, "example.gaps");
        assertFalse(points.isEmpty(), "the body draws a line on the length");
        assertFalse(provedAny(points), "there is no string of length three");
    }

    @Test
    void aSetOfEveryStringButOneProvesNoEdgeOnTheLengthOfThatOne() {
        List<BorderAssessment.Point> points = owedPoints(NOT_EMPTY, "example.notempty");
        assertFalse(points.isEmpty(), "the body draws a line on the length");
        assertFalse(provedAny(points), "there is no string of length nought");
    }

    @Test
    void aRunWhoseEndIsNotAValueStaysAmongTheRulesThatDrewNoLine() {
        String report = human(MARKED);
        assertFalse(report.contains("no line: invariant Marked"),
                "the strings are a run, so this is not a rule that draws no line: " + report);
        assertTrue(report.contains("no line can be drawn on here"),
                "what was not established about the run is said: " + report);
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return souther.compiler.report.AdequacyReport.of(compilation).human(
                souther.compiler.diag.SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The points a line on a number whose name holds {@code fragment} is owed. A rule on one
     *  number draws lines of its own, and those are not what the body asked about. */
    private static java.util.stream.Stream<BorderAssessment.Point> onNumberNamed(
            List<BorderAssessment.Point> points, String fragment) {
        return points.stream().filter(p -> String.valueOf(p.asked()).contains(fragment));
    }

    private static List<String> labels(List<BorderAssessment.Point> points) {
        return points.stream().map(p -> String.valueOf(p.asked())).toList();
    }

    private static boolean provedAny(List<BorderAssessment.Point> points) {
        return points.stream().anyMatch(p -> p.owed().writabilityEvidence()
                .has(ItemAssessment.WritabilityEvidence.Ground.IT_IS_PROVED));
    }

    private static List<BorderAssessment.Point> owedPoints(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        return BorderAssessment.pointsOf(boundaries.get("f")).stream()
                .filter(p -> p.owed() != null).toList();
    }
}
