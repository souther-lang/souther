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
        assertTrue(human(MARKED).contains("no line: invariant Marked"),
                "the rule restricts the position and places no line, and that is said");
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return souther.compiler.report.AdequacyReport.of(compilation).human(
                souther.compiler.diag.SourceRendering.namedByIdentity(compilation.texts()));
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
