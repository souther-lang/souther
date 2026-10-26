package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that compares a number of a string with one past what a String holds owes no point on the
 * side no String reaches.
 *
 * <p>A String holds no more than 268435455 code points, so a length never passes what that comes
 * to, nor does a sum of lengths pass the sum of what each can be. That is where the values stop and
 * not a distinction a model made: it settles which points can be written and divides nothing, so
 * the longest string is no class of a position and no line of its own.
 */
class ALineBeyondWhatAStringHoldsIsNoLineTest {

    private static final long LONGEST = 268435455L;

    private static Compilation measured(String parameters, String body) {
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (%s) -> Bool
                let f (%s) = %s
                """.formatted(parameters, parameters.replaceAll(": *\\w+", ""), body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return compilation;
    }

    /** What each point of each line of the behavior is owed, by the role it plays. */
    private static List<Map<PointRole, ItemAssessment>> linesOf(String parameters, String body) {
        Compilation compilation = measured(parameters, body);
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), "m");
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.get("f").stream().map(border -> {
            Map<PointRole, ItemAssessment> byRole = new LinkedHashMap<>();
            for (BorderAssessment.Point point : BorderAssessment.pointsOf(List.of(border))) {
                byRole.put(point.role(), point.item());
            }
            return byRole;
        }).toList();
    }

    private static String report(String parameters, String body) {
        Compilation compilation = measured(parameters, body);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static boolean noValueStands(ItemAssessment item) {
        return item instanceof ItemAssessment.NotOwed;
    }

    private static boolean owed(ItemAssessment item) {
        return item instanceof ItemAssessment.Owed;
    }

    /** The side a comparison holds on has no String, so its points are not owed; the side it fails
     *  on has them, and a row there still shows which way the behavior goes. */
    @Test
    void aLengthPastTheLongestStringOwesNothingOnTheSideNoStringReaches() {
        for (String body : new String[] {"String.length(s) >= 268435456",
                "String.length(s) > 268435455"}) {
            List<Map<PointRole, ItemAssessment>> lines = linesOf("s: String", body);

            assertEquals(1, lines.size(), body);
            Map<PointRole, ItemAssessment> points = lines.getFirst();
            assertTrue(noValueStands(points.get(PointRole.ON)), body + " " + points);
            assertTrue(noValueStands(points.get(PointRole.IN)), body + " " + points);
            assertTrue(owed(points.get(PointRole.OFF)), body + " " + points);
            assertTrue(owed(points.get(PointRole.OUT)), body + " " + points);
        }
    }

    @Test
    void theSameFromTheOtherSide() {
        List<Map<PointRole, ItemAssessment>> lines =
                linesOf("s: String", "String.length(s) < 268435456");

        Map<PointRole, ItemAssessment> points = lines.getFirst();
        assertTrue(owed(points.get(PointRole.ON)), points.toString());
        assertTrue(owed(points.get(PointRole.IN)), points.toString());
        assertTrue(noValueStands(points.get(PointRole.OFF)), points.toString());
        assertTrue(noValueStands(points.get(PointRole.OUT)), points.toString());
    }

    @Test
    void theLongestStringIsAValueOfTheLengthAtItsEnd() {
        Map<PointRole, ItemAssessment> points =
                linesOf("s: String", "String.length(s) >= 268435455").getFirst();

        assertTrue(owed(points.get(PointRole.ON)), points.toString());
    }

    @Test
    void aLengthBelowTheLongestStringOwesAllFourPoints() {
        Map<PointRole, ItemAssessment> points =
                linesOf("s: String", "String.length(s) >= 3").getFirst();

        for (PointRole role : PointRole.values()) {
            assertTrue(owed(points.get(role)), role + " " + points);
        }
    }

    /** A form of several lengths is held to what each can be, whichever way it adds them up. */
    @Test
    void twoLengthsAddedPassTwiceTheLongestOnlyWhereNoStringIs() {
        Map<PointRole, ItemAssessment> past = linesOf("a: String, b: String",
                "String.length(a) + String.length(b) > " + 2 * LONGEST).getFirst();
        Map<PointRole, ItemAssessment> within = linesOf("a: String, b: String",
                "String.length(a) + String.length(b) > " + (2 * LONGEST - 1)).getFirst();

        assertTrue(noValueStands(past.get(PointRole.ON)), past.toString());
        assertTrue(noValueStands(past.get(PointRole.IN)), past.toString());
        assertTrue(owed(within.get(PointRole.ON)), within.toString());
    }

    @Test
    void aLengthLessAnotherPassesTheLongestOnlyWhereNoStringIs() {
        Map<PointRole, ItemAssessment> past = linesOf("a: String, b: String",
                "String.length(a) - String.length(b) >= " + (LONGEST + 1)).getFirst();
        Map<PointRole, ItemAssessment> within = linesOf("a: String, b: String",
                "String.length(a) - String.length(b) >= " + LONGEST).getFirst();

        assertTrue(noValueStands(past.get(PointRole.ON)), past.toString());
        assertTrue(owed(within.get(PointRole.ON)), within.toString());
    }

    /** A weight multiplies what each can be. */
    @Test
    void twiceALengthPassesTwiceTheLongestOnlyWhereNoStringIs() {
        Map<PointRole, ItemAssessment> past = linesOf("s: String",
                "2 * String.length(s) > " + 2 * LONGEST).getFirst();

        assertTrue(noValueStands(past.get(PointRole.ON)), past.toString());
    }

    /** The longest string is where Strings stop and not a case two lengths part company at: the
     *  classes of a relation between them are the ones it had before there was a longest. */
    @Test
    void theLongestStringIsNoClassOfARelationBetweenTwoLengths() {
        String report = report("a: String, b: String", "String.length(a) > String.length(b)");

        assertFalse(report.contains(String.valueOf(LONGEST)), report);
        assertFalse(report.contains("axes 2"), report);
    }

    /** And of one rule on one length, where the ends of the run are what the rules leave. */
    @Test
    void theLongestStringIsNoClassOfALengthAnyRuleCutsInTwo() {
        String report = report("s: String", "String.length(s) >= 3");

        assertFalse(report.contains(String.valueOf(LONGEST)), report);
    }

    /** A line past the longest takes nothing from the line beside it on the same length. */
    @Test
    void aLinePastTheLongestDoesNotTakeTheProofFromTheLineBesideIt() {
        String declared = """
                module m

                data Named = String
                    invariant String.length(value) >= 3

                behavior f : (s: Named) -> Bool
                let f (s) = String.length(s.value) >= %s
                """;
        long pastAndProved = proved(declared.formatted(LONGEST + 1), "= 3");
        long besideAndProved = proved(declared.formatted(7), "= 3");

        assertEquals(besideAndProved, pastAndProved,
                "the declared line is proved writable whichever line the body draws beside it");
        assertTrue(pastAndProved > 0, "and it is proved");
    }

    private static long proved(String source, String fragment) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return Adequacy.searchedBoundariesOf(compilation.db(), "m").values().stream()
                .flatMap(each -> BorderAssessment.pointsOf(each).stream())
                .filter(point -> point.owed() != null)
                .filter(point -> String.valueOf(point.asked()).contains(fragment))
                .filter(point -> point.owed().writabilityEvidence()
                        .has(ItemAssessment.WritabilityEvidence.Ground.IT_IS_PROVED))
                .count();
    }
}
