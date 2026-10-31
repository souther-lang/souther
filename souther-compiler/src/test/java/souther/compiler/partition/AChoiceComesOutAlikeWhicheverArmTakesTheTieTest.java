package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of a choice is read as the one function the choice is, whichever arm the tie
 * between its arms is given to: what each arm shows of how the comparison comes out is joined, a
 * row taking one arm, and the lines are where the joined answer changes.
 *
 * <p>{@code Decimal.min(x, 0.0m)} answers {@code x} where {@code x} is below nought, a run open at
 * nought, and {@code Decimal.min(0.0m, x)} answers it where {@code x} is at nought or below. On the
 * open run, {@code x <= c} is true whatever {@code x} is at the finest step below nought, so that
 * arm alone shows nothing of {@code c} there; the arm answering nought is false at every {@code c}
 * below nought, so the comparison comes out either way below nought and holding from nought up.
 */
class AChoiceComesOutAlikeWhicheverArmTakesTheTieTest {

    private static final List<String> THE_LESSER_OF_X_AND_NOUGHT = List.of(
            "Decimal.min(0.0m, x)", "Decimal.min(x, 0.0m)", "(if x < 0.0m then x else 0.0m)");

    /** The three spellings of the lesser of {@code x} and nought are read alike: nothing is left
     *  unshown, the one line on {@code c} is at nought, and the measurement is complete. */
    @Test
    void theLesserOfAValueAndNoughtIsReadAlikeHoweverItIsSpelled() {
        for (String lesser : THE_LESSER_OF_X_AND_NOUGHT) {
            Compilation compilation = compiled("", "x: Decimal, c: Decimal",
                    "Decimal.compare(" + lesser + ", c) <= 0", "");
            assertEquals(List.of(), unreadReasonsOf(measured(compilation)), lesser);
            assertEquals(List.of("0"), valuesOfTheLinesOn("f/c", linesOf(compilation)), lesser);
            assertTrue(human(compilation).contains("measurement: complete"), lesser);
        }
    }

    /** The greater of {@code x} and nought reads alike in both orders, as it did. */
    @Test
    void theGreaterOfAValueAndNoughtIsReadAlikeInBothOrders() {
        for (String greater : List.of("Decimal.max(0.0m, x)", "Decimal.max(x, 0.0m)")) {
            Compilation compilation = compiled("", "x: Decimal, c: Decimal",
                    "Decimal.compare(" + greater + ", c) <= 0", "");
            assertEquals(List.of(), unreadReasonsOf(measured(compilation)), greater);
            assertEquals(List.of("0"), valuesOfTheLinesOn("f/c", linesOf(compilation)), greater);
        }
    }

    /** Joined over the values the place holds and no others: with {@code c} declared at minus five
     *  or above, its end is the line the declaration draws and nothing is left unshown. */
    @Test
    void theArmsAreJoinedOverTheValuesThePlaceHolds() {
        Compilation compilation = compiled("""
                data Low = Decimal
                    invariant value >= -5.0m
                """, "x: Decimal, c: Low", "Decimal.compare(Decimal.min(x, 0.0m), c.value) <= 0",
                "");
        assertEquals(List.of(), unreadReasonsOf(measured(compilation)));
    }

    /**
     * The row below nought, where the comparison is false, is built: the arm answering nought, at
     * a {@code c} below it. Written out as an example with what it comes to, it is run, and holds.
     */
    @Test
    void theRowBelowNoughtIsBuiltAndRuns() {
        Compilation offering = compiled("", "x: Decimal, c: Decimal",
                "Decimal.compare(Decimal.min(x, 0.0m), c) <= 0", "");
        BorderAssessment atNought = linesOf(offering).stream()
                .filter(line -> line.axis().equals("f/c") && line.value().equals("0"))
                .findFirst().orElseThrow();
        List<String> below = rowAt(atNought, "InTheRegion[side=BELOW]");
        assertEquals(2, below.size(), below.toString());
        Compilation run = compiled("", "x: Decimal, c: Decimal",
                "Decimal.compare(Decimal.min(x, 0.0m), c) <= 0", """

                example f
                    | "below nought" : (%s) -> No
                """.formatted(String.join(", ", below)));
        String human = human(run);
        assertTrue(human.contains("rows 1"), human);
        assertTrue(!human.contains("does not hold"), human);
    }

    /**
     * With {@code x} declared at nought or above, the lesser is nought: no line is drawn from the
     * arm answering {@code x}, which no row reaches, and the line on {@code c} is the other's.
     */
    @Test
    void anArmNoRowReachesDrawsNothing() {
        Compilation compilation = compiled("""
                data NonNeg = Decimal
                    invariant value >= 0.0m
                """, "x: NonNeg, c: Decimal", "Decimal.compare(Decimal.min(x.value, 0.0m), c) <= 0",
                "");
        assertEquals(List.of(), unreadReasonsOf(measured(compilation)));
        List<BorderAssessment> lines = linesOf(compilation);
        assertEquals(List.of("0"), valuesOfTheLinesOn("f/c", lines));
        assertEquals(List.of(), valuesOfTheLinesOn("f/x", lines).stream()
                .filter(value -> !value.equals("0")).toList());
    }

    /**
     * A choice whose arms leave a value unshown the same way is reported as each arm leaves it:
     * {@code x <= c} below nought and {@code y <= c} for a {@code y} below nought both hold at the
     * finest step below nought whatever is taken, and neither arm shows the comparison failing
     * there.
     */
    @Test
    void aValueNoArmShowsIsStillSaidUnshown() {
        Compilation compilation = compiled("""
                data Neg = Decimal
                    invariant value < 0.0m
                """, "x: Decimal, y: Neg, c: Decimal",
                "Decimal.compare(if x < 0.0m then x else y.value, c) <= 0", "");
        assertTrue(unreadReasonsOf(measured(compilation))
                        .contains(UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                unreadReasonsOf(measured(compilation)).toString());
    }

    /**
     * A value the arms leave unshown between them is said unshown though every place what they
     * show changes is a line: with {@code c} below nought, {@code if x < 0.0m then x else -1.0m}
     * fails nowhere from minus one up that either arm shows — the arm answering {@code x} fails
     * at no {@code c} at the finest step below nought, the other at none from minus one — and the
     * line at minus one is the other arm's.
     */
    @Test
    void aValueTheArmsLeaveUnshownBetweenTheirLinesIsStillSaidUnshown() {
        Compilation compilation = compiled("""
                data Below = Decimal
                    invariant value < 0.0m
                """, "x: Decimal, c: Below",
                "Decimal.compare(if x < 0.0m then x else -1.0m, c.value) <= 0", "");
        assertTrue(unreadReasonsOf(measured(compilation))
                        .contains(UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                unreadReasonsOf(measured(compilation)).toString());
    }

    /** What the row built for {@code point} of {@code line} was written as, one text per input. */
    private static List<String> rowAt(BorderAssessment line, String point) {
        List<String> out = new ArrayList<>();
        line.items().forEach((at, item) -> {
            if (at.toString().equals(point) && item instanceof ItemAssessment.Owed owed) {
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified
                            && out.isEmpty()) {
                        certified.row().inputs().forEach(each -> out.add(each.text()));
                    }
                }
            }
        });
        return out;
    }

    private static List<String> valuesOfTheLinesOn(String axis, List<BorderAssessment> lines) {
        return lines.stream().filter(each -> each.axis().equals(axis))
                .map(BorderAssessment::value).distinct().toList();
    }

    private static String human(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).toString();
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static PartitionEvidence measured(Compilation compilation) {
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    /** The reasons that say a rule was not read, leaving out those that say it was read and
     *  divides no position. */
    private static List<UndividedPosition.Reason> unreadReasonsOf(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(PartitionEvidence.NotRead::reason).distinct()
                .filter(reason -> reason != UndividedPosition.Reason.RULE_RELATING_TWO_VALUES
                        && reason != UndividedPosition.Reason.RULE_ABOUT_A_RUN
                        && reason != UndividedPosition.Reason.RULE_NEVER_TURNS_ON_THIS_LINE)
                .toList();
    }

    /** {@code f} over {@code parameters}, guarded by {@code condition}, after the declarations
     *  {@code prelude} writes and with the examples after it. */
    private static Compilation compiled(String prelude, String parameters, String condition,
                                        String examples) {
        String names = String.join(", ", List.of(parameters.split(", ")).stream()
                .map(each -> each.substring(0, each.indexOf(':'))).toList());
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Ok
                data No

                %s

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                %s
                """.formatted(prelude, parameters, names, condition, examples), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
