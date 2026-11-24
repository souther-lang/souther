package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.meaning.CasesHeldTo;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeSymbol;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison of what a called behavior answers is a line the caller's runs place, drawn once for
 * each case its other side is chosen by, and a row stands on the line of its own case.
 *
 * <p>How long the answer is, a run of the call works out, and each row's run says it. Which number
 * it is compared with is the case's, so the same length is at the line in one case and beside it in
 * the other.
 */
class ALineTheRunsPlaceIsDrawnInEachCaseItsOtherSideIsChosenByTest {

    private static final String MODEL = """
            module m
            data Low
            data High
            data Level = Low | High
            let needed (level: Level): Int =
                match level with
                    | Low -> 1
                    | High -> 2
            behavior above : (xs: List<Int>) -> List<Int>
            let above (xs) = List.drop(1, List.reverse(xs))
            behavior enough : (xs: List<Int>, level: Level) -> Bool
            let enough (xs, level) = List.length(above(xs)) >= needed(level)
            example enough
                | "one above, one needed" : ([1, 2], Low) -> true
                | "one above, two needed" : ([1, 2], High) -> false
                | "two above, two needed" : ([1, 2, 3], High) -> true
            """;

    @Test
    void aRowStandsOnTheLineOfItsOwnCase() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);

        Set<String> met = new TreeSet<>();
        for (BorderAssessment.Point point : BorderAssessment.pointsOf(
                Adequacy.boundariesOf(compilation.db(), "m").get("enough"))) {
            if (point.owed() != null && point.owed().hasRowWitness()) {
                ExactRatio at = point.owed().criterion().anchor().asANumber();
                met.add(point.role() + " at " + at + " where " + caseOf(point));
            }
        }
        assertEquals(Set.of("ON at 0 where Low", "OFF at -1 where High", "ON at 0 where High"),
                met);
    }

    /** The one case the line of {@code point} is decided in. */
    private static String caseOf(BorderAssessment.Point point) {
        LineOrigin.ComparisonOrigin origin =
                (LineOrigin.ComparisonOrigin) point.border().border().origin();
        Set<String> named = new TreeSet<>();
        CasesHeldTo.of(origin.part().orElseThrow().decides()).forEach((_, held) -> {
            if (held instanceof CasesHeldTo.Held.OneOf(var cases)) {
                cases.leavesOfASum().forEach(leaf ->
                        named.add(((TypeSymbol.AtModule) leaf).name()));
            }
        });
        return String.join("|", named);
    }
}
