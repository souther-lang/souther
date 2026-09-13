package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number several values answer is composed beside another location being fixed, like any other.
 *
 * <p>How many values answer a number says which of them a realizer offers and says nothing about
 * whether the one it offers is right: every value built for a number reads back as that number,
 * one way round and not as an inverse. A composer refusing to try because the number is met by
 * several was reading the first fact as the second.
 *
 * <p><b>What is held here is the permission and not the promise.</b> That the value built answers
 * the number is {@code WhatIsRealizedForANumberReadsBackAsThatNumberTest}'s, stated of the
 * realizer alone; that a candidate landing elsewhere is refused and the search goes on is
 * {@code ARowIsOfferedForAPointOnlyWhereItStandsThereTest}'s. This one holds that the composer
 * asks at all. Written to re-prove the others, a failure here would not say which of the three
 * broke.
 *
 * <p>The row is read again after it is composed, so a point that comes back answered is a point
 * whose row was found standing at it — which is why the rows below are asserted and no reading of
 * them is done here.
 */
class AManyValuedNumberIsComposedBesideAnotherLocationTest {

    /** How long a list is, beside a position whose number is what that position holds. */
    private static final String A_COUNT_BESIDE_A_VALUE = """
            module example.counted

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (xs: List<Int>, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let f (xs, n) = {
                guard List.length(xs) < n else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** Two numbers several values each answer, at two locations. */
    private static final String A_MEASURE_BESIDE_A_MEASURE = """
            module example.sized

            data Yes = { v: Int }
            data No = { why: Int }

            behavior cmp : (a: String, b: String) -> Yes | No
                constructs Yes
                constructs No

            let cmp (a, b) = {
                guard String.length(a) > String.length(b) else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /**
     * The same shape over numbers one value each answers, which always composed.
     *
     * <p>The baseline, so that the two above are read as the composer treating them alike rather
     * than as everything passing. A number that is what a position holds was never refused here.
     */
    private static final String A_VALUE_BESIDE_A_VALUE = """
            module example.plain

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (m: Int, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let f (m, n) = {
                guard m < n else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    @Test
    void aNumberSeveralValuesAnswerIsComposedForLikeOneValueAnswers() {
        for (String model : List.of(A_COUNT_BESIDE_A_VALUE, A_MEASURE_BESIDE_A_MEASURE,
                A_VALUE_BESIDE_A_VALUE)) {
            assertEquals(List.of(), whatNothingCouldShow(model),
                    () -> "every point of this line has a row composed for it:\n" + model);
        }
    }

    /**
     * And the rows offered put the lengths where the line is, which is what being composed for the
     * point comes to.
     *
     * <p>Asserted as the values rather than as the count of them: a row for each point and each of
     * them at a different place is the thing that would be missing if one value were written for
     * every point of the line.
     */
    @Test
    void theRowsOfferedStandWhereTheLineIs() {
        String counted = generated(A_COUNT_BESIDE_A_VALUE);

        for (String row : List.of("([], 1)", "([], 0)", "([], 2)", "([0], 0)")) {
            assertTrue(counted.contains(row),
                    () -> "the row for one of the four points: " + counted);
        }
        String sized = generated(A_MEASURE_BESIDE_A_MEASURE);
        assertTrue(sized.contains("(\"x\", \"\")") && sized.contains("(\"\", \"\")"),
                () -> "one longer by a character, and two of one length: " + sized);
    }

    private static List<String> whatNothingCouldShow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing could show a row can be written at the ")) {
                found.add(line.trim());
            }
        }
        return found;
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static String human(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String generated(String model) {
        Compilation compilation = measured(model);
        return GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }
}
