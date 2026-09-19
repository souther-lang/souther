package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule cutting a position where no carrier counts is answered for, wherever the cut can stand.
 *
 * <p>A quotient puts a fraction where a rule compares, and a third is no value of either carrier.
 * What the geometry does with such a line is decline it — the border is there and no row is owed at
 * it — and declining is an answer a reader gets. Reaching one as a premise instead, the compile of a
 * model nothing is wrong with ends where the level was asked for a place it is not.
 *
 * <p><b>Over the roles a number can be in, and not over the one that was found.</b> A line lands in
 * a rule at the threshold, inside a coefficient, on either side of a comparison, and on a quantity
 * whose own lattice it makes fractional; both carriers hold it, and every operator an author can
 * write reaches it by a different arm. The shapes are crossed rather than sampled, because which of
 * them a level survives is what this is about — held on one, a reading that answered for the
 * threshold alone would pass.
 *
 * <p><b>And what is asked for is the report and not the absence of a throw.</b> A harness that
 * compiled nothing would see no throw either, so one model here is held to drawing a line: it is
 * the same matrix under a claim that cannot be met by falling silent.
 */
class ALineAtANumberNoCarrierCountsToIsAnsweredForTest {

    /** The rules over one position, each written with an operator put in. */
    private static final List<String> ONE_POSITION = List.of(
            "n %s 1 / 3",
            "n %s 2 / 3",
            "n %s 1 / 7",
            "n %s -1 / 3",
            "1 / 3 * n %s 2",
            "n / 3 %s 2",
            "n / 3 %s 1 / 3");

    /** And over two, where a third is a coefficient and where it is on both sides at once. */
    private static final List<String> TWO_POSITIONS = List.of(
            "m %s -1 / 3 * n + 30",
            "m / 3 %s n / 3",
            "n / 3 + m / 6 %s 1 / 2");

    /** Every operator a rule over two numbers can be written with. The disequality is not one this
     *  language writes, so it is not one an author reaches a line at a third by. */
    private static final List<String> OPERATORS = List.of("<", "<=", ">", ">=", "==");

    /**
     * Every one of them is answered for.
     *
     * <p>Counted rather than asserted one at a time: what a reader needs is every rule this could
     * not answer for, and a run that stopped at the first of them says one model and leaves the
     * population it was standing for unmeasured.
     */
    @Test
    void everyRuleCuttingAPositionAtSuchANumberIsAnsweredFor() {
        List<String> unanswered = new ArrayList<>();
        int asked = 0;
        for (String type : List.of("Int", "Decimal")) {
            for (String operator : OPERATORS) {
                for (String shape : ONE_POSITION) {
                    asked++;
                    unanswered.addAll(answeredFor(onePosition(type, shape.formatted(operator))));
                }
                for (String shape : TWO_POSITIONS) {
                    asked++;
                    unanswered.addAll(answeredFor(twoPositions(type, shape.formatted(operator))));
                }
            }
        }
        assertEquals(List.of(), unanswered);
        assertEquals(2 * OPERATORS.size() * (ONE_POSITION.size() + TWO_POSITIONS.size()), asked,
                "every shape was crossed with every operator on both carriers");
    }

    /**
     * And the matrix is one a silent reading could not pass.
     *
     * <p>The measurement beside the sweep. A third on a whole-numbered position parts it between two
     * whole numbers, which is a line with points either side — so a harness that answered for every
     * model by compiling none of them fails here.
     */
    @Test
    void andAModelInItDrawsALine() {
        assertFalse(bordersOf(onePosition("Int", "n > 1 / 3")).isEmpty(),
                "a third parts the whole numbers");
    }

    /** What the report could not answer for in this model, which is nothing where it answered. */
    private static List<String> answeredFor(String model) {
        try {
            bordersOf(model);
            return List.of();
        } catch (RuntimeException e) {
            return List.of(model.lines().filter(line -> line.contains("guard")).findFirst()
                    .orElse("?").trim() + " — " + e);
        }
    }

    private static Map<String, BorderAssessment> bordersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), "example.form");
        Map<String, BorderAssessment> out = new java.util.LinkedHashMap<>();
        boundaries.values().forEach(each -> each.forEach(b -> out.put(b.label(), b)));
        return out;
    }

    private static String onePosition(String type, String guard) {
        return """
                module example.form

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: %s) -> Result
                    constructs Yes, No

                let f (n) = {
                    guard %s else No { why = 0 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (%s) -> No { why = 0 }
                """.formatted(type, guard, type.equals("Int") ? "0" : "0m");
    }

    private static String twoPositions(String type, String guard) {
        String value = type.equals("Int") ? "0" : "0m";
        return """
                module example.form

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: %s, m: %s) -> Result
                    constructs Yes, No

                let f (n, m) = {
                    guard %s else No { why = 0 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (%s, %s) -> No { why = 0 }
                """.formatted(type, type, guard, value, value);
    }
}
