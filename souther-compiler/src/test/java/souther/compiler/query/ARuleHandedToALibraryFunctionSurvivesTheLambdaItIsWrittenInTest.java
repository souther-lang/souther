package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rule handed to a library function stays the rule that was handed when the call is written
 * inside a lambda another library function applies.
 *
 * <p>The call to {@code List.filter} is expanded where it is written, and the lambda it stands in
 * is then copied into the expansion of {@code List.flatMap}. Every owner in the copy is moved under
 * the owner the copy has, so the fork of {@code filter} the copy carries stands in an owner the
 * record of what {@code filter} was handed was never filed under. Nothing then said which rule the
 * fork decides by, and the arms of every {@code filter} written that way were put out of the count
 * as arms nothing tells apart.
 */
class ARuleHandedToALibraryFunctionSurvivesTheLambdaItIsWrittenInTest {

    private static final String MODULE = "example.rules";

    private static Adequacy.BranchEvidence arms(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.BranchEvidence said = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("sweep");
        assertNotNull(said, "the model under test compiles");
        return said;
    }

    private static String sweep(String filters) {
        return """
                module example.rules

                data Hit = { limit: Int, n: Int }

                behavior sweep : (days: List<Int>, limits: List<Int>) -> List<Hit>

                let sweep (days, limits) =
                    List.flatMap(limit ->
                        %s,
                        limits)

                example sweep
                    | "none" : ([], []) -> []
                """.formatted(filters);
    }

    private static final String ONE = """
            days
                            |> List.map(n -> Hit { limit = limit, n = n })
                            |> List.filter(h -> h.n > h.limit)""";

    private static final String TWO = """
            days
                            |> List.map(n -> Hit { limit = limit, n = n })
                            |> List.filter(h -> h.n > h.limit)
                            |> List.filter(h -> h.n < 100)""";

    /** The control: written beside nothing, the call is one fork and settled. */
    @Test
    void aFilterWrittenOutsideAnyLambdaIsSettled() {
        Adequacy.BranchEvidence evidence = arms("""
                module example.rules

                data Hit = { limit: Int, n: Int }

                behavior sweep : (days: List<Int>, limits: List<Int>) -> List<Hit>

                let sweep (days, limits) =
                    days
                        |> List.map(n -> Hit { limit = 1, n = n })
                        |> List.filter(h -> h.n > h.limit)

                example sweep
                    | "none" : ([], []) -> []
                """);

        assertEquals(List.of(), evidence.arms().exclusions());
    }

    @Test
    void aFilterWrittenInALambdaAnotherFunctionAppliesIsSettled() {
        Adequacy.BranchEvidence evidence = arms(sweep(ONE));

        assertEquals(List.of(), evidence.arms().exclusions(),
                () -> "the rule handed to `filter` is the one written, wherever the lambda is"
                        + " copied to: " + evidence.arms().exclusions());
    }

    /**
     * And what is moved is still told apart: two rules written in that lambda are two obligations,
     * so the second `filter` adds the two arms of its own.
     */
    @Test
    void twoRulesWrittenInThatLambdaAreTwoObligations() {
        int one = arms(sweep(ONE)).arms().counted();
        int two = arms(sweep(TWO)).arms().counted();

        assertEquals(one + 2, two,
                "the second rule is a fork of its own, not the first one counted again");
    }
}
