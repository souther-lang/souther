package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.check.BehaviorAnswers.RunsAnswered;
import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a run stops in a behavior called is asked of the behavior over its own inputs, and where
 * the behavior is not shown to answer every run of a row, the caller's comparison over the call is
 * not said to be read to the end.
 *
 * <p>No body of a behavior is read where a call of it stands, so a stop in one is nothing a caller
 * reads; it is said by what the behavior answers of itself ({@link Adequacy.RunsAnsweredBy}). A
 * body that stops only past what the representation holds answers the runs of rows and is not
 * shown to answer every run there is: the two are told apart, since a proof of the second is not
 * made of the first.
 */
class ACallOfABehaviorIsGottenPastByTheRunsTheBehaviorAnswersTest {

    private static final String NOT_RESOLVED = "stop not resolved";

    /** A caller comparing what `made` answers, each of its two cases expected by a row. */
    private static final String CALLER = """

            data Out = Low | High
            behavior chosen : (n: Int) -> Out
            let chosen (n) = if made(n) >= 5 then Low else High
            example chosen
                | (40) -> Low
                | (2) -> High
            """;

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource("module m\n" + model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        return ACompiledModel.compiles(compilation);
    }

    private static String reportOf(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).only(null, behavior)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static RunsAnswered runsAnswered(Compilation compilation, String behavior) {
        return compilation.db().ask(new Adequacy.RunsAnsweredBy("m", behavior)).value();
    }

    private static boolean answersEveryRun(Compilation compilation, String behavior) {
        return runsAnswered(compilation, behavior) == RunsAnswered.EVERY_ONE;
    }

    /** A text and a list made one longer stop where the representation does: every run of a row
     *  is answered and not every run there is, in the body that makes it and in one that calls
     *  it. The caller's comparison is read, as it is beside the operation itself. */
    @Test
    void whereOnlyTheRepresentationStopsItTheRunsOfRowsAreAnsweredAndNotEveryRun() {
        Compilation compilation = measured("""
                behavior text : (s: String) -> String
                let text (s) = s ++ "x"
                behavior list : (xs: List<Int>) -> List<Int>
                let list (xs) = xs ++ [1]
                behavior through : (s: String) -> String
                let through (s) = text(s)
                data Out = Low | High
                behavior chosen : (xs: List<Int>) -> Out
                let chosen (xs) = if List.length(list(xs)) >= 3 then Low else High
                """);

        for (String behavior : new String[] {"text", "list", "through"}) {
            assertEquals(RunsAnswered.ALL_BUT_PAST_THE_REPRESENTATION,
                    runsAnswered(compilation, behavior), behavior);
        }
        assertFalse(reportOf(compilation, "chosen").contains(NOT_RESOLVED));
        assertTrue(reportOf(compilation, "list").contains("a run stops only where"));
    }

    @Test
    void aBehaviorThatMayStopLeavesTheCallersAccountOpen() {
        Compilation compilation = measured("""
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                """ + CALLER);
        String report = reportOf(compilation, "chosen");

        assertFalse(answersEveryRun(compilation, "made"));
        assertFalse(answersEveryRun(compilation, "chosen"), "it calls one that may stop");
        assertTrue(report.contains(NOT_RESOLVED), report);
        assertTrue(report.contains("measurement: partial"), report);
        assertFalse(report.contains("adequacy: satisfied"), report);
    }

    @Test
    void aBehaviorThatAnswersEveryRunLeavesNothingOpen() {
        Compilation compilation = measured("""
                behavior made : (n: Int) -> Int
                let made (n) = if n < 10 then 1 else 20
                """ + CALLER);
        String report = reportOf(compilation, "chosen");

        assertTrue(answersEveryRun(compilation, "made"));
        assertTrue(answersEveryRun(compilation, "chosen"));
        assertFalse(report.contains(NOT_RESOLVED), report);
        assertFalse(report.contains("not accounted for"), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /** The inputs it is asked over are the ones it declares, and not what a caller hands it. */
    @Test
    void theInputsItIsAskedOverAreTheBehaviorsOwn() {
        Compilation declared = measured("""
                data Divisor = Int
                    invariant value >= 1
                behavior made : (n: Divisor) -> Int
                let made (n) = Int.floorMod(100, n.value)
                """);
        Compilation handedAConstant = measured("""
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                behavior chosen : (n: Int) -> Int
                let chosen (n) = made(7) + n
                """);

        assertTrue(answersEveryRun(declared, "made"));
        assertFalse(answersEveryRun(handedAConstant, "made"));
        assertFalse(answersEveryRun(handedAConstant, "chosen"));
    }

    /** A value the body builds is asked by its definition, which is run where it is built. */
    @Test
    void aValueTheBodyReadsIsAskedByItsDefinition() {
        Compilation compilation = measured("""
                let limit: Int = {
                    let half = 3
                    half + half
                }
                behavior made : (n: Int) -> Int
                let made (n) = if n < 3 then limit else n
                let never: Int = {
                    let nought = limit - 6
                    Int.floorMod(100, nought)
                }
                behavior mayStop : (n: Int) -> Int
                let mayStop (n) = if n < 3 then never else n
                """);

        assertTrue(answersEveryRun(compilation, "made"));
        assertFalse(answersEveryRun(compilation, "mayStop"));
    }

    /** A sum past what an `Int` holds ends the run, and one its inputs are declared within does
     *  not: a range the author declares is what shows it. */
    @Test
    void anOperationIsAskedByTheNumbersItsInputsAreDeclaredWithin() {
        Compilation compilation = measured("""
                data Small = Int
                    invariant value >= 0 && value <= 1000
                behavior ofAny : (a: Int, b: Int) -> Int
                let ofAny (a, b) = a + b
                behavior ofSmall : (a: Small, b: Small) -> Int
                let ofSmall (a, b) = a.value + b.value
                """);

        assertFalse(answersEveryRun(compilation, "ofAny"));
        assertTrue(answersEveryRun(compilation, "ofSmall"));
    }

    /** One with no body in the model is not known to answer, called or injected. */
    @Test
    void aBehaviorWithNoBodyIsNotKnownToAnswer() {
        Compilation compilation = measured("""
                data Out = Low | High
                behavior made : (n: Int) -> Int
                behavior chosen : (n: Int) -> Out
                    depends on made
                let chosen (n, made) = if made(n) >= 5 then Low else High
                """);

        assertFalse(answersEveryRun(compilation, "made"));
        assertFalse(answersEveryRun(compilation, "chosen"));
        assertTrue(reportOf(compilation, "chosen").contains(NOT_RESOLVED));
    }

    /** One behavior called on several inputs is one answer about itself: each comparison over a
     *  call of it is left open, or none is. */
    @Test
    void aBehaviorCalledOnSeveralInputsIsOneAnswer() {
        Compilation compilation = measured("""
                data Out = Low | High
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                behavior twice : (a: Int, b: Int) -> Out
                let twice (a, b) = if made(a) >= 5 && made(b) >= 5 then Low else High
                example twice
                    | (40, 40) -> Low
                    | (40, 2) -> High
                """);
        String report = reportOf(compilation, "twice");

        assertEquals(2, report.lines().filter(line -> line.contains(NOT_RESOLVED)).count(), report);
        assertTrue(report.contains("measurement: partial"), report);
    }

    /** A measured caller reads it though the build does not measure the behavior called. */
    @Test
    void itIsAskedOfABehaviorTheBuildDoesNotMeasure() {
        Compilation compilation = Compilation.ofSource("""
                module m
                behavior made : (n: Int) -> Int
                let made (n) = if n < 10 then 1 else 20
                """ + CALLER, "Main");
        compilation.choose(new Adequacy.Choice(null, "chosen"));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);

        String report = reportOf(compilation, "chosen");
        assertFalse(report.contains(NOT_RESOLVED), report);
    }
}
