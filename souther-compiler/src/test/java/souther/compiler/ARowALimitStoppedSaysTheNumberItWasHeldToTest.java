package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.WorkFigure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;

import java.time.Duration;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row stopped by one of the limits it is evaluated under says which limit, at the number this
 * run held it to.
 *
 * <p>One word covers the steps, the depth and the clock, because what a measure lost is the same for
 * all three. What a reader would widen is not, and only the run knows which of the three it was and
 * what it stood at. So each is asked of a run held to numbers of its own rather than the defaults:
 * a figure read off a default would agree with a run under the default and with nothing else.
 */
class ARowALimitStoppedSaysTheNumberItWasHeldToTest {

    /** A helper that tail-calls itself with the same argument, which the emitter compiles to a loop:
     *  it spends steps forever and never grows the stack. */
    private static final String LOOPS = """
            module example.loops
            data N = Int
            data Out = Int
            partial let spin (n: Int): Int = spin(n)
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(spin(n.value))
            example run
              | "loops": (N(1)) -> Out(0)
            """;

    /** A helper that calls itself before it adds, so every call is a frame deeper. */
    private static final String DESCENDS = """
            module example.loops
            data N = Int
            data Out = Int
            partial let down (n: Int): Int = down(n + 1) + 1
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(down(n.value))
            example run
              | "descends": (N(1)) -> Out(0)
            """;

    /** The steps, at whichever number the run was held to. */
    @Test
    void aRowThatSpentItsStepsSaysTheStepsItWasAllowed() {
        assertEquals(Optional.of(WorkFigure.EVALUATION_STEPS.at(10_000L)),
                figureOf(LOOPS, EvaluationPolicy.of(10_000L)
                        .withCompilerTimeout(Duration.ofSeconds(30))));
        assertEquals(Optional.of(WorkFigure.EVALUATION_STEPS.at(20_000L)),
                figureOf(LOOPS, EvaluationPolicy.of(20_000L)
                        .withCompilerTimeout(Duration.ofSeconds(30))),
                "the same row under another policy says that policy's number");
    }

    /** The depth, at the number the run was held to and not the default. */
    @Test
    void aRowThatWentTooDeepSaysTheDepthItWasAllowed() {
        assertEquals(Optional.of(WorkFigure.RECURSION_DEPTH.at(100L)),
                figureOf(DESCENDS, EvaluationPolicy.of(1_000_000L).withRecursionDepthLimit(100)
                        .withCompilerTimeout(Duration.ofSeconds(30))));
    }

    /**
     * The clock, at the wait the run gave the row, and carried to where the report reads it.
     *
     * <p>Asked of what the report reads rather than of the observation: a figure the row carried
     * and something on the way dropped is a figure nobody is told.
     */
    @Test
    void aRowThatStoppedAnsweringSaysTheWaitItWasGivenAllTheWayToTheReport() {
        Compilation compilation = Compilation.ofSource(LOOPS, "Main");
        compilation.withEvaluationPolicy(DoesNotComeBack.POLICY.withCompilerTimeout(
                DoesNotComeBack.WAIT));
        compilation.withJvmExampleDeadlines(DoesNotComeBack.overrunningOn(
                DoesNotComeBack.everythingAboutRowsOf("run")));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        List<Incompleteness.Met> gaps = AdequacyReport.of(compilation).modules().get(0)
                .behaviors().get(0).reading().gaps().stream().toList();
        assertEquals(1, gaps.size(), gaps::toString);
        assertEquals(Incompleteness.Code.ROW_EVALUATION_LIMIT_REACHED, gaps.get(0).fact().code());
        assertEquals(List.of(WorkFigure.COMPILER_TIME.at("100")), gaps.get(0).figures(),
                "the wait this compile gave the row, in the milliseconds it is written in");
    }

    /** The figure the one row of {@code source} was stopped at, under {@code policy}. */
    private static Optional<Figure> figureOf(String source, EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.withEvaluationPolicy(policy);
        compilation.answerEverything();
        SourceId sourceId = compilation.exampleSourcesOf("example.loops").getFirst();
        List<Incompleteness> gaps = compilation.db().ask(new Output.Examples("example.loops",
                sourceId, ArmObservation.OMIT)).value().incompleteness();
        assertEquals(1, gaps.size(), gaps::toString);
        assertEquals(Incompleteness.Code.ROW_EVALUATION_LIMIT_REACHED, gaps.get(0).code());
        return gaps.get(0).figure();
    }
}
