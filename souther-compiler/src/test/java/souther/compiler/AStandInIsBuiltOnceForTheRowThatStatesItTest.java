package souther.compiler;

import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row states of a stand-in and what the run applies the behavior with come of one reading.
 *
 * <p>A stand-in is written as a value, and a value is built by applying whatever helpers it names.
 * The run needs it as something the behavior can be constructed with, and the row needs it as values
 * an output can be handed; read twice, the helpers behind it run twice — charged twice against the
 * row's budget, and doing whatever they do twice.
 *
 * <p>Counted rather than argued. What a row spends is what this compile counted its generated code
 * through, fixtures and application alike, so a helper applied a second time is a second helping of
 * steps and shows up here as one.
 */
class AStandInIsBuiltOnceForTheRowThatStatesItTest {

    /**
     * Three rows of one behavior, differing in where the work is.
     *
     * <p>The first states nothing costly, the second spends a helper building an input, and the
     * third spends the same helper building what stands in for the dependency. So what the third
     * costs over the first is what building a stand-in costs, and the second says what one
     * application of that helper is.
     */
    private static final String MODEL = """
            module example.once

            data N = Int
            data Out = Int
            data Rate = Int

            partial let spin (n: Int): Int = if n == 0 then 0 else spin(n - 1)

            behavior rateFor : () -> Rate

            behavior run : (n: N) -> Out
                depends on rateFor
                constructs Out

            let run (n, rateFor) = Out(n.value + rateFor().value)

            fake rateFor
                | _ -> Rate(1)

            example run
              | "nothing costly" : (N(0)) -> Out(1)
              | "a helper in an input" : (N(spin(1000))) -> Out(1)
              | "the same helper in the stand-in" : (N(0)) with rateFor = Rate(spin(1000)) -> Out(0)
            """;

    @Test
    void aStandInCostsWhatBuildingItOnceCosts() {
        List<RowOutcome> rows = rowsOf(MODEL);
        assertEquals(3, rows.size(), () -> "the rows read are " + rows);

        long cheap = steps(rows.get(0));
        long inAnInput = steps(rows.get(1));
        long inTheStandIn = steps(rows.get(2));

        // The premise of the measurement, measured: a helper that cost nothing would make every
        // comparison below hold whatever the reading did.
        long once = inAnInput - cheap;
        assertTrue(once > 500, () -> "one application of the helper costs " + once
                + " steps, so nothing below is being told apart by it");

        long standingIn = inTheStandIn - cheap;
        assertTrue(standingIn > once / 2, () -> "the stand-in cost " + standingIn + " steps and"
                + " building it once costs " + once + ": the helper it names did not run");
        assertTrue(standingIn < once * 3 / 2, () -> "the stand-in cost " + standingIn + " steps and"
                + " building it once costs " + once + ": it was built more than once");
    }

    /** What a row spent: the counted work of its whole evaluation, fixtures and application alike. */
    private static long steps(RowOutcome row) {
        return assertInstanceOf(Counting.Read.class, row.run().counting(),
                "the row came back, so its counting was read").steps();
    }

    private static List<RowOutcome> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.withEvaluationPolicy(
                EvaluationPolicy.of(10_000_000L).withOuterTimeout(Duration.ofSeconds(30)));
        compilation.answerEverything();
        SourceId sourceId = compilation.exampleSourcesOf("example.once").getFirst();
        return compilation.db()
                .ask(new Output.Examples("example.once", sourceId, ArmObservation.OMIT)).value()
                .rows();
    }
}
