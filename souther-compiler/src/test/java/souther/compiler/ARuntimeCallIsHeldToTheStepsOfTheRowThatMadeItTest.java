package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Counting;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call the evaluated code makes into the runtime spends the row's steps as it works, and is stopped
 * by them part of the way through.
 *
 * <p>Each pair of rows here builds the same long text and then makes one call over it: in one row a
 * call that goes over the whole text — a match the whole text is read for, a search that finds
 * nothing — and in the other the same kind of call answered at the first character. The generated
 * code around the call has no loop of its own, so what the first row spends beyond the second is
 * what its call spent, and a call that passed no checkpoint would leave the two rows costing the
 * same.
 */
class ARuntimeCallIsHeldToTheStepsOfTheRowThatMadeItTest {

    /** How long a text the rows build. */
    private static final int LONG = 100_000;

    private static String row(String call, boolean answer) {
        return """
                module example.calling
                data Length = Int
                data Out = Bool
                behavior run : (n: Length) -> Out constructs Out
                let run (n) = Out(%s)
                example run
                  | "a long text": (Length(%d)) -> Out(%s)
                """.formatted(call.formatted("String.repeat(n.value, \"a\")"), LONG, answer);
    }

    /** A match the whole text is read for, and one decided by its first character. */
    private static final String MATCHES_ALL = row("String.matches(\"a*\", %s)", true);
    private static final String MATCHES_NONE = row("String.matches(\"b\", %s)", false);

    /** A search that goes over the whole text and finds nothing, and a test of its first character. */
    private static final String SEARCHES_ALL = row("String.contains(\"b\", %s)", false);
    private static final String SEARCHES_NONE = row("String.startsWith(\"b\", %s)", false);

    private static EvaluationPolicy holdingTo(long steps) {
        return EvaluationPolicy.of(steps).withCompilerTimeout(Duration.ofSeconds(30));
    }

    private static RowOutcome onlyRowOf(String source, EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.withEvaluationPolicy(policy);
        compilation.answerEverything();
        SourceId sourceId = compilation.exampleSourcesOf("example.calling").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.calling", sourceId, ArmObservation.OMIT)).value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    private static long spentWithRoom(String source) {
        RowOutcome row = onlyRowOf(source, holdingTo(EvaluationPolicy.DEFAULT_STEP_LIMIT));
        assertEquals(Disposition.HELD, row.disposition(), row.toString());
        return assertInstanceOf(Counting.Read.class, row.run().counting()).steps();
    }

    @Test
    void aMatchSpendsTheTextItReads() {
        long whole = spentWithRoom(MATCHES_ALL);
        long first = spentWithRoom(MATCHES_NONE);

        // The one reads every character and the other the first, which is all but one of them more.
        assertTrue(whole - first >= LONG - 1L,
                "reading " + (LONG - 1L) + " characters more cost " + (whole - first) + " steps more");
    }

    @Test
    void aSearchSpendsTheTextItGoesOver() {
        long whole = spentWithRoom(SEARCHES_ALL);
        long first = spentWithRoom(SEARCHES_NONE);

        assertTrue(whole - first >= LONG - 1L,
                "going over " + (LONG - 1L) + " characters more cost " + (whole - first) + " steps more");
    }

    /**
     * Given steps enough to build the text and not to read it all, the match is stopped part of the
     * way through, and the row decided at the first character holds with the same allowance.
     */
    @Test
    void aMatchIsStoppedByTheStepsInsideTheCall() {
        long building = spentWithRoom(MATCHES_NONE);
        EvaluationPolicy between = holdingTo(building + LONG / 2);

        RowOutcome stopped = onlyRowOf(MATCHES_ALL, between);
        assertEquals(Disposition.INCOMPLETE, stopped.disposition(), stopped.toString());
        assertEquals(FailurePhase.STEP_LIMIT, stopped.failurePhase());
        assertEquals(Disposition.HELD, onlyRowOf(MATCHES_NONE, between).disposition());
    }

    @Test
    void aSearchIsStoppedByTheStepsInsideTheCall() {
        long building = spentWithRoom(SEARCHES_NONE);
        EvaluationPolicy between = holdingTo(building + LONG / 2);

        RowOutcome stopped = onlyRowOf(SEARCHES_ALL, between);
        assertEquals(Disposition.INCOMPLETE, stopped.disposition(), stopped.toString());
        assertEquals(FailurePhase.STEP_LIMIT, stopped.failurePhase());
        assertEquals(Disposition.HELD, onlyRowOf(SEARCHES_NONE, between).disposition());
    }
}
