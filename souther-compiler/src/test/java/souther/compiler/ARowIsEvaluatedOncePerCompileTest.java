package souther.compiler;

import souther.compiler.examples.Deadline;
import souther.compiler.execute.jvm.JvmDeadlines;
import souther.compiler.execute.jvm.JvmExampleDeadlines;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row is run once, whatever the compile was asked to measure.
 *
 * <p>Running it twice — once to check it and again to see which arms it took — put one row in front
 * of two different sets of bytecode on two separate waits, each free to answer differently. Two sets
 * of outcomes for one model can disagree, and a report built from both says a case is verified and
 * its branch unreached in the same breath. What a measurement needs beyond a compile is recorded
 * while the row runs, not by running it again.
 */
class ARowIsEvaluatedOncePerCompileTest {

    private static final String MODEL = """
            module example.once

            data N = Int
            data Ok = { n: N }
            data Refused = { why: String }

            behavior take : (n: N) -> Ok | Refused
                constructs Ok, Refused

            let take (n) = if n.value > 0 then Ok { n = n } else Refused { why = "not positive" }

            example take
                | "positive" : (N(1)) -> Ok { n = N(1) }
                | "zero"     : (N(0)) -> Refused { why = "not positive" }
            """;

    /** Every piece of work the compile gave a deadline to, in the order it was given one. */
    private static List<Deadline.Work> workOf(Adequacy.Asked measure) {
        List<Deadline.Work> given = new ArrayList<>();
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.withJvmExampleDeadlines(recording(given));
        compilation.measure(measure);
        compilation.answerEverything();
        return given;
    }

    /** The build's own arrangement, with each piece of work written down as it is handed over. It
     *  is asked for the wait this compilation was given, the way the build asks for it. */
    private static JvmExampleDeadlines recording(List<Deadline.Work> into) {
        JvmExampleDeadlines build = JvmDeadlines.onWorkers();
        return compilerTimeout -> {
            Deadline inner = build.forThisCompile(compilerTimeout);
            return new Deadline() {

                @Override
                public Duration timeout() {
                    return inner.timeout();
                }

                @Override
                public <T> Outcome<T> given(Work work, Callable<T> body) {
                    synchronized (into) {
                        into.add(work);
                    }
                    return inner.given(work, body);
                }
            };
        };
    }

    private static long rowsRunIn(Adequacy.Asked measure) {
        return workOf(measure).stream().filter(w -> w instanceof Deadline.Work.WholeRow).count();
    }

    /** Two rows, two evaluations — not four. */
    @Test
    void everyRowRunsOnceWhenNothingIsMeasured() {
        assertEquals(2, rowsRunIn(Adequacy.Asked.NOTHING));
    }

    /**
     * And once when the arms are measured too.
     *
     * <p>This is the count that used to double. Asking what the rows covered ran all of them a second
     * time, against instrumented classes, and the second run was held to its own wait — so a compile
     * that measured could report a row the same compile had just seen hold.
     */
    @Test
    void everyRowStillRunsOnceWhenTheArmsAreMeasured() {
        assertEquals(2, rowsRunIn(Adequacy.Asked.fullReport()));
    }

    /** The measurement still gets what it asks for: a compile that measures reads the arms. */
    @Test
    void measuringStillReadsTheArmsTheRowsTook() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        Adequacy.Of measured = compilation.adequacy("example.once");

        assertEquals(List.of(), measured.branches().get("take").unreached().orElseThrow(),
                "both arms of `take` were taken, and both were recorded");
    }
}
