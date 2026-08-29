package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.partition.Partitions;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A clause of the value a case was narrowed out of draws its line once, not once per case.
 *
 * <p>The reading of a value hands over the clauses that value's declarations wrote, and a case
 * narrowed out of it is a reading of its own. Both are opened, so the clause above is handed over by
 * the value that wrote it — asked for again from underneath, one rule would draw two lines and owe
 * two rows where the author wrote one thing.
 *
 * <p>Which is where handing over clauses parts from answering about a position. A position owes
 * every rule that reaches it, wherever it was written, because that is what a reader standing at the
 * position is asking. A reading owes the clauses it holds, because every reading that holds any is
 * opened.
 */
class AClauseAboveASumDrawsItsLineOnceTest {

    private static final String MODULE = "example.above";

    /**
     * The relation is written on the value the sum sits in, and both cases spread the fields.
     *
     * <p>So the clause reaches the positions under either case, and there are two of them for it to
     * be handed over from if anything asked underneath.
     */
    private static final String MODEL = """
            module example.above

            data Ok
            data Fast
            data Slow
            data Speed = Fast | Slow

            data Window =
                { how: Speed
                , opens: Int
                , closes: Int
                }
                invariant opens <= closes

            behavior read : (w: Window) -> Ok
            let read (w) = Ok

            example read | "x" : (Window { how = Fast, opens = 1, closes = 3 }) -> Ok
            """;

    private static Partitions.Partitioning divided() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided(MODULE, "read")).value();
        assertNotNull(divided, "the model under test compiles and is measured");
        return divided;
    }

    /** One clause, one line, however many readings the value it is written on is read under. */
    @Test
    void theClauseAboveDrawsOneLine() {
        List<?> between = divided().between();
        assertEquals(1, between.size(),
                () -> "the relation is one line and not one per reading: " + between);
    }
}
