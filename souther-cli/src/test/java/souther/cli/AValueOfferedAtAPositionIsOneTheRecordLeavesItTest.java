package souther.cli;

import souther.cli.Main;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value offered at a position comes from what the record leaves that position.
 *
 * <p>A newtype's candidate has been read from there for a while. A bare {@code Int} or {@code Decimal}
 * had not: every primitive branch answered from the type and returned before what was left of the
 * position was looked at, so a field a clause bounds from below was offered a zero the record refuses
 * and the row it was part of never built.
 */
class AValueOfferedAtAPositionIsOneTheRecordLeavesItTest {

    private static String rowsFor(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-offered").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }

    private static String model(String clauses, String field) {
        return """
                module example.offered

                data R =
                    { a: FIELD
                    , b: FIELD
                    }
                CLAUSES

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """.replace("CLAUSES", clauses).replace("FIELD", field);
    }

    /**
     * The projection exists and was being discarded.
     *
     * <p>{@code a >= 0} beside {@code a < b} leaves {@code b} at 1 and above. Read, the row builds;
     * discarded, both fields are offered a zero and {@code a < b} refuses the only pair there was.
     */
    @Test
    void aFieldTheRecordBoundsFromBelowIsOfferedAValueAboveIt() throws Exception {
        String rows = rowsFor(model("""
                    invariant lower = a >= 0
                    invariant ordered = a < b""", "Int"));

        assertTrue(rows.contains("R { a = 0, b = 1 }"),
                () -> "1 is the least `b` a pair can hold:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /** The same the other way up: a field capped below zero is offered the cap and not a zero it
     * cannot hold. */
    @Test
    void aFieldTheRecordCapsBelowZeroIsOfferedTheCap() throws Exception {
        String rows = rowsFor(model("""
                    invariant negative = a <= -3
                    invariant ordered = b < a""", "Int"));

        assertTrue(rows.contains("a = -3"), () -> "the greatest `a` there is:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /**
     * A range that starts below zero starts where it starts.
     *
     * <p>Zero is a value both fields hold here, and offering it to both is what the pair refuses:
     * `a < b` relates them and no value chosen for one in ignorance of the other satisfies it. The
     * ends do, because they are a step apart — which is the low end of each, not a zero that happens
     * to be inside both.
     */
    @Test
    void aRangeThatStartsBelowZeroIsOfferedItsOwnStart() throws Exception {
        String rows = rowsFor(model("""
                    invariant span = a >= -10
                    invariant ordered = a < b""", "Int"));

        assertTrue(rows.contains("R { a = -10, b = -9 }"),
                () -> "the pair the ends make:\n" + rows);
    }

    /** A decimal position is read the same way, and its end is not taken in to a whole number. */
    @Test
    void aDecimalFieldIsOfferedTheEndAsItIs() throws Exception {
        String rows = rowsFor(model("""
                    invariant lower = a >= 0.5m""", "Decimal"));

        assertTrue(rows.contains("a = 0.5m"), () -> "0.5 is where the position starts:\n" + rows);
    }

    /** Nothing is offered from a range this cannot read, and the position keeps what it had. */
    @Test
    void aFieldNothingBoundsIsStillOfferedZero() throws Exception {
        String rows = rowsFor(model("", "Int"));

        assertTrue(rows.contains("R { a = 0, b = 0 }"), () -> rows);
    }
}
