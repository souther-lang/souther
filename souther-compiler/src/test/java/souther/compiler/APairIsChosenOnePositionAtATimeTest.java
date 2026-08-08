package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule relating two positions is met by choosing one of them knowing the other.
 *
 * <p>Every position took its value from what the rules leave it on its own, and the search then went
 * through the product of those lists. A clause relating two of them was satisfied only where the
 * lists happened to already hold a pair that does — so two bare {@code Int}s under {@code a < b} were
 * offered a zero each, and the one assignment there was is the one the record refuses. Nothing about
 * it is a boundary, a newtype or a decimal: it is ordinary partition fill finding no row at all.
 */
class APairIsChosenOnePositionAtATimeTest {

    private static String rowsFor(String clauses) throws Exception {
        String model = """
                module example.paired

                data R =
                    { a: Int
                    , b: Int
                    }
                    invariant ordered = CLAUSE

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """.replace("CLAUSE", clauses);
        Path file = Files.createTempDirectory("souther-paired").resolve("model.sou");
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

    @Test
    void twoFieldsAnOrderingRelatesAreFilledInThatOrder() throws Exception {
        String rows = rowsFor("a < b");

        assertTrue(rows.contains("R { a = 0, b = 1 }"),
                () -> "0 leaves 1 for the other end:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /**
     * The reason widening the lists is not the answer.
     *
     * <p>No pair drawn from two lists chosen in ignorance of each other satisfies this, however many
     * values each list holds. Asserting the first choice into the domain leaves the second bounded at
     * 101, and there is only ever one list to draw from.
     */
    @Test
    void aRelationWithAnOffsetIsMetTheSameWay() throws Exception {
        String rows = rowsFor("a + 100 < b");

        assertTrue(rows.contains("R { a = 0, b = 101 }"),
                () -> "101 is the least `b` a zero leaves:\n" + rows);
    }

    /** Nothing is invented for a relation this cannot read. The rows stay unfilled and the report says
     * what it always said about them. */
    @Test
    void aRelationOutsideWhatTheDomainHoldsFillsNothing() throws Exception {
        String rows = rowsFor("a * b < 10");

        assertTrue(rows.contains("R { a = 0, b = 0 }"),
                () -> "the pair each field's own range offers, which this one happens to admit:\n"
                        + rows);
    }

    /**
     * A search that stopped at its bound has not tried everything it had.
     *
     * <p>Eleven positions, each with a hole in its range, and the assignment that satisfies all of
     * them is the last the walk would reach. What the reader is owed is which of the two happened:
     * that everything was refused is a stronger claim than that the search ran out, and it is the one
     * a later reader would take for an impossibility.
     */
    @Test
    void aSearchThatRanOutSaysSoRatherThanThatEverythingWasRefused() throws Exception {
        StringBuilder fields = new StringBuilder("    { a1: Int\n");
        StringBuilder rule = new StringBuilder("a1 /= 0");
        for (int i = 2; i <= 11; i++) {
            fields.append("    , a").append(i).append(": Int\n");
            rule.append(" && a").append(i).append(" /= 0");
        }
        String model = """
                module example.budget

                data R =
                FIELDS    }
                    invariant rule = RULE

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """.replace("FIELDS", fields.toString()).replace("RULE", rule.toString());
        Path file = Files.createTempDirectory("souther-budget").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(was);
        }
        String rows = out.toString(StandardCharsets.UTF_8);

        assertTrue(rows.contains("the search stopped before reaching it"),
                () -> "it ran out of assignments to compose:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"),
                () -> "and it did not try them all:\n" + rows);
    }

    /**
     * Spending the last of the bound is not being short of it.
     *
     * <p>Eight positions of two values each is exactly what the search is allowed to compose. Every
     * one of them is refused, and every one of them was tried — so what the reader is owed is that
     * nothing here builds, and not that the search gave up one assignment early.
     */
    @Test
    void aSearchThatSpentItsLastAssignmentSaysEverythingWasRefused() throws Exception {
        StringBuilder fields = new StringBuilder("    { a1: Int\n");
        for (int i = 2; i <= 8; i++) {
            fields.append("    , a").append(i).append(": Int\n");
        }
        String model = """
                module example.exact

                data R =
                FIELDS    }
                    invariant rule = a1 * a2 >= 5

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """.replace("FIELDS", fields.toString());
        Path file = Files.createTempDirectory("souther-exact").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(was);
        }
        String rows = out.toString(StandardCharsets.UTF_8);

        assertTrue(rows.contains("every value tried was refused"),
                () -> "256 assignments, all composed and all refused:\n" + rows);
        assertFalse(rows.contains("the search stopped before reaching it"),
                () -> "and none of them was left untried:\n" + rows);
    }

    /**
     * A dense strict bound is reached by a value off the end, and not by the order of choosing.
     *
     * <p>Choosing {@code low} first leaves {@code high} at zero and above, because {@code low < high}
     * over the decimals is recorded as {@code low - high <= 0} — so the end the projection offers is
     * the one value the rule refuses. What gets past it is a second value from the range, and the
     * ends themselves stay where they were: the report still cannot say that a {@code high} of zero
     * is impossible rather than untried, because the bound it would have to read that off is the
     * weakened one (#483).
     */
    @Test
    void aStrictBoundOverDecimalsIsReachedOffTheEnd() throws Exception {
        String model = """
                module example.band

                data Ratio = Decimal
                    invariant range = value >= 0.0m && value <= 1.0m

                data Band =
                    { low: Ratio
                    , high: Ratio
                    }
                    invariant ordered = low < high

                data Ok

                behavior f : (band: Band, flag: Bool) -> Ok
                    constructs Ok

                let f (band, flag) = Ok
                """;
        Path file = Files.createTempDirectory("souther-band").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--generate", "--boundaries", file.toString()});
        } finally {
            System.setOut(was);
        }
        String rows = out.toString(StandardCharsets.UTF_8);

        assertTrue(rows.contains("high = Ratio(1m)"),
                () -> "the far end of what `high` can hold, which the range names:\n" + rows);
        assertTrue(rows.contains("no row for `band.high = 0`"),
                () -> "and the end itself is still where nothing can be written:\n" + rows);
    }
}
