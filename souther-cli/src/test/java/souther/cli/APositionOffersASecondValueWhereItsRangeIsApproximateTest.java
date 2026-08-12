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
 * One value is enough only where the range a position is chosen from is the whole of its rules.
 *
 * <p>Three ways it is not. A disequality is a hole no range keeps; a form that is neither an interval
 * nor a difference is not recorded at all; a strict bound over the decimals is recorded as the
 * non-strict one. In each of them the end a projection names can be the one value the rules refuse,
 * and a position offering only that has nothing left to try — however the choosing is ordered, because
 * ordering it changes which range is read and not how many values come out of one.
 */
class APositionOffersASecondValueWhereItsRangeIsApproximateTest {

    private static String rowsFor(String clause) throws Exception {
        String model = """
                module example.approximate

                data R =
                    { a: Int
                    , b: Int
                    }
                    invariant rule = CLAUSE

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """.replace("CLAUSE", clause);
        Path file = Files.createTempDirectory("souther-approximate").resolve("model.sou");
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

    /** A hole in a range, which a range cannot hold. The projection says nothing, so the position is
     * offered the zero it would have been offered anyway, and the rule refuses exactly that. */
    @Test
    void aDisequalityIsMetByTheValueBesideTheHole() throws Exception {
        String rows = rowsFor("a /= 0");

        assertTrue(rows.contains("a = 1"), () -> "one step off the value the rule rules out:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /** The same where the bound is real and the hole sits on it. */
    @Test
    void aHoleOnTheEndOfARangeIsSteppedOff() throws Exception {
        String rows = rowsFor("a >= 0 && a /= 0");

        assertTrue(rows.contains("a = 1"), () -> rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /** A sum of two atoms is neither an interval nor a difference, so nothing about it reaches the
     * range either position is chosen from. */
    @Test
    void aFormTheDomainCannotHoldIsMetByTheSecondValue() throws Exception {
        String rows = rowsFor("a + b >= 1");

        assertTrue(rows.contains("R { a = 0, b = 1 }"), () -> rows);
        assertFalse(rows.contains("every value tried was refused"), () -> rows);
    }

    /** A product needs both positions off their ends, which is what a search rather than a rule does. */
    @Test
    void aProductNeedsBothPositionsMoved() throws Exception {
        String rows = rowsFor("a * b >= 1");

        assertTrue(rows.contains("R { a = 1, b = 1 }"), () -> rows);
    }

    /**
     * A bare decimal between two ends is offered the one between them.
     *
     * <p>A newtype holds its far end back for the search that runs before this one; a bare number has
     * no such reserve, and the end it is offered first is the one a weakened strict bound puts it at.
     * The midpoint is an ordinary decimal the range names.
     */
    @Test
    void aBareDecimalIsOfferedTheValueBetweenItsEnds() throws Exception {
        String model = """
                module example.bare

                data R =
                    { a: Decimal
                    , b: Decimal
                    }
                    invariant aRange = a >= 0.0m && a <= 1.0m
                    invariant bRange = b >= 0.0m && b <= 1.0m
                    invariant ordered = a < b

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok
                    constructs Ok

                let f (r, flag) = Ok
                """;
        Path file = Files.createTempDirectory("souther-bare").resolve("model.sou");
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

        assertTrue(rows.contains("R { a = 0m, b = 0.5m }"),
                () -> "half way between the ends `b` has:\n" + rows);
    }

    /**
     * A decimal open at its only end is offered a value from inside it.
     *
     * <p>`low < high` with both at zero and above leaves `high` starting at zero without holding it,
     * and a dense order has no next value to move onto. What the position offers is a value the range
     * admits rather than the number it stops at — chosen the same way every time and carrying no claim
     * to be the nearest one, which is what a candidate is for.
     */
    @Test
    void aDecimalOpenAtItsOnlyEndOffersAValueInsideIt() throws Exception {
        String model = """
                module example.halfopen

                data Rate = Decimal
                    invariant lower = value >= 0.0m

                data Pair =
                    { low: Rate
                    , high: Rate
                    }
                    invariant ordered = low < high

                data Ok

                behavior f : (pair: Pair, flag: Bool) -> Ok
                    constructs Ok

                let f (pair, flag) = Ok
                """;
        Path file = Files.createTempDirectory("souther-halfopen").resolve("model.sou");
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

        assertTrue(rows.contains("Pair { low = Rate(0m), high = Rate(1m) }"),
                () -> "`low` reaches its end and `high` starts a step past it:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"),
                () -> "and nothing had to be refused to get there:\n" + rows);
    }
}
