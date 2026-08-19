package souther.cli;

import souther.cli.Main;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior is owed rows for is what its author wrote, not what expansion made of it.
 *
 * <p>A non-recursive helper is spliced into every body that calls it, so a table written once stands
 * in the tree as many times as it is called. Counted per copy, the arms a behavior owes become a
 * product of its call graph: factoring a table out and calling it from two places would double what
 * every caller owes, and covering the second copy would establish nothing the first had not. The
 * measure is branch-arm coverage, which is a count of the forks the author wrote.
 *
 * <p>What is <em>not</em> shared is the question. Two behaviors calling one helper each owe its arms,
 * because the measurement is about a behavior and a row written for one is not a row written for the
 * other.
 */
class AHelpersArmIsOneObligationHoweverOftenItIsCalledTest {

    /** A three-arm table written once, called once from one behavior and twice from another. */
    private static final String TABLE = """
            module example.arms

            data Grade = Int
                invariant value >= 0

            data A
            data B
            data C
            data Band = A | B | C

            let rate (band: Band): Grade =
                match band with
                    | A -> Grade(1)
                    | B -> Grade(2)
                    | C -> Grade(3)

            data Left
            data Right
            data Side = Left | Right

            behavior once : (band: Band) -> Grade
                constructs Grade
            let once (band) = rate(band)

            behavior twice : (side: Side, band: Band) -> Grade
                constructs Grade
            let twice (side, band) =
                match side with
                    | Left -> rate(band)
                    | Right -> rate(band)

            example once
                | "A" : (A) -> Grade(1)
                | "B" : (B) -> Grade(2)
                | "C" : (C) -> Grade(3)

            example twice
                | "left A" : (Left, A) -> Grade(1)
                | "left B" : (Left, B) -> Grade(2)
                | "left C" : (Left, C) -> Grade(3)
            """;

    @Test
    void aTableCalledTwiceIsCountedOnce() throws Exception {
        String report = reportOn(TABLE);

        // `twice` writes two arms and calls a three-arm table: five, not its own two plus the table
        // once per call.
        assertTrue(report.contains("branch      4/5"),
                () -> "two arms of its own and the table's three:\n" + report);
        assertEquals(1, count(report, "no row goes through"),
                () -> "the one arm no row takes is its own `Right`:\n" + report);
        assertTrue(report.contains("no row goes through `case Right`"),
                () -> "and it is named:\n" + report);
    }

    /** The behavior beside it, which owes the table's arms too. A quotient taken across behaviors
     * would let one behavior's rows answer for another's. */
    @Test
    void thebehaviorBesideItOwesTheTableSeparately() throws Exception {
        String report = reportOn(TABLE);

        assertTrue(report.contains("branch      3/3"),
                () -> "`once` owes the table's three arms and its rows go through them:\n" + report);
    }

    /**
     * Through the call graph rather than the call sites. A helper calling a helper multiplied at
     * every level: a behavior whose three bodies hold seven arms between them was owed eighteen.
     */
    @Test
    void aHelperCallingAHelperIsCountedOnceAtEachLevel() throws Exception {
        String report = reportOn("""
                module example.nest

                data Grade = Int
                    invariant value >= 0

                data A
                data B
                data C
                data Band = A | B | C

                data Left
                data Right
                data Side = Left | Right

                let rate (band: Band): Grade =
                    match band with
                        | A -> Grade(1)
                        | B -> Grade(2)
                        | C -> Grade(3)

                let both (side: Side, band: Band): Grade =
                    match side with
                        | Left -> rate(band)
                        | Right -> rate(band)

                behavior twice : (side: Side, band: Band) -> Grade
                    constructs Grade
                let twice (side, band) =
                    match side with
                        | Left -> both(side, band)
                        | Right -> both(side, band)

                example twice
                    | "left A" : (Left, A) -> Grade(1)
                """);

        assertTrue(report.contains("branch      3/7"),
                () -> "two arms in each of the three bodies but the table's three:\n" + report);
    }

    /**
     * Two arms the author wrote separately are two obligations, however alike they are made. This is
     * why what holds the copies together has to be where a fork was written rather than what it is
     * made of.
     */
    @Test
    void twoForksTheAuthorWroteSeparatelyAreStillTwo() throws Exception {
        String report = reportOn("""
                module example.same

                data Grade = Int
                    invariant value >= 0

                data A
                data B
                data Band = A | B

                behavior both : (first: Band, second: Band) -> Grade
                    constructs Grade
                let both (first, second) =
                    match first with
                        | A ->
                            match second with
                                | A -> Grade(1)
                                | B -> Grade(2)
                        | B ->
                            match second with
                                | A -> Grade(1)
                                | B -> Grade(2)

                example both
                    | "A A" : (A, A) -> Grade(1)
                """);

        assertTrue(report.contains("branch      2/6"),
                () -> "the outer two and two inner `match`es of two arms each:\n" + report);
    }

    /**
     * The case a position could not answer. A helper of another module has its body stamped with the
     * call site, so two copies of one of its arms are written at two different places — and a row
     * through either is a row through the arm.
     */
    @Test
    void twoCallsOfOneLibraryHelperOweItsArmsOnceAndCoverThemBetweenThem() throws Exception {
        String report = reportOn("""
                module example.two

                data Kept
                data Dropped
                data Mark = Kept | Dropped

                data Item = { mark: Mark }

                data Count = Int
                    invariant value >= 0

                behavior twoFilters : (items: List<Item>) -> Count
                    constructs Count, Kept, Dropped
                let twoFilters (items) =
                    Count(List.length(List.filter(i -> i.mark == Kept, items))
                        + List.length(List.filter(i -> i.mark == Dropped, items)))

                example twoFilters
                    | "one kept" : ([ Item { mark = Kept } ]) -> Count(1)
                """);

        // The body writes no fork of its own. `List.filter` writes one, and the row keeps its element
        // at the first call and drops it at the second — so between them both arms were taken.
        assertTrue(report.contains("branch      2/2"),
                () -> "one fork, and the row went both ways through it:\n" + report);
    }

    /**
     * The same for a line a guard drew, which multiplied the same way and for the same reason. Two
     * readings of one guard used to leave two entries at one value, spelled identically.
     */
    @Test
    void aGuardInsideAHelperDrawsOneLineHoweverOftenItIsCalled() throws Exception {
        String report = reportOn("""
                module example.banding

                data Amount = Int
                    invariant value >= 0

                data Small
                data Large
                data Size = Small | Large

                data Left
                data Right
                data Side = Left | Right

                let band (a: Amount): Size =
                    if a.value <= 100 then Small else Large

                behavior twice : (side: Side, a: Amount) -> Size
                let twice (side, a) =
                    match side with
                        | Left -> band(a)
                        | Right -> band(a)

                example twice
                    | "left small" : (Left, Amount(1)) -> Small
                    | "left large" : (Left, Amount(500)) -> Large
                """);

        // The record's own minimum, and the two the guard draws at 100.
        assertTrue(report.contains("border      0/3"),
                () -> "one line per rule, not one per reading of it:\n" + report);
        assertEquals(1, count(report, "a = 100"),
                () -> "and the line at 100 is written once:\n" + report);
        assertEquals(1, count(report, "a = 101"),
                () -> "as is the one above it:\n" + report);
    }

    private static int count(String haystack, String needle) {
        int seen = 0;
        for (int at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
            seen++;
        }
        return seen;
    }

    private static String reportOn(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-obligations").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }
}
