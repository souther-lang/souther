package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An end is read off the rule that drew it.
 *
 * <p>The bounds a position is measured at used to be read from the constraints codegen emits, which
 * are the shapes the runtime has a check for. That list answers a different question. It has a case
 * for a decimal above zero because the runtime states that one directly, and none for a decimal above
 * five — so a rule that draws a line at five was read as drawing none, and one that draws a line at
 * zero was read as drawing it at one, which is the whole number a positive integer starts at and a
 * value no decimal rule here mentions.
 */
class AnEndIsWhereItsRuleStopsTest {

    private static final String MODEL = """
            module example.probe

            data Positive = Decimal
                invariant positive = value > 0m

            data AboveFive = Decimal
                invariant above = value > 5.0m

            data Holder = { p: Positive, a: AboveFive }

            data Ok

            behavior take : (h: Holder) -> Ok
                constructs Ok

            let take (h) = Ok
            """;

    /** A boundary is at a value some rule wrote. Nothing here writes a one. */
    @Test
    void anEdgeIsNotAtAValueNoRuleNamed() throws Exception {
        String report = reportOn(MODEL);

        assertFalse(report.contains("take/h.p = 1"),
                () -> "`value > 0m` says nothing about one:\n" + report);
    }

    /** And a line five is drawn at is a line, though the runtime has no word for it. */
    @Test
    void aStrictBoundAwayFromZeroIsALineTheModelDraws() throws Exception {
        String report = reportOn(MODEL);

        assertFalse(report.contains("not derivable: h.a"),
                () -> "`value > 5.0m` divides the position at five:\n" + report);
    }

    /**
     * A rule this reads is a rule the value's edges are promised against.
     *
     * <p>Whether every rule was taken in is asked once for the whole value, so one clause nobody
     * could read leaves every edge beside it unpromised. The clause here is `value > 5.0m`, which is
     * read now, and the edge is the other field's — which has nothing to do with it and was being
     * held back all the same.
     */
    @Test
    void anEdgeIsPromisedWhereEveryRuleBesideItWasRead() throws Exception {
        String report = reportOn("""
                module example.probe

                data AboveFive = Decimal
                    invariant above = value > 5.0m

                data AtMostTen = Decimal
                    invariant capped = value <= 10.0m

                data Holder = { a: AboveFive, b: AtMostTen }

                data Ok

                behavior take : (h: Holder) -> Ok
                    constructs Ok

                let take (h) = Ok

                example take
                    | "a" : (Holder { a = AboveFive(6m), b = AtMostTen(1m) }) -> Ok
                """);

        assertFalse(report.contains("not known to be writable: take/h.b = 10"), () -> report);
        assertTrue(report.contains("no row is at take/h.b = 10"),
                () -> "and the edge is one a row is owed at:\n" + report);
    }

    /**
     * A value offered for an open end is one inside it.
     *
     * <p>Over the decimals there is no value beside the end to step onto, so what a position can
     * offer is a value from inside the range and not one next to its edge — a midpoint where both
     * ends are known, and a step where only one is. Nothing about the choice is the nearest value
     * the rule admits, because over a dense order there is no such thing; what it has to be is one
     * the rule admits at all, decided the same way every time.
     */
    @Test
    void aPositionOpenAtAnEndOffersAValueFromInsideIt() throws Exception {
        String rows = reportOn("""
                module example.probe

                data AboveFive = Decimal
                    invariant above = value > 5.0m

                data UnderOne = Decimal
                    invariant under = value < 1.0m

                data Between = Decimal
                    invariant between = value > 5.0m && value < 6.0m

                data Holder = { a: AboveFive, u: UnderOne, b: Between, flag: Bool }

                data Ok

                behavior take : (h: Holder) -> Ok
                    constructs Ok

                let take (h) = Ok
                """, "--generate");

        assertTrue(rows.contains("a = AboveFive(6m)"),
                () -> "a step up from an end nothing sits on:\n" + rows);
        assertTrue(rows.contains("u = UnderOne(0m)"),
                () -> "and a step down from the other:\n" + rows);
        assertTrue(rows.contains("b = Between(5.5m)"),
                () -> "and between two of them, the value between them:\n" + rows);
        assertFalse(rows.contains("every value tried was refused"),
                () -> "none of which the rules refuse:\n" + rows);
    }

    /**
     * A comparison against a value the position cannot hold divides nothing.
     *
     * <p>A guard draws a line and both sides of it ordinarily hold values a row can write. Where the
     * line is the end the position stops short of, one side holds nothing — and a class nothing can
     * be written in is a gap no author can close.
     */
    @Test
    void aGuardAtAnEndThePositionDoesNotReachDividesNothing() throws Exception {
        String report = reportOn("""
                module example.probe

                data Ratio = Decimal
                    invariant above = value > 5.0m

                data Ok
                data No

                behavior pick : (r: Ratio) -> Ok | No
                    constructs Ok, No

                let pick (r) = {
                    guard r.value > 5.0m else No
                    Ok
                }

                example pick
                    | "a" : (Ratio(6m)) -> Ok
                """, "--generate");

        assertFalse(report.contains("5 <= x <= 5"),
                () -> "nothing of `value > 5.0m` is five:\n" + report);
        assertFalse(report.contains("every value tried was refused"),
                () -> "so no row is asked for there:\n" + report);
    }

    /**
     * A position of no type but {@code Decimal} is offered a value from inside its range too.
     *
     * <p>What is left of a position once the rest of the assignment is settled is read off the record
     * either way — `low < high` leaves `high` above whatever `low` took, and above it without holding
     * it. A value offered at the number the range stops at is refused whether or not somebody wrapped
     * a name round the position.
     */
    @Test
    void aBareDecimalIsOfferedAValueItsRangeHolds() throws Exception {
        String rows = reportOn("""
                module example.probe

                data Pair =
                    { low: Decimal
                    , high: Decimal
                    }
                    invariant lower = low > 0m

                data Ok

                behavior take : (p: Pair, flag: Bool) -> Ok
                    constructs Ok

                let take (p, flag) = Ok
                """, "--generate");

        assertFalse(rows.contains("every value tried was refused"),
                () -> "a low above zero is a row that builds:\n" + rows);
    }

    /**
     * A guard on a position open at its end leaves ranges that are open there too.
     *
     * <p>The ranges a comparison leaves are cut out of what the position holds, and one of their ends
     * is that position's own. Rebuilt as closed, the first of them holds the value the invariant
     * refuses and offers it as the value standing for the whole class.
     */
    @Test
    void aRangeCutOutOfAnOpenEndIsOpenThere() throws Exception {
        String report = reportOn("""
                module example.probe

                data AboveFive = Decimal
                    invariant above = value > 5m

                data Ok
                data No

                behavior pick : (r: AboveFive) -> Ok | No
                    constructs Ok, No

                let pick (r) = {
                    guard r.value < 10m else No
                    Ok
                }

                example pick
                    | "over" : (AboveFive(20m)) -> No
                """, "--generate");

        assertFalse(report.contains("5 <= x"),
                () -> "nothing of `value > 5m` is five:\n" + report);
        assertFalse(report.contains("AboveFive(5m)"),
                () -> "so five stands for no class of it:\n" + report);
    }

    private static String reportOn(String model, String... extra) throws Exception {
        Path file = Files.createTempDirectory("souther-ends").resolve("model.sou");
        Files.writeString(file, model);
        List<String> args = new java.util.ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(extra));
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(args.toArray(String[]::new));
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }
}
