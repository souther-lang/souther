package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The layout a construct takes whatever its width. {@link AConstructIsFlatUpToTheCanonicalWidthTest}
 * asks where the width decides; these are the constructs it never gets to decide, and every fixture
 * here is short enough that a width-decided layout would have written it on one line.
 *
 * <p>Each test method is one obligation, and the constructs it quantifies over are its rows. Written
 * this way so that removing one forced break from the formatter fails the method that claims it and
 * nothing else: a whole-file fixture fails whichever break is removed, which tells you something
 * changed and not which rule it was.
 */
class AForcedBreakIsWrittenWhateverTheWidthTest {

    private static final int WIDTH = 100;

    /**
     * A construct written down the page, and the parts of it that each take a line. At least two,
     * because a construct that keeps one part on its own line says nothing about keeping them apart;
     * and the head the parts are written under wherever no other rule owns where that head ends —
     * a clause joined to its signature is on a line of its own by every test that only compares the
     * clauses with each other.
     */
    record Vertical(String name, String source, List<String> parts) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Vertical> verticals() {
        return Stream.of(
                new Vertical("example rows",
                        """
                        module fmtprobe exposing ( j )

                        example j
                            | "a" : (Alpha(1)) -> Beta
                            | "b" : (Alpha(2)) -> Gamma
                        """,
                        List.of("example j",
                                "| \"a\" : (Alpha(1)) -> Beta", "| \"b\" : (Alpha(2)) -> Gamma")),

                new Vertical("fake rows",
                        """
                        module fmtprobe exposing ( j )

                        fake clock
                            | (Alpha(1)) -> Beta
                            | (Alpha(2)) -> Gamma
                        """,
                        List.of("fake clock",
                                "| (Alpha(1)) -> Beta", "| (Alpha(2)) -> Gamma")),

                new Vertical("invariant clauses",
                        """
                        module fmtprobe exposing ( A )

                        data Amount = Int
                            invariant one = value >= 0
                            invariant two = value <= 9
                        """,
                        List.of("data Amount = Int",
                                "invariant one = value >= 0", "invariant two = value <= 9")),

                new Vertical("product fields",
                        """
                        module fmtprobe exposing ( P )

                        data P =
                            { alpha: Int
                            , beta: Int
                            }
                        """,
                        // not the `data P =` the body opens under: where that brace goes is the
                        // rule below, and a body joined to its head still writes its fields apart
                        List.of("{ alpha: Int", ", beta: Int")),

                new Vertical("the clauses under a signature",
                        """
                        module fmtprobe exposing ( pay )

                        behavior pay : (a: Amount) -> Paid
                            depends on clock
                            constructs Paid
                        """,
                        List.of("behavior pay : (a: Amount) -> Paid",
                                "depends on clock", "constructs Paid")),

                new Vertical("the departures of a guard",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = {
                            guard Amount(a) as amount else
                                | one -> Refused
                                | two -> Denied
                            amount
                        }
                        """,
                        List.of("guard Amount(a) as amount else",
                                "| one -> Refused", "| two -> Denied")),

                new Vertical("match arms",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            match a with
                                | Zero -> alpha
                                | One -> beta
                        """,
                        List.of("match a with", "| Zero -> alpha", "| One -> beta")),

                new Vertical("the statements of a block",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = {
                            let alpha = one
                            beta
                        }
                        """,
                        List.of("let alpha = one", "beta")),

                new Vertical("top-level items",
                        """
                        module fmtprobe exposing ( f )

                        data Alpha

                        data Beta
                        """,
                        List.of("data Alpha", "data Beta")));
    }

    /**
     * Which line of {@code text} holds {@code part}, where exactly one does. Asking for the line
     * rather than for a line holding {@code part} and nothing else keeps this obligation apart from
     * the one below: a bracket that joined a member's line leaves the member where it was, and it is
     * the bracket's own rule that says it may not be there.
     */
    private static int lineHolding(String text, String part) {
        String[] lines = text.split("\n", -1);
        List<Integer> found = new ArrayList<>();
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(part)) {
                found.add(i);
            }
        }
        assertEquals(1, found.size(),
                found.size() + " lines hold `" + part + "` in:\n" + text);
        return found.get(0);
    }

    /**
     * The two members fit beside each other, so a construct laid out by the width would have written
     * them on one line. Without this the rows below would pass on a formatter with no forced break in
     * it at all, as long as the fixtures were long enough.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("verticals")
    void thePartsWouldHaveFittedOnOneLine(Vertical vertical) {
        int together = vertical.parts().stream().mapToInt(String::length).sum()
                + vertical.parts().size() - 1;
        assertTrue(together <= WIDTH,
                vertical.name() + ": the parts are " + together + " columns together, over the width,"
                        + " so the width would have separated them anyway");
    }

    /** Each of these constructs writes its members one to a line. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("verticals")
    void aVerticalConstructWritesItsMembersOneToALine(Vertical vertical) {
        String formatted = Formatter.format(vertical.source());
        List<String> parts = vertical.parts();
        for (int i = 0; i < parts.size(); i++) {
            for (int j = i + 1; j < parts.size(); j++) {
                int one = lineHolding(formatted, parts.get(i));
                int other = lineHolding(formatted, parts.get(j));
                assertTrue(one != other,
                        vertical.name() + ": `" + parts.get(i) + "` and `" + parts.get(j)
                                + "` share line " + one + " of:\n" + formatted);
            }
        }
    }

    /**
     * A bracket, and what is written on the line beside it — the head the construct opens under, or
     * the last member it closes after.
     */
    record Bracket(String name, String source, String neighbour, String bracket) {
        @Override
        public String toString() {
            return name;
        }
    }

    private static final String TWO_FIELDS = """
            module fmtprobe exposing ( P )

            data P =
                { alpha: Int
                , beta: Int
                }
            """;

    private static final String TWO_STATEMENTS = """
            module fmtprobe exposing ( f )

            let f (a: Int): Int = {
                let alpha = one
                beta
            }
            """;

    static Stream<Bracket> brackets() {
        return Stream.of(
                new Bracket("what a product body opens under", TWO_FIELDS, "data P =", "{"),
                new Bracket("what a product body closes after", TWO_FIELDS, ", beta: Int", "}"),
                new Bracket("what a block closes after", TWO_STATEMENTS, "beta", "}"));
    }

    /**
     * A product body and a block are written between lines of their own, so the bracket that opens or
     * closes one is on neither the line above it nor the line below. A block opens on the line its
     * declaration ends — that brace is written where it was, and the rule is about the other three.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("brackets")
    void aBracketOfAConstructWrittenDownThePageTakesALineOfItsOwn(Bracket bracket) {
        String formatted = Formatter.format(bracket.source());
        String[] lines = formatted.split("\n", -1);
        String beside = lines[lineHolding(formatted, bracket.neighbour())];
        assertTrue(!beside.contains(bracket.bracket()),
                bracket.name() + ": `" + beside.strip() + "` holds the `" + bracket.bracket()
                        + "` as well as what is written beside it, in:\n" + formatted);
    }

    private static final String TWO_ITEMS = """
            module fmtprobe exposing ( f )
            import some.place ( alpha )

            data Alpha

            data Beta
            """;

    /** The blank lines between the line holding {@code above} and the line holding {@code below}. */
    private static int blankLinesBetween(String text, String above, String below) {
        String[] lines = text.split("\n", -1);
        int from = -1;
        int to = -1;
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].strip().equals(above)) {
                from = i;
            } else if (lines[i].strip().equals(below)) {
                to = i;
            }
        }
        assertTrue(from >= 0 && to > from,
                "`" + above + "` and `" + below + "` are not on two lines in that order in:\n" + text);
        List<String> between = new ArrayList<>();
        for (int i = from + 1; i < to; i++) {
            between.add(lines[i]);
        }
        assertTrue(between.stream().allMatch(String::isBlank),
                "there is more than the blank between them in:\n" + text);
        return between.size();
    }

    /** One blank line between top-level items, and none between a module header and its imports. */
    @Test
    void oneBlankLineSeparatesTopLevelItemsAndAnImportFollowsItsHeader() {
        String formatted = Formatter.format(TWO_ITEMS);
        assertEquals(1, blankLinesBetween(formatted, "data Alpha", "data Beta"));
        assertEquals(0, blankLinesBetween(formatted,
                "module fmtprobe exposing ( f )", "import some.place ( alpha )"));
    }

    /** A file ends with a newline, and with one. */
    @Test
    void aFileEndsWithOneNewline() {
        String formatted = Formatter.format(TWO_ITEMS);
        assertTrue(formatted.endsWith("\n"), "the file does not end with a newline");
        assertTrue(!formatted.endsWith("\n\n"),
                "the file ends with a blank line:\n" + formatted.substring(formatted.length() - 20));
    }
}
