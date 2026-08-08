package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What goes between two top-level items, as a function of both of them. The formatter writes one
 * blank line between items unless a module header or an import is followed by an import, which is a
 * decision about a pair and not about the file: a table with one row for {@code SOURCE_FILE} cannot
 * hold it, and a fixture with a header and an import in it does not reach the pair where the first
 * of the two is itself an import.
 *
 * <p>Every ordered pair the grammar admits is a row. The pairs it does not admit are their own
 * claim below, because what makes this table forty-three cells rather than sixty-four is the grammar
 * and not a choice the formatter made.
 */
class WhatSeparatesTwoItemsComesFromBothOfThemTest {

    /** A top-level item, as its kind and as something to write. */
    record Item(String name, SyntaxKind kind, String text, boolean opensAFile) {
        @Override
        public String toString() {
            return name;
        }
    }

    private static final List<Item> ITEMS = List.of(
            new Item("module header", SyntaxKind.MODULE_HEADER,
                    "module m exposing ( f )", true),
            new Item("examples file header", SyntaxKind.EXAMPLES_FILE_HEADER,
                    "examples for m", true),
            new Item("import", SyntaxKind.IMPORT_DECL,
                    "import some.place ( alpha )", false),
            new Item("data", SyntaxKind.DATA_DEF,
                    "data Alpha", false),
            new Item("behavior", SyntaxKind.BEHAVIOR_DEF,
                    "behavior b : (a: A) -> R", false),
            new Item("definition", SyntaxKind.FN_DEF,
                    "let f (a: Int): Int = alpha", false),
            new Item("example", SyntaxKind.EXAMPLE_DEF,
                    "example j\n    | \"a\" : (A(1)) -> B", false),
            new Item("fake", SyntaxKind.FAKE_DEF,
                    "fake clock\n    | (A(1)) -> B", false));

    /** An import follows the header of its file or another import, and nothing else. */
    private static boolean canFollow(Item first, Item second) {
        if (second.opensAFile()) {
            return false;                       // a header opens a file and cannot come second
        }
        if (second.kind() == SyntaxKind.IMPORT_DECL) {
            return first.opensAFile() || first.kind() == SyntaxKind.IMPORT_DECL;
        }
        return true;
    }

    record Pair(Item first, Item second) {
        @Override
        public String toString() {
            return first.name() + " then " + second.name();
        }

        /** The two written one after the other, under a module header where neither is one. */
        String source() {
            String head = first.opensAFile() ? "" : "module m exposing ( f )\n";
            return head + first.text() + "\n" + second.text() + "\n";
        }
    }

    static Stream<Pair> pairs() {
        List<Pair> out = new ArrayList<>();
        for (Item first : ITEMS) {
            for (Item second : ITEMS) {
                if (canFollow(first, second)) {
                    out.add(new Pair(first, second));
                }
            }
        }
        return out.stream();
    }

    /**
     * The pairs written with no blank line between them. Written out rather than computed, so that
     * the formatter deciding differently fails this rather than agreeing with itself.
     */
    private static final Set<String> TIGHT = Set.of(
            "module header then import",
            "import then import");

    /** The lines between the last line of {@code first} and the first line of {@code second}. */
    private static int blanksBetween(String formatted, Pair pair) {
        List<String> lines = List.of(formatted.split("\n", -1));
        String[] firstLines = pair.first().text().split("\n");
        String ends = firstLines[firstLines.length - 1].strip();
        String opens = pair.second().text().split("\n")[0].strip();
        int from = -1;
        int to = -1;
        for (int i = 0; i < lines.size(); i++) {
            if (from < 0 && lines.get(i).strip().equals(ends)) {
                from = i;
            } else if (from >= 0 && to < 0 && lines.get(i).strip().equals(opens)) {
                to = i;
            }
        }
        assertTrue(from >= 0 && to > from,
                pair + ": the two items are not both written, in:\n" + formatted);
        int blanks = 0;
        for (int i = from + 1; i < to; i++) {
            assertTrue(lines.get(i).isBlank(),
                    pair + ": `" + lines.get(i) + "` is between them, in:\n" + formatted);
            blanks++;
        }
        return blanks;
    }

    /**
     * The pair is one the grammar admits, read from the parser rather than from the model above that
     * generated it. `Formatter.format` assumes a clean parse and does not check, so without this a
     * row whose source the grammar refuses would be formatted from a tree with an error token in it
     * and answer about something else.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("pairs")
    void theGrammarAdmitsThisPair(Pair pair) {
        assertEquals(List.of(), CstParser.parse(pair.source()).errors(),
                pair + ": the grammar refuses this, so it is not a row of the table");
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("pairs")
    void whatGoesBetweenThem(Pair pair) {
        String formatted = Formatter.format(pair.source());
        assertEquals(TIGHT.contains(pair.toString()) ? 0 : 1, blanksBetween(formatted, pair),
                pair + ": blank lines between them, in:\n" + formatted);
    }

    /** And it is where the canonical form stays. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("pairs")
    void andThatIsAFixedPoint(Pair pair) {
        String formatted = Formatter.format(pair.source());
        assertEquals(formatted, Formatter.format(formatted));
    }

    /**
     * The table covers every kind the formatter writes as an item. A kind added to the file's walk
     * without a row here is a pair whose separation nothing states.
     */
    @Test
    void everyKindTheFormatterWritesAsAnItemHasARow() {
        Set<SyntaxKind> written = new LinkedHashSet<>();
        for (SyntaxKind k : SyntaxKind.values()) {
            if (Formatter.isTopLevel(k)) {
                written.add(k);
            }
        }
        Set<SyntaxKind> covered = new LinkedHashSet<>();
        for (Item item : ITEMS) {
            covered.add(item.kind());
        }
        assertEquals(written, covered);
    }

    /** Both answers the table gives are reached, and by more than one pair each. */
    @Test
    void theTableIsNotOneAnswer() {
        long tight = pairs().filter(p -> TIGHT.contains(p.toString())).count();
        long apart = pairs().count() - tight;
        assertEquals(2, tight, "pairs written with no blank line between them");
        assertEquals(41, apart, "pairs written with one");
    }

    /**
     * What keeps the table to forty-three cells: an import is refused after anything but the header
     * of its file or another import, so the pairs left out above are pairs no source can hold. Read
     * from the parser, because a formatter is not what decides this and a pair silently dropped from
     * the table above would otherwise look the same as a pair the grammar forbids.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("refusedPairs")
    void anImportComesBeforeEverythingElse(Pair pair) {
        assertTrue(!CstParser.parse(pair.source()).errors().isEmpty(),
                pair + ": the grammar admits this, so the table above is missing a row for it");
    }

    static Stream<Pair> refusedPairs() {
        List<Pair> out = new ArrayList<>();
        for (Item first : ITEMS) {
            for (Item second : ITEMS) {
                if (!canFollow(first, second) && !second.opensAFile()) {
                    out.add(new Pair(first, second));
                }
            }
        }
        return out.stream();
    }
}
