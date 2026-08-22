package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rows of a table write each of their connectors at one column.
 *
 * <p>What is measured is the layout's own answers and the display column each connector was written
 * at, never a stretch of the output quoted whole. A table is the one construct where quoting the
 * text would be self-defeating: adding a row to it moves every other row, so an expectation written
 * as the text would have to be rewritten for a change it is not about — which is the complaint
 * issue #938 makes about the formatter itself.
 */
class ARowOfATableIsWrittenAtItsTablesColumnTest {

    /** Two tables, each with rows of unequal width, and a row with no description. */
    private static final String TWO_TABLES = """
            examples for demo

            example price
                | "a description of some length" : (Off, None) -> P(1)
                | "short" : (On, Some) -> P(2)
                | (Off, Some) -> P(3)

            example other
                | "x" : (E) -> Q(1)
                | "yy" : (F) -> Q(2)
            """;

    /**
     * A source that reaches the column with a tab where the canonical form writes spaces. Its rows
     * line up on a screen and its text is not the canonical form, which is the pair of facts a rule
     * reading only the column the source arrived at cannot tell apart.
     */
    private static final String A_TAB_REACHING_THE_COLUMN =
            "examples for demo\n\nexample f\n"
                    + "    | \"1234567\" : (A) -> X\n"
                    + "    | \"a\"\t: (B) -> Y\n";

    /** A source with a tab inside a token written after a column, where how far the tab advances
     *  depends on the padding in front of it. */
    private static final String A_TAB_AFTER_A_COLUMN =
            "examples for demo\n\nexample f\n"
                    + "    | \"long description\" : (\"abc\") -> X\n"
                    + "    | \"short\" : (\"\t\") -> Y\n";

    /**
     * A table of one row that wrote no separator at all. There is no question about lining rows up
     * here — a table of one row is at its own width — so what is wrong with it is that a space is
     * missing, and nothing else.
     */
    private static final String NO_SEPARATOR =
            "examples for demo\n\nfake f\n    | (A)-> X\n";

    /** The canonical form of a source, with both texts' tokens read back. */
    private record Written(Formatter.CanonicalForm form, Witnesses.Pairing pairing) {

        static Written of(String source) {
            Formatter.CanonicalForm form =
                    Formatter.canonicalize(CstParser.parse(source).root());
            return new Written(form, new Witnesses.Pairing(source, form));
        }

        List<SyntaxToken> code() {
            return pairing.writesCode();
        }

        List<Witnesses.CanonicalStop> stops() {
            return Witnesses.stops(form, code());
        }

        /** The display column the connector of one stop was written at. */
        int columnOf(Witnesses.CanonicalStop stop) {
            return Witnesses.columnAt(form.text(), code().get(stop.adjacency() + 1).start());
        }

        /** Where each column of each table was settled, in the order the tables are written. */
        List<Integer> columns() {
            return form.layout().columns().stream().map(ColumnDecision::column).toList();
        }
    }

    /**
     * Every row written to a column has its connector at that column, on the screen.
     *
     * <p>The decision and the text are two things: the layout says where the column is and the
     * output is where the row ended up, and it is the second a reader sees. Held over every source
     * in the repository as well as the fixtures here, so the statement is about the formatter rather
     * than about these tables.
     */
    @Test
    void everyRowWrittenToAColumnIsAtIt() {
        List<String> wrong = new ArrayList<>();
        int held = 0;
        for (String source : sources()) {
            Written written = Written.of(source);
            Map<Columns.Unit, Integer> settled = new LinkedHashMap<>();
            for (ColumnDecision decision : written.form().layout().columns()) {
                settled.put(decision.unit(), decision.column());
            }
            Map<Columns.Unit, Integer> howMany = new LinkedHashMap<>();
            for (ColumnOccurrence stop : written.form().layout().stops()) {
                howMany.merge(stop.unit(), 1, Integer::sum);
            }
            held += howMany.values().stream().filter(n -> n > 1).toList().size();
            for (Witnesses.CanonicalStop stop : written.stops()) {
                int at = written.columnOf(stop);
                int column = settled.get(stop.occurrence().unit());
                if (at != column) {
                    wrong.add(stop.occurrence().unit().stop() + ": written at column " + at
                            + " and the column is " + column);
                }
            }
        }
        assertEquals(List.of(), wrong);
        // And it is a statement about tables rather than about rows. A column one row is written to
        // is at that row's own width whatever the rule does, so what says the rule was asked is the
        // columns two or more rows share.
        assertTrue(held >= 2, "only " + held + " columns anywhere hold more than one row");
    }

    /**
     * The column is the greatest the rows need, and not merely one they all fit inside.
     *
     * <p>Both halves. That every row reaches the column would be true of a formatter that wrote
     * every table at column 200; what rules that out is that some row of the table is at the column
     * with nothing written for it.
     */
    @Test
    void theColumnIsTheGreatestTheRowsNeed() {
        for (String source : sources()) {
            Written written = Written.of(source);
            Map<Columns.Unit, List<Integer>> natural = new LinkedHashMap<>();
            for (ColumnOccurrence stop : written.form().layout().stops()) {
                natural.computeIfAbsent(stop.unit(), _ -> new ArrayList<>())
                        .add(stop.naturalColumn());
            }
            for (ColumnDecision decision : written.form().layout().columns()) {
                List<Integer> reached = natural.get(decision.unit());
                assertEquals(reached.stream().max(Integer::compare).orElseThrow(),
                        decision.column(),
                        "the column of " + decision.unit().stop() + " against what its rows reach");
                assertTrue(reached.contains(decision.column()),
                        "no row of this table needed column " + decision.column());
            }
        }
    }

    /**
     * A table's widths are its own. Widening a row of one table moves that table's columns and
     * leaves every other table where it was.
     *
     * <p>A pair rather than a constant. What this is about is that two tables do not share a width,
     * and a fixed set of numbers would say that only for the day the fixture was written.
     */
    @Test
    void aTableSettlesItsOwnColumnsAndNobodyElses() {
        List<Integer> before = Written.of(TWO_TABLES).columns();
        List<Integer> after = Written.of(
                TWO_TABLES.replace("\"a description of some length\"",
                        "\"a description of considerably more length than that\"")).columns();

        assertEquals(4, before.size(), "two tables with two columns each");
        assertNotEquals(before.subList(0, 2), after.subList(0, 2), "the table that was widened");
        assertEquals(before.subList(2, 4), after.subList(2, 4), "the table that was not");
    }

    /**
     * A row the canonical form writes down the page takes no part. Its connector opens a line, where
     * a column is not something a token can be at, so it neither reaches for one nor says how wide
     * the table is.
     *
     * <p>Measured as a pair: the table with the long row and the table without it settle the same
     * columns. A formatter that let the broken row set the width would move every other row out to
     * a column none of them can be written at.
     */
    @Test
    void aRowWrittenDownThePageTakesNoPartInTheColumns() {
        String longRow = "    | \"" + "d".repeat(60) + "\" : (" + "a".repeat(60) + ") -> P(9)\n";
        Written with = Written.of(TWO_TABLES.replace("    | (Off, Some) -> P(3)\n",
                "    | (Off, Some) -> P(3)\n" + longRow));
        Written without = Written.of(TWO_TABLES);

        assertEquals(without.columns(), with.columns(), "the columns the other rows settle");
        assertEquals(without.stops().size(), with.stops().size(),
                "the long row is written to no column");
        // And the row is still written. Said as the tokens the two texts share rather than as a
        // stretch of the output: what could go wrong here is a row dropped, and a row dropped is
        // tokens the canonical form does not have.
        assertEquals(with.pairing().hadCode().size(), with.code().size(),
                "the canonical form writes every code token the source had");
    }

    /**
     * Padding is not content the width has to make room for. A row carried past the width by its
     * table's column is not broken for it — the alternative is a column decided by which rows came
     * out flat, and which rows came out flat decided by the column.
     *
     * <p>The fixture writes lines over the width to say so: if the padding were measured, the rows
     * being padded are the ones that would break.
     */
    @Test
    void paddingIsNotMeasuredAgainstTheWidth() {
        String wide = """
                examples for demo

                example price
                    | "%s" : (A) -> P(1)
                    | "b" : (%s) -> P(2)
                """.formatted("d".repeat(60), "c".repeat(60));
        Written written = Written.of(wide);

        int longest = 0;
        for (String line : written.form().text().split("\n", -1)) {
            longest = Math.max(longest, Witnesses.columnAt(line + "\n", line.length()));
        }
        assertTrue(longest > 100, "the fixture writes a line over the width; it reaches " + longest);
        for (GroupDecision decision : written.form().layout().decisions()) {
            assertEquals(Outcome.Flat.class, decision.outcome().getClass(),
                    "a group broken although nothing but padding took it past the width");
        }
    }

    /**
     * A match forms no column. Its arms are read from the top down rather than against each other,
     * and lining their arrows up would move every arm out to the width of the longest.
     *
     * <p>Said as what the layout wrote rather than as what {@link Columns} lists: a table listed and
     * never reached and a construct that is not a table are the same list and different outputs.
     */
    @Test
    void theArmsOfAMatchFormNoColumn() {
        Written written = Written.of("""
                module demo

                let f (x) =
                    match x with
                        | Aaaaaaaaaaaaaaaa -> 1
                        | B -> 2
                """);

        assertEquals(List.of(), written.form().layout().stops());
        assertEquals(List.of(), written.form().layout().columns());
    }

    /**
     * Both halves of the report. A source whose table is not aligned is told which rule it departed
     * from, and repairing what the rules say writes the canonical form — so nothing about the table
     * is left for {@link Deviations.Report#whole} to be false about.
     *
     * <p>And the spacing rule says nothing there. The run before a connector is one rule's, and two
     * of them answering about the same characters is a conflict the model says is not there.
     */
    @Test
    void aTableThatIsNotAlignedIsReportedAsThisRule() {
        String misaligned = """
                examples for demo

                example price
                    | "a description of some length" : (Off, None) -> P(1)
                    | "short" : (On, Some) -> P(2)
                """;
        Deviations.Report report = Deviations.of(misaligned);

        Set<String> rules = new LinkedHashSet<>();
        report.deviations().forEach(d -> rules.add(d.rule()));
        assertEquals(Set.of(Columns.Stop.THE_INPUT_OF_AN_EXAMPLE.said(),
                        Columns.Stop.THE_RESULT_OF_AN_EXAMPLE.said()), rules);
        assertTrue(report.whole(), "every difference from the canonical form was named");

        Formatter.CanonicalForm form =
                Formatter.canonicalize(CstParser.parse(misaligned).root());
        for (Witness w : Witnesses.spacing(misaligned, form)) {
            assertEquals(Witness.BetweenTwoTokens.class, w.getClass());
        }
        assertEquals(0, Witnesses.spacing(misaligned, form).size(),
                "the spacing rule is not asked at a stop");
    }

    /**
     * A source that reaches the column by other characters is told so all the same.
     *
     * <p>The column rule answers about a column and a tab reaches one as well as spaces do, so what
     * the two texts differ by there is not something a column can be the answer about. The spacing
     * rule says it — the run before a connector is its answer and then the column's padding, and
     * that split is made on the source's side as well as on the canonical form's.
     *
     * <p>What this is really about is {@link Deviations.Report#whole}. Left to the column rule
     * alone, this source has nothing at all reported against it and is still not the canonical
     * form.
     */
    @Test
    void aSourceThatReachesTheColumnByOtherCharactersIsToldWhatItWrote() {
        Deviations.Report report = Deviations.of(A_TAB_REACHING_THE_COLUMN);

        Set<String> rules = new LinkedHashSet<>();
        report.deviations().forEach(d -> rules.add(d.rule()));
        assertTrue(rules.contains("what goes between two tokens on a line"),
                "the rule that quotes characters says what was written: " + rules);
        assertTrue(report.whole(), "every difference from the canonical form was named");
    }

    /**
     * A tab written after a column advances from where it stands, not from where it would have
     * stood unpadded.
     *
     * <p>How far a token carries a line depends on the column it starts at, which is the whole of
     * what a tab is. So the column a row reaches is counted on its own and not as what the width
     * measured plus the padding so far — the second is right for every token but that one, and
     * wrong for the rows of a table that holds it.
     */
    @Test
    void aTabWrittenAfterAColumnIsMeasuredFromWhereItStands() {
        Written written = Written.of(A_TAB_AFTER_A_COLUMN);

        Set<Integer> arrows = new LinkedHashSet<>();
        for (Witnesses.CanonicalStop stop : written.stops()) {
            if (stop.occurrence().unit().stop() == Columns.Stop.THE_RESULT_OF_AN_EXAMPLE) {
                arrows.add(written.columnOf(stop));
            }
        }
        assertEquals(1, arrows.size(), "the two rows write their arrow at " + arrows);
        assertTrue(Deviations.of(A_TAB_AFTER_A_COLUMN).whole(),
                "and repairing what the rules say writes it");
    }

    /**
     * A row that wrote no separator is told that, and not that its rows do not line up.
     *
     * <p>What the canonical form writes at a stop is the separator and then the padding, and which
     * of the two rules answers is settled by whether the source's run comes apart the same way. A
     * run of spaces and no separator comes apart that way only if the separator is nothing — so a
     * source that wrote no space at all is the spacing rule's, and the table is not brought into
     * it. Asked instead whether what stands there is spaces, an empty run answers yes, and this
     * one-row table is told its rows disagree with each other.
     */
    @Test
    void aRowThatWroteNoSeparatorIsToldThatAndNotAboutItsColumn() {
        Deviations.Report report = Deviations.of(NO_SEPARATOR);

        Set<String> rules = new LinkedHashSet<>();
        report.deviations().forEach(d -> rules.add(d.rule()));
        assertEquals(Set.of("what goes between two tokens on a line"), rules);
        assertTrue(report.whole(), "and repairing what the rules say writes the canonical form");
        assertEquals(List.of(), Witnesses.columns(NO_SEPARATOR,
                Formatter.canonicalize(CstParser.parse(NO_SEPARATOR).root())),
                "the column rule has nothing to say about this run");
    }

    /** Every stop the rule lists is one some source in the repository writes. */
    @Test
    void everyStopIsReached() {
        Set<Columns.Stop> reached = new LinkedHashSet<>();
        for (String source : sources()) {
            for (ColumnOccurrence stop : Written.of(source).form().layout().stops()) {
                reached.add(stop.unit().stop());
            }
        }
        assertEquals(Set.of(Columns.Stop.values()), reached);
    }

    /**
     * What these properties are held over: the fixtures above, the corpus the formatter's rules are
     * measured against — chosen to reach every kind of node the grammar has — and every {@code .sou}
     * file the repository holds.
     *
     * <p>The third of those is the one that makes this about the formatter rather than about a
     * fixture. The first two are what makes it about the cases a repository of well-written sources
     * does not contain: a corpus written by hand reaches no tab and no row too long for a line.
     */
    private static List<String> sources() {
        List<String> out = new ArrayList<>(
                List.of(TWO_TABLES, A_TAB_REACHING_THE_COLUMN, A_TAB_AFTER_A_COLUMN,
                        NO_SEPARATOR));
        out.addAll(WhatGoesBetweenTwoTokensOnALineTest.corpus());
        out.addAll(inTheRepository());
        return out;
    }

    /** Every {@code .sou} the repository holds, a build's copies of them left out. */
    private static List<String> inTheRepository() {
        try (java.util.stream.Stream<java.nio.file.Path> walk =
                java.nio.file.Files.walk(java.nio.file.Path.of(".."))) {
            List<String> out = new ArrayList<>();
            for (java.nio.file.Path p : walk.filter(q -> q.toString().endsWith(".sou"))
                    .filter(q -> !q.toString().contains("target")).sorted().toList()) {
                out.add(java.nio.file.Files.readString(p));
            }
            return out;
        } catch (java.io.IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }
}
