package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many members a bracketed construct holds is a formatting decision, and it is not a kind of
 * node. A corpus that builds every node kind can still hold every bracketed construct with members
 * in it and never write one empty, and an empty one is where the layout of the brackets themselves
 * is decided — the two boundaries a construct writes just inside its brackets meet, and whatever
 * they write lands in one gap.
 *
 * <p>That is not hypothetical. Sweeping this found two things: a construct written open put two
 * spaces between its brackets ({@code exposing (  )}), which no rule said; and a product body with
 * no fields lost its opening brace altogether and did not reparse, because the block writes that
 * brace on its first member's line and there was no member to write it on.
 *
 * <p>So the unit swept here is the construct and its cardinality — none, one, and more than one —
 * and the cardinalities a construct cannot take are read from the parser, as the pairs a file cannot
 * hold are in {@link WhatSeparatesTwoItemsComesFromBothOfThemTest}.
 */
class AllOfABracketedConstructsCardinalitiesAreSweptTest {

    private static final Set<SyntaxKind> OPENS =
            Set.of(SyntaxKind.LPAREN, SyntaxKind.LBRACKET, SyntaxKind.LBRACE);
    private static final Set<SyntaxKind> CLOSES =
            Set.of(SyntaxKind.RPAREN, SyntaxKind.RBRACKET, SyntaxKind.RBRACE);

    /**
     * How many members a bracketed node holds, or null where it is not a bracketed node — one whose
     * own children hold the opening bracket and the closing one.
     */
    private static String cardinality(SyntaxNode n) {
        List<SyntaxElement> kids = new ArrayList<>(n.children());
        int open = -1;
        int close = -1;
        for (int i = 0; i < kids.size(); i++) {
            if (kids.get(i) instanceof SyntaxToken t && !t.isTrivia()) {
                if (open < 0 && OPENS.contains(t.kind())) {
                    open = i;
                } else if (open >= 0 && CLOSES.contains(t.kind())) {
                    close = i;
                }
            }
        }
        if (open < 0 || close < 0) {
            return null;
        }
        int commas = 0;
        boolean anything = false;
        for (int i = open + 1; i < close; i++) {
            if (kids.get(i) instanceof SyntaxNode) {
                anything = true;
            } else if (kids.get(i) instanceof SyntaxToken t && !t.isTrivia()) {
                anything = true;
                if (t.kind() == SyntaxKind.COMMA) {
                    commas++;
                }
            }
        }
        return !anything ? "none" : commas == 0 ? "one" : "many";
    }

    private static void walk(SyntaxNode n, List<SyntaxNode> out) {
        out.add(n);
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                walk(c, out);
            }
        }
    }

    /** Every bracketed construct in the corpus, against the cardinalities the corpus writes it at. */
    private static Map<String, Set<String>> observed() {
        Map<String, Set<String>> out = new TreeMap<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            List<SyntaxNode> all = new ArrayList<>();
            walk(CstParser.parse(Formatter.format(source)).root(), all);
            for (SyntaxNode n : all) {
                String card = cardinality(n);
                if (card != null) {
                    out.computeIfAbsent(n.kind().name(), _ -> new TreeSet<>()).add(card);
                }
            }
        }
        return out;
    }

    /** The cardinalities the grammar admits, per bracketed construct. */
    private static final Map<String, Set<String>> ADMITTED = admitted();

    private static Map<String, Set<String>> admitted() {
        Map<String, Set<String>> out = new TreeMap<>();
        out.put("ARG_LIST", Set.of("none", "one", "many"));
        out.put("EXPOSING_CLAUSE", Set.of("none", "one", "many"));
        out.put("LIST_EXPR", Set.of("none", "one", "many"));
        out.put("NAME_LIST", Set.of("none", "one", "many"));
        out.put("NEW_DATA_EXPR", Set.of("none", "one", "many"));
        out.put("PARAM_LIST", Set.of("none", "one", "many"));
        out.put("PATTERN_RECORD", Set.of("none", "one", "many"));
        out.put("PRODUCT_BODY", Set.of("none", "one", "many"));
        out.put("FN_TYPE", Set.of("none", "one", "many"));
        // A block ends in a result expression, so it holds one thing at least — and its statements
        // are not separated by commas, so this measure cannot tell one from several. That a block
        // writes each of them on a line of its own is what AForcedBreakIsWrittenWhateverTheWidthTest
        // says, and this row is about its brackets.
        out.put("BLOCK_EXPR", Set.of("one"));
        // `let f ()` is refused: a definition with no parameters is written without brackets
        out.put("FN_PARAM_LIST", Set.of("one", "many"));
        // a lambda's parameters open an expression, and `()` opens none
        out.put("LAMBDA_EXPR", Set.of("one", "many"));
        // what a constructor opens, and what an arm destructures, is one value
        out.put("PATTERN_CTOR", Set.of("one"));
        out.put("MATCH_CASE", Set.of("one", "many"));
        // brackets around one expression, one type, one pattern
        out.put("PAREN_EXPR", Set.of("one"));
        // brackets around one expression are a parenthesised expression, not a tuple of one
        out.put("TUPLE_EXPR", Set.of("many"));
        out.put("TUPLE_TYPE", Set.of("one", "many"));
        out.put("PATTERN_TUPLE", Set.of("one", "many"));
        // an element and the guards over it
        out.put("LIST_COMP", Set.of("one", "many"));
        return out;
    }

    /**
     * Every bracketed construct the corpus builds has a row saying which cardinalities it admits. A
     * construct added to the grammar, or one that starts holding brackets, is a construct whose empty
     * form nothing has looked at.
     */
    @Test
    void everyBracketedConstructHasARow() {
        assertEquals(new TreeSet<>(ADMITTED.keySet()), new TreeSet<>(observed().keySet()));
    }

    /** And the corpus writes each of them at every cardinality its row admits. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("bracketed")
    void theCorpusWritesItAtEveryCardinalityItAdmits(String construct) {
        assertEquals(new TreeSet<>(ADMITTED.get(construct)),
                new TreeSet<>(observed().getOrDefault(construct, Set.of())),
                construct + ": the cardinalities the corpus writes it at");
    }

    static Stream<String> bracketed() {
        return ADMITTED.keySet().stream();
    }

    /** The sources whose cardinality the grammar refuses, which is what keeps the rows above short. */
    record Refused(String name, String source) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Refused> refused() {
        return Stream.of(
                new Refused("a block with no result", "module m\n\nlet f (a: Int): Int = {}\n"),
                new Refused("a definition with empty brackets", "module m\n\nlet f (): Int = 1\n"),
                new Refused("a lambda with no parameter",
                        "module m\n\nlet f (a: Int): Int = call(() -> 1)\n"),
                new Refused("an arm destructuring nothing",
                        "module m\n\nlet f (a: Int): Int = match a with\n    | A() -> 1\n"),
                new Refused("a constructor opening nothing",
                        "module m\n\nlet f (w: W): Int = {\n    let W() = w\n    1\n}\n"));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("refused")
    void andTheGrammarRefusesTheCardinalitiesNoRowAdmits(Refused refused) {
        assertTrue(!CstParser.parse(refused.source()).errors().isEmpty(),
                refused.name() + ": the grammar admits this, so a row above is missing a cardinality");
    }

    /**
     * A construct with nothing between its brackets writes them with nothing between them. This is
     * the decision the empty form is about, and the one that was being made by two boundaries landing
     * in the same gap.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("empties")
    void bracketsWithNothingBetweenThemAreWrittenTogether(String source) {
        String canonical = Formatter.format(source);
        assertTrue(canonical.contains("()") || canonical.contains("{}") || canonical.contains("[]"),
                "nothing in this holds a pair of brackets with nothing between them:\n" + canonical);
        assertTrue(!canonical.contains("(  )") && !canonical.contains("{  }")
                        && !canonical.contains("[  ]") && !canonical.contains("( )")
                        && !canonical.contains("{ }") && !canonical.contains("[ ]"),
                "a pair of brackets holds only whitespace:\n" + canonical);
        assertEquals(canonical, Formatter.format(canonical), "and it is where the canonical form stays");
        assertTrue(CstParser.parse(canonical).errors().isEmpty(),
                "the canonical form does not reparse:\n" + canonical);
    }

    static Stream<String> empties() {
        return Stream.of(
                "module m exposing ()\n",
                "module m\n\nimport other.mod ()\n",
                "module m\n\ndata R = {}\n",
                "module m\n\nlet f (a: Int): Int = g()\n",
                "module m\n\nlet f (a: Int): List<Int> = []\n",
                "module m\n\nlet f (a: Int): R = R {}\n",
                "module m\n\nbehavior b : () -> R\n",
                "module m\n\nlet f (t: () -> Int): Int = 1\n",
                "module m\n\nlet f (r: R): Int = {\n    let {} = r\n    1\n}\n");
    }

    /**
     * A bracketed construct holding only comments is not empty. The comments stand where a member
     * would, so the brackets keep the lines they open and close, and nothing is dropped on the way.
     */
    @Test
    void bracketsHoldingOnlyCommentsKeepTheirLines() {
        assertEquals("""
                module m

                data R =
                    {
                    // nothing yet
                    }
                """, Formatter.format("""
                module m

                data R = {
                // nothing yet
                }
                """));
    }
}
