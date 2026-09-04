package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many members a construct holds between one pair of brackets is a formatting decision, and it is
 * neither a kind of node nor a property of one. A corpus can build every node kind the grammar has
 * and still write every construct with something between its brackets, and the empty one is where the
 * layout of the brackets themselves is settled — what a construct writes just inside each of them
 * meets in one gap when there is nothing to separate.
 *
 * <p>The unit is the <b>bracket site</b>: a node kind and the bracket that opens the run, because one
 * node can hold several. A match arm holds the parentheses a constructor opens and the braces a
 * record destructuring opens, and they are not the same decision — one is written closed and the
 * other open, and the arm can nest more of the first inside itself.
 *
 * <p>Which cardinalities a site admits is not written down here. Each cell carries a source that
 * would produce it, and what the cell admits is what the parser and the tree say that source builds:
 * a source the grammar refuses admits nothing, and so does one that parses as a different site. The
 * expected set per site is checked against that, so a cell claimed and a cell reachable cannot drift
 * apart.
 *
 * <p>Sweeping this found three defects. A construct written open put two spaces between its brackets
 * ({@code exposing (  )}). A product body with no fields lost its opening brace and did not reparse.
 * And a match arm's record destructuring, which is built as a run of tokens rather than as a
 * document, wrote {@code A { }} where every other empty bracket is written together.
 */
@Tag("population")
class AllOfABracketedConstructsCardinalitiesAreSweptTest {

    /** A pair of brackets a construct is written between, and what the corpus writes in it. */
    record Site(SyntaxKind node, SyntaxKind opener) implements Comparable<Site> {
        @Override
        public String toString() {
            return node + " " + opener;
        }

        @Override
        public int compareTo(Site other) {
            return toString().compareTo(other.toString());
        }
    }

    /** Each matched pair of brackets among a node's own children, and how many members it holds. */
    private static Map<Site, String> bracketsOf(SyntaxNode n) {
        List<SyntaxElement> kids = new ArrayList<>(n.children());
        Deque<Integer> opened = new ArrayDeque<>();
        Map<Site, String> out = new LinkedHashMap<>();
        for (int i = 0; i < kids.size(); i++) {
            if (!(kids.get(i) instanceof SyntaxToken t) || t.isTrivia()) {
                continue;
            }
            if (Formatter.isOpeningBracket(t.kind())) {
                opened.push(i);
            } else if (Formatter.isClosingBracket(t.kind()) && !opened.isEmpty()) {
                int from = opened.pop();
                out.put(new Site(n.kind(), ((SyntaxToken) kids.get(from)).kind()),
                        held(kids, from, i));
            }
        }
        return out;
    }

    /**
     * None, one, or more than one member between these brackets. Counted as the commas at this
     * bracket's own depth, less the one a trailing comma contributes — every comma-separated list may
     * carry one, and it separates a member from nothing. Reading the count off the commas alone says
     * {@code g(a,)} holds two, which is what a detector that had only ever seen canonical output
     * would never find out: the formatter does not write a trailing comma, so it cannot be measured
     * downstream of one.
     */
    private static String held(List<SyntaxElement> kids, int from, int to) {
        int commas = 0;
        int depth = 0;
        boolean anything = false;
        boolean endsWithAComma = false;
        for (int i = from + 1; i < to; i++) {
            if (kids.get(i) instanceof SyntaxNode) {
                anything = true;
                endsWithAComma = false;
            } else if (kids.get(i) instanceof SyntaxToken t && !t.isTrivia()) {
                anything = true;
                endsWithAComma = false;
                if (Formatter.isOpeningBracket(t.kind())) {
                    depth++;
                } else if (Formatter.isClosingBracket(t.kind())) {
                    depth--;
                } else if (t.kind() == SyntaxKind.COMMA && depth == 0) {
                    commas++;
                    endsWithAComma = true;
                }
            }
        }
        if (!anything) {
            return "none";
        }
        int members = commas - (endsWithAComma ? 1 : 0) + 1;
        return members <= 1 ? "one" : "many";
    }

    private static void walk(SyntaxNode n, List<SyntaxNode> out) {
        out.add(n);
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                walk(c, out);
            }
        }
    }

    /** Every bracket site of a tree, against the cardinalities it holds them at. */
    private static Map<Site, Set<String>> sitesOf(SyntaxNode root) {
        Map<Site, Set<String>> out = new TreeMap<>();
        List<SyntaxNode> all = new ArrayList<>();
        walk(root, all);
        for (SyntaxNode n : all) {
            bracketsOf(n).forEach((site, held) ->
                    out.computeIfAbsent(site, _ -> new TreeSet<>()).add(held));
        }
        return out;
    }

    /** What the grammar builds from a source, which is a question for the parser alone. */
    private static Map<Site, Set<String>> sitesWritten(String source) {
        return sitesOf(CstParser.parse(source).root());
    }

    /** What the canonical form of a source holds, which is a question about the formatter. */
    private static Map<Site, Set<String>> sitesInTheCanonicalForm(String source) {
        return sitesOf(CstParser.parse(Formatter.format(source)).root());
    }

    /**
     * A cell of the sweep: one bracket site, one cardinality, and a source that would write it.
     *
     * @param admitted what the cell is expected to be — checked against what the source actually
     *     builds, so it is a claim about the grammar and not a licence to skip one
     */
    record Cell(Site site, String cardinality, String source, boolean admitted) {
        @Override
        public String toString() {
            return site + " holding " + cardinality + (admitted ? "" : " — which it cannot");
        }
    }

    private static final String IN_A_BLOCK =
            "module m\n\nlet f (r: R): Int = {\n    %s\n    1\n}\n";
    private static final String AS_A_BODY = "module m\n\nlet f (a: Int): Int = %s\n";
    private static final String AS_A_PARAM = "module m\n\nlet f (t: %s): Int = 1\n";
    private static final String AS_AN_ARM =
            "module m\n\nlet f (a: Int): Int =\n    match a with\n        | %s -> 1\n";

    private static Cell cell(SyntaxKind node, SyntaxKind opener, String cardinality,
            String source, boolean admitted) {
        return new Cell(new Site(node, opener), cardinality, source, admitted);
    }

    static Stream<Cell> cells() {
        return Stream.of(
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "none", AS_A_BODY.formatted("g()"), true),
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "one", AS_A_BODY.formatted("g(a)"), true),
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("g(a, a)"), true),

                cell(SyntaxKind.BLOCK_EXPR, SyntaxKind.LBRACE, "none", AS_A_BODY.formatted("{}"), false),
                cell(SyntaxKind.BLOCK_EXPR, SyntaxKind.LBRACE, "one", IN_A_BLOCK.formatted("let x = 1"), true),
                // a block's statements are not separated by commas, so this measure cannot see more
                // than one of them; that each takes a line of its own is the forced-break rule's
                cell(SyntaxKind.BLOCK_EXPR, SyntaxKind.LBRACE, "many", IN_A_BLOCK.formatted("let x = 1"), false),

                cell(SyntaxKind.EXPOSING_CLAUSE, SyntaxKind.LPAREN, "none", "module m exposing ()\n", true),
                cell(SyntaxKind.EXPOSING_CLAUSE, SyntaxKind.LPAREN, "one", "module m exposing ( f )\n", true),
                cell(SyntaxKind.EXPOSING_CLAUSE, SyntaxKind.LPAREN, "many", "module m exposing ( f, g )\n", true),

                cell(SyntaxKind.FN_PARAM_LIST, SyntaxKind.LPAREN, "none", "module m\n\nlet f (): Int = 1\n", false),
                cell(SyntaxKind.FN_PARAM_LIST, SyntaxKind.LPAREN, "one", "module m\n\nlet f (a: Int): Int = 1\n", true),
                cell(SyntaxKind.FN_PARAM_LIST, SyntaxKind.LPAREN, "many", "module m\n\nlet f (a: Int, b: Int): Int = 1\n", true),

                cell(SyntaxKind.FN_TYPE, SyntaxKind.LPAREN, "none", AS_A_PARAM.formatted("() -> Int"), true),
                cell(SyntaxKind.FN_TYPE, SyntaxKind.LPAREN, "one", AS_A_PARAM.formatted("(Int) -> Int"), true),
                cell(SyntaxKind.FN_TYPE, SyntaxKind.LPAREN, "many", AS_A_PARAM.formatted("(Int, Int) -> Int"), true),

                cell(SyntaxKind.LAMBDA_EXPR, SyntaxKind.LPAREN, "none", AS_A_BODY.formatted("call(() -> 1)"), false),
                cell(SyntaxKind.LAMBDA_EXPR, SyntaxKind.LPAREN, "one", AS_A_BODY.formatted("call((x) -> x)"), true),
                cell(SyntaxKind.LAMBDA_EXPR, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("call((x, y) -> x)"), true),

                // `[]` is a list, not a comprehension over nothing
                cell(SyntaxKind.LIST_COMP, SyntaxKind.LBRACKET, "none", AS_A_BODY.formatted("[]"), false),
                cell(SyntaxKind.LIST_COMP, SyntaxKind.LBRACKET, "one", AS_A_BODY.formatted("[x | x > 0]"), true),
                cell(SyntaxKind.LIST_COMP, SyntaxKind.LBRACKET, "many", AS_A_BODY.formatted("[x | x > 0, x < 9]"), true),

                cell(SyntaxKind.LIST_EXPR, SyntaxKind.LBRACKET, "none", AS_A_BODY.formatted("[]"), true),
                cell(SyntaxKind.LIST_EXPR, SyntaxKind.LBRACKET, "one", AS_A_BODY.formatted("[a]"), true),
                cell(SyntaxKind.LIST_EXPR, SyntaxKind.LBRACKET, "many", AS_A_BODY.formatted("[a, a]"), true),

                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LBRACE, "none", AS_AN_ARM.formatted("A {}"), true),
                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LBRACE, "one", AS_AN_ARM.formatted("A { a }"), true),
                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LBRACE, "many", AS_AN_ARM.formatted("A { a, b }"), true),

                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LPAREN, "none", AS_AN_ARM.formatted("A()"), false),
                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LPAREN, "one", AS_AN_ARM.formatted("A(x)"), true),
                // what a constructor opens is one value; a second is left for the arrow to refuse
                cell(SyntaxKind.MATCH_CASE, SyntaxKind.LPAREN, "many", AS_AN_ARM.formatted("A(x, y)"), false),

                cell(SyntaxKind.NAME_LIST, SyntaxKind.LPAREN, "none", "module m\n\nimport other.mod ()\n", true),
                cell(SyntaxKind.NAME_LIST, SyntaxKind.LPAREN, "one", "module m\n\nimport other.mod ( a )\n", true),
                cell(SyntaxKind.NAME_LIST, SyntaxKind.LPAREN, "many", "module m\n\nimport other.mod ( a, b )\n", true),

                cell(SyntaxKind.NEW_DATA_EXPR, SyntaxKind.LBRACE, "none", AS_A_BODY.formatted("R {}"), true),
                cell(SyntaxKind.NEW_DATA_EXPR, SyntaxKind.LBRACE, "one", AS_A_BODY.formatted("R { a = 1 }"), true),
                cell(SyntaxKind.NEW_DATA_EXPR, SyntaxKind.LBRACE, "many", AS_A_BODY.formatted("R { a = 1, b = 2 }"), true),

                cell(SyntaxKind.PARAM_LIST, SyntaxKind.LPAREN, "none", "module m\n\nbehavior b : () -> R\n", true),
                cell(SyntaxKind.PARAM_LIST, SyntaxKind.LPAREN, "one", "module m\n\nbehavior b : (a: A) -> R\n", true),
                cell(SyntaxKind.PARAM_LIST, SyntaxKind.LPAREN, "many", "module m\n\nbehavior b : (a: A, b: B) -> R\n", true),

                // `()` is no expression, and two are a tuple
                cell(SyntaxKind.PAREN_EXPR, SyntaxKind.LPAREN, "none", AS_A_BODY.formatted("()"), false),
                cell(SyntaxKind.PAREN_EXPR, SyntaxKind.LPAREN, "one", AS_A_BODY.formatted("(a)"), true),
                cell(SyntaxKind.PAREN_EXPR, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("(a, a)"), false),

                cell(SyntaxKind.PATTERN_CTOR, SyntaxKind.LPAREN, "none", IN_A_BLOCK.formatted("let W() = r"), false),
                cell(SyntaxKind.PATTERN_CTOR, SyntaxKind.LPAREN, "one", IN_A_BLOCK.formatted("let W(x) = r"), true),
                cell(SyntaxKind.PATTERN_CTOR, SyntaxKind.LPAREN, "many", IN_A_BLOCK.formatted("let W(x, y) = r"), false),

                cell(SyntaxKind.PATTERN_RECORD, SyntaxKind.LBRACE, "none", IN_A_BLOCK.formatted("let {} = r"), true),
                cell(SyntaxKind.PATTERN_RECORD, SyntaxKind.LBRACE, "one", IN_A_BLOCK.formatted("let { a } = r"), true),
                cell(SyntaxKind.PATTERN_RECORD, SyntaxKind.LBRACE, "many", IN_A_BLOCK.formatted("let { a, b } = r"), true),

                cell(SyntaxKind.PATTERN_TUPLE, SyntaxKind.LPAREN, "none", IN_A_BLOCK.formatted("let () = r"), true),
                cell(SyntaxKind.PATTERN_TUPLE, SyntaxKind.LPAREN, "one", IN_A_BLOCK.formatted("let (a) = r"), true),
                cell(SyntaxKind.PATTERN_TUPLE, SyntaxKind.LPAREN, "many", IN_A_BLOCK.formatted("let (a, b) = r"), true),

                cell(SyntaxKind.PRODUCT_BODY, SyntaxKind.LBRACE, "none", "module m\n\ndata R = {}\n", true),
                cell(SyntaxKind.PRODUCT_BODY, SyntaxKind.LBRACE, "one", "module m\n\ndata R =\n    { a: Int\n    }\n", true),
                cell(SyntaxKind.PRODUCT_BODY, SyntaxKind.LBRACE, "many",
                        "module m\n\ndata R =\n    { a: Int\n    , b: Int\n    }\n", true),

                cell(SyntaxKind.TUPLE_EXPR, SyntaxKind.LPAREN, "none", AS_A_BODY.formatted("()"), false),
                cell(SyntaxKind.TUPLE_EXPR, SyntaxKind.LPAREN, "one", AS_A_BODY.formatted("(a)"), false),
                cell(SyntaxKind.TUPLE_EXPR, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("(a, a)"), true),

                cell(SyntaxKind.TUPLE_TYPE, SyntaxKind.LPAREN, "none", AS_A_PARAM.formatted("()"), true),
                cell(SyntaxKind.TUPLE_TYPE, SyntaxKind.LPAREN, "one", AS_A_PARAM.formatted("(Int)"), true),
                cell(SyntaxKind.TUPLE_TYPE, SyntaxKind.LPAREN, "many", AS_A_PARAM.formatted("(Int, Int)"), true));
    }

    /**
     * What the source of a cell actually builds, read from the tree the parser makes of it. The
     * formatter is not asked: it is what these rows are about, and a source normalised before being
     * measured is a source measured against the answer.
     */
    private static boolean builds(Cell cell) {
        if (!CstParser.parse(cell.source()).errors().isEmpty()) {
            return false;
        }
        return sitesWritten(cell.source()).getOrDefault(cell.site(), Set.of())
                .contains(cell.cardinality());
    }

    /**
     * What a cell claims is what its source builds. A cell claimed and refused, or claimed and parsed
     * as some other site, is the hand-written half of a grammar model drifting from the grammar.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("cells")
    void whatTheCellClaimsIsWhatItsSourceBuilds(Cell cell) {
        assertEquals(cell.admitted(), builds(cell),
                cell.admitted()
                        ? "this source does not build it, so the cell claims a cardinality the"
                                + " grammar does not admit here:\n" + cell.source()
                        : "this source builds it, so the cell denies a cardinality the grammar"
                                + " admits:\n" + cell.source());
    }

    /** Every cell the grammar admits writes a canonical form that reparses and stays put. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("cells")
    void andItsCanonicalFormReparsesAndStays(Cell cell) {
        if (!cell.admitted()) {
            return;
        }
        String canonical = Formatter.format(cell.source());
        assertTrue(CstParser.parse(canonical).errors().isEmpty(),
                "the canonical form does not reparse:\n" + canonical);
        assertEquals(canonical, Formatter.format(canonical), "and it is not a fixed point");
    }

    /**
     * A construct with nothing between its brackets writes them with nothing between them. This is
     * the decision the empty form is about, and the one that was being made by two boundaries landing
     * in the same gap — and, on the path that builds a run of tokens rather than a document, by a
     * separator that knew nothing about brackets.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("empty")
    void bracketsWithNothingBetweenThemAreWrittenTogether(Cell cell) {
        String canonical = Formatter.format(cell.source());
        for (String held : List.of("(  )", "( )", "{  }", "{ }", "[  ]", "[ ]")) {
            assertTrue(!canonical.contains(held),
                    cell.site() + " writes `" + held + "`, which is a rule nothing states:\n" + canonical);
        }
    }

    static Stream<Cell> empty() {
        return cells().filter(c -> c.admitted() && c.cardinality().equals("none"));
    }

    /**
     * A trailing comma separates a member from nothing, so it does not add one. Measured on the tree
     * the parser makes, because the canonical form never has one to measure: a detector that counted
     * commas would answer "many" for a list of one, and reading it downstream of the formatter would
     * never show that.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("trailingCommas")
    void aTrailingCommaSeparatesAMemberFromNothing(Cell cell) {
        assertEquals(cell.admitted(), builds(cell),
                "the members between these brackets, counted on the source:\n" + cell.source());
    }

    static Stream<Cell> trailingCommas() {
        return Stream.of(
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "one", AS_A_BODY.formatted("g(a,)"), true),
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("g(a,)"), false),
                cell(SyntaxKind.ARG_LIST, SyntaxKind.LPAREN, "many", AS_A_BODY.formatted("g(a, a,)"), true),
                cell(SyntaxKind.LIST_EXPR, SyntaxKind.LBRACKET, "one", AS_A_BODY.formatted("[a,]"), true),
                cell(SyntaxKind.LIST_EXPR, SyntaxKind.LBRACKET, "many", AS_A_BODY.formatted("[a,]"), false),
                cell(SyntaxKind.FN_PARAM_LIST, SyntaxKind.LPAREN, "one",
                        "module m\n\nlet f (a: Int,): Int = 1\n", true),
                cell(SyntaxKind.PRODUCT_BODY, SyntaxKind.LBRACE, "one",
                        "module m\n\ndata R =\n    { a: Int,\n    }\n", true));
    }

    /**
     * Every bracket site the corpus builds has a row here, and the corpus writes it at every
     * cardinality the rows admit. A construct that starts holding a second pair of brackets — as a
     * match arm holds the parentheses of a constructor and the braces of a record — is a site whose
     * empty form nothing has looked at.
     */
    @Test
    void everyBracketSiteInTheCorpusIsSwept() {
        Map<Site, Set<String>> written = new TreeMap<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            sitesInTheCanonicalForm(source).forEach((site, held) ->
                    written.computeIfAbsent(site, _ -> new TreeSet<>()).addAll(held));
        }
        Map<Site, Set<String>> claimed = new TreeMap<>();
        cells().filter(Cell::admitted).forEach(c ->
                claimed.computeIfAbsent(c.site(), _ -> new TreeSet<>()).add(c.cardinality()));
        assertEquals(claimed.keySet(), written.keySet(), "the bracket sites swept, against those written");
        assertEquals(claimed, written, "the cardinalities swept, against those the corpus writes");
    }
}
