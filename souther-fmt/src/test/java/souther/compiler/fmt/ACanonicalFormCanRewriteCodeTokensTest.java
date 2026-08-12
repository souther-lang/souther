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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the canonical form changes that is not whitespace. The rules swept elsewhere in this package
 * decide layout — where a line breaks, how far a level indents, what goes between two tokens. These
 * decide the tokens.
 *
 * <p>There are three kinds of them, and they are not the same problem:
 *
 * <ul>
 *   <li>a token is <b>removed</b> — a trailing comma, which every comma-separated list may carry and
 *       the canonical form writes none of. Each of those lists is a row here: the grammar admits one
 *       in fourteen constructs, which is every loop in {@code CstParser} that reads a comma;
 *   <li>a token is <b>added</b> — the {@code |} in front of a match's first arm, which the grammar
 *       makes optional and the canonical form always writes;
 *   <li>tokens are <b>rewritten</b> — a definition whose right-hand side is a lambda is written with
 *       its parameters on the left, which moves the {@code =} and drops the {@code ->}.
 * </ul>
 *
 * <p>This is written down because of what rests on it. The sweep in
 * {@link WhatGoesBetweenTwoTokensOnALineTest} compares the gap between the source's token <i>i</i>
 * and the canonical form's token <i>i</i>, and #444 derived from that correspondence that computing
 * a deviation witness is an index operation rather than a sequence alignment. That holds while the
 * two token streams are the same, and over this repository's sources they are — none of them writes
 * a trailing comma, an unbarred first arm, or a lambda on the right of a definition. Over the
 * language they are not, and the third kind is not repairable by aligning around insertions and
 * deletions either.
 *
 * <p>Whether the canonical form should do any of this is a question about what canonical form is,
 * and it is not settled by leaving it unwritten. What it does today is here.
 */
class ACanonicalFormCanRewriteCodeTokensTest {

    /** @param change what the canonical form does to the code tokens */
    record Rewrite(String name, String change, String source, String canonical) {
        @Override
        public String toString() {
            return name + " — " + change;
        }
    }

    private static final String REMOVED = "a token is removed";
    private static final String ADDED = "a token is added";
    private static final String REWRITTEN = "the tokens are rewritten";

    static Stream<Rewrite> rewrites() {
        return Stream.of(
                new Rewrite("a trailing comma in a call's arguments", REMOVED,
                        "module m\n\nlet f (a: Int): Int = g(a,)\n",
                        "module m\n\nlet f (a: Int): Int = g(a)\n"),
                new Rewrite("a trailing comma in a list", REMOVED,
                        "module m\n\nlet f (a: Int): List<Int> = [a,]\n",
                        "module m\n\nlet f (a: Int): List<Int> = [a]\n"),
                new Rewrite("a trailing comma in a definition's parameters", REMOVED,
                        "module m\n\nlet f (a: Int,): Int = 1\n",
                        "module m\n\nlet f (a: Int): Int = 1\n"),
                new Rewrite("a trailing comma in a module's exposed names", REMOVED,
                        "module m exposing ( f, )\n",
                        "module m exposing ( f )\n"),
                new Rewrite("a trailing comma in a product's fields", REMOVED,
                        "module m\n\ndata R =\n    { a: Int,\n    }\n",
                        "module m\n\ndata R =\n    { a: Int\n    }\n"),
                new Rewrite("a trailing comma in a tuple", REMOVED,
                        "module m\n\nlet t = (1, 2,)\n",
                        "module m\n\nlet t = (1, 2)\n"),
                new Rewrite("a trailing comma in a tuple type", REMOVED,
                        "module m\n\nlet f (a: (Int, Int,)): Int = 1\n",
                        "module m\n\nlet f (a: (Int, Int)): Int = 1\n"),
                new Rewrite("a trailing comma in a record literal's fields", REMOVED,
                        "module m\n\ndata R =\n    { a: Int\n    }\n\nlet r = R { a = 1, }\n",
                        "module m\n\ndata R =\n    { a: Int\n    }\n\nlet r = R { a = 1 }\n"),
                new Rewrite("a trailing comma in a type argument list", REMOVED,
                        "module m\n\nlet f (a: Map<String, Int,>): Int = 1\n",
                        "module m\n\nlet f (a: Map<String, Int>): Int = 1\n"),
                new Rewrite("a trailing comma in a lambda's parameters", REMOVED,
                        "module m\n\nlet f: (Int, Int) -> Int = (x, y,) -> x\n",
                        "module m\n\nlet f: (Int, Int) -> Int = (x, y) -> x\n"),
                new Rewrite("a trailing comma in a `constructs` name list", REMOVED,
                        "module m exposing (b)\n\ndata R =\n    { a: Int\n    }\n\nbehavior b : (n: Int)"
                                + " -> R\n    constructs R,\n\nlet b (n) = R { a = n }\n",
                        "module m exposing ( b )\n\ndata R =\n    { a: Int\n    }\n\nbehavior b :"
                                + " (n: Int) -> R\n    constructs R\n\nlet b (n) = R { a = n }\n"),
                new Rewrite("a trailing comma in a behavior's parameters", REMOVED,
                        "module m exposing (b)\n\ndata R =\n    { a: Int\n    }\n\nbehavior b :"
                                + " (n: Int,) -> R\n    constructs R\n\nlet b (n) = R { a = n }\n",
                        "module m exposing ( b )\n\ndata R =\n    { a: Int\n    }\n\nbehavior b :"
                                + " (n: Int) -> R\n    constructs R\n\nlet b (n) = R { a = n }\n"),
                new Rewrite("a trailing comma in an example row's arguments", REMOVED,
                        "module m exposing (b)\n\ndata R =\n    { a: Int\n    }\n\nbehavior b :"
                                + " (n: Int) -> R\n    constructs R\n\nlet b (n) = R { a = n }\n\n"
                                + "example b\n    | (1,) -> R { a = 1 }\n",
                        "module m exposing ( b )\n\ndata R =\n    { a: Int\n    }\n\nbehavior b :"
                                + " (n: Int) -> R\n    constructs R\n\nlet b (n) = R { a = n }\n\n"
                                + "example b\n    | (1) -> R { a = 1 }\n"),
                new Rewrite("a trailing comma in an example row's `with` bindings", REMOVED,
                        "examples for m\n\nexample helper\n"
                                + "    | (1) with dep = two, other = three, -> 2\n",
                        "examples for m\n\nexample helper\n"
                                + "    | (1) with dep = two, other = three -> 2\n"),

                new Rewrite("the bar in front of a match's first arm", ADDED,
                        "module m\n\nlet f (a: Int): Int =\n    match a with\n        A -> 1\n        | B -> 2\n",
                        "module m\n\nlet f (a: Int): Int =\n    match a with\n        | A -> 1\n        | B -> 2\n"),

                new Rewrite("a definition whose body is a lambda", REWRITTEN,
                        "module m\n\nlet f = (x) -> x\n",
                        "module m\n\nlet f (x) = x\n"),
                new Rewrite("and one taking more than one parameter", REWRITTEN,
                        "module m\n\nlet f = (x, y) -> x\n",
                        "module m\n\nlet f (x, y) = x\n"));
    }

    private static List<String> codeTokens(String source) {
        List<SyntaxToken> all = new ArrayList<>();
        collect(CstParser.parse(source).root(), all);
        List<String> out = new ArrayList<>();
        for (SyntaxToken t : all) {
            if (!t.isTrivia() && t.kind() != SyntaxKind.EOF) {
                out.add(t.kind().name());
            }
        }
        return out;
    }

    private static void collect(SyntaxNode n, List<SyntaxToken> out) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                collect(c, out);
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
    }

    /** Each source is one the grammar admits, so these are rules and not repairs. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("rewrites")
    void theGrammarAdmitsTheSource(Rewrite rewrite) {
        assertEquals(List.of(), CstParser.parse(rewrite.source()).errors());
    }

    /** And this is what the canonical form makes of it. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("rewrites")
    void andThisIsWhatTheCanonicalFormWrites(Rewrite rewrite) {
        assertEquals(rewrite.canonical(), Formatter.format(rewrite.source()));
    }

    /**
     * The code tokens are not the ones the source wrote. Stated as which of the three kinds of change
     * it is, because they cost a deviation witness different things: one deletion can be aligned
     * around, one insertion can be aligned around, and a rewrite that moves a token past another
     * cannot be described as either.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("rewrites")
    void andTheCodeTokenStreamChangedInThisWay(Rewrite rewrite) {
        List<String> before = codeTokens(rewrite.source());
        List<String> after = codeTokens(rewrite.canonical());
        assertTrue(!before.equals(after), "the code tokens did not change at all");
        switch (rewrite.change()) {
            case REMOVED -> assertEquals(before.size() - 1, after.size(),
                    "one fewer token was expected\n  " + before + "\n  " + after);
            case ADDED -> assertEquals(before.size() + 1, after.size(),
                    "one more token was expected\n  " + before + "\n  " + after);
            case REWRITTEN -> {
                assertEquals(before.size() - 1, after.size(),
                        "the `->` was expected to go\n  " + before + "\n  " + after);
                assertTrue(before.indexOf("ASSIGN") < before.indexOf("LPAREN"),
                        "the source writes `=` before the parameters: " + before);
                assertTrue(after.indexOf("ASSIGN") > after.indexOf("RPAREN"),
                        "the canonical form writes it after them: " + after);
            }
            default -> throw new AssertionError("no such change: " + rewrite.change());
        }
    }

    /** And what it writes reparses and stays where it is. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("rewrites")
    void andWhatItWritesStaysWhereItIs(Rewrite rewrite) {
        assertTrue(CstParser.parse(rewrite.canonical()).errors().isEmpty());
        assertEquals(rewrite.canonical(), Formatter.format(rewrite.canonical()));
    }

    /**
     * All three kinds occur. Without this the rows above could be read as one thing the canonical
     * form does to code tokens, which is what they were read as until the third was found.
     */
    @Test
    void allThreeKindsOfChangeAreHere() {
        Set<String> kinds = new LinkedHashSet<>();
        rewrites().forEach(r -> kinds.add(r.change()));
        assertEquals(Set.of(REMOVED, ADDED, REWRITTEN), kinds);
    }
}
