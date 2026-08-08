package souther.compiler.fmt;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The one thing the canonical form changes that is not whitespace. Every comma-separated list may
 * carry a single trailing comma, which the specification says is optional and means nothing; the
 * formatter writes none, so formatting a source that has one deletes a code token.
 *
 * <p>This is written down because of what rests on it. The sweep in {@link
 * WhatGoesBetweenTwoTokensOnALineTest} compares the gap between the source's token <i>i</i> and the
 * canonical form's token <i>i</i>, and that correspondence is an index only while the two streams
 * are the same length. Over this repository's sources they are, because none of them writes a
 * trailing comma. Over the language they are not.
 *
 * <p>So it belongs to a family of its own: the rules swept in this package decide layout, and this
 * one decides a code token. Which of the two the canonical form should be is a question for #444 and
 * not something to settle by leaving it unwritten.
 */
class ATrailingCommaIsRemovedAndIsNotWhitespaceTest {

    record Written(String name, String source, String canonical) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Written> lists() {
        return Stream.of(
                new Written("a call's arguments",
                        "module m\n\nlet f (a: Int): Int = g(a,)\n",
                        "module m\n\nlet f (a: Int): Int = g(a)\n"),
                new Written("a list",
                        "module m\n\nlet f (a: Int): List<Int> = [a,]\n",
                        "module m\n\nlet f (a: Int): List<Int> = [a]\n"),
                new Written("a definition's parameters",
                        "module m\n\nlet f (a: Int,): Int = 1\n",
                        "module m\n\nlet f (a: Int): Int = 1\n"),
                new Written("a module's exposed names",
                        "module m exposing ( f, )\n",
                        "module m exposing ( f )\n"),
                new Written("a product's fields",
                        "module m\n\ndata R =\n    { a: Int,\n    }\n",
                        "module m\n\ndata R =\n    { a: Int\n    }\n"));
    }

    private static List<String> codeTokens(String source) {
        List<SyntaxToken> all = new ArrayList<>();
        collect(CstParser.parse(source).root(), all);
        List<String> out = new ArrayList<>();
        for (SyntaxToken t : all) {
            if (!t.isTrivia() && t.kind() != SyntaxKind.EOF) {
                out.add(t.kind() + " " + t.text());
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

    /** The source is one the grammar admits, so this is a rule and not a repair. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("lists")
    void theGrammarAdmitsATrailingComma(Written written) {
        assertEquals(List.of(), CstParser.parse(written.source()).errors());
    }

    /** The canonical form drops it. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("lists")
    void theCanonicalFormWritesNone(Written written) {
        assertEquals(written.canonical(), Formatter.format(written.source()));
    }

    /**
     * And that is a code token, not whitespace: one fewer than the source had, and every token after
     * it moved. So the correspondence the deviation witness rests on — source token <i>i</i> against
     * canonical token <i>i</i> — does not hold for a source that writes one.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("lists")
    void andTheCodeTokenStreamIsOneShorter(Written written) {
        List<String> before = codeTokens(written.source());
        List<String> after = codeTokens(written.canonical());
        assertEquals(before.size() - 1, after.size(),
                "the source's tokens are " + before + "\nand the canonical form's " + after);
        List<String> withoutTheLastComma = new ArrayList<>(before);
        withoutTheLastComma.remove(lastComma(before));
        assertEquals(withoutTheLastComma, after, "and it is the trailing comma that went");
    }

    private static int lastComma(List<String> tokens) {
        for (int i = tokens.size() - 1; i >= 0; i--) {
            if (tokens.get(i).startsWith("COMMA")) {
                return i;
            }
        }
        throw new AssertionError("no comma in " + tokens);
    }

    /** Removing it is idempotent, so the canonical form is still a fixed point. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("lists")
    void andTheCanonicalFormStaysWhereItIs(Written written) {
        assertTrue(CstParser.parse(written.canonical()).errors().isEmpty());
        assertEquals(written.canonical(), Formatter.format(written.canonical()));
    }
}
