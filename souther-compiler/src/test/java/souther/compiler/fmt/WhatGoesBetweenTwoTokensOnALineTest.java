package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.Reserved;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the canonical form writes between two code tokens that share a line. Two things are asserted,
 * and the second is a bound on what a rule for the first may read.
 *
 * <p>There is no third separator: whatever the source wrote between two tokens, the canonical form
 * writes nothing or one space. That is where the alignment goes.
 *
 * <p>And the choice between the two is not a function of the tokens. Neither their kinds nor their
 * text decides it — the same pair takes both answers in one file — so a rule for this reads where
 * the tokens are and not what they are.
 */
class WhatGoesBetweenTwoTokensOnALineTest {

    private static List<SyntaxToken> tokens(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                out.addAll(tokens(c));
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
        return out;
    }

    /** What the canonical form of {@code source} writes between each pair of code tokens that share
     * a line. Pairs that a break separated are not this rule's, and are left out. */
    private static List<String> separatorsIn(String canonical) {
        List<SyntaxToken> code = tokens(CstParser.parse(canonical).root()).stream()
                .filter(t -> !t.isTrivia()).toList();
        List<String> out = new ArrayList<>();
        for (int i = 0; i + 1 < code.size(); i++) {
            String gap = canonical.substring(code.get(i).end(), code.get(i + 1).start());
            if (!gap.contains("\n")) {
                out.add(gap);
            }
        }
        return out;
    }

    /** The bundled standard library, which is the largest body of Souther this repository has. */
    static Stream<String> stdlibModules() {
        return Reserved.MODULES.stream().map(m -> m.moduleName().substring("souther.".length()));
    }

    private static String read(String module) {
        String resource = "/souther/" + module + ".sou";
        try (InputStream in = WhatGoesBetweenTwoTokensOnALineTest.class.getResourceAsStream(resource)) {
            assertTrue(in != null, "missing bundled source " + resource);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * Nothing or one space, over every adjacent pair the standard library writes. Alignment is what
     * this rules out: a column of {@code =} signs lined up under each other needs a run of spaces
     * between two tokens, and no such run survives.
     */
    @ParameterizedTest(name = "{0}.sou")
    @MethodSource("stdlibModules")
    void everySeparatorIsNothingOrOneSpace(String module) {
        String canonical = Formatter.format(read(module));
        Set<String> seen = new LinkedHashSet<>(separatorsIn(canonical));
        assertEquals(Set.of("", " "), seen,
                module + ".sou writes " + seen + " between tokens that share a line");
    }

    /** And there is enough of it for that to mean something. */
    @Test
    void theStandardLibraryHasBothOfThem() {
        List<String> all = new ArrayList<>();
        stdlibModules().forEach(m -> all.addAll(separatorsIn(Formatter.format(read(m)))));
        assertTrue(all.size() > 1000, "only " + all.size() + " adjacent pairs to look at");
        assertTrue(all.contains(""), "no pair is written with nothing between it");
        assertTrue(all.contains(" "), "no pair is written with a space between it");
    }

    /**
     * A pair of tokens written both ways in one file. The two occurrences are the same two tokens —
     * the same text, and so the same kinds — so nothing about the pair itself can tell them apart.
     *
     * @param joined how the pair reads where the canonical form writes nothing between them
     * @param spaced how it reads where it writes a space
     */
    record BothWays(String name, String source, String joined, String spaced) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<BothWays> bothWays() {
        return Stream.of(
                new BothWays("a name and the `(` after it",
                        """
                        module m exposing ( f )

                        let mapTwice (xs: List<Int>): List<Int> = mapTwice(xs)
                        """,
                        "mapTwice(xs)", "mapTwice (xs: List<Int>)"),

                new BothWays("a name and the `<` after it",
                        """
                        module m exposing ( f )

                        data Wrapper = List<Int>

                        let lessThan (a: Int, b: Int): Bool = a < b
                        """,
                        "List<Int>", "a < b"),

                new BothWays("a `)` and what follows it",
                        """
                        module m exposing ( f )

                        let f (a: Int): Int = alpha
                        """,
                        "(a: Int):", "(a: Int): Int ="));
    }

    /**
     * The same two tokens, written with nothing between them in one place and a space in another. So
     * the pair does not decide it, and a rule that reads only the tokens — their kinds, or their text
     * — cannot be written. What is left for a rule to read is the position: which construct is being
     * written, and which part of it.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("bothWays")
    void theSamePairOfTokensIsWrittenBothWays(BothWays pair) {
        String canonical = Formatter.format(pair.source());
        assertTrue(canonical.contains(pair.joined()),
                pair.name() + ": nothing holds `" + pair.joined() + "` in:\n" + canonical);
        assertTrue(canonical.contains(pair.spaced()),
                pair.name() + ": nothing holds `" + pair.spaced() + "` in:\n" + canonical);
    }
}
