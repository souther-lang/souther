package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link Spacing#between} writes what the canonical form writes. Every separator in the output is
 * now this function's, so what this says is not that a new function agrees with the constructs that
 * used to spell them — it is that the one place they were moved to still writes what they wrote.
 *
 * <p>What it is held against is the rendered text: the corpus is formatted, the output is parsed
 * again, and the interval between two tokens the output left on one line is read off the output.
 * The table the function holds is not consulted. {@link WhatGoesBetweenTwoTokensOnALineTest} states
 * the same rule as a table of its own and reaches it the same way, and the two transcriptions are
 * deliberately separate: this one is the implementation's, that one is the specification's, and
 * they meet only here, through what the formatter actually wrote.
 *
 * <p>Only the intervals the output left unbroken. What is written at a boundary the layout broke is
 * a newline and an indent, and those are the break rules' — the function has no answer for them.
 */
class TheSpacingRuleAgreesWithTheCanonicalFormTest {

    /** Every pair the corpus writes, written as the function says it is. */
    @Test
    void everyUnbrokenAdjacencyIsWrittenAsTheRuleSays() {
        List<String> wrong = new ArrayList<>();
        for (WhatGoesBetweenTwoTokensOnALineTest.Adjacency a
                : WhatGoesBetweenTwoTokensOnALineTest.adjacencies()) {
            String answer;
            try {
                answer = Spacing.between(a.joins(), a.left(), a.right());
            } catch (IllegalStateException e) {
                wrong.add(a.joins() + ": " + a.pair() + " -> " + e.getMessage());
                continue;
            }
            if (!answer.equals(a.separator())) {
                wrong.add(a.joins() + ": " + a.pair()
                        + " -> the rule says [" + answer + "] and the canonical form has ["
                        + a.separator() + "]");
            }
        }
        assertEquals(List.of(), wrong.stream().distinct().toList(),
                "adjacencies written against the rule");
    }

    /**
     * And it is not passing on an empty hand: this many distinct pairs are reached. It does not say
     * the rule holds no row the corpus never asks about — it holds several, and what says those are
     * right is that every {@code .sou} in the repository formats as it did.
     */
    @Test
    void andTheCorpusReachesThisManyPairs() {
        Set<String> reached = new LinkedHashSet<>();
        for (WhatGoesBetweenTwoTokensOnALineTest.Adjacency a
                : WhatGoesBetweenTwoTokensOnALineTest.adjacencies()) {
            reached.add(a.pair());
        }
        assertEquals(191, reached.size(),
                "the pairs the corpus writes: 45 tight, 137 spaced, 9 the construct decides");
    }

    /**
     * A value written out is a value written out, whichever kind of one it is. The corpus reaches
     * one of them in a position and a source reaches another — an integer in a list where someone
     * else writes a decimal — and the rule answers both, because it reads the rows under one class
     * for them. Before it did, a decimal in a list was an adjacency no row held and the formatter
     * refused a source it had nothing wrong with.
     */
    @Test
    void aValueWrittenOutIsAnsweredWhicheverKindOfOneItIs() {
        String source = """
                module m

                let listed (a: Int): List<Decimal> = [2.5m, 3.5m]

                let called (a: Int): Int = f(1.5m, "x", true, false)

                let made (a: Int): R = R { k = 1.5m, s = "t", b = false }

                let compared (a: Decimal): Bool = a <= 1.5m
                """;
        assertEquals(source, Formatter.format(source));
    }
}
