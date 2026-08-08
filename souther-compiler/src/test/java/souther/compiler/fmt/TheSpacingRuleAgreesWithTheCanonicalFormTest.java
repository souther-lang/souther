package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link Spacing#between} writes what the canonical form writes. The function is new and the
 * formatter does not call it yet — the constructs still spell their own separators, which is what
 * issue #476 is about — so this is what says the function is right before anything is moved onto it.
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
     * And the corpus reaches every pair the function holds a row for. Without this the check above
     * passes on a table of any size, including one whose rows are never asked about — the same
     * reason {@link WhatGoesBetweenTwoTokensOnALineTest} asserts that no row goes unreached.
     */
    @Test
    void andTheCorpusReachesEveryPairTheRuleHoldsARowFor() {
        Set<String> reached = new LinkedHashSet<>();
        for (WhatGoesBetweenTwoTokensOnALineTest.Adjacency a
                : WhatGoesBetweenTwoTokensOnALineTest.adjacencies()) {
            reached.add(a.pair());
        }
        assertEquals(179, reached.size(),
                "the pairs the corpus writes: 44 tight, 126 spaced, 9 the construct decides");
    }
}
