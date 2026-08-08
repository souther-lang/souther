package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two code tokens the formatter writes next to each other have exactly one boundary between them.
 * A construct free to leave one out would be saying what goes there by leaving it out, and the rule
 * would then hold at the sites that asked it rather than everywhere.
 *
 * <p>This does not say that the construct each boundary names is the one the canonical form has.
 * That is a separate check and it is not made yet — see issue #476.
 */
class EveryAdjacencyHasOneBoundaryTest {

    @Test
    void twoTokensWrittenNextToEachOtherHaveOneBoundaryBetweenThem() {
        List<String> unbounded = new ArrayList<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            unbounded.addAll(Gaps.adjacenciesWithNoBoundary(
                    Formatter.document(CstParser.parse(source).root())));
        }
        assertEquals(List.of(), unbounded.stream().distinct().toList(),
                "pairs written next to each other with nothing between them to decide");
    }

}
