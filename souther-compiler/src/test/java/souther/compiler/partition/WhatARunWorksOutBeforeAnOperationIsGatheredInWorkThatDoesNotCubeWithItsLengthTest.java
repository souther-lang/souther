package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A fold over a list written out hands each step the answer so far, which every operation told
 * before it gave. What an operation over it is worked out after is gathered from those, and the
 * operations each of them is worked out after are already among them: gathered in work that grows
 * with the square of the elements and not with their cube, which is what putting each one's own
 * list in again comes to.
 *
 * <p>Counted and not timed: the operations put into what an operation is worked out after, as
 * the elements double. The square is four times and the cube eight.
 */
class WhatARunWorksOutBeforeAnOperationIsGatheredInWorkThatDoesNotCubeWithItsLengthTest {

    private static String foldOver(int elements) {
        StringBuilder list = new StringBuilder();
        for (int i = 1; i <= elements; i++) {
            list.append(i == 1 ? "" : ", ").append("q + ").append(i);
        }
        return "module m\n\nbehavior b : (q: Int) -> Int\nlet b (q) = if "
                + "List.fold((w, l) -> w + l, 0, [" + list + "]) >= q then 1 else 2\n";
    }

    private static long putIn(int elements) {
        long[] counting = {0};
        AffineReading.INCLUDED = counting;
        try {
            ACompiledModel.measured(foldOver(elements),
                    new Adequacy.Asked(Adequacy.Level.OFF, false));
        } finally {
            AffineReading.INCLUDED = null;
        }
        return counting[0];
    }

    @Test
    void twiceTheElementsCostLessThanFiveTimesTheWork() {
        SequencedMap<Integer, Long> work = new LinkedHashMap<>();
        for (int elements : new int[] {16, 32}) {
            work.put(elements, putIn(elements));
        }
        Growth.eachAtMost(work, 5, 1);
    }
}
