package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.WhatTheLibraryComputes;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;
import souther.test.ClosedWorldContract;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk after where an element stands counts from the far end through an operation declared to
 * answer its argument the other way round, so the declaration is held to what the kernel computes:
 * the first of its answer is the last of the argument, the second the one before it, and so on.
 *
 * <p>The statements about a kernel run in {@code EveryAxiomAboutAKernelHoldsOfWhatItComputesTest}
 * say which values an answer holds and how many, and none of them names an index, so the order is
 * run here. The operations declared are swept, each run on a list of distinct values, so a
 * declaration added without a run here is a failure of this test.
 */
@ClosedWorldContract
class EveryKernelDeclaredToAnswerItsArgumentTheOtherWayRoundDoesSoTest {

    @Test
    void everyDeclaredOperationAnswersItsArgumentFromTheLastToTheFirst() throws Exception {
        Stdlib stdlib = DefaultStdlib.get();
        List<String> declared = new ArrayList<>();
        for (ValueName.Stdlib.Operation operation : stdlib.entries().keySet()) {
            if (Combinators.positionOfTheArgumentReversed(stdlib, operation) >= 0) {
                declared.add(operation.alias() + "." + operation.name());
            }
        }
        assertEquals(List.of("List.reverse"), declared,
                "a declaration is run below before it is trusted");

        WhatTheLibraryComputes.Program program = new WhatTheLibraryComputes.Program("demo", """
                module demo

                data In = { xs: List<Int> }
                data Out = { xs: List<Int> }

                behavior turn : (in: In) -> Out
                let turn (in) = Out { xs = List.reverse(in.xs) }
                """);
        assertEquals(Map.of("xs", List.of(5L, 4L, 3L, 2L, 1L)),
                program.answer("turn", "In", "Out", Map.of("xs", List.of(1L, 2L, 3L, 4L, 5L))));
        assertEquals(Map.of("xs", List.of()),
                program.answer("turn", "In", "Out", Map.of("xs", List.of())));
        assertEquals(Map.of("xs", List.of(7L)),
                program.answer("turn", "In", "Out", Map.of("xs", List.of(7L))));
    }

    /** The operations that put a list's elements in another order or keep some of them say
     *  nothing of the order, and are declared to turn none round. */
    @Test
    void anOperationThatSaysNothingOfTheOrderIsDeclaredToTurnNoneRound() {
        Stdlib stdlib = DefaultStdlib.get();
        for (String name : List.of("sort", "take", "drop", "distinct", "map", "filter")) {
            assertEquals(-1, Combinators.positionOfTheArgumentReversed(stdlib,
                    ValueName.Stdlib.operation("List", name)), name);
        }
        assertEquals(-1, Combinators.positionOfTheArgumentReversed(stdlib,
                ValueName.Stdlib.operation("Set", "toList")));
    }
}
