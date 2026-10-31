package souther.compiler.program;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A model that composes two behaviors, states what one of them ensures, and guards the
 * construction of a value is a program an output outside the compiler can read.
 *
 * <p>Each of the three is a way the program is assembled that a behavior written plainly is not:
 * a composition is read as the stages it joins and has no body of its own, an {@code ensures} is a
 * rule on the answer that the assembler reads beside the body, and a construction under a guard
 * has places it can end the run that a construction without one has not.
 */
class AProgramIsAssembledOfABehaviorThatComposesEnsuresAndGuardsAConstructionTest {

    private static final String SOURCE = """
            module probe.assembled exposing ( Qty, Ticket, Refused, price, finish, total : Int, graded )

            data Qty = Int
                invariant low = value >= 0
                invariant high = value <= 100

            data Ticket = { qty: Qty }
            data Refused

            behavior price : (n: Int) -> Ticket | Refused
                constructs Ticket, Qty
                ensures Ticket -> value.qty.value == n

            let price (n) = if Qty(n) as q then Ticket { qty = q } else
                | low -> Refused
                | high -> Refused

            behavior step : (n: Int) -> Int
            let step (n) = n + 1

            behavior finish : (n: Int) -> Int
            let finish (n) = n * 2

            behavior total = step >-> finish

            behavior graded : (x: Int) -> Int
                constructs Qty
            let graded (x) = if Qty(x) as r then 0 else
                | low -> 1
                | high -> 2
            """;

    private static CheckedProgram assembled() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().titleKey()).toList(),
                "the model compiles");
        return CheckedProgramAssembler.of(compilation);
    }

    @Test
    void aComposedBehaviorIsTheStagesItJoinsAndAWrittenOneIsItsBody() {
        List<String> kinds = new ArrayList<>();
        for (CheckedModule module : assembled().modules()) {
            for (CheckedBehavior behavior : module.behaviors()) {
                kinds.add(behavior.name() + " " + behavior.implementation().getClass()
                        .getSimpleName());
            }
        }
        assertTrue(kinds.contains("probe.assembled.total Composed"), () -> "a composition is read as one: " + kinds);
        assertTrue(kinds.contains("probe.assembled.graded Body"), () -> "a written behavior has a body: " + kinds);
    }
}
