package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Counting;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row's expectation is computed by running the module's own code, and it is run once.
 *
 * <p>Two readers want it now — what the row asserts, for comparing, and the value itself, for
 * holding to what the behavior declares — and the second of those was added after the first. Asking
 * for it twice would apply the expectation's helpers twice: counted twice against the row's budget,
 * and done twice for whatever they do.
 *
 * <p>Measured without a constant in it. Two rows apply the same behavior to lists of the same
 * length and name the same helper once each — one in the input, one in the expectation — so
 * whatever a row of this shape costs, the two cost the same. A reader that ran the expectation
 * twice would make the second row's evaluation the cheaper of the two, and by exactly the helper
 * the first ran again.
 */
class AnExpectationIsEvaluatedOnceTest {

    private static final String MODEL = """
            module example.counted
            import List ( map )

            data Numbers = { values: List<Int> }

            let doubled (xs: List<Int>) = map(x -> x * 2, xs)

            behavior double : (ns: Numbers) -> Numbers
                constructs Numbers

            let double (ns) = Numbers { values = doubled(ns.values) }

            example double
                | "the helper is in the input"       : (Numbers { values = doubled([1, 2, 3]) }) -> Numbers { values = [4, 8, 12] }
                | "the helper is in the expectation" : (Numbers { values = [1, 2, 3] }) -> Numbers { values = doubled([1, 2, 3]) }
            """;

    @Test
    void namingAHelperInTheExpectationCostsWhatNamingItInAnInputCosts() {
        List<RowOutcome> rows = rows(MODEL);

        assertEquals(2, rows.size());
        for (RowOutcome row : rows) {
            assertEquals(Disposition.HELD, row.disposition(), "both rows hold, so both were run");
        }
        assertTrue(steps(rows.get(0)) > 0, "the helper is counted into, so there is something to read");
        assertEquals(steps(rows.get(0)), steps(rows.get(1)),
                "the expectation's helper ran once, as the input's did");
    }

    /** What a row spent: the counted work of its whole evaluation, fixtures and application alike. */
    private static long steps(RowOutcome row) {
        return assertInstanceOf(Counting.Read.class, row.run().counting(),
                "the row came back, so its counting was read").steps();
    }

    private static List<RowOutcome> rows(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        return compilation.db()
                .ask(Output.Examples.asked(compilation.db(), compilation.modules().get(0),
                        compilation.sourceIds().get(0)))
                .value().rows();
    }
}
