package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.Accumulation;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * {@link Question#ACCUMULATION} asks what an operation means, and {@link Accumulations} answers it
 * for every operation in range — including the two that answer a string, which no check that reads
 * numbers will ever ask about.
 *
 * <p>That is the whole of what this holds. A registry written to suit the one reader it has today
 * says of {@code String.concat} that the library's own reading of it — {@code join("", xs)} — is not
 * a reading at all, and the next question asked of the table gets the answer the last reader's
 * limits shaped. What may be carried as a number is asked after this table, of its answer.
 */
class AnAccumulationIsWrittenForWhatItMeansAndNotForWhatCanReadItTest {

    @Test
    void everyOperationAnsweringWhatItsContainerHoldsIsAsked() {
        List<String> inRange = new ArrayList<>();
        for (Map.Entry<ValueName.Stdlib.Operation, Stdlib.Entry> e
                : DefaultStdlib.get().entries().entrySet()) {
            if (Question.askedOf(DefaultStdlib.get(), e.getValue().signature()).contains(Question.ACCUMULATION)) {
                inRange.add(e.getKey().qualified());
            }
        }
        assertEquals(List.of("List.concat", "List.product", "List.sum", "String.concat",
                        "String.join"),
                inRange.stream().sorted().toList(),
                "these are the operations that answer a value of the type a container argument"
                        + " holds, and each of them is asked whether it accumulates");
    }

    @Test
    void whatEachAccumulatesIsWhatItStartsFromAndTheStepItRepeats() {
        assertEquals(new Accumulation(
                        Accumulation.Identity.ZERO, Accumulation.Combine.ADD),
                Accumulations.of(op("List", "sum")));
        assertEquals(new Accumulation(
                        Accumulation.Identity.ONE, Accumulation.Combine.MULTIPLY),
                Accumulations.of(op("List", "product")));
        assertEquals(new Accumulation(
                        Accumulation.Identity.EMPTY, Accumulation.Combine.APPEND),
                Accumulations.of(op("List", "concat")),
                "a list of lists is joined from the empty list through the same append two lists"
                        + " are joined by");
    }

    @Test
    void aStringIsAccumulatedAsAListIsAndIsWrittenDownAsOne() {
        assertEquals(new Accumulation(
                        Accumulation.Identity.EMPTY, Accumulation.Combine.APPEND),
                Accumulations.of(op("String", "concat")),
                "the library states String.concat as join(\"\", xs), and what it means does not"
                        + " depend on there being a check that can read it");
    }

    @Test
    void aSeparatorStandingBetweenElementsIsNotOneStepOverTwoValues() {
        assertNull(Accumulations.of(op("String", "join")),
                "join carries whether anything came before the element it is at, which an identity"
                        + " and a combine over two values of one type have nowhere to keep");
        assertEquals(true, Accumulations.NO_SIMPLE_ACCUMULATION.contains(op("String", "join")),
                "so it answers by being named as one there is nothing of this to say of");
    }

    /**
     * The range holds an operation nobody thought of. It is read off the shape of a declaration, so
     * a set summed, or a map's values joined, would be asked the day the library declares one —
     * which is what makes the question a check on the library rather than a list of what it has.
     */
    @Test
    void anOperationTheLibraryDoesNotHaveYetIsInRangeByItsShape() {
        Stdlib.Signature setSummed = new Stdlib.Signature(
                List.of(new Type.SetOf(Type.Prim.INT)), Type.Prim.INT);
        assertEquals(true, Question.askedOf(DefaultStdlib.get(), setSummed).contains(Question.ACCUMULATION));
    }

    private static ValueName op(String alias, String name) {
        return ValueName.Stdlib.operation(alias, name);
    }
}
