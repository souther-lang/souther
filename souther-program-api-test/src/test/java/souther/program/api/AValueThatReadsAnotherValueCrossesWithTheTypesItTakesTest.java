package souther.program.api;

import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A value emitted as a method that takes another value crosses with the type that value settled as.
 *
 * <p>The parameter such a method takes is one the lowering added, so no source annotates it. Its
 * type is the check's answer and the program carries that answer.
 */
class AValueThatReadsAnotherValueCrossesWithTheTypesItTakesTest {

    private static final String MODULE = """
            module m

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)

            behavior f : (n: Int) -> Int

            let f (n) = List.length(ys) + n
            """;

    @Test
    void theMethodOfAValueThatReadsAValueTakesTheTypeThatValueSettledAs() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        List<List<Type>> taken = module.helpers().stream()
                .filter(helper -> !helper.parameters().isEmpty())
                .map(helper -> helper.parameters().stream()
                        .map(CheckedHelper.Parameter::type).toList())
                .toList();

        assertFalse(taken.isEmpty(), "the module carries a method that takes a value");
        assertEquals(List.of(List.of(Type.list(Type.INT))), taken);
    }
}
