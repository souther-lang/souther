package souther.program.api;

import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

        CheckedHelper ys = module.helper(new ValueName.Helper("m", "ys"));

        assertEquals(List.of(Type.list(Type.INT)),
                ys.parameters().stream().map(CheckedHelper.Parameter::type).toList());
    }
}
