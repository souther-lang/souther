package souther.program.api;

import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A value that reads another value crosses as a value, handed the value it reads with the type that
 * value settled as.
 *
 * <p>The method {@code ys} runs as takes {@code ks}, which the region building {@code ys} has built
 * already. That parameter is one the lowering added, so no source annotates it: its type is the
 * check's answer, and which value it holds is the lowering's, and the program carries both. And
 * {@code ys} is still a value although its method takes something, which is what a reader counting
 * parameters to decide it would get wrong.
 */
class AValueThatReadsAnotherValueCrossesWithTheTypesItTakesTest {

    private static final String MODULE = """
            module m

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)

            behavior f : (n: Int) -> Int

            let f (n) = List.length(ys) + n
            """;

    private static final ValueName.Helper YS = new ValueName.Helper("m", "ys");

    @Test
    void theMethodOfAValueThatReadsAValueTakesTheTypeThatValueSettledAs() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        CheckedValue ys = module.value(YS);

        assertEquals(List.of(Type.list(Type.INT)),
                ys.handovers().stream().map(CheckedValue.Handover::type).toList());
    }

    @Test
    void whatItIsHandedSaysWhichValueItHolds() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        assertEquals(List.of(new ValueName.Helper("m", "ks")),
                module.value(YS).handovers().stream().map(CheckedValue.Handover::carries).toList());
    }

    @Test
    void aValueThatTakesSomethingIsNoHelper() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        assertEquals(List.of(), module.helpers().stream().map(CheckedHelper::declares)
                .filter(YS::equals).toList());
        assertThrows(IllegalArgumentException.class, () -> module.helper(YS));
    }
}
