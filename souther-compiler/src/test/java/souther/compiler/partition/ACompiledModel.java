package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A model compiled for a test that reads what is said of it, held to compile.
 *
 * <p>A model that does not compile is said nothing of: its report holds no position and no line.
 * A test asking that nothing of some kind is said, or that everything said is of some kind, passes
 * on that empty report whatever the compiler would say of the model it meant. So every reading of
 * a report starts here, and a model with an error stops the test.
 */
final class ACompiledModel {

    private ACompiledModel() { }

    /** {@code source} compiled, measured as {@code asked}, and answered in full. */
    static Compilation measured(String source, Adequacy.Asked asked) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(asked);
        model.answerEverything();
        return compiles(model);
    }

    /** {@code source} compiled and answered in full, with no measure asked. */
    static Compilation answered(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.answerEverything();
        return compiles(model);
    }

    private static Compilation compiles(Compilation model) {
        assertEquals(List.of(), model.errors().stream()
                .map(e -> e.diagnostic().code()).toList(), "the model compiles");
        return model;
    }
}
