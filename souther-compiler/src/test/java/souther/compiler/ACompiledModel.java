package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
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
 * a report starts here, and a model with an error stops the test. A test that means the model not
 * to compile says which errors it is meant to be refused with ({@link #refusedWith}), and that is
 * the look. A look at {@code errors()} written in the test is not one: nothing says what became of
 * what it showed.
 */
public final class ACompiledModel {

    private ACompiledModel() { }

    /** {@code source} compiled, measured as {@code asked}, and answered in full. */
    public static Compilation measured(String source, Adequacy.Asked asked) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(asked);
        return compiles(model);
    }

    /** {@code source} compiled and answered in full, with no measure asked. */
    public static Compilation answered(String source) {
        return compiles(Compilation.ofSource(source, "Main"));
    }

    /** {@code model}, answered in full, held to compile. */
    public static Compilation compiles(Compilation model) {
        return refusedWith(List.of(), model);
    }

    /**
     * {@code model}, answered in full, held to be refused with {@code codes} and nothing else, in
     * the order the compiler gives them, whether it reports them or stops with them. The model
     * comes last, as the value compared stands last
     * in an assertion, so that a test reads {@code refusedWith(List.of("E1013"), model)} as what
     * it expects of it.
     */
    public static Compilation refusedWith(List<String> codes, Compilation model) {
        List<String> refused;
        try {
            model.answerEverything();
            refused = model.errors().stream().map(e -> e.diagnostic().code()).toList();
        } catch (CompileException stopped) {
            refused = stopped.diagnostics().stream().map(Diagnostic::code).toList();
        }
        assertEquals(codes, refused,
                codes.isEmpty() ? "the model compiles" : "the model is refused as meant");
        return model;
    }
}
