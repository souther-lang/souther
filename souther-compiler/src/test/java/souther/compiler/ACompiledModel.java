package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

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
     * comes last, as the value compared stands last in an assertion, so that a test reads
     * {@code refusedWith(List.of("E1013"), model)} as what it expects of it.
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

    /**
     * {@code model}, answered in full, held to be refused with no error but those of
     * {@code allowed}, as many times as it is. For a model whose rows are generated, so that how
     * many of them are refused is not fixed, and what is fixed is what they can be refused with.
     */
    public static Compilation refusedOnlyWith(Set<String> allowed, Compilation model) {
        List<String> refused;
        try {
            model.answerEverything();
            refused = model.errors().stream().map(e -> e.diagnostic().code()).toList();
        } catch (CompileException stopped) {
            refused = stopped.diagnostics().stream().map(Diagnostic::code).toList();
        }
        assertEquals(List.of(), refused.stream().filter(code -> !allowed.contains(code)).toList(),
                "the model is refused with nothing but " + allowed);
        return model;
    }

    /**
     * The errors {@code model} is refused with after it was answered in full: those it stops with,
     * and those it reports. For a test that says what a refusal is and compares it with what it
     * meant. It answers the model and says nothing of the model compiling, so what a test goes on
     * to read of the model besides its errors is read of a model nobody asked about.
     */
    public static List<Diagnostic> diagnosticsOf(Compilation model) {
        List<Diagnostic> said = new ArrayList<>();
        try {
            model.answerEverything();
        } catch (CompileException stopped) {
            said.addAll(stopped.diagnostics());
        }
        model.errors().forEach(found -> said.add(found.diagnostic()));
        return said;
    }

    /**
     * {@code model}, read without being compiled, because compiling it is what a test cannot do:
     * the model is too large for the compiler's own stack, or is a buffer stopped half way
     * through a line, and what the test asks of it is not a report. Said so, with why, and held to
     * a closed list of the tests that may:
     * {@code ATestThatReadsAModelsReportAsksThatTheModelCompilesTest}.
     */
    public static Compilation notCompiled(Compilation model, String reason) {
        Objects.requireNonNull(reason, "a model that is not compiled says why");
        return model;
    }

    /**
     * Models a class of tests builds once and reads in many, each held to what it was built to be
     * every time it is given out.
     *
     * <p>The model is kept and the look is not: a test reading the shared model is handed it by
     * the call that asks, so what it reads is a model that was asked about whichever test made it.
     * Released when the class is done with them, because a fork keeps its JVM and what is held
     * statically is held for every class after.
     */
    public static final class Shared {

        private final Map<String, Compilation> held = new ConcurrentHashMap<>();

        /** The model {@code made} makes for {@code key}, held to compile. */
        public Compilation compiles(String key, Supplier<Compilation> made) {
            return refusedWith(List.of(), key, made);
        }

        /** The model {@code made} makes for {@code key}, held to be refused with {@code codes}. */
        public Compilation refusedWith(List<String> codes, String key, Supplier<Compilation> made) {
            return ACompiledModel.refusedWith(codes, held.computeIfAbsent(key, ignored -> made.get()));
        }

        /** Lets go of every model held. */
        public void release() {
            held.clear();
        }
    }
}
