package souther.compiler.query;

import souther.compiler.check.BehaviorBodies;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.codegen.Backend;
import souther.compiler.codegen.Emissions;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior is emitted as is decided by where the module was classified, and the definition
 * an implemented one is emitted from is asked for only once that says it is implemented.
 *
 * <p>Whether a definition is at hand is not a second way to tell the three states apart. Handed a
 * table that calls a behavior implemented where the module has no definition of it, the emitter
 * has nothing to emit the behavior from, and says so: read the other way round, it would find no
 * definition, take the behavior for one Java supplies or one nobody has written, and emit nothing
 * with nothing said.
 */
class AnImplementedBehaviorMustHaveTheImplementationItWasClassifiedAsHavingTest {

    private static final String SOURCE = """
            module m exposing ( Out, supplied, written )
            data Out = { n: Int }
            behavior supplied : (n: Int) -> Out
            behavior written : (n: Int) -> Out
                constructs Out
            let written (n) = Out { n = n }
            """;

    @Test
    void theModuleAsClassifiedIsEmitted() {
        Map<String, BehaviorImplementation> claimed = new LinkedHashMap<>();
        claimed.put("supplied", BehaviorImplementation.INJECTION_TARGET);
        claimed.put("written", BehaviorImplementation.IMPLEMENTED);

        Emissions emitted = assertDoesNotThrow(() -> emittedWith(claimed));

        assertNotNull(emitted);
    }

    @Test
    void aBehaviorClassifiedAsImplementedWithNoDefinitionIsNotSilentlyLeftOut() {
        Map<String, BehaviorImplementation> claimed = new LinkedHashMap<>();
        claimed.put("supplied", BehaviorImplementation.IMPLEMENTED);
        claimed.put("written", BehaviorImplementation.IMPLEMENTED);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> emittedWith(claimed),
                "the module has no definition of `supplied`, and the table says it has a body");

        assertTrue(refused.getMessage().contains("m.supplied"), refused.getMessage());
        assertTrue(refused.getMessage().contains("classified as implemented"),
                refused.getMessage());
    }

    /** The module's classes, emitted against {@code claimed} where the module was classified. */
    private static Emissions emittedWith(Map<String, BehaviorImplementation> claimed) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        Output.Classes.Inputs in = Output.Classes.inputs(compilation.db(), "m",
                Output.Classes.Elaboration.WHOLE);
        assertNotNull(in, "the module reaches the emitter, or this says nothing");
        return Backend.generate(in.lowered(), in.scope(), in.published(), in.kinds(),
                in.scope().library().kernelSignatures(), in.typePackages(), in.sigs(),
                in.requirementSigs(), in.injected(), new BehaviorBodies("m", claimed),
                in.callees(), in.requirements(), in.foreignStages(), in.checked(),
                in.compositions(), in.dischargeClauses(), in.invariantStatements(), in.shapes(),
                in.checks(), in.standingCalls(), new TheTextsThisCompileHolds(compilation.db()));
    }
}
