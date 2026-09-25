package souther.compiler.query;

import souther.compiler.codegen.Backend;
import souther.compiler.codegen.Emissions;
import souther.compiler.codegen.LinkageReader;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior is emitted as is decided by its projection, where the module's classification
 * reaches the classes, and the definition an implemented one is emitted from is asked for only once
 * that says it is implemented.
 *
 * <p>Whether a definition is at hand is not a second way to tell the three states apart. Handed a
 * projection that calls a behavior implemented where the module has no definition of it, the
 * emitter has nothing to emit the behavior from, and says so: read the other way round, it would
 * find no definition, take the behavior for one Java supplies or one nobody has written, and emit
 * nothing with nothing said.
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
        Map<String, LinkageProjection.Realization> claimed = Map.of(
                "supplied", LinkageProjection.Realization.SUPPLIED_BY_JAVA,
                "written", LinkageProjection.Realization.IMPLEMENTED);

        Emissions emitted = assertDoesNotThrow(() -> emittedWith(claimed));

        assertNotNull(emitted);
    }

    @Test
    void aBehaviorClassifiedAsImplementedWithNoDefinitionIsNotSilentlyLeftOut() {
        Map<String, LinkageProjection.Realization> claimed = Map.of(
                "supplied", LinkageProjection.Realization.IMPLEMENTED,
                "written", LinkageProjection.Realization.IMPLEMENTED);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> emittedWith(claimed),
                "the module has no definition of `supplied`, and its projection says it has a body");

        assertTrue(refused.getMessage().contains("m.supplied"), refused.getMessage());
        assertTrue(refused.getMessage().contains("classified as implemented"),
                refused.getMessage());
    }

    /**
     * The module's classes, emitted against its own projections with each behavior in
     * {@code claimed} realized as it says.
     *
     * <p>A behavior claimed implemented is built as {@code written} is. Both take and answer the
     * same, and what matters here is only that the projection says there is something to build.
     */
    private static Emissions emittedWith(Map<String, LinkageProjection.Realization> claimed) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        Output.Classes.Inputs in = Output.Classes.inputs(compilation.db(), "m",
                Output.Classes.Elaboration.WHOLE);
        assertNotNull(in, "the module reaches the emitter, or this says nothing");
        Linkages.Of own = compilation.db().ask(new Linkages.Provided("m")).value();
        Map<LinkageTarget, LinkageProjection> provides = new HashMap<>(own.provides());
        Optional<LinkageProjection.Construction> built =
                behavior(provides, "written").construction();
        claimed.forEach((name, realization) -> {
            LinkageProjection.Behavior was = behavior(provides, name);
            provides.put(was.target(), new LinkageProjection.Behavior(was.behavior(), realization,
                    was.exposed(), was.takes(), was.answers(), was.heldAs(), was.apply(),
                    realization == LinkageProjection.Realization.IMPLEMENTED
                            ? built : Optional.empty(),
                    was.answeredThrough()));
        });
        LinkageReader linkage = new LinkageReader("m", provides,
                Linkages.reading(compilation.db()), own.read());
        return Backend.generate(in.lowered(), in.scope(), in.published(), in.kinds(),
                in.scope().library().kernelSignatures(), in.typePackages(), in.sigs(),
                in.requirements(), in.checked(), in.compositions(), in.dischargeClauses(),
                in.invariantStatements(), in.shapes(), in.checks(), in.standingCalls(),
                new TheTextsThisCompileHolds(compilation.db()), linkage);
    }

    private static LinkageProjection.Behavior behavior(Map<LinkageTarget, LinkageProjection> provides,
                                                       String name) {
        return (LinkageProjection.Behavior) provides.get(
                new LinkageTarget.Behavior(new ValueName.Behavior("m", name)));
    }
}
