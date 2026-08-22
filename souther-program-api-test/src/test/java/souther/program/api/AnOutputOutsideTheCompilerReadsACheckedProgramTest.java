package souther.program.api;

import souther.compiler.core.Composition;
import souther.compiler.core.Core;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output that is not this compiler can do with a checked Souther program.
 *
 * <p>This artifact depends on {@code souther-compiler} and on nothing else of the project, which is
 * the position a WebAssembly compiler or any other output would be in. Everything below is written
 * with what such an artifact can name: no query, no code generation, no syntax tree. What it needs
 * is decisions the language compiler made, and this is a reading of them.
 */
class AnOutputOutsideTheCompilerReadsACheckedProgramTest {

    private static final String MODULE = """
            module demo

            data Name = String
            data Employee = { boss: Employee?, name: Name }
            data Depth = Int
            data Deep = { depth: Int }

            // Java supplies this one (spec §injected-behavior)
            behavior loadEmployee : (name: Name) -> Employee

            // Walking the reporting line is a recursion no fold expresses, so this helper stays a
            // definition of its own rather than being expanded where it is used.
            let depth (e: Employee): Int =
                match e.boss with
                    | Some b -> depth(b) + 1
                    | None -> 1

            behavior measureDepth : (e: Employee) -> Depth constructs Depth

            let measureDepth (e) = Depth(depth(e))

            behavior toDeep : (d: Depth) -> Deep constructs Deep

            let toDeep (d) = Deep { depth = d.value }

            behavior measure = measureDepth >-> toDeep
            """;

    private static CheckedModule demo() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    private static CheckedBehavior named(CheckedModule module, String name) {
        CheckedBehavior behavior = module.behavior(new ValueName.Behavior(module.name(), name));
        assertNotNull(behavior, name);
        return behavior;
    }

    @Test
    void theProgramHoldsTheModulesItChecked() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertEquals(List.of("demo"), program.modules().stream().map(CheckedModule::name).toList());
    }

    @Test
    void aBehaviorIsReachedByItsResolvedNameAndSaysWhatItTakesAndAnswers() {
        CheckedBehavior measureDepth = named(demo(), "measureDepth");

        assertEquals(new ValueName.Behavior("demo", "measureDepth"), measureDepth.name());
        assertEquals(1, measureDepth.signature().takes().size(),
                "one input, as it was declared");
        assertNotNull(measureDepth.signature().answers());
    }

    /**
     * The four states an implementation is in, told apart by asking rather than by finding nothing
     * where a body would be.
     *
     * <p>The switch has no {@code default}: a state added later stops this compiling, which is what
     * a consumer outside the compiler wants from a set it is meant to handle all of.
     */
    @Test
    void whereAnImplementationComesFromIsAskedAndNotInferredFromAnAbsence() {
        CheckedModule demo = demo();

        assertEquals("body", where(named(demo, "measureDepth")));
        assertEquals("injected", where(named(demo, "loadEmployee")));
        assertEquals("composed", where(named(demo, "measure")));
    }

    private static String where(CheckedBehavior behavior) {
        return switch (behavior.implementation()) {
            case CheckedImplementation.Body body -> {
                assertNotNull(body.body().type(), "the checker typed it");
                yield "body";
            }
            case CheckedImplementation.Composed composed -> {
                assertFalse(composed.composition().stages().isEmpty());
                yield "composed";
            }
            case CheckedImplementation.Injected ignored -> "injected";
            case CheckedImplementation.Unwritten ignored -> "unwritten";
        };
    }

    /**
     * A composition arrives routed.
     *
     * <p>Which cases a stage is offered is what makes {@code >->} Railway (spec §type-routing), and
     * it is the language's answer rather than each output's. An output reads it here instead of
     * working it out from the stages' signatures, which is what the JVM emitter used to do.
     */
    @Test
    void aCompositionSaysWhatEachStageIsOfferedAndWhatItAnswers() {
        CheckedImplementation implementation = named(demo(), "measure").implementation();
        assertTrue(implementation instanceof CheckedImplementation.Composed);
        Composition composed = ((CheckedImplementation.Composed) implementation).composition();

        assertEquals(List.of(new ValueName.Behavior("demo", "measureDepth"),
                        new ValueName.Behavior("demo", "toDeep")),
                composed.stages().stream().map(Composition.Stage::behavior).toList());
        // the first stage takes the composition's own arguments, so nothing is routed into it
        assertTrue(composed.stages().get(0).routing() instanceof Composition.Routing.Always);
        assertNotNull(composed.answers());
        for (Composition.Stage stage : composed.stages()) {
            assertNotNull(stage.answers(), "what the stage answers is on the stage");
        }
    }

    /**
     * A call in a body reaches a helper, and the helper is here to be walked.
     *
     * <p>The half a set of behaviors alone would miss. Most helpers are gone by the time a module is
     * checked; the one that is left is a recursion, and a body's call names it. An output handed
     * only the behaviors would find that call reaching something it had never been given.
     */
    @Test
    void aCallReachesAHelperTheProgramHoldsAndItsBodyIsWalkedToo() {
        CheckedModule demo = demo();
        Core body = ((CheckedImplementation.Body) named(demo, "measureDepth").implementation())
                .body();

        Set<ValueName.Helper> called = helpersCalledIn(body);
        assertEquals(Set.of(new ValueName.Helper("demo", "depth")), called,
                "the recursive helper the body calls");

        CheckedHelper depth = demo.helper(new ValueName.Helper("demo", "depth"));
        assertNotNull(depth, "and the program holds it");
        assertEquals(1, depth.parameters().size());
        assertNotNull(depth.parameters().get(0).binder().binding(), "the binding its body reads");
        assertNotNull(depth.body().type(), "what it answers, as the checker typed it");
        assertTrue(helpersCalledIn(depth.body()).contains(new ValueName.Helper("demo", "depth")),
                "and it calls itself, which is why it is a definition of its own");
    }

    /** Every helper a call in {@code body} reaches, walking every node of it. */
    private static Set<ValueName.Helper> helpersCalledIn(Core body) {
        Set<ValueName.Helper> called = new LinkedHashSet<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Call call
                    && call.fn() instanceof Core.Reached reached
                    && reached.denotes() instanceof ValueName.Helper helper) {
                called.add(helper);
            }
        }
        return called;
    }

    private static List<Core> everyNodeOf(Core body) {
        List<Core> nodes = new ArrayList<>();
        collect(body, nodes);
        return nodes;
    }

    private static void collect(Core node, List<Core> into) {
        into.add(node);
        Core.forEachChild(node, child -> collect(child, into));
    }
}
