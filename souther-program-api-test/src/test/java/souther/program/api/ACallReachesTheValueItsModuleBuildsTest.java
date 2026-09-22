package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedValue;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call to a value its module builds says it reaches a value, and the module holds that value.
 *
 * <p>A value and a helper are two things to run: a value runs in the one place its module builds it
 * and lives past the call that reads it, and a helper's method is a copy a call was left standing
 * to. So a call says which of the two it reaches, and the module answers each from its own list. A
 * call that said it reached a helper and found a value, or the other way round, would leave an
 * output deciding for itself which one it had been handed.
 */
class ACallReachesTheValueItsModuleBuildsTest {

    /**
     * A value read by another value and by a behavior, a recursion, and a value published for other
     * modules — whose entry is a method of its own that reads the value.
     */
    private static final String MODULE = """
            module m exposing ( Node, ys, f )

            data Node = { n: Int, kids: List<Node> }

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)

            let flatten (t: Node): List<Int> = [t.n] ++ List.flatMap(k -> flatten(k), t.kids)

            behavior f : (t: Node) -> Int

            let f (t) = List.length(ys) + List.length(flatten(t))
            """;

    @Test
    void everyCallToAValueReachesOneTheModuleBuilds() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        List<Core.Reaches> reached = reachedFrom(module);
        List<ValueName.Helper> values = new ArrayList<>();
        for (Core.Reaches reaches : reached) {
            if (reaches instanceof Core.Reaches.AValue(ValueName.Helper value)) {
                values.add(module.value(value).name());
            }
        }

        assertEquals(Set.of(new ValueName.Helper("m", "ks"), new ValueName.Helper("m", "ys")),
                new LinkedHashSet<>(values), "the calls to values reached " + reached);
    }

    @Test
    void everyCallToAHelperReachesOneTheModuleCarries() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        List<ValueName> helpers = new ArrayList<>();
        for (Core.Reaches reaches : reachedFrom(module)) {
            if (reaches instanceof Core.Reaches.AHelper(ValueName declaration)) {
                helpers.add(module.helper(declaration).declares());
            }
        }

        assertTrue(helpers.contains(new ValueName.Helper("m", "flatten")),
                "the recursion is reached as a helper: " + helpers);
    }

    /** The behavior reads {@code ys} as a value, not as a method a call was left standing to. */
    @Test
    void theBehaviorsReadOfAValueIsACallToAValue() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        List<Core.Reached> toYs = new ArrayList<>();
        module.behaviors().forEach(behavior -> {
            if (behavior.implementation() instanceof CheckedImplementation.Body body) {
                collectCallsTo(body.body(), "ys", toYs);
            }
        });

        assertFalse(toYs.isEmpty(), "the behavior calls the method ys runs as");
        toYs.forEach(call -> assertInstanceOf(Core.Reached.OfValue.class, call));
    }

    @Test
    void aValueIsNotAlsoAHelper() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        Set<ValueName> helpers = new LinkedHashSet<>();
        for (CheckedHelper helper : module.helpers()) {
            helpers.add(helper.declares());
        }
        for (CheckedValue value : module.values()) {
            assertFalse(helpers.contains(value.name()), value + " is carried as a helper too");
        }
        assertFalse(module.values().isEmpty(), "the module builds values");
    }

    /** What every call in every body {@code module} emits reaches: its behaviors', its helpers' and
     *  its values'. */
    private static List<Core.Reaches> reachedFrom(CheckedModule module) {
        List<Core> bodies = new ArrayList<>();
        module.behaviors().forEach(behavior -> {
            if (behavior.implementation() instanceof CheckedImplementation.Body body) {
                bodies.add(body.body());
            }
        });
        module.helpers().forEach(helper -> bodies.add(helper.body()));
        module.values().forEach(value -> bodies.add(value.body()));
        List<Core.Reaches> reached = new ArrayList<>();
        for (Core body : bodies) {
            collectReaches(body, reached);
        }
        return reached;
    }

    private static void collectReaches(Core node, List<Core.Reaches> into) {
        if (node instanceof Core.Call call) {
            switch (call.fn()) {
                case Core.Reached.OfDeclaration declaration -> into.add(declaration.reaches());
                case Core.Reached.OfValue value -> into.add(value.reaches());
                case Core.Reached.OfPublishedValue published -> into.add(published.reaches());
                case Core.Reached.OfKernel _, Core.Emitted _ -> { }
            }
        }
        Core.forEachChild(node, child -> collectReaches(child, into));
    }

    private static void collectCallsTo(Core node, String name, List<Core.Reached> into) {
        if (node instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes().name().equals(name)) {
            into.add(reached);
        }
        Core.forEachChild(node, child -> collectCallsTo(child, name, into));
    }
}
