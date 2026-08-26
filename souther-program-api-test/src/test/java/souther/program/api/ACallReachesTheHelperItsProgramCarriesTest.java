package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call an output holds reaches a helper the program carries, and says which one.
 *
 * <p>Most of what the library declares expands at the place it is written and never reaches an
 * output. A recursion cannot, so the module that calls one carries the body — and the call in that
 * body is the only thing an output has to get from the one to the other. What the call says the
 * callee is, and what the carried helper is filed under, have to be the same value, or the output
 * is left joining them by a spelling it assembles itself.
 */
class ACallReachesTheHelperItsProgramCarriesTest {

    /** A recursion of its own, so {@code app} below carries the body rather than expanding it. */
    private static final String LIB = """
            module lib exposing ( Node, flatten )

            data Node = { n: Int, kids: List<Node> }

            let flatten (t: Node): List<Int> = [t.n] ++ List.flatMap(k -> flatten(k), t.kids)
            """;

    private static final String APP = """
            module app exposing ( Out, go )

            import lib ( Node, flatten )

            data Out = { xs: List<Int> }

            behavior go : (t: Node) -> Out constructs Out
            let go (t) = Out { xs = flatten(t) }
            """;

    /** The library's own recursion, reached under the alias the library publishes it under. */
    private static final String FOLDS = """
            module folds exposing ( Total, sumOf )

            data Total = Int

            behavior sumOf : (xs: List<Int>) -> Total constructs Total
            let sumOf (xs) = Total(List.fold((acc, x) -> acc + x, 0, xs))
            """;

    /**
     * The declaration a call names, and the declaration the carried helper is filed under, are one
     * value.
     *
     * <p>Asked of a helper another module declares. The call carries what resolution settled —
     * {@code lib.flatten} — and the module emitting it carries the body; nothing else an output
     * holds relates the two.
     */
    @Test
    void aCallToAnotherModulesHelperNamesWhatTheCarriedHelperIsFiledUnder() {
        CheckedProgram program = CheckedProgram.of(List.of(LIB, APP));
        CheckedModule app = program.module("app");
        ValueName reached = theOneCallReaching(app, "flatten");

        assertEquals(Set.of(reached), filedUnder(app),
                "the call names " + reached + " and the module carries " + filedUnder(app));
    }

    /** The same, for the library's own recursion, which {@code folds} carries for the same reason. */
    @Test
    void aCallToTheLibrarysHelperNamesWhatTheCarriedHelperIsFiledUnder() {
        CheckedProgram program = CheckedProgram.of(List.of(FOLDS));
        CheckedModule folds = program.module("folds");
        ValueName reached = theOneCallReaching(folds, "foldFrom");

        assertEquals(Set.of(reached), filedUnder(folds),
                "the call names " + reached + " and the module carries " + filedUnder(folds));
    }

    /**
     * And the identity a carried helper is filed under answers what it is a declaration of.
     *
     * <p>{@code souther.list} declares {@code foldFrom}, so a reader asking the helper's name
     * whether the language declares it is told that it does. Filed under the module that emits the
     * method, it is told that {@code folds} declares an operation of the standard library.
     *
     * <p>Asked through {@link ValueName.Helper} because that is what the snapshot answers with, and
     * a library operation is not one — which is the same fact arriving as a type rather than as an
     * answer.
     */
    @Test
    void whatACarriedHelperIsFiledUnderSaysWhoDeclaredIt() {
        CheckedProgram program = CheckedProgram.of(List.of(FOLDS));
        CheckedHelper carried = only(program.module("folds").helpers());

        assertTrue(carried.name().isDeclaredByLanguage(),
                "the language declares what `" + carried.name() + "` is a copy of");
    }

    /**
     * Where a declaration is reached from decides the reach name and nothing else.
     *
     * <p>{@code lib} reaches its own {@code flatten} bare and {@code app} reaches the same
     * declaration under the module that declares it. Two references, one declaration — so the reach
     * names differ, and what they denote does not.
     */
    @Test
    void whereACallIsWrittenDecidesTheReachNameAndNotTheDeclaration() {
        CheckedProgram program = CheckedProgram.of(List.of(LIB, APP));

        ReachName inLib = reachOf(program.module("lib"), "flatten");
        ReachName inApp = reachOf(program.module("app"), "flatten");

        ValueName.Helper declared = new ValueName.Helper("lib", "flatten");
        assertEquals(new ReachName.Bare(declared), inLib, "lib reaches its own bare");
        assertEquals(new ReachName.OfModule(declared), inApp,
                "app reaches it under the module that declares it");
        assertEquals(theOneCallReaching(program.module("lib"), "flatten"),
                theOneCallReaching(program.module("app"), "flatten"),
                "and the two reach one declaration");
    }

    /** What every carried helper of {@code module} is filed under. */
    private static Set<ValueName> filedUnder(CheckedModule module) {
        Set<ValueName> names = new LinkedHashSet<>();
        for (CheckedHelper helper : module.helpers()) {
            names.add(helper.name());
        }
        return names;
    }

    /**
     * What every call in {@code module} reaching {@code operation} denotes.
     *
     * <p>One answer for all of them, and the agreement is the point. A module that carries a helper
     * calls it from the body that wanted it and from the helper's own recursion, and both are
     * references to one declaration from one module — so a reader finding two answers here has
     * found two identities for one thing.
     */
    private static ValueName theOneCallReaching(CheckedModule module, String operation) {
        return theOne(callsReaching(module, operation).stream().map(Core.Reached::denotes).toList());
    }

    /** How every call in {@code module} reaching {@code operation} reaches it, which is one way. */
    private static ReachName reachOf(CheckedModule module, String operation) {
        return theOne(callsReaching(module, operation).stream().map(Core.Reached::name).toList());
    }

    /** The one value {@code found} holds, refusing an empty walk and a disagreement alike. */
    private static <T> T theOne(List<T> found) {
        assertEquals(1, new LinkedHashSet<>(found).size(),
                () -> "expected one answer, found " + found);
        return found.get(0);
    }

    /**
     * Every call in {@code module}'s bodies and carried helpers whose callee is named
     * {@code operation}.
     *
     * <p>Matched on the name the callee denotes, which is the question this test is about — not on
     * how the call renders, which is what an output has to stop doing.
     */
    private static List<Core.Reached> callsReaching(CheckedModule module, String operation) {
        List<Core> bodies = new ArrayList<>();
        module.behaviors().forEach(behavior -> {
            if (behavior.implementation() instanceof CheckedImplementation.Body body) {
                bodies.add(body.body());
            }
        });
        module.helpers().forEach(helper -> bodies.add(helper.body()));
        List<Core.Reached> found = new ArrayList<>();
        for (Core body : bodies) {
            collectReaching(body, operation, found);
        }
        return found;
    }

    private static void collectReaching(Core node, String operation, List<Core.Reached> into) {
        if (node instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes().name().equals(operation)) {
            into.add(reached);
        }
        Core.forEachChild(node, child -> collectReaching(child, operation, into));
    }

    private static <T> T only(List<T> found) {
        assertEquals(1, found.size(), () -> "expected exactly one, found " + found);
        assertNotNull(found.get(0));
        return found.get(0);
    }
}
