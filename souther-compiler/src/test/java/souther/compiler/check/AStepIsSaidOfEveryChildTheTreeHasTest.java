package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@link ScopeStep#forEachChild} hands over the children {@link Core#forEachChild} does, in the same
 * order.
 *
 * <p>Which slots a node has is {@code Core}'s answer. The nodes that change what a name means are
 * written out a second time where the step into each slot is said, and a slot added to one of them
 * in {@code Core} and not there would be walked by nothing that carries an environment. The
 * exhaustive switch stops a node kind being missed; this stops a slot being missed.
 *
 * <p>Over a body that holds each of the nodes the steps are written out for, which is checked
 * rather than taken on trust: a model that stopped holding one would leave this green about nothing.
 */
class AStepIsSaidOfEveryChildTheTreeHasTest {

    private static final String MODEL = """
            module demo
            data Q = Int
                invariant value >= 0
            data Red
            data Green
            data Color = Red | Green
            data Item = { n: Int }
            data Nope
            data Yes
            data No
            behavior f : (x: Int, c: Color, items: List<Item>) -> Yes | No | Nope
                constructs Q
            let f (x, c, items) = {
                let big = List.filter(i -> i.n > 3, items)
                guard Q(x) as q else Nope
                match c with
                    | Red -> if q.value > List.length(big) then Yes else No
                    | Green -> No
            }
            """;

    /** The nodes whose steps are written out rather than taken from {@link Core#forEachChild}. */
    private static final Set<String> WRITTEN_OUT =
            Set.of("If", "IfConstructed", "LetIn", "Block", "Match");

    @Test
    void theStepsAreSaidOfTheChildrenTheTreeHasInItsOrder() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("f");
        assertNotNull(body, "the behavior under test has a body");

        Set<String> met = new TreeSet<>();
        compare(body, met);

        assertEquals(new TreeSet<>(WRITTEN_OUT), met, "the body holds each of them");
    }

    private static void compare(Core e, Set<String> met) {
        if (e == null) {
            return;
        }
        if (WRITTEN_OUT.contains(e.getClass().getSimpleName())) {
            met.add(e.getClass().getSimpleName());
        }
        List<Core> tree = new ArrayList<>();
        Core.forEachChild(e, tree::add);
        List<Core> stepped = new ArrayList<>();
        ScopeStep.forEachChild(e, (child, step) -> stepped.add(child));

        assertEquals(tree.size(), stepped.size(), () -> "the children of " + e);
        for (int i = 0; i < tree.size(); i++) {
            assertSame(tree.get(i), stepped.get(i), "child " + i + " of " + e);
        }
        tree.forEach(child -> compare(child, met));
    }
}
