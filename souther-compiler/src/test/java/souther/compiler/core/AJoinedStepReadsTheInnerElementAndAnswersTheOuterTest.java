package souther.compiler.core;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two walks joined into one ({@link GrowingFold}) take each element as the inner step took it and
 * answer what the outer step answered.
 *
 * <p>The two steps are written so that neither side's types are the other's: the inner step reads a
 * {@code Bool} and answers a list of {@code Int}, the outer reads an {@code Int} and answers a list
 * of {@code Bool}. A join that took its element from the outer step, or its answer from the inner,
 * disagrees here.
 */
class AJoinedStepReadsTheInnerElementAndAnswersTheOuterTest {

    @Test
    void theJoinedStepReadsWhatTheInnerStepReadAndAnswersWhatTheOuterAnswered() {
        Compilation c = Compilation.ofSource("""
                module demo
                behavior run : (bs: List<Bool>) -> List<Bool>
                let run (bs) = List.map(n -> n > 0, List.map(b -> if b then 1 else 0, bs))
                """, "Main");
        Bodies.CheckedBody checked = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value();
        List<Core.Call> builds = new ArrayList<>();
        each(checked.body(), e -> {
            if (e instanceof Core.Call call && call.fn() == Core.Emitted.BUILD_LIST) {
                builds.add(call);
            }
        });
        assertEquals(1, builds.size(), "the two walks are one: " + builds);
        Core.Block step = (Core.Block) Core.withoutStanding(builds.getFirst().args().getFirst());

        assertEquals(Type.BOOL, step.paramTypes().get(1),
                "the element arrives as the inner step read it");
        assertEquals(new Type.ListOf(Type.BOOL), step.type().result(),
                "and the step answers what the outer step answered");
    }

    private static void each(Core e, Consumer<Core> f) {
        if (e == null) {
            return;
        }
        f.accept(e);
        Core.forEachChild(e, child -> each(child, f));
    }
}
