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
 * Two walks joined into one ({@link GrowingFold}) grow the outer step's accumulator, take each
 * element as the inner step took it, and answer what the outer step answered.
 *
 * <p>The steps are written so that neither side's types are the other's. A join that kept the inner
 * step's accumulator, took its element from the outer step, or its answer from the inner, disagrees
 * here.
 */
class AJoinedStepTakesTheOuterAccumulatorAndTheInnerElementTest {

    /** The inner step reads a {@code Bool} and builds a list of {@code Int}; the outer reads an
     *  {@code Int} and builds a list of {@code Bool}. */
    @Test
    void aMapOverAMapGrowsTheOuterListFromTheInnerElement() {
        Core.Block step = theJoinedStep("""
                module demo
                behavior run : (bs: List<Bool>) -> List<Bool>
                let run (bs) = List.map(n -> n > 0, List.map(b -> if b then 1 else 0, bs))
                """);

        assertEquals(List.of(new Type.ListOf(Type.BOOL), Type.BOOL), step.paramTypes(),
                "the accumulator is the outer step's, and the element arrives as the inner step"
                        + " read it");
        assertEquals(new Type.ListOf(Type.BOOL), step.type().result(),
                "and the step answers what the outer step answered");
    }

    /**
     * A {@code filter} answers through a fork, one side adding and the other handing the accumulator
     * back. Once the {@code map} stands where the add was, both sides answer the mapped list, and
     * the side handing the accumulator back reads it as that list rather than as the filtered one
     * standing as it.
     */
    @Test
    void aMapOverAFilterAnswersTheMappedListOnBothSidesOfTheFork() {
        Core.Block step = theJoinedStep("""
                module demo
                behavior run : (xs: List<Int>) -> List<Bool>
                let run (xs) = List.map(n -> n > 0, List.filter(n -> n > 1, xs))
                """);
        Type mapped = new Type.ListOf(Type.BOOL);

        assertEquals(List.of(mapped, Type.INT), step.paramTypes(),
                "the accumulator is the mapped list, and the element is the filter's");
        Core.If fork = (Core.If) step.body();
        assertEquals(mapped, fork.type(), "the fork answers the mapped list");
        assertEquals(mapped, fork.then().type(), "the side the map stands on answers it");
        Core.Read handedBack = (Core.Read) fork.els();
        assertEquals(step.params().getFirst().binding(), handedBack.binding(),
                "the other side hands the accumulator back");
        assertEquals(mapped, handedBack.type(), "and reads it as the mapped list");
    }

    private static Core.Block theJoinedStep(String source) {
        Compilation c = Compilation.ofSource(source, "Main");
        Bodies.CheckedBody checked = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value();
        List<Core.Call> builds = new ArrayList<>();
        each(checked.body(), e -> {
            if (e instanceof Core.Call call && call.fn() == Core.Emitted.BUILD_LIST) {
                builds.add(call);
            }
        });
        assertEquals(1, builds.size(), "the two walks are one: " + builds);
        return (Core.Block) Core.withoutStanding(builds.getFirst().args().getFirst());
    }

    private static void each(Core e, Consumer<Core> f) {
        if (e == null) {
            return;
        }
        f.accept(e);
        Core.forEachChild(e, child -> each(child, f));
    }
}
