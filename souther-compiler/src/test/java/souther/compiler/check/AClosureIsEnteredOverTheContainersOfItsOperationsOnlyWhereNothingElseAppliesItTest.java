package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A closure is entered where one of the containers the operations applying it walk holds something,
 * and only where operations are the whole of what applies it.
 *
 * <p>A closure that is also applied directly, or handed to a function of the author's, is applied
 * by something that needs no container. What the operations over containers say of it is then not
 * what a run needs to be inside it, and nothing is said.
 */
class AClosureIsEnteredOverTheContainersOfItsOperationsOnlyWhereNothingElseAppliesItTest {

    private static final String HEAD = """
            module m exposing (f)

            let apply (g: (Int) -> Bool): Bool = g(0)

            partial let repeat (g: (Int) -> Bool, k: Int): Bool =
                if k <= 0 then g(0) else repeat(g, k - 1)

            behavior f : (n: Int, xs: List<Int>, ys: List<Int>) -> Bool
            """;

    /** What the closure {@code over} of the behavior's body is entered over, one for each
     *  operation. */
    private static List<Core> enteredOver(String body) {
        Bodies.CheckedBody checked = Compiler.compiled(HEAD + body, "m").db()
                .ask(new Bodies.CheckedBehavior("m", "f")).value();
        Core.Block block = firstBlockIn(checked.analysis().core());
        assertFalse(block == null, "the body writes a closure");
        return ElementBindings.of(checked.analysis(), DeclarationNewtypes.NONE)
                .enteredOver(block.params().getFirst().binding());
    }

    private static Core.Block firstBlockIn(Core e) {
        if (e instanceof Core.Block block) {
            return block;
        }
        List<Core.Block> found = new ArrayList<>();
        Core.forEachChild(e, child -> {
            Core.Block inside = found.isEmpty() ? firstBlockIn(child) : null;
            if (inside != null) {
                found.add(inside);
            }
        });
        return found.isEmpty() ? null : found.getFirst();
    }

    @Test
    void anOperationOverAContainerEntersTheClosure() {
        assertEquals(1, enteredOver("""
                let f (n, xs, ys) = {
                    let over = x -> n > 5
                    List.any(over, xs)
                }
                """).size());
    }

    @Test
    void aClosureTwoOperationsShareIsEnteredOverEachOfTheirContainers() {
        assertEquals(2, enteredOver("""
                let f (n, xs, ys) = {
                    let over = x -> n > 5
                    List.any(over, xs) || List.any(over, ys)
                }
                """).size());
    }

    /**
     * A direct application, and the application a function that is expanded where it stands makes,
     * are each a copy of the closure with a comparison of their own: what enters the original is
     * the operation alone.
     */
    @Test
    void anApplicationThatIsACopyOfItsOwnIsNotAUseOfTheOriginal() {
        assertEquals(1, enteredOver("""
                let f (n, xs, ys) = {
                    let over = x -> n > 5
                    over(0) || apply(over) || List.any(over, xs)
                }
                """).size());
    }

    /** A function that is not expanded where it stands applies the very closure it is handed. */
    @Test
    void aClosureHandedToAFunctionThatIsNotExpandedIsEnteredOverNothingKnown() {
        assertEquals(List.of(), enteredOver("""
                let f (n, xs, ys) = {
                    let over: (Int) -> Bool = x -> n > 5
                    repeat(over, 3) || List.any(over, xs)
                }
                """));
    }
}
