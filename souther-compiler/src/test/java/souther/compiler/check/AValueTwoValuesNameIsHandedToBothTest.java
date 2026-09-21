package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value two values name is built once in the region that builds them, and handed to both.
 *
 * <p>A chain whose links reach the previous one through two intermediate values names nothing
 * twice in any one body. What is asked is whether the two intermediates each build the previous
 * link for themselves, which doubles what is evaluated with every link, or are handed the one the
 * region built.
 *
 * <p>Held as a count of builds in the tree the backend emits from, and not as a time: what the
 * sharing is for is what a run evaluates, and that is a property of the tree.
 */
class AValueTwoValuesNameIsHandedToBothTest {

    private static final int LINKS = 20;

    private static String diamonds(int links) {
        StringBuilder source = new StringBuilder(
                "module m exposing (f)\n\nlet a0 = List.length([1, 2, 3])\n");
        for (int i = 1; i <= links; i++) {
            String previous = "a" + (i - 1);
            source.append("let x").append(i).append(" = ").append(previous).append(" + 1\n");
            source.append("let y").append(i).append(" = ").append(previous).append(" + 2\n");
            source.append("let a").append(i).append(" = x").append(i).append(" + y").append(i)
                    .append('\n');
        }
        return source.append("\nbehavior f : (n: Int) -> Int\nlet f (n) = a")
                .append(links).append('\n').toString();
    }

    private static int builds(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Hir.Materialised || e instanceof Hir.ValueInvocation ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += builds(child));
        return held[0];
    }

    @Test
    void everyValueOfADiamondChainIsBuiltOnce() {
        Hir.Expr body = Compiler.compiled(diamonds(LINKS), "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().writtenBody();

        assertEquals(3 * LINKS + 1, builds(body),
                "one build per value: a value two values name is handed to both, and not built by"
                        + " each of them");
    }
}
