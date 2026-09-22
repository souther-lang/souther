package souther.compiler.core;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value another module declares is named in this one without being copied into it.
 *
 * <p>{@link AValueNamedTwiceIsBuiltOnceTest} holds this for the module that declares the chain. A
 * chain published across a module boundary is the same chain, and what arrives through the import
 * is held to the same size: the tree a behavior is emitted from grows with the length of the chain
 * and not with what naming every link twice multiplies out to.
 */
class AValueAnotherModuleDeclaresIsBuiltOnceTest {

    private static final int LINKS = 24;

    /** What one link may add over the one before it, in nodes of the downstream body. */
    private static final int PER_LINK = 8;

    private static String upstream(int links) {
        StringBuilder source = new StringBuilder("module up exposing (a" + links + ")\n\nlet a0 = 1m\n");
        for (int i = 1; i <= links; i++) {
            source.append("let a").append(i).append(" = a").append(i - 1)
                    .append(" * a").append(i - 1).append('\n');
        }
        return source.toString();
    }

    private static String downstream(int links) {
        return "module down exposing (f)\n\nimport up ( a" + links + " )\n\n"
                + "behavior f : (x: Int) -> Decimal\nlet f (x) = a" + links + "\n";
    }

    private static int nodesIn(int links) {
        Compilation compiled = Compiler.compiledModules(
                List.of(upstream(links), downstream(links)), ModulePath.EMPTY, new ArrayList<>());
        Hir.Expr body = compiled.db()
                .ask(new Bodies.LoweredBody("down", new DefinitionName("f")))
                .value().value().definition().writtenBody();
        return count(body);
    }

    private static int count(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {1};
        Hir.forEachChild(e, child -> held[0] += count(child));
        return held[0];
    }

    @Test
    void theBodyOfABehaviorNamingAPublishedChainIsAsLongAsTheChain() {
        int shorter = nodesIn(LINKS / 2);
        int longer = nodesIn(LINKS);
        assertTrue(longer <= shorter * 3 + LINKS * PER_LINK,
                "a published chain of " + LINKS + " links was built from " + longer
                        + " nodes where one of " + (LINKS / 2) + " was built from " + shorter
                        + ": a value another module declares is being written where it is named");
    }
}
