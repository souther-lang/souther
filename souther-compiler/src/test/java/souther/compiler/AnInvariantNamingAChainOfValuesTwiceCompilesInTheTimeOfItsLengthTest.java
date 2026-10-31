package souther.compiler;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A type whose invariant is over a chain of values, each naming the one before it twice, is
 * compiled, and compiled against by a module that includes it, by work that grows with the length
 * of the chain. The invariant's clause holds each value as one node in two slots, so a walk that
 * meets a node once per path to it makes 2^N visits for N links.
 *
 * <p>The bound is a hang guard. At this length the walk that follows every path does not finish
 * in any time a test waits; the node count the walk makes is held in
 * {@code ASharedNodeIsVisitedOnceByTheDistinctWalkTest}.
 */
class AnInvariantNamingAChainOfValuesTwiceCompilesInTheTimeOfItsLengthTest {

    private static final int LINKS = 30;

    private static String chainModule() {
        StringBuilder source = new StringBuilder("module lib.t exposing ( Base )\n");
        source.append("let c0 = 2\n");
        for (int i = 1; i <= LINKS; i++) {
            source.append("let c%d = c%d + c%d\n".formatted(i, i - 1, i - 1));
        }
        source.append("data Base = { total: Int }\n");
        source.append("    invariant bound = total <= c%d\n".formatted(LINKS));
        return source.toString();
    }

    private static final String INCLUDES_THE_TYPE = """
            module app.w exposing ( Wrapped, wrap )
            import lib.t ( Base )
            data Wrapped = { ...Base, w: Int }
            behavior wrap : (n: Int) -> Wrapped
            let wrap (n) = Wrapped { total = 1, w = n }
            """;

    @Test
    void theModuleAndAModuleThatIncludesItsTypeCompileAtThirtyLinks() {
        assertTimeoutPreemptively(Duration.ofSeconds(60), () ->
                Compiler.compileModules(List.of(INCLUDES_THE_TYPE),
                        ModulePath.of(Compiler.compile(chainModule()))));
    }
}
