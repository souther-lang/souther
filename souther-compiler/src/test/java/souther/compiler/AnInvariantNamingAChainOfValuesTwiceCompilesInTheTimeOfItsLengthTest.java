package souther.compiler;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A type whose invariant is over a chain of values, each naming the one before it twice, is
 * compiled, and compiled against by a module that includes it, by work that grows with the length
 * of the chain. The invariant's clause holds each value as one node in two slots, so a walk that
 * meets a node once per path to it makes 2^N visits for N links.
 *
 * <p>Each test asks that the compile finishes with nothing refused. At this length a walk that
 * follows every path does not finish in any time a test waits, and a time limit would not stop it,
 * so the work the walks make is held where it is counted: the nodes {@code Core.forEachDistinctNode}
 * visits in {@code ASharedNodeIsVisitedOnceByTheDistinctWalkTest}, and that the clause reader walks
 * through it in {@code AClauseIsReadForItsFieldsByAWalkThatMeetsEachNodeOnceTest}.
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

    private static final String BUILDS_AGAINST_THE_WRAPPER = """
            module app.x exposing ( through )
            import app.w ( Wrapped, wrap )
            behavior through : (n: Int) -> Wrapped
            let through (n) = wrap(n)
            """;

    private static final String BUILDS_THE_TYPE = """
            behavior mk : (n: Int) -> Base
            let mk (n) = Base { total = 1 }
            example mk
                | "one" : (1) -> Base { total = 1 }
            """;

    @Test
    void theModuleAndAModuleThatIncludesItsTypeCompileAtThirtyLinks() {
        Compiler.compileModules(List.of(INCLUDES_THE_TYPE),
                ModulePath.of(Compiler.compile(chainModule())));
    }

    @Test
    void aThirdModuleBuiltAgainstThatOneCompilesAtThirtyLinks() {
        Map<String, ClassFileImage> lib = Compiler.compile(chainModule());
        Map<String, ClassFileImage> path = new HashMap<>(lib);
        path.putAll(Compiler.compileModules(List.of(INCLUDES_THE_TYPE), ModulePath.of(lib)));
        Compiler.compileModules(List.of(BUILDS_AGAINST_THE_WRAPPER), ModulePath.of(path));
    }

    /** Every reading that follows the compile — what the type's values are, the classes of its
     *  behaviors, the emission sites — meets the clause too, and none of them finds more nodes
     *  than the clause has. */
    @Test
    void everyReadingOfAModuleHoldingTheChainAnswersAtThirtyLinks() {
        Compilation compilation = Compilation.ofSource(chainModule() + BUILDS_THE_TYPE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors());
    }
}
