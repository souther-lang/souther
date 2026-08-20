package souther.compiler;

import souther.compiler.source.SourceId;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A row runs the classes this compile generated, not ones of the same name found further up.
 *
 * <p>The compile's classes sit over a module path, and the whole point of that order is that a module
 * being compiled is the one that runs. A loader that delegates to its parent first inverts it: a
 * class file left from an earlier build answers, and the row is compared against an implementation
 * this compile did not produce. A correct model is then reported as one whose example does not hold,
 * and the author is sent to look at a row that is right.
 *
 * <p>It is also where the budget goes missing. Counted points are put in the classes this compile
 * generates, so running someone else's classes runs code with no counting in it at all.
 *
 * <p>A module on the path that carries its published declarations is refused outright, which covers
 * the tidy case. What is left is everything the module check cannot recognise as a module — a
 * directory of loose class files, a jar built before the declarations were stamped on — and those are
 * exactly the ones that used to win.
 */
class AnEvaluationRunsTheClassesThisCompileGeneratedTest {

    /** What an earlier build left behind: it answers 1 whatever it is given. */
    private static final String EARLIER = """
            module example.stale
            data N = Int
            data Out = Int
            behavior answer : (n: N) -> Out constructs Out
            let answer (n) = Out(1)
            """;

    /** What is being compiled now: it answers with its input, and the row states that. */
    private static final String NOW = """
            module example.stale
            data N = Int
            data Out = Int
            behavior answer : (n: N) -> Out constructs Out
            let answer (n) = Out(n.value)
            example answer
              | "answers with its input": (N(7)) -> Out(7)
            """;

    /**
     * The earlier build's classes, with the published declarations left off.
     *
     * <p>Without them the module check cannot see a module here at all, so nothing refuses the
     * compile and the classes are simply on the path — which is the shape a directory of loose class
     * files has.
     */
    private static ModulePath leftOverClassFiles() {
        Map<String, byte[]> built = new LinkedHashMap<>(Compiler.compile(EARLIER));
        built.keySet().remove(Emitted.declarations("example.stale"));
        return built::get;
    }

    @Test
    void aRowRunsTheImplementationBeingCompiledAndNotOneLeftOnThePath() {
        Compilation compilation = Compilation.ofSources(List.of(NOW), leftOverClassFiles());
        compilation.answerEverything();

        assertNull(compilation.failure(),
                "the model is correct, so nothing is wrong with it");

        SourceId sourceId = compilation.exampleSourcesOf("example.stale").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.stale", sourceId, Output.CoverageMode.NONE))
                .value().rows();

        assertEquals(1, rows.size(), rows.toString());
        assertEquals(Disposition.HELD, rows.get(0).disposition(),
                "the row was compared against the implementation this compile generated");
    }

    /** And the names it does not hold are still the parent's: the runtime a generated class calls
     *  into is loaded once, by whoever already has it, not defined a second time here. */
    @Test
    void anameThisCompileDidNotGenerateStillComesFromTheParent() throws Exception {
        Map<String, byte[]> mine = Compiler.compile(EARLIER);
        MemoryClassLoader loader =
                new MemoryClassLoader(mine, AnEvaluationRunsTheClassesThisCompileGeneratedTest.class
                        .getClassLoader());

        assertEquals(souther.runtime.Behavior.class, loader.loadClass("souther.runtime.Behavior"),
                "the runtime class is the one the caller already has");
    }
}
