package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

/**
 * That the shapes these measurements are taken against still compile.
 *
 * <p>{@link CorpusTest} makes this claim about the sources carried in this module. The generated
 * ones had nobody making it, and they are the arrangement most of the reasoning here rests on: a
 * language change that leaves one of them behind leaves a measurement being taken of a compile that
 * stops early, which is faster than one that finishes and reads as an improvement. Nothing about a
 * timing says which of the two it timed.
 *
 * <p>At small sizes. What is asked here is whether the shape is admissible, and a shape that is
 * admissible at ten modules is admissible at two hundred — the sizes are what the measurement varies
 * and are no part of this. Held small on purpose: a test that took as long as the benchmark would be
 * a benchmark, and would stop being run.
 */
class EveryShapeThatIsTimedStillCompilesTest {

    /** Enough of each shape to be that shape: a chain of four has a middle, and a wide link at four
     *  imports {@link Scale#LINKS} modules rather than however many there are. */
    private static final int MODULES = Scale.LINKS + 2;

    /** Enough values that a fan-out fans and a chain has links that are not its ends. */
    private static final int VALUES = 8;

    @Test
    void everyWorkspaceShapeCompiles() {
        compiles("independent", Scale.independent(MODULES));
        compiles("chain", Scale.chain(MODULES));
        compiles("narrow", Scale.narrow(MODULES));
        compiles("wide", Scale.wide(MODULES));
    }

    @Test
    void everyModuleShapeCompiles() {
        compiles("chain", List.of(Values.chain(VALUES, false)));
        compiles("chain bottom-up", List.of(Values.chain(VALUES, true)));
        compiles("chain via helpers", List.of(Values.throughHelpers(VALUES, false)));
        compiles("same, bottom-up", List.of(Values.throughHelpers(VALUES, true)));
        compiles("fan-out", List.of(Values.fanOut(VALUES)));
        compiles("flat", List.of(Values.flat(VALUES)));
    }

    /**
     * That the wide link is wide.
     *
     * <p>The shape is written by a loop over what a module imports, and a loop that produced one
     * import would still compile, still be timed, and still be reported under a name saying it was
     * several. What the measurement is for is the difference between this and {@code narrow}, and
     * there is no difference to measure if the two are the same arrangement.
     */
    @Test
    void aWideLinkImportsSeveralModules() {
        String last = Scale.wide(MODULES).getLast();
        long imports = last.lines().filter(line -> line.startsWith("import ")).count();
        if (imports != Scale.LINKS) {
            throw new AssertionError("a wide link imports " + imports + " module(s), not "
                    + Scale.LINKS + ":\n" + last);
        }
    }

    private static void compiles(String shape, List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        List<String> errors = new ArrayList<>();
        for (List<Diagnostic> found : Located.diagnosticsOf(compilation.diagnostics()).values()) {
            for (Diagnostic diagnostic : found) {
                if (diagnostic.severity() == Severity.ERROR) {
                    errors.add(diagnostic.code() + " at " + diagnostic.primary());
                }
            }
        }
        if (!errors.isEmpty()) {
            throw new AssertionError("the `" + shape + "` shape no longer compiles:\n  "
                    + String.join("\n  ", errors));
        }
        // Asked after the errors, and asked at all: a shape that compiles to nothing is one the
        // measurement walks past, and the timing would be of a compile that reached no back end.
        if (compilation.classes().isEmpty()) {
            throw new AssertionError("the `" + shape + "` shape generated no classes");
        }
    }
}
