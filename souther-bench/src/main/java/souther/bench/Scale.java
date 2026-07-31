package souther.bench;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

/**
 * How a whole-workspace compile grows with the number of modules.
 *
 * <p>The modules are generated rather than carried, because what this asks is not what real code
 * costs but whether anything in the compiler is quadratic in the size of the workspace — and a
 * question about shape is answered by holding every module the same and varying only how many there
 * are. Each is the smallest thing that still goes all the way through: a data type, a behavior over
 * it, and a body that constructs one.
 *
 * <p>Two shapes, because they stress different things. Independent modules share nothing, so the
 * cost should be the sum of theirs. A chain has each module importing the one before it, so a name
 * resolved at the end is resolved through every link — the arrangement where a per-module
 * re-derivation shows up as a curve.
 */
final class Scale {

    private Scale() {}

    private static final int[] SIZES = {10, 25, 50, 100, 200};

    static void measure(Report report) {
        for (int modules : SIZES) {
            Timing independent = timeOf(independent(modules));
            Timing chain = timeOf(chain(modules));
            report.line("SCALE n=%-4d  independent %7.1f ms (%5.3f ms/module)   "
                            + "chain %7.1f ms (%5.3f ms/module)",
                    modules, independent.medianMillis(), independent.medianMillis() / modules,
                    chain.medianMillis(), chain.medianMillis() / modules);
        }
    }

    private static Timing timeOf(List<String> sources) {
        return Timing.of(3, 5, () -> {
            Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
            compilation.answerEverything();
            compilation.classes();
        });
    }

    private static List<String> independent(int modules) {
        List<String> sources = new ArrayList<>();
        for (int i = 0; i < modules; i++) {
            sources.add("""
                    module m%d exposing ( D%d, f%d )
                    data D%d = { v: Int, name: String }
                    behavior f%d : (d: D%d) -> D%d
                    let f%d (d) = D%d { v = d.v + 1, name = d.name }
                    """.formatted(i, i, i, i, i, i, i, i, i));
        }
        return sources;
    }

    private static List<String> chain(int modules) {
        List<String> sources = new ArrayList<>();
        sources.add("""
                module c0 exposing ( D0, f0 )
                data D0 = { v: Int, name: String }
                behavior f0 : (d: D0) -> D0
                let f0 (d) = D0 { v = d.v + 1, name = d.name }
                """);
        for (int i = 1; i < modules; i++) {
            sources.add("""
                    module c%d exposing ( D%d, f%d )
                    import c%d ( D%d, f%d )
                    data D%d = { inner: D%d }
                    behavior f%d : (d: D%d) -> D%d
                    let f%d (d) = D%d { inner = f%d(d.inner) }
                    """.formatted(i, i, i, i - 1, i - 1, i - 1, i, i - 1, i, i, i, i, i, i - 1));
        }
        return sources;
    }
}
