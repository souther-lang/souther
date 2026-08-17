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
 * <p>Independent modules share nothing, so the cost should be the sum of theirs. A chain has each
 * module importing the one before it and holding its type, so a name resolved at the end is resolved
 * through every link — the arrangement where a per-module re-derivation shows up as a curve.
 *
 * <p>Neither says anything about how much a module imports, because a module in either imports one
 * thing or none. A walk that re-reads a module's imports once per import is quadratic in that number
 * and flat at one, so {@link #imports} varies that number itself — {@link #WIDTHS}, at one size — and
 * holds everything else still. {@link Values} asks this of a module's values and has had the fan-out
 * shape from the start.
 *
 * <p>Held still means every module of every width declaring the same data, the same behavior and the
 * same body, down to the text. An import with no name list is what makes that possible: the module is
 * resolved and read, and nothing in the body has to mention it, so what separates two widths is the
 * imports and not the expressions written to justify them. The figure to read is the cost per import
 * — per module, a wider module doing more is what widening means, and the question is whether each
 * import costs the same as the last.
 *
 * <p>Two shapes this is not. Widening the chain does not answer it: each of its types contains the
 * one before it, so a module importing four contains four and each of those four, and what grows is
 * the type as a tree — measured, that cost four times a chain of the same length at fourteen modules
 * and was doubling every two. Nor does importing a name and using it: the use is a construction, a
 * call, a field read and an addition, so four imports carry four of each and the difference between
 * two widths is mostly the bodies.
 */
final class Scale {

    private Scale() {}

    private static final int[] SIZES = {10, 25, 50, 100, 200};

    /** Imports per module, doubling, so the ratio between two lines names the exponent the way the
     *  doubling sizes do. Zero is among them and is the floor the rest are read against: what an
     *  import costs is what a line has above that one. */
    static final int[] WIDTHS = {0, 1, 2, 4, 8};

    /** The size the widths are measured at: the largest, where the fixed cost of a compile is
     *  smallest against the rest and a difference between widths is least buried in it. */
    private static final int WIDTH_MODULES = 200;

    static void measure(Report report) {
        for (int modules : SIZES) {
            line(report, modules, "independent", independent(modules));
            line(report, modules, "chain", chain(modules));
        }
        for (int width : WIDTHS) {
            Timing timing = timeOf(imports(WIDTH_MODULES, width));
            report.line("SCALE n=%-4d imports=%-2d  %5d links  %7.1f ms",
                    WIDTH_MODULES, width, links(WIDTH_MODULES, width), timing.medianMillis());
        }
    }

    /** One line per shape, as {@link Values} reports: the per-module figure is the one to read, and
     *  four numbers of two shapes on one line left no room for a third. */
    private static void line(Report report, int modules, String shape, List<String> sources) {
        Timing timing = timeOf(sources);
        report.line("SCALE n=%-4d %-18s %7.1f ms (%5.3f ms/module)",
                modules, shape, timing.medianMillis(), timing.medianMillis() / modules);
    }

    private static Timing timeOf(List<String> sources) {
        return Timing.of(3, 5, () -> {
            Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
            compilation.answerEverything();
            compilation.classes();
        });
    }

    /**
     * {@code modules} modules, each importing the {@code width} written just before it.
     *
     * <p>Every module is the same module. It declares the same data under a different number, the
     * same behavior over it and the same body, and the import lines are the only text that differs
     * between one width and another — so are the only thing a difference between two of these can be
     * about.
     *
     * <p>The first {@code width} modules import fewer, there being fewer written before them. At the
     * sizes this is measured at that is a fixed handful against the rest and it is the same handful
     * at every width.
     */
    /**
     * How many imports {@link #imports} writes, which is not {@code modules * width}: the first
     * {@code width} modules import what is written before them and there is less of it.
     */
    static int links(int modules, int width) {
        int total = 0;
        for (int i = 0; i < modules; i++) {
            total += Math.min(i, width);
        }
        return total;
    }

    static List<String> imports(int modules, int width) {
        List<String> sources = new ArrayList<>();
        for (int i = 0; i < modules; i++) {
            StringBuilder imported = new StringBuilder();
            for (int j = Math.max(0, i - width); j < i; j++) {
                imported.append("import i%d%n".formatted(j));
            }
            sources.add("""
                    module i%d exposing ( D%d, f%d )
                    %sdata D%d = { v: Int }
                    behavior f%d : (d: D%d) -> D%d
                    let f%d (d) = D%d { v = d.v + 1 }
                    """.formatted(i, i, i, imported, i, i, i, i, i, i));
        }
        return sources;
    }

    static List<String> independent(int modules) {
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

    static List<String> chain(int modules) {
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
