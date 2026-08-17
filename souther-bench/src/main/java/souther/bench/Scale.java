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
 * and flat at one, so {@link #narrow} and {@link #wide} vary it and nothing else: same modules, same
 * declarations, a type that holds nothing across a boundary, and one import against {@link #LINKS}.
 * {@link Values} asks this of a module's values and has had the fan-out shape from the start.
 *
 * <p>Widening the chain instead does not answer it. Each of its types contains the one before it, so
 * a module importing four would contain four, and each of those four — the type grows as a tree
 * rather than the imports as a list. Measured at fourteen modules that shape already cost four times
 * a chain of the same length and was doubling every two, which is a number about the type and not
 * about the imports.
 */
final class Scale {

    private Scale() {}

    private static final int[] SIZES = {10, 25, 50, 100, 200};

    /** How many modules a wide link imports. Enough that a term in the square of it is visible
     *  against the linear one, and small enough to be an arrangement someone writes. */
    static final int LINKS = 4;

    static void measure(Report report) {
        for (int modules : SIZES) {
            line(report, modules, "independent", independent(modules));
            line(report, modules, "chain", chain(modules));
            line(report, modules, "narrow (1 import)", narrow(modules));
            line(report, modules, "wide (%d imports)".formatted(LINKS), wide(modules));
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
     * A chain whose modules import one another and hold nothing of one another.
     *
     * <p>This exists to be read against {@link #wide}, and the two differ in one thing. It cannot be
     * read against {@link #chain}, whose data nests: there each module's type contains the one
     * before it, so widening those links would multiply the type as well as the imports and the
     * difference between the two lines would be neither.
     */
    static List<String> narrow(int modules) {
        return flat("p", modules, 1);
    }

    /**
     * The same, with each module importing the {@link #LINKS} before it.
     *
     * <p>Read against {@link #narrow} at the same size, what is between the two lines is what the
     * imports cost, because that is all there is between the two workspaces: the same modules, the
     * same declarations, the same flat type, and every body doing the same thing to each module it
     * names.
     */
    static List<String> wide(int modules) {
        return flat("q", modules, LINKS);
    }

    /**
     * {@code modules} modules, each importing up to {@code links} of those before it and calling
     * every one of them.
     *
     * <p>Nothing is held across a module boundary. A module's data is one {@code Int} whatever it
     * imports, so what a compile walks grows with the number of modules and not with what they name
     * — which is what lets the number of imports be varied on its own.
     */
    private static List<String> flat(String prefix, int modules, int links) {
        List<String> sources = new ArrayList<>();
        sources.add("""
                module %s0 exposing ( D0, f0 )
                data D0 = { v: Int }
                behavior f0 : (d: D0) -> D0
                let f0 (d) = D0 { v = d.v + 1 }
                """.formatted(prefix));
        for (int i = 1; i < modules; i++) {
            StringBuilder imports = new StringBuilder();
            StringBuilder sum = new StringBuilder();
            for (int j = Math.max(0, i - links); j < i; j++) {
                imports.append("import %s%d ( D%d, f%d )%n".formatted(prefix, j, j, j));
                sum.append(sum.isEmpty() ? "" : " + ")
                        .append("f%d(D%d { v = d.v }).v".formatted(j, j));
            }
            sources.add("""
                    module %s%d exposing ( D%d, f%d )
                    %sdata D%d = { v: Int }
                    behavior f%d : (d: D%d) -> D%d
                    let f%d (d) = D%d { v = %s }
                    """.formatted(prefix, i, i, i, imports, i, i, i, i, i, i, sum));
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
