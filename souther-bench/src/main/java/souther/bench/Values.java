package souther.bench;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * How a compile grows with the number of values one module declares.
 *
 * <p>{@link Scale} asks the same question of a workspace and this asks it of a module, because the
 * two have different answers: a value is substituted where it is named, so what a module declares
 * can cost more than the sum of its declarations while what a workspace holds does not.
 *
 * <p>The shapes differ in what a value reaches and in where the thing it reaches is written, which
 * is what the answer turns on. A chain has each value name the one before it. A chain through
 * helpers has each value call a helper that names the one before it, so the same reaching is there
 * and no value writes another's name. Either written bottom to top is the module where nothing a
 * value reaches has been read yet by the time the value is. The fan-out has one value reach every
 * other, which is the shape a walk that re-reads a name's edges once per edge is quadratic in and a
 * chain says nothing about. The flat shape declares as many values reaching none of them: the same
 * number of declarations with nothing to share, and so the floor the rest are read against.
 *
 * <p>The per-value figure is the one to read. A total that grows is only the module growing; a
 * per-value figure that grows with the module is a term above linear, and it is reported at sizes
 * that double so the ratio between two lines names the exponent.
 */
final class Values {

    private Values() {}

    // Doubling from a size the fixed cost of a compile is already small against: below a hundred
    // values a module costs about what an empty one does, and a per-value figure taken there says
    // more about that floor than about the curve.
    private static final int[] SIZES = {100, 200, 400, 800};

    static void measure(Report report) {
        for (int values : SIZES) {
            line(report, values, "chain", chain(values, false));
            line(report, values, "chain bottom-up", chain(values, true));
            line(report, values, "chain via helpers", throughHelpers(values, false));
            line(report, values, "same, bottom-up", throughHelpers(values, true));
            line(report, values, "fan-out", fanOut(values));
            line(report, values, "flat", flat(values));
        }
    }

    private static void line(Report report, int values, String shape, String source) {
        Timing timing = timeOf(source);
        report.line("VALUES n=%-4d %-18s %7.1f ms (%5.3f ms/value)",
                values, shape, timing.medianMillis(), timing.medianMillis() / values);
    }

    private static Timing timeOf(String source) {
        return Timing.of(2, 5, () -> {
            Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
            compilation.answerEverything();
            compilation.classes();
        });
    }

    /** {@code n} values, each naming the one before it — {@code bottomUp} writing the one that
     * names before the one it names. */
    static String chain(int n, boolean bottomUp) {
        List<String> declarations = new ArrayList<>();
        declarations.add("let v0 = 1");
        for (int i = 1; i < n; i++) {
            declarations.add("let v" + i + " = v" + (i - 1) + " + 1");
        }
        return module("chain", declarations, bottomUp, n - 1);
    }

    /** The same reaching with none of the names: each value calls a helper, and the helper is what
     * names the value before it. */
    static String throughHelpers(int n, boolean bottomUp) {
        List<String> declarations = new ArrayList<>();
        declarations.add("let v0 = 1");
        for (int i = 1; i < n; i++) {
            declarations.add("let step" + i + " (x: Int) = v" + (i - 1) + " + x");
            declarations.add("let v" + i + " = step" + i + "(1)");
        }
        return module("helpers", declarations, bottomUp, n - 1);
    }

    /** One value reaching every other, written as a list so that reaching many is not also nesting
     * deeply. */
    static String fanOut(int n) {
        List<String> declarations = new ArrayList<>();
        StringBuilder hub = new StringBuilder("let hub = [ ");
        for (int i = 0; i < n; i++) {
            declarations.add("let v" + i + " = " + i + " + 1");
            hub.append(i == 0 ? "" : ", ").append("v").append(i);
        }
        declarations.add(hub.append(" ]").toString());
        return module("fanout", declarations, false, 0);
    }

    /** {@code n} values reaching none of them. */
    static String flat(int n) {
        List<String> declarations = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            declarations.add("let v" + i + " = " + i + " + 1");
        }
        return module("flat", declarations, false, n - 1);
    }

    /** The module {@code declarations} make, with a behavior naming {@code named} — reversed first
     * where the point is that nothing a value reaches is written above it. */
    private static String module(String name, List<String> declarations, boolean bottomUp,
                                 int named) {
        List<String> written = new ArrayList<>(declarations);
        if (bottomUp) {
            Collections.reverse(written);
        }
        StringBuilder source = new StringBuilder("module " + name + " exposing ( f )\n\n");
        for (String declaration : written) {
            source.append(declaration).append('\n');
        }
        return source.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v")
                .append(named).append("\n").toString();
    }
}
