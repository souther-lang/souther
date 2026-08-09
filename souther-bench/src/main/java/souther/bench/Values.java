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
 * <p>Three shapes, held the same apart from what a value names and where it is written. Each value
 * of the chain names the one before it, so the last of them stands for the whole chain and the
 * module's source shares what its elaboration copies. The reversed chain is that module written
 * bottom to top, where no value is settled by the time the one naming it is read unless the check
 * puts them in an order of its own. The flat shape declares as many values naming none of them,
 * which is the same number of declarations with nothing to share — so the distance from it is what
 * substitution costs, and a chain's own per-value figure is what says whether that cost is
 * proportional to what the module declares.
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
            Timing chain = timeOf(chain(values, false));
            Timing reversed = timeOf(chain(values, true));
            Timing flat = timeOf(flat(values));
            report.line("VALUES n=%-4d  chain %7.1f ms (%5.3f)   reversed %7.1f ms (%5.3f)   "
                            + "flat %7.1f ms (%5.3f)   ms/value",
                    values, chain.medianMillis(), chain.medianMillis() / values,
                    reversed.medianMillis(), reversed.medianMillis() / values,
                    flat.medianMillis(), flat.medianMillis() / values);
        }
    }

    private static Timing timeOf(String source) {
        return Timing.of(2, 5, () -> {
            Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
            compilation.answerEverything();
            compilation.classes();
        });
    }

    /** {@code n} values, each naming the one before it, and a behavior naming the last —
     * {@code bottomUp} writing the one that names before the one it names. */
    private static String chain(int n, boolean bottomUp) {
        List<String> declarations = new ArrayList<>();
        declarations.add("let v0 = 1");
        for (int i = 1; i < n; i++) {
            declarations.add("let v" + i + " = v" + (i - 1) + " + 1");
        }
        if (bottomUp) {
            Collections.reverse(declarations);
        }
        StringBuilder source = new StringBuilder("module chain exposing ( f )\n\n");
        for (String declaration : declarations) {
            source.append(declaration).append('\n');
        }
        return source.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v")
                .append(n - 1).append("\n").toString();
    }

    /** {@code n} values naming none of them, and a behavior naming the last. */
    private static String flat(int n) {
        StringBuilder source = new StringBuilder("module flat exposing ( f )\n\n");
        for (int i = 0; i < n; i++) {
            source.append("let v").append(i).append(" = ").append(i).append(" + 1\n");
        }
        return source.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v")
                .append(n - 1).append("\n").toString();
    }
}
