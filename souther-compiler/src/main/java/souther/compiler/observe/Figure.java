package souther.compiler.observe;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * A figure this compiler held a piece of its work to, as it stood where the work was compared
 * against it and stopped.
 *
 * <p>Carried by what stopped, from the place the comparison was made. A reader told a figure
 * stopped something is told which one, and a figure that is only known to have been some figure
 * is not one of these: what is not carried is not said, and nothing reconstructs it later from a
 * word that several figures share.
 *
 * <p>Two kinds: the figures the composing stage holds itself to ({@link Budget}), and the rest of
 * this compiler's ({@link WorkFigure.At}). Each is some fixed where it is declared and some a
 * compilation is set up with, so each carries the number it stood at where it was reached, and
 * a reader is told the number the compilation it is reading used. Sealed, so a figure is a value
 * whose equality is its kind's and its number's, and an answer that holds one is compared by
 * what it holds.
 */
public sealed interface Figure permits Figure.Budget, WorkFigure.At {

    /**
     * One of the composing stage's budgets, and the figure it stood at where it was reached
     * ({@link CompositionBudget#reached}): the one the compilation reaching it held it to, or the
     * share of it the work that stopped was held to where the budget is shared out among several
     * ({@link CompositionBudget#reachedAShareOf}).
     */
    record Budget(CompositionBudget budget, int at) implements Figure {

        public Budget {
            Objects.requireNonNull(budget, "a budget reached is some budget");
            if (at < 0) {
                throw new IllegalArgumentException("a budget stands at no fewer than none: " + at);
            }
        }

        @Override
        public String name() {
            return budget.name();
        }

        @Override
        public String counts() {
            return budget.counts();
        }

        @Override
        public String most() {
            return Integer.toString(at);
        }
    }

    /** What this compiler calls it where it is declared. */
    String name();

    /** What it counts, in the words a report says it in: "how many …". */
    String counts();

    /** The figure itself as it stood on the run that reached it, in the words of what it counts. */
    String most();

    /**
     * {@code figures}, each once, in the one order a holder of several keeps them in: by name, and
     * by what it stood at where one figure was reached at two numbers.
     *
     * <p>Here and not where they are collected, because they arrive in whatever order a walk met
     * them, and two holders that each put them in an order of their own would say the same figures
     * in two orders.
     */
    static List<Figure> inOrder(Collection<? extends Figure> figures) {
        Set<Figure> once = new HashSet<>(figures);
        List<Figure> out = new ArrayList<>(once);
        out.sort(Comparator.comparing(Figure::name).thenComparing(Figure::most));
        return List.copyOf(out);
    }

    /**
     * Two lists of figures, each in {@link #inOrder}, figure by figure and then the shorter first:
     * the order a holder compares by where what tells two of it apart includes the figures.
     */
    static int compare(List<Figure> these, List<Figure> those) {
        for (int i = 0; i < Math.min(these.size(), those.size()); i++) {
            int byName = these.get(i).name().compareTo(those.get(i).name());
            if (byName != 0) {
                return byName;
            }
            int byMost = these.get(i).most().compareTo(those.get(i).most());
            if (byMost != 0) {
                return byMost;
            }
        }
        return Integer.compare(these.size(), those.size());
    }
}
