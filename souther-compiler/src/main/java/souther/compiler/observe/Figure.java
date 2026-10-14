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
 * <p>Two kinds: the figures the composing stage holds itself to, which are fixed
 * ({@link Budget}), and the rest of this compiler's, some fixed and some handed to a run
 * ({@link WorkFigure.At}). Sealed, so a figure is a value whose equality is its kind's and an
 * answer that holds one is compared by what it holds.
 */
public sealed interface Figure permits Figure.Budget, WorkFigure.At {

    /** One of the composing stage's budgets, which stands at the figure it declares. */
    record Budget(CompositionBudget budget) implements Figure {

        public Budget {
            Objects.requireNonNull(budget, "a budget reached is some budget");
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
            return Integer.toString(budget.maximum());
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
}
