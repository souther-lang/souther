package souther.compiler.observe;

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
 * ({@code CompositionBudget}), and the rest of this compiler's, some fixed and some handed to a
 * run ({@link WorkFigure}).
 */
public interface Figure {

    /** What this compiler calls it where it is declared. */
    String name();

    /** What it counts, in the words a report says it in: "how many …". */
    String counts();

    /** The figure itself as it stood on the run that reached it, in the words of what it counts. */
    String most();
}
