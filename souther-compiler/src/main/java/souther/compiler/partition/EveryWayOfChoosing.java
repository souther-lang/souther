package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Every way of choosing one of each of some lists, in turn: the first of the first list with each
 * way of choosing from the rest, then the second of it, and so on — walked as a
 * {@link DepthFirst} search, a way at a time, each one a unit of the figure.
 *
 * <p>The lists are fixed before the walk and none depends on what was chosen from another. That is
 * what lets a list with nothing in it be answered before anything is walked: there is then no way
 * of choosing at all, and nothing is spent. Nothing else falls away on the walk, so it has no dead
 * end, and the figure is a count of the ways handed out.
 *
 * <p>Each way handed out is a value of its own, in the order of the lists.
 */
final class EveryWayOfChoosing {

    private EveryWayOfChoosing() {
    }

    /** What is done with one way of choosing; whether to go on to the next. */
    @FunctionalInterface
    interface Visit<T> {
        boolean goOn(List<T> chosen);
    }

    /** {@code visit} handed each way of choosing one of each of {@code lists}, a unit of
     *  {@code tries} each, until it stops or no unit is left; every way is handed out where there
     *  is none. */
    static <T> DepthFirst.Walked each(List<? extends List<T>> lists, Tries tries,
                                      Visit<T> visit) {
        for (List<T> list : lists) {
            if (list.isEmpty()) {
                return DepthFirst.Walked.EVERY_END_REACHED;
            }
        }
        return DepthFirst.walk(List.<T>of(), tries, chosen -> chosen.size() == lists.size() ? null
                : () -> lists.get(chosen.size()).stream().map(each -> with(chosen, each))
                        .iterator(), visit::goOn);
    }

    private static <T> List<T> with(List<T> chosen, T each) {
        List<T> out = new ArrayList<>(chosen.size() + 1);
        out.addAll(chosen);
        out.add(each);
        return Collections.unmodifiableList(out);
    }
}
