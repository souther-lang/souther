package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * Every way of choosing one of each of some lists, in turn: the first of the first list with each
 * way of choosing from the rest, then the second of it, and so on.
 *
 * <p>The lists are fixed before the walk and none depends on what was chosen from another. That is
 * what lets a list with nothing in it be answered before anything is walked: there is then no way
 * of choosing at all. A walk that went through the ways before it first would go through every way
 * of choosing from the lists ahead of the empty one with no way at the end of any of them — work
 * that whatever bounds the ways handed out never sees, as many times over as those lists multiply.
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

    /** {@code visit} handed each way of choosing one of each of {@code lists}, until it stops; and
     *  whether every way was handed out, which is so where there is none. */
    static <T> boolean each(List<? extends List<T>> lists, Visit<T> visit) {
        for (List<T> list : lists) {
            if (list.isEmpty()) {
                return true;
            }
        }
        return from(lists, 0, new ArrayList<>(lists.size()), visit);
    }

    private static <T> boolean from(List<? extends List<T>> lists, int at, List<T> chosen,
                                    Visit<T> visit) {
        if (at == lists.size()) {
            return visit.goOn(List.copyOf(chosen));
        }
        for (T each : lists.get(at)) {
            chosen.add(each);
            boolean more = from(lists, at + 1, chosen, visit);
            chosen.removeLast();
            if (!more) {
                return false;
            }
        }
        return true;
    }
}
