package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * Every way of choosing one of each of some lists, in turn: the first of the first list with each
 * way of choosing from the rest, then the second of it, and so on.
 *
 * <p>Made a way at a time, as each is asked for, and never laid out whole: the ways are as many
 * as the lists' lengths multiply, and a search bounded by a figure takes only as many of them as
 * it can spend on. Laid out first, they would be work done before the figure was asked about,
 * which the figure never bounds.
 *
 * <p>The lists are fixed before the walk and none depends on what was chosen from another. That is
 * what lets a list with nothing in it be answered before anything is made: there is then no way
 * of choosing at all. No lists at all is one way, of choosing nothing.
 *
 * <p>Each way handed out is a value of its own, in the order of the lists.
 */
public final class EveryWayOfChoosing {

    private EveryWayOfChoosing() {
    }

    /** What is done with one way of choosing; whether to go on to the next. */
    @FunctionalInterface
    interface Visit<T> {
        boolean goOn(List<T> chosen);
    }

    /** The ways of choosing one of each of {@code lists}, each made when it is asked for. */
    public static <T> Iterable<List<T>> inTurn(List<? extends List<T>> lists) {
        for (List<T> list : lists) {
            if (list.isEmpty()) {
                return List.of();
            }
        }
        return () -> new Iterator<>() {
            /** Which of each list the next way chooses, or null where every way was made. */
            private int[] next = new int[lists.size()];

            @Override
            public boolean hasNext() {
                return next != null;
            }

            @Override
            public List<T> next() {
                if (next == null) {
                    throw new NoSuchElementException();
                }
                List<T> way = new ArrayList<>(lists.size());
                for (int at = 0; at < lists.size(); at++) {
                    way.add(lists.get(at).get(next[at]));
                }
                int at = lists.size() - 1;
                while (at >= 0 && next[at] + 1 == lists.get(at).size()) {
                    next[at] = 0;
                    at--;
                }
                if (at < 0) {
                    next = null;
                } else {
                    next[at]++;
                }
                return Collections.unmodifiableList(way);
            }
        };
    }

    /** {@code visit} handed each way of choosing one of each of {@code lists}, a unit of
     *  {@code tries} each, until it stops or no unit is left; every way is handed out where there
     *  is none. */
    static <T> DepthFirst.Walked each(List<? extends List<T>> lists, Tries tries,
                                      Visit<T> visit) {
        Iterator<List<T>> ways = inTurn(lists).iterator();
        while (ways.hasNext()) {
            if (!tries.spend()) {
                return DepthFirst.Walked.CUT_SHORT;
            }
            if (!visit.goOn(ways.next())) {
                return DepthFirst.Walked.TAKEN;
            }
        }
        return DepthFirst.Walked.EVERY_END_REACHED;
    }
}
