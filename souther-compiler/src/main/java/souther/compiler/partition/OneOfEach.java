package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The ways a list of things asked of a row comes to where some of them are one of several things:
 * one alternative of each taken in its place, and the ways along which nothing holds together left
 * out.
 *
 * <p><b>Choices that turn on no position in common are chosen apart.</b> Whether an alternative of
 * one holds together with what is asked beside it turns on the positions it asks about, so two
 * choices asking about none in common never close each other, and what closes one closes it beside
 * any alternative of the other. The choices are parted into such groups first, and each group is
 * walked on its own: the walk over a group is a product of its choices, and the walk over the whole
 * is the sum of those and not their product.
 *
 * <p><b>And the ways handed on are no product either.</b> A row along one way of each group is a
 * row of the whole, so every open way of every group is handed on once, beside the first open way
 * of every other group — enough for each alternative to be composed along, and as many as the
 * groups' ways added up.
 *
 * <p><b>A proof only from a group walked to the end.</b> Where every way of one group closes, no
 * row is past the choices, whatever the others hold — and the way that closed first says why. A
 * group the figure stopped proves nothing, however many of its ways closed.
 *
 * <p>Nested choices — an alternative asking one of several things itself — are chosen where they
 * stand, in the group of the choice they are inside.
 */
final class OneOfEach {

    private OneOfEach() {
    }

    /**
     * What the walk needs to know of an entry, and how what is taken in so far stands.
     *
     * @param <E> an entry of what is asked
     * @param <S> what the entries taken in so far come to, as far as whether they hold together
     */
    interface Vocabulary<E, S> {

        /** The alternatives {@code entry} is one of, each as the entries it asks; null where it is
         *  no choice. */
        List<List<E>> alternatives(E entry);

        /** The positions whether {@code entry} holds beside others turns on. */
        Set<TermPath> positions(E entry);

        /** Nothing taken in. */
        S nothing();

        /** {@code so} with {@code entry} taken in, or null where the two cannot hold together. */
        S with(S so, E entry);
    }

    /**
     * What the walk came to.
     *
     * @param ways     each way handed on, as the entries it asks with every choice in it replaced
     *                 by the entries of the alternative taken; empty where no way is open
     * @param closedBy where the choices of some group were all closed, the first way of it that
     *                 closed, with the choices it had not reached left out — what says why no row
     *                 is past the whole; null where no group was walked to the end and found closed
     * @param stoppedBy the figure that stopped the walk or the handing on, null where every way
     *                  was looked at and every open way is handed on
     */
    record Walked<E>(List<List<E>> ways, List<E> closedBy, CompositionBudget stoppedBy) {

        Walked {
            ways = ways.stream().map(List::copyOf).toList();
            closedBy = closedBy == null ? null : List.copyOf(closedBy);
        }

        /** Whether every way was looked at and every open one is handed on. */
        boolean everyWay() {
            return stoppedBy == null;
        }
    }

    /**
     * The ways {@code entries} comes to, looking at as many alternatives as {@code looking} lets
     * and handing on as many ways as {@code handing} does.
     */
    static <E, S> Walked<E> walk(List<E> entries, Vocabulary<E, S> vocabulary,
                                 CompositionBudget looking, CompositionBudget handing) {
        S base = vocabulary.nothing();
        List<E> choices = new ArrayList<>();
        for (E each : entries) {
            if (vocabulary.alternatives(each) != null) {
                choices.add(each);
                continue;
            }
            base = vocabulary.with(base, each);
            if (base == null) {
                return new Walked<>(List.of(), rebuilt(entries, vocabulary, Map.of()), null);
            }
        }
        if (choices.isEmpty()) {
            return new Walked<>(List.of(entries), null, null);
        }
        int[] left = {looking.maximum()};
        CompositionBudget stoppedBy = null;
        List<List<Map<E, Integer>>> open = new ArrayList<>();
        for (List<E> group : groups(choices, vocabulary)) {
            Group<E, S> walked = new Group<>(vocabulary, handing.maximum(), left);
            walked.from(new ArrayDeque<>(group), new IdentityHashMap<>(), base);
            if (walked.open.isEmpty() && walked.whole) {
                return new Walked<>(List.of(),
                        rebuilt(entries, vocabulary, walked.firstClosed), null);
            }
            if (!walked.whole) {
                stoppedBy = left[0] == 0 ? looking : handing;
            }
            if (walked.open.isEmpty()) {
                return new Walked<>(List.of(), null, stoppedBy);
            }
            open.add(walked.open);
        }
        List<List<E>> ways = new ArrayList<>();
        for (Map<E, Integer> chosen : handedOn(open)) {
            if (ways.size() == handing.maximum()) {
                stoppedBy = stoppedBy == null ? handing : stoppedBy;
                break;
            }
            ways.add(rebuilt(entries, vocabulary, chosen));
        }
        return new Walked<>(ways, null, stoppedBy);
    }

    /**
     * Every open way of each group once, beside the first open way of every other group, the
     * first of all of them first.
     */
    private static <E> List<Map<E, Integer>> handedOn(List<List<Map<E, Integer>>> open) {
        List<Map<E, Integer>> out = new ArrayList<>();
        out.add(together(open, -1, 0));
        for (int group = 0; group < open.size(); group++) {
            for (int way = 1; way < open.get(group).size(); way++) {
                out.add(together(open, group, way));
            }
        }
        return out;
    }

    /** The first open way of every group, but the {@code way}-th of {@code group}. */
    private static <E> Map<E, Integer> together(List<List<Map<E, Integer>>> open, int group,
                                                int way) {
        Map<E, Integer> out = new IdentityHashMap<>();
        for (int each = 0; each < open.size(); each++) {
            out.putAll(open.get(each).get(each == group ? way : 0));
        }
        return out;
    }

    /** {@code entries} with each choice {@code chosen} names replaced where it stands by the
     *  entries of its alternative, and each it does not name left out. */
    private static <E, S> List<E> rebuilt(List<E> entries, Vocabulary<E, S> vocabulary,
                                          Map<E, Integer> chosen) {
        List<E> out = new ArrayList<>();
        for (E each : entries) {
            List<List<E>> alternatives = vocabulary.alternatives(each);
            if (alternatives == null) {
                out.add(each);
                continue;
            }
            Integer taken = chosen.get(each);
            if (taken != null) {
                out.addAll(rebuilt(alternatives.get(taken), vocabulary, chosen));
            }
        }
        return out;
    }

    /**
     * {@code choices} parted into groups no two of which turn on a position in common, each in the
     * order the choices came — a position counting as in common with any position above or below
     * it, since what is asked of a value is asked of what is inside it.
     */
    private static <E, S> List<List<E>> groups(List<E> choices, Vocabulary<E, S> vocabulary) {
        List<Set<TermPath>> turnsOn = new ArrayList<>();
        for (E each : choices) {
            Set<TermPath> positions = new LinkedHashSet<>();
            allPositions(each, vocabulary, positions);
            turnsOn.add(positions);
        }
        int[] groupOf = new int[choices.size()];
        for (int each = 0; each < choices.size(); each++) {
            groupOf[each] = each;
        }
        for (int one = 0; one < choices.size(); one++) {
            for (int other = one + 1; other < choices.size(); other++) {
                if (sharesAPosition(turnsOn.get(one), turnsOn.get(other))) {
                    int from = root(groupOf, other);
                    int to = root(groupOf, one);
                    if (from != to) {
                        groupOf[Math.max(from, to)] = Math.min(from, to);
                    }
                }
            }
        }
        Map<Integer, List<E>> byRoot = new LinkedHashMap<>();
        for (int each = 0; each < choices.size(); each++) {
            byRoot.computeIfAbsent(root(groupOf, each), _ -> new ArrayList<>())
                    .add(choices.get(each));
        }
        return List.copyOf(byRoot.values());
    }

    private static int root(int[] groupOf, int at) {
        int here = at;
        while (groupOf[here] != here) {
            here = groupOf[here];
        }
        return here;
    }

    /** Every position {@code entry} turns on, inside its alternatives as well. */
    private static <E, S> void allPositions(E entry, Vocabulary<E, S> vocabulary,
                                            Set<TermPath> into) {
        List<List<E>> alternatives = vocabulary.alternatives(entry);
        if (alternatives == null) {
            into.addAll(vocabulary.positions(entry));
            return;
        }
        for (List<E> alternative : alternatives) {
            for (E each : alternative) {
                allPositions(each, vocabulary, into);
            }
        }
    }

    private static boolean sharesAPosition(Set<TermPath> one, Set<TermPath> other) {
        for (TermPath a : one) {
            for (TermPath b : other) {
                if (a.isAtOrUnder(b) || b.isAtOrUnder(a)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The walk over one group: each choice in turn, each of its alternatives taken in beside what
     * was taken before it, a nested choice chosen where it stands.
     */
    private static final class Group<E, S> {

        private final Vocabulary<E, S> vocabulary;
        private final int most;
        private final int[] left;
        private final List<Map<E, Integer>> open = new ArrayList<>();
        private Map<E, Integer> firstClosed;
        private boolean whole = true;

        Group(Vocabulary<E, S> vocabulary, int most, int[] left) {
            this.vocabulary = vocabulary;
            this.most = most;
            this.left = left;
        }

        /** @return whether the walk may go on */
        boolean from(Deque<E> pending, Map<E, Integer> chosen, S so) {
            E next = pending.pollFirst();
            while (next != null && chosen.containsKey(next)) {
                next = pending.pollFirst();
            }
            if (next == null) {
                if (open.size() == most) {
                    whole = false;
                    return false;
                }
                open.add(new IdentityHashMap<>(chosen));
                return true;
            }
            List<List<E>> alternatives = vocabulary.alternatives(next);
            for (int which = 0; which < alternatives.size(); which++) {
                if (left[0] == 0) {
                    whole = false;
                    return false;
                }
                left[0]--;
                chosen.put(next, which);
                S here = so;
                Deque<E> after = new ArrayDeque<>(pending);
                List<E> nested = new ArrayList<>();
                for (E each : alternatives.get(which)) {
                    if (vocabulary.alternatives(each) != null) {
                        nested.add(each);
                    } else if (here != null) {
                        here = vocabulary.with(here, each);
                    }
                }
                if (here == null) {
                    if (firstClosed == null) {
                        firstClosed = new IdentityHashMap<>(chosen);
                    }
                } else {
                    for (int each = nested.size() - 1; each >= 0; each--) {
                        after.addFirst(nested.get(each));
                    }
                    if (!from(after, chosen, here)) {
                        chosen.remove(next);
                        return false;
                    }
                }
                chosen.remove(next);
            }
            return true;
        }
    }
}
