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
 * walked on its own: the looking is the groups' ways added up, and not every way of taking them
 * together.
 *
 * <p><b>Every way a row takes, or some of them and the figure that left the rest.</b> A row past
 * the choices is along one open way of each group at once, so the ways a row takes are every
 * combination of them. Those are handed on where the figure lets them all be, and then a row past
 * the choices is along one of them — which is what a reader concluding something of every row
 * from what holds along each of them needs. Where they are more, each open way of each group is
 * handed on once, beside the first open way of every other group: enough for each alternative to
 * be composed along, and never said to be every way a row takes ({@link Walked.Open#stoppedBy}).
 *
 * <p><b>A proof only from a group walked to the end.</b> Where every way of one group closes, no
 * row is past the choices, whatever the others hold — and the way that closed first, with what
 * closed it, says why. A group the figure stopped proves nothing, however many of its ways closed.
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
     * @param <R> why entries do not hold together, as the reader of the walk says it
     */
    interface Vocabulary<E, S, R> {

        /** The alternatives {@code entry} is one of, each as the entries it asks; null where it is
         *  no choice. */
        List<List<E>> alternatives(E entry);

        /** The positions whether {@code entry} holds beside others turns on. */
        Set<TermPath> positions(E entry);

        /** Nothing taken in. */
        S nothing();

        /** {@code so} with {@code entry} taken in, or why the two cannot hold together. */
        Step<S, R> with(S so, E entry);
    }

    /**
     * What taking one more entry in came to: what the entries hold together as, or why they do
     * not. The one judge of it, so that what a walk found closed is said in the words of what
     * closed it and is never worked out again by a reader with fewer of them.
     */
    sealed interface Step<S, R> {

        /** They hold together, as {@code so}. */
        record Held<S, R>(S so) implements Step<S, R> {}

        /** They do not, for {@code why}. */
        record Closed<S, R>(R why) implements Step<S, R> {}
    }

    /**
     * One way some row may take: the entries it asks, with each choice the walk chose replaced by
     * the entries of the alternative taken.
     *
     * <p>Two kinds, and no list of entries common to both, so that a reader composing along a way
     * says which it has. A way that left a choice is not what the entries whole ask: a row along
     * the entries it chose has been asked none of what the choice asks.
     */
    sealed interface Way<E> {

        /**
         * Every choice on it chosen.
         *
         * @param entries what the way asks, each choice replaced by its alternative's entries
         * @param choices each choice taken and the alternative it was taken as, where it stands
         *                and in the order the way holds them: the way's identity among the ways of
         *                the same entries, which {@code entries} does not say where two
         *                alternatives ask alike. Every one of them — two entries alike are two
         *                choices the walk made apart, as it walks them apart
         */
        record Chosen<E>(List<E> entries, List<Choice<E>> choices) implements Way<E> {

            public Chosen {
                entries = List.copyOf(entries);
                choices = List.copyOf(choices);
            }
        }

        /**
         * Some choices on it left as they stand: the figure stopped the walk before their group
         * found a way open, so nothing about them was looked at.
         *
         * @param chosen   what the way asks of the choices that were chosen and beside them
         * @param unchosen the choices left, in the order they were written; one or more
         */
        record LeftUnchosen<E>(List<E> chosen, List<E> unchosen) implements Way<E> {

            public LeftUnchosen {
                chosen = List.copyOf(chosen);
                unchosen = List.copyOf(unchosen);
                if (unchosen.isEmpty()) {
                    throw new IllegalArgumentException("a way that left a choice left one");
                }
            }
        }
    }

    /**
     * One choice a way made: the entry that was one of several things, and which of its
     * alternatives the way took.
     *
     * <p>The entry where it stood, which is what the walk chooses by: two entries alike standing
     * at two places are two choices, and each may be taken another way. What is said by them
     * together — that a row along the way meets both alternatives — is for a reader of the way to
     * say.
     */
    record Choice<E>(E entry, int alternative) {

        Choice {
            if (alternative < 0) {
                throw new IllegalArgumentException("an alternative is one of the entry's");
            }
        }
    }

    /** What the walk came to. */
    sealed interface Walked<E, R> {

        /**
         * No row is past the entries: every way of some group closes, or what is asked beside
         * the choices does.
         *
         * @param way the first way that closed, as the entries it asks with the choices it had not
         *            reached left out
         * @param why what closed it
         */
        record Closed<E, R>(List<E> way, R why) implements Walked<E, R> {

            public Closed {
                way = List.copyOf(way);
            }
        }

        /**
         * Ways some row may take.
         *
         * @param ways      one or more
         * @param stoppedBy null where every way a row takes is among {@code ways} — every
         *                  combination of the open alternatives — so that every row past the
         *                  entries is along one of them; otherwise the figure that left the rest
         *                  unlooked at or not handed on, and {@code ways} are only some of them.
         *                  Never null where some way left a choice unchosen
         */
        record Open<E, R>(List<Way<E>> ways, CompositionBudget stoppedBy)
                implements Walked<E, R> {

            public Open {
                ways = List.copyOf(ways);
                if (ways.isEmpty()) {
                    throw new IllegalArgumentException("ways left open are one or more");
                }
                if (stoppedBy == null
                        && ways.stream().anyMatch(Way.LeftUnchosen.class::isInstance)) {
                    throw new IllegalArgumentException(
                            "a choice is left unchosen only where a figure stopped the walk");
                }
            }

            /** Whether every way a row takes is among these. */
            public boolean everyWay() {
                return stoppedBy == null;
            }
        }

        /**
         * Nothing is said of the ways: the figure stopped the walk before any way was found open
         * or closed whole.
         *
         * @param stoppedBy the figure
         */
        record Stopped<E, R>(CompositionBudget stoppedBy) implements Walked<E, R> {

            public Stopped {
                if (stoppedBy == null) {
                    throw new IllegalArgumentException("a walk stopped is stopped by a figure");
                }
            }
        }
    }

    /**
     * The ways {@code entries} comes to, looking at as many alternatives as {@code looking} lets
     * and handing on as many ways as {@code handing} does.
     */
    static <E, S, R> Walked<E, R> walk(List<E> entries, Vocabulary<E, S, R> asked,
                                       CompositionBudget looking, CompositionBudget handing) {
        Vocabulary<E, S, R> vocabulary = new Once<>(asked);
        S base = vocabulary.nothing();
        List<E> choices = new ArrayList<>();
        for (E each : entries) {
            if (vocabulary.alternatives(each) != null) {
                choices.add(each);
                continue;
            }
            switch (vocabulary.with(base, each)) {
                case Step.Held<S, R>(S so) -> base = so;
                case Step.Closed<S, R>(R why) -> {
                    return new Walked.Closed<>(rebuilt(entries, vocabulary, Map.of(), null),
                            why);
                }
            }
        }
        if (choices.isEmpty()) {
            return new Walked.Open<>(List.of(new Way.Chosen<>(entries, List.of())), null);
        }
        int[] left = {looking.maximum()};
        CompositionBudget stoppedBy = null;
        List<List<Map<E, Integer>>> open = new ArrayList<>();
        for (List<E> group : groups(choices, vocabulary)) {
            Group<E, S, R> walked = new Group<>(vocabulary, looking, handing, left);
            walked.from(new ArrayDeque<>(group), new IdentityHashMap<>(), base);
            if (walked.open.isEmpty() && walked.stoppedBy == null) {
                return new Walked.Closed<>(rebuilt(entries, vocabulary, walked.firstClosed, null),
                        walked.firstWhy);
            }
            if (walked.stoppedBy != null && stoppedBy == null) {
                stoppedBy = walked.stoppedBy;
            }
            // A group the figure stopped before it found a way open is one whose choices go
            // unchosen: the ways the groups before it found are handed on with them left as they
            // stand, and the figure says so.
            if (!walked.open.isEmpty()) {
                open.add(walked.open);
            }
        }
        if (open.isEmpty()) {
            return new Walked.Stopped<>(stoppedBy);
        }
        List<Map<E, Integer>> handedOn;
        if (stoppedBy == null && noMoreThan(handing.maximum(), open)) {
            handedOn = everyCombination(open);
        } else {
            handedOn = eachOnce(open);
            stoppedBy = stoppedBy == null ? handing : stoppedBy;
        }
        List<Way<E>> ways = new ArrayList<>();
        for (Map<E, Integer> chosen : handedOn) {
            if (ways.size() == handing.maximum()) {
                break;
            }
            List<E> unchosen = new ArrayList<>();
            List<Choice<E>> made = new ArrayList<>();
            List<E> taken = rebuilt(entries, vocabulary, chosen, unchosen, made);
            ways.add(unchosen.isEmpty() ? new Way.Chosen<>(taken, made)
                    : new Way.LeftUnchosen<>(taken, unchosen));
        }
        return new Walked.Open<>(ways, stoppedBy);
    }

    /**
     * One of each of {@code parts} taken together: every combination where they are no more than
     * {@code most}, and otherwise each of each part once beside the first of every other part.
     *
     * @param ways     every combination, the first part's turning slowest; or the first of every
     *                 part, and then each part's second beside the others' firsts before any
     *                 part's third, and no more than the figure — so that where it stops, no part
     *                 was passed over for another's
     * @param everyWay whether {@code ways} is every combination
     */
    record Taken<T>(List<List<T>> ways, boolean everyWay) {

        Taken {
            ways = ways.stream().map(List::copyOf).toList();
        }
    }

    /** {@code parts}, each one or more, taken together as {@link Taken} says, by {@code most}. */
    static <T> Taken<T> ofEachPart(List<List<T>> parts, int most) {
        long every = 1;
        for (List<T> part : parts) {
            every = Math.min(every * part.size(), most + 1L);
        }
        if (every <= most) {
            List<List<T>> out = new ArrayList<>();
            out.add(List.of());
            for (List<T> part : parts) {
                List<List<T>> wider = new ArrayList<>();
                for (List<T> before : out) {
                    for (T one : part) {
                        List<T> with = new ArrayList<>(before);
                        with.add(one);
                        wider.add(with);
                    }
                }
                out = wider;
            }
            return new Taken<>(out, true);
        }
        List<T> firsts = parts.stream().map(List::getFirst).toList();
        List<List<T>> out = new ArrayList<>();
        out.add(firsts);
        int longest = parts.stream().mapToInt(List::size).max().orElse(1);
        for (int way = 1; way < longest; way++) {
            for (int part = 0; part < parts.size(); part++) {
                if (out.size() == most) {
                    return new Taken<>(out, false);
                }
                if (way < parts.get(part).size()) {
                    List<T> one = new ArrayList<>(firsts);
                    one.set(part, parts.get(part).get(way));
                    out.add(one);
                }
            }
        }
        return new Taken<>(out, false);
    }

    /** Whether the combinations of one open way of each group are no more than {@code most}. */
    private static <E> boolean noMoreThan(int most, List<List<Map<E, Integer>>> open) {
        long out = 1;
        for (List<Map<E, Integer>> group : open) {
            out *= group.size();
            if (out > most) {
                return false;
            }
        }
        return true;
    }

    /** Every combination of one open way of each group, the first group's ways turning
     *  slowest. */
    private static <E> List<Map<E, Integer>> everyCombination(
            List<List<Map<E, Integer>>> open) {
        List<Map<E, Integer>> out = new ArrayList<>();
        out.add(new IdentityHashMap<>());
        for (List<Map<E, Integer>> group : open) {
            List<Map<E, Integer>> wider = new ArrayList<>();
            for (Map<E, Integer> before : out) {
                for (Map<E, Integer> way : group) {
                    Map<E, Integer> both = new IdentityHashMap<>(before);
                    both.putAll(way);
                    wider.add(both);
                }
            }
            out = wider;
        }
        return out;
    }

    /**
     * Every open way of each group once, beside the first open way of every other group, the
     * first of all of them first.
     */
    private static <E> List<Map<E, Integer>> eachOnce(List<List<Map<E, Integer>>> open) {
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

    /**
     * {@code entries} with each choice {@code chosen} names replaced where it stands by the
     * entries of its alternative, and each it does not name left out — and added to
     * {@code unchosen}, where that is given.
     */
    private static <E, S, R> List<E> rebuilt(List<E> entries, Vocabulary<E, S, R> vocabulary,
                                             Map<E, Integer> chosen, List<E> unchosen) {
        return rebuilt(entries, vocabulary, chosen, unchosen, null);
    }

    /** The same, and each choice taken, where it stands, added to {@code taken} where that is
     *  given. */
    private static <E, S, R> List<E> rebuilt(List<E> entries, Vocabulary<E, S, R> vocabulary,
                                             Map<E, Integer> chosen, List<E> unchosen,
                                             List<Choice<E>> taken) {
        List<E> out = new ArrayList<>();
        for (E each : entries) {
            List<List<E>> alternatives = vocabulary.alternatives(each);
            if (alternatives == null) {
                out.add(each);
                continue;
            }
            Integer which = chosen.get(each);
            if (which != null) {
                if (taken != null) {
                    taken.add(new Choice<>(each, which));
                }
                out.addAll(rebuilt(alternatives.get(which), vocabulary, chosen, unchosen, taken));
            } else if (unchosen != null) {
                unchosen.add(each);
            }
        }
        return out;
    }

    /**
     * {@code choices} parted into groups no two of which turn on a position in common, each in the
     * order the choices came — a position counting as in common with any position above or below
     * it, since what is asked of a value is asked of what is inside it.
     */
    private static <E, S, R> List<List<E>> groups(List<E> choices,
                                                  Vocabulary<E, S, R> vocabulary) {
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
    private static <E, S, R> void allPositions(E entry, Vocabulary<E, S, R> vocabulary,
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
     * {@code asked}, answering each entry's alternatives once.
     *
     * <p>A choice is filed under the entry it is, by identity, from the walk to the ways handed
     * on: a choice nested in an alternative is an entry of that alternative, and a vocabulary
     * making the alternatives afresh each time it is asked hands back another entry equal to it,
     * under which nothing was filed — so the nested choice would be left out of the way. Answered
     * once, the alternatives are the one tree the walk and the ways are both read off.
     */
    private static final class Once<E, S, R> implements Vocabulary<E, S, R> {

        private final Vocabulary<E, S, R> asked;
        private final Map<E, List<List<E>>> alternatives = new IdentityHashMap<>();

        Once(Vocabulary<E, S, R> asked) {
            this.asked = asked;
        }

        @Override
        public List<List<E>> alternatives(E entry) {
            if (alternatives.containsKey(entry)) {
                return alternatives.get(entry);
            }
            List<List<E>> out = asked.alternatives(entry);
            alternatives.put(entry, out);
            return out;
        }

        @Override
        public Set<TermPath> positions(E entry) {
            return asked.positions(entry);
        }

        @Override
        public S nothing() {
            return asked.nothing();
        }

        @Override
        public Step<S, R> with(S so, E entry) {
            return asked.with(so, entry);
        }
    }

    /**
     * The walk over one group: each choice in turn, each of its alternatives taken in beside what
     * was taken before it, a nested choice chosen where it stands.
     */
    private static final class Group<E, S, R> {

        private final Vocabulary<E, S, R> vocabulary;
        private final CompositionBudget looking;
        private final CompositionBudget handing;
        private final int[] left;
        private final List<Map<E, Integer>> open = new ArrayList<>();
        /** The first way that closed, and what closed it. */
        private Map<E, Integer> firstClosed;
        private R firstWhy;
        /** The figure that stopped this group's walk, or null where it was walked to the end. */
        private CompositionBudget stoppedBy;

        Group(Vocabulary<E, S, R> vocabulary, CompositionBudget looking,
              CompositionBudget handing, int[] left) {
            this.vocabulary = vocabulary;
            this.looking = looking;
            this.handing = handing;
            this.left = left;
        }

        /** @return whether the walk may go on */
        boolean from(Deque<E> pending, Map<E, Integer> chosen, S so) {
            E next = pending.pollFirst();
            while (next != null && chosen.containsKey(next)) {
                next = pending.pollFirst();
            }
            if (next == null) {
                if (open.size() == handing.maximum()) {
                    stoppedBy = handing;
                    return false;
                }
                open.add(new IdentityHashMap<>(chosen));
                return true;
            }
            List<List<E>> alternatives = vocabulary.alternatives(next);
            for (int which = 0; which < alternatives.size(); which++) {
                if (left[0] == 0) {
                    stoppedBy = looking;
                    return false;
                }
                left[0]--;
                chosen.put(next, which);
                S here = so;
                R closedBy = null;
                Deque<E> after = new ArrayDeque<>(pending);
                List<E> nested = new ArrayList<>();
                for (E each : alternatives.get(which)) {
                    if (vocabulary.alternatives(each) != null) {
                        nested.add(each);
                    } else if (closedBy == null) {
                        switch (vocabulary.with(here, each)) {
                            case Step.Held<S, R>(S held) -> here = held;
                            case Step.Closed<S, R>(R why) -> closedBy = why;
                        }
                    }
                }
                if (closedBy != null) {
                    if (firstClosed == null) {
                        firstClosed = new IdentityHashMap<>(chosen);
                        firstWhy = closedBy;
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
