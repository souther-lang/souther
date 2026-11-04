package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
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
 * from what holds along each of them needs. Where they are more, a way is handed on for each
 * alternative of each choice, beside the first open way of every other group, in the order of
 * {@link AlternativeOrder}: enough for each alternative to be composed along as far as the figure
 * lets, and never said to be every way a row takes ({@link Walked.Open#stoppedBy}).
 *
 * <p><b>A proof only from a group walked to the end.</b> Where every way of one group closes, no
 * row is past the choices, whatever the others hold — and the way that closed first, with what
 * closed it, says why. A group the figure stopped proves nothing, however many of its ways closed.
 *
 * <p>Nested choices — an alternative asking one of several things itself — are chosen where they
 * stand, in the group of the choice they are inside.
 *
 * <p><b>A choice is the place it stands at.</b> An entry is a value, and a value made again may be
 * handed out as the one made before ({@link OnTheWay.OneOf#of}), so which object an entry is says
 * nothing of where it stands. One entry standing at two places — two alternatives holding the same
 * nested choice, or the same choice asked twice along a way — is two choices, each taken its own
 * way, as two entries alike are ({@link Choice}). The walk files what it chose under the place,
 * never under the entry.
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

        /**
         * Whether {@link #with} does nothing but answer: asking it spends nothing that a later
         * answer turns on. A walk looking for the way of one alternative asks such a vocabulary
         * ahead of where it stands, whether what that way has to take in holds beside what is
         * taken so far. Of a vocabulary whose answers spend something — steps or conditions it
         * takes in, shared with what asks it next — the walk asks only what it takes.
         */
        default boolean answersAlone() {
            return false;
        }
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
         *                alternatives ask alike. Every one of them — two entries alike, or one entry
         *                at two places, are two choices the walk made apart, as it walks them apart
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
     * at two places, or one entry standing at two, are two choices, and each may be taken another
     * way. What is said by them together — that a row along the way meets both alternatives — is
     * for a reader of the way to say.
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
        List<Place<E>> places = Place.of(entries, vocabulary, null, 0);
        S base = vocabulary.nothing();
        List<Place<E>> choices = new ArrayList<>();
        for (int at = 0; at < entries.size(); at++) {
            if (places.get(at) != null) {
                choices.add(places.get(at));
                continue;
            }
            switch (vocabulary.with(base, entries.get(at))) {
                case Step.Held<S, R>(S so) -> base = so;
                case Step.Closed<S, R>(R why) -> {
                    return new Walked.Closed<>(rebuilt(entries, places, Map.of(), null, null),
                            why);
                }
            }
        }
        if (choices.isEmpty()) {
            return new Walked.Open<>(List.of(new Way.Chosen<>(entries, List.of())), null);
        }
        int[] left = {looking.maximum()};
        CompositionBudget stoppedBy = null;
        List<List<Map<Place<E>, Integer>>> open = new ArrayList<>();
        List<List<Place<E>>> groups = groups(choices, vocabulary);
        List<Group<E, S, R>> walkedGroups = new ArrayList<>();
        for (List<Place<E>> group : groups) {
            Group<E, S, R> walked = new Group<>(vocabulary, looking, handing, left);
            walked.from(new ArrayDeque<>(group), new HashMap<>(), base);
            if (walked.open.isEmpty() && walked.stoppedBy == null) {
                return new Walked.Closed<>(
                        rebuilt(entries, places, walked.firstClosed, null, null),
                        walked.firstWhy);
            }
            walkedGroups.add(walked);
        }
        for (Group<E, S, R> walked : walkedGroups) {
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
        List<Map<Place<E>, Integer>> handedOn;
        if (stoppedBy == null && noMoreThan(handing.maximum(), open)) {
            handedOn = everyCombination(open);
        } else {
            handedOn = fairly(groups, walkedGroups, base, handing.maximum());
            stoppedBy = stoppedBy == null ? handing : stoppedBy;
        }
        List<Way<E>> ways = new ArrayList<>();
        for (Map<Place<E>, Integer> chosen : handedOn) {
            if (ways.size() == handing.maximum()) {
                break;
            }
            List<E> unchosen = new ArrayList<>();
            List<Choice<E>> made = new ArrayList<>();
            List<E> taken = rebuilt(entries, places, chosen, unchosen, made);
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
        AlternativeOrder<Integer> order = new AlternativeOrder<>();
        for (int part = 0; part < parts.size(); part++) {
            order.met(part, parts.get(part).size());
        }
        for (AlternativeOrder.Target<Integer> target = order.next();
                target != null && out.size() < most; target = order.next()) {
            if (target.alternative() > 0) {
                List<T> one = new ArrayList<>(firsts);
                one.set(target.choice(), parts.get(target.choice()).get(target.alternative()));
                out.add(one);
            }
        }
        return new Taken<>(out, false);
    }

    /** Whether the combinations of one open way of each group are no more than {@code most}. */
    private static <E> boolean noMoreThan(int most, List<List<Map<Place<E>, Integer>>> open) {
        long out = 1;
        for (List<Map<Place<E>, Integer>> group : open) {
            out *= group.size();
            if (out > most) {
                return false;
            }
        }
        return true;
    }

    /** Every combination of one open way of each group, the first group's ways turning
     *  slowest. */
    private static <E> List<Map<Place<E>, Integer>> everyCombination(
            List<List<Map<Place<E>, Integer>>> open) {
        List<Map<Place<E>, Integer>> out = new ArrayList<>();
        out.add(new HashMap<>());
        for (List<Map<Place<E>, Integer>> group : open) {
            List<Map<Place<E>, Integer>> wider = new ArrayList<>();
            for (Map<Place<E>, Integer> before : out) {
                for (Map<Place<E>, Integer> way : group) {
                    Map<Place<E>, Integer> both = new HashMap<>(before);
                    both.putAll(way);
                    wider.add(both);
                }
            }
            out = wider;
        }
        return out;
    }

    /** A choice and the group of the walk that came to it. */
    private record Looked<E>(int group, Place<E> choice) {}

    /**
     * The ways handed on where those of the groups together are more than {@code most}, or any
     * group stopped at a figure: the first way of every group, then a way for each alternative of
     * each choice the groups came to that no way before takes, in the order of
     * {@link AlternativeOrder}, each beside the first way of every other group — and, once every
     * alternative has its way, the ways the groups found after their first, a way of each group
     * at a time.
     *
     * <p>Whether a way before takes an alternative is asked of the condition, the entry as what it
     * is: a choice equal to one at another place has its alternative taken by a way taking it at
     * either. A reader composes along an alternative of a condition, which it reads off the ways
     * by condition ({@link HeldOutcome#byCondition}), so a way owed again for the second place
     * would spend the figure on an alternative already composed along, and leave another
     * condition's without one.
     *
     * <p>A group that did not go to its end is looked in for the way of an alternative it has
     * none for ({@code Group.wayTaking}), with what the walks of all the groups left of the
     * looking. Every group has been walked as far as it was going to be before any of them is
     * asked for another way, so that the alternatives of one are never bought with the looking of
     * another.
     */
    private static <E, S, R> List<Map<Place<E>, Integer>> fairly(
            List<List<Place<E>>> groups, List<Group<E, S, R>> walked, S base, int most) {
        List<Integer> live = new ArrayList<>();
        for (int at = 0; at < walked.size(); at++) {
            if (!walked.get(at).open.isEmpty()) {
                live.add(at);
            }
        }
        List<Map<Place<E>, Integer>> out = new ArrayList<>();
        Map<Place<E>, Integer> firsts = firstsOf(walked, live);
        out.add(firsts);
        Map<E, Set<Integer>> covered = new HashMap<>();
        noteCovered(covered, firsts);
        AlternativeOrder<Looked<E>> order = new AlternativeOrder<>();
        for (int at : live) {
            for (Place<E> choice : walked.get(at).met) {
                order.met(new Looked<>(at, choice), choice.alternatives.size());
            }
        }
        for (AlternativeOrder.Target<Looked<E>> target = order.next();
                target != null && out.size() < most; target = order.next()) {
            Place<E> choice = target.choice().choice();
            if (covered.getOrDefault(choice.entry, Set.of()).contains(target.alternative())) {
                continue;
            }
            int at = target.choice().group();
            List<Place<E>> newlyMet = new ArrayList<>();
            Map<Place<E>, Integer> way = walked.get(at).wayTaking(choice, target.alternative(),
                    groups.get(at), base, newlyMet);
            for (Place<E> each : newlyMet) {
                order.met(new Looked<>(at, each), each.alternatives.size());
            }
            if (way == null) {
                continue;
            }
            noteCovered(covered, way);
            out.add(together(walked, live, at, way));
        }
        for (int number = 1; out.size() < most; number++) {
            boolean more = false;
            for (int at : live) {
                List<Map<Place<E>, Integer>> found = walked.get(at).open;
                if (number < found.size()) {
                    more = true;
                    Map<Place<E>, Integer> one = together(walked, live, at, found.get(number));
                    if (out.size() < most && !out.contains(one)) {
                        out.add(one);
                    }
                }
            }
            if (!more) {
                break;
            }
        }
        return out;
    }

    /** The first way of every group in {@code live}. */
    private static <E, S, R> Map<Place<E>, Integer> firstsOf(List<Group<E, S, R>> walked,
                                                             List<Integer> live) {
        Map<Place<E>, Integer> out = new HashMap<>();
        for (int at : live) {
            out.putAll(walked.get(at).open.getFirst());
        }
        return out;
    }

    /** The first way of every group in {@code live}, but {@code way} for {@code group}. */
    private static <E, S, R> Map<Place<E>, Integer> together(List<Group<E, S, R>> walked,
                                                             List<Integer> live, int group,
                                                             Map<Place<E>, Integer> way) {
        Map<Place<E>, Integer> out = new HashMap<>();
        for (int at : live) {
            out.putAll(at == group ? way : walked.get(at).open.getFirst());
        }
        return out;
    }

    private static <E> void noteCovered(Map<E, Set<Integer>> covered,
                                        Map<Place<E>, Integer> way) {
        way.forEach((choice, which) ->
                covered.computeIfAbsent(choice.entry, _ -> new HashSet<>()).add(which));
    }

    /**
     * {@code entries}, standing at {@code places}, with each choice {@code chosen} names replaced
     * where it stands by the entries of its alternative, and each it does not name left out — and
     * added to {@code unchosen}, where that is given — and each choice taken, where it stands,
     * added to {@code taken} where that is given.
     */
    private static <E> List<E> rebuilt(List<E> entries, List<Place<E>> places,
                                       Map<Place<E>, Integer> chosen, List<E> unchosen,
                                       List<Choice<E>> taken) {
        List<E> out = new ArrayList<>();
        for (int at = 0; at < entries.size(); at++) {
            Place<E> place = places.get(at);
            if (place == null) {
                out.add(entries.get(at));
                continue;
            }
            Integer which = chosen.get(place);
            if (which != null) {
                if (taken != null) {
                    taken.add(new Choice<>(place.entry, which));
                }
                out.addAll(rebuilt(place.alternatives.get(which), place.inside(which), chosen,
                        unchosen, taken));
            } else if (unchosen != null) {
                unchosen.add(place.entry);
            }
        }
        return out;
    }

    /**
     * {@code choices} parted into groups no two of which turn on a position in common, each in the
     * order the choices came — a position counting as in common with any it bears on
     * ({@link TermPath#bearsOn}): what is asked of a value is asked of what is inside it, and of
     * the value narrowed to a case.
     */
    private static <E, S, R> List<List<Place<E>>> groups(List<Place<E>> choices,
                                                         Vocabulary<E, S, R> vocabulary) {
        List<Set<TermPath>> turnsOn = new ArrayList<>();
        for (Place<E> each : choices) {
            Set<TermPath> positions = new LinkedHashSet<>();
            allPositions(each.entry, vocabulary, positions);
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
        Map<Integer, List<Place<E>>> byRoot = new LinkedHashMap<>();
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
                if (a.bearsOn(b)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * {@code asked}, answering each entry's alternatives once.
     *
     * <p>A vocabulary may make the alternatives afresh each time it is asked, as another list of
     * entries equal to the last. Answered once, every place an entry stands at reads its
     * alternatives off the one answer, and an entry met again costs nothing to ask.
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

        @Override
        public boolean answersAlone() {
            return asked.answersAlone();
        }
    }

    /**
     * A choice where it stands: the entry, and the alternative of the choice it stands in, or
     * none for one written among the entries walked. What the walk files a choice under, equal
     * only to itself, so that one entry at two places is two of these.
     *
     * <p>The places inside an alternative are made when it is first taken and are the same every
     * time after, so that the ways of one walk, and the looking for an alternative's way after
     * it, name the one place.
     */
    private static final class Place<E> {

        private final E entry;
        private final List<List<E>> alternatives;
        private final Vocabulary<E, ?, ?> vocabulary;
        /** The choice this stands in an alternative of, or null for one among the entries. */
        private final Place<E> in;
        private final int inAlternative;
        private final List<List<Place<E>>> inside;

        private Place(E entry, List<List<E>> alternatives, Vocabulary<E, ?, ?> vocabulary,
                      Place<E> in, int inAlternative) {
            this.entry = entry;
            this.alternatives = alternatives;
            this.vocabulary = vocabulary;
            this.in = in;
            this.inAlternative = inAlternative;
            this.inside = new ArrayList<>(alternatives.size());
            for (int each = 0; each < alternatives.size(); each++) {
                inside.add(null);
            }
        }

        /** The place of each of {@code entries}, standing in alternative {@code inAlternative} of
         *  {@code in}: null for an entry that is no choice. */
        static <E> List<Place<E>> of(List<E> entries, Vocabulary<E, ?, ?> vocabulary,
                                     Place<E> in, int inAlternative) {
            List<Place<E>> out = new ArrayList<>(entries.size());
            for (E each : entries) {
                List<List<E>> alternatives = vocabulary.alternatives(each);
                out.add(alternatives == null ? null
                        : new Place<>(each, alternatives, vocabulary, in, inAlternative));
            }
            return out;
        }

        /** The place of each entry of alternative {@code which}, null for one that is no
         *  choice. */
        List<Place<E>> inside(int which) {
            List<Place<E>> out = inside.get(which);
            if (out == null) {
                out = of(alternatives.get(which), vocabulary, this, which);
                inside.set(which, out);
            }
            return out;
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
        /** The alternatives a way must take for this walk to hand it on: the one it looks for the
         *  way of, and those of the choices holding it. Empty for a walk that takes any way. */
        private final Map<Place<E>, Integer> pinned;
        /** What each alternative this walk is held to asks that is no choice, by the place
         *  whose alternative it is: what a way it hands on takes in, whatever else it chooses. */
        private final Map<Place<E>, List<E>> held = new LinkedHashMap<>();
        private final List<Map<Place<E>, Integer>> open = new ArrayList<>();
        /** Every choice the walk came to, in the order it came to them. */
        private final List<Place<E>> met = new ArrayList<>();
        private final Set<Place<E>> metSet = new HashSet<>();
        /** The first way that closed, and what closed it. */
        private Map<Place<E>, Integer> firstClosed;
        private R firstWhy;
        /** The figure that stopped this group's walk, or null where it was walked to the end. */
        private CompositionBudget stoppedBy;

        Group(Vocabulary<E, S, R> vocabulary, CompositionBudget looking,
              CompositionBudget handing, int[] left) {
            this(vocabulary, looking, handing, left, Map.of());
        }

        private Group(Vocabulary<E, S, R> vocabulary, CompositionBudget looking,
                      CompositionBudget handing, int[] left, Map<Place<E>, Integer> pinned) {
            this.vocabulary = vocabulary;
            this.looking = looking;
            this.handing = handing;
            this.left = left;
            this.pinned = pinned;
            pinned.forEach((place, which) -> {
                List<E> asks = place.alternatives.get(which);
                List<Place<E>> standing = place.inside(which);
                List<E> takes = new ArrayList<>();
                for (int at = 0; at < asks.size(); at++) {
                    if (standing.get(at) == null) {
                        takes.add(asks.get(at));
                    }
                }
                held.put(place, takes);
            });
        }

        /**
         * Whether no way past {@code chosen}, standing as {@code so}, takes what this walk is held
         * to: what the alternatives it is held to ask, of those not taken yet, does not hold
         * beside {@code so}. Asked only of a vocabulary that answers alone; of any other, never.
         *
         * <p>A way handed on takes every alternative it is held to, so it takes in what each of
         * them asks beside everything else it takes; where what they ask closes beside part of
         * that, no row is along the way, whatever comes after. So a walk held to an alternative
         * that closes beside what an early choice took finds it there, and not once for every
         * way of the choices between.
         */
        private boolean closesAhead(S so, Map<Place<E>, Integer> chosen) {
            if (held.isEmpty() || !vocabulary.answersAlone()) {
                return false;
            }
            S probe = so;
            for (Map.Entry<Place<E>, List<E>> each : held.entrySet()) {
                if (chosen.containsKey(each.getKey())) {
                    continue;
                }
                for (E entry : each.getValue()) {
                    switch (vocabulary.with(probe, entry)) {
                        case Step.Held<S, R>(S taken) -> probe = taken;
                        case Step.Closed<S, R> _ -> {
                            return true;
                        }
                    }
                }
            }
            return false;
        }

        /**
         * A way of this group that takes alternative {@code alternative} of {@code choice}, or null
         * where there is none to be had.
         *
         * <p>One this walk already found, if any does. Otherwise, where the walk stopped at a
         * figure and so did not find every way, the way is looked for with the walk held to the
         * alternative and to those of the choices holding it, and the first way open past them is
         * the way. A walk that went to its end has found every way, so what it did not find does
         * not exist; one that ran out of looking has nothing to look with.
         *
         * @param newlyMet the choices the search came to that this walk had not, added to
         */
        Map<Place<E>, Integer> wayTaking(Place<E> choice, int alternative, List<Place<E>> group,
                                         S base, List<Place<E>> newlyMet) {
            for (Map<Place<E>, Integer> each : open) {
                if (Integer.valueOf(alternative).equals(each.get(choice))) {
                    return each;
                }
            }
            if (stoppedBy == null || left[0] == 0) {
                return null;
            }
            Group<E, S, R> past = new Group<>(vocabulary, looking, handing, left,
                    holdingIt(choice, alternative));
            if (past.closesAhead(base, Map.of())) {
                return null;
            }
            past.from(new ArrayDeque<>(group), new HashMap<>(), base);
            for (Place<E> each : past.met) {
                if (metSet.add(each)) {
                    met.add(each);
                    newlyMet.add(each);
                }
            }
            return past.open.isEmpty() ? null : past.open.getFirst();
        }

        /** The alternative {@code which} of {@code choice}, with the alternatives of the choices
         *  it stands in that lead to it, from it outward. */
        private static <E> Map<Place<E>, Integer> holdingIt(Place<E> choice, int which) {
            Map<Place<E>, Integer> out = new LinkedHashMap<>();
            out.put(choice, which);
            for (Place<E> at = choice; at.in != null; at = at.in) {
                out.put(at.in, at.inAlternative);
            }
            return out;
        }

        /** Whether the way {@code chosen} takes every alternative this walk is held to. */
        private boolean takesWhatItIsHeldTo(Map<Place<E>, Integer> chosen) {
            for (Map.Entry<Place<E>, Integer> each : pinned.entrySet()) {
                if (!each.getValue().equals(chosen.get(each.getKey()))) {
                    return false;
                }
            }
            return true;
        }

        /** @return whether the walk may go on */
        boolean from(Deque<Place<E>> pending, Map<Place<E>, Integer> chosen, S so) {
            Place<E> next = pending.pollFirst();
            if (next == null) {
                if (!takesWhatItIsHeldTo(chosen)) {
                    return true;
                }
                if (open.size() == handing.maximum()) {
                    stoppedBy = handing;
                    return false;
                }
                open.add(new HashMap<>(chosen));
                // The way held to an alternative is the first open past it, and no more.
                return pinned.isEmpty();
            }
            if (metSet.add(next)) {
                met.add(next);
            }
            Integer held = pinned.get(next);
            for (int which = 0; which < next.alternatives.size(); which++) {
                if (held != null && held != which) {
                    continue;
                }
                if (left[0] == 0) {
                    stoppedBy = looking;
                    return false;
                }
                left[0]--;
                chosen.put(next, which);
                S here = so;
                R closedBy = null;
                Deque<Place<E>> after = new ArrayDeque<>(pending);
                List<Place<E>> nested = new ArrayList<>();
                List<E> asks = next.alternatives.get(which);
                List<Place<E>> standing = next.inside(which);
                for (int at = 0; at < asks.size(); at++) {
                    if (standing.get(at) != null) {
                        nested.add(standing.get(at));
                    } else if (closedBy == null) {
                        switch (vocabulary.with(here, asks.get(at))) {
                            case Step.Held<S, R>(S taken) -> here = taken;
                            case Step.Closed<S, R>(R why) -> closedBy = why;
                        }
                    }
                }
                if (closedBy != null) {
                    if (firstClosed == null) {
                        firstClosed = new HashMap<>(chosen);
                        firstWhy = closedBy;
                    }
                } else if (!closesAhead(here, chosen)) {
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
