package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.IntFunction;

/**
 * Which readings some cases choose among one beside another.
 *
 * <p><b>What every way holds.</b> What a case holds on every way of choosing it, with no choice
 * made further, is read once for each case ({@link #heldOnEveryWay}): a case its own parts, cases
 * held together what any of them holds, one of several what all of them hold, and no case
 * nothing. Every reading below of what a case holds is that one, so what a choice leaves out of
 * what tells it apart is still what the choice around it is told apart by.
 *
 * <p><b>What a choice is told apart by.</b> A choice is any one of several alternatives, and what
 * it chooses by is what its alternatives differ in: the parts one alternative holds on every way
 * that some other alternative does not, held as the alternative holds them, so a part and its
 * denial are two. A part every alternative holds alike tells none apart, wherever it was written.
 * The readings that made the parts a choice chooses by are the readings that tell it apart.
 *
 * <p><b>When two readings are chosen beside one another.</b> Two choices are made together, each
 * among more than one way, and the readings of one thing that tell one of them apart are none of
 * those that tell the other apart. Made together in two shapes, read off how
 * {@link DecidingCase.Cases#waysOfChoosing} counts: as two factors of a group, which multiply;
 * and as a choice made again past more than one alternative of another, which follows whichever of
 * those is taken, and so multiplies with the choice among them — the way a walk reaching a
 * candidate only past every way the one before it fails is taken apart. Alternatives among
 * themselves only add, and so does a choice past one alternative alone. No case is held nowhere
 * ({@link DecidingCase.Cases#NONE}), so every case below the one asked is some way of choosing.
 *
 * <p><b>Said only where it is shown.</b> A part some readings made together is theirs alike, and
 * where one reading may tell both choices apart — the same reading, or one said with less of
 * where it was made than the other — one reading is all the two need however it is declared, so
 * nothing is said of them. Where a choice gathers several, those of a factor are all it is told
 * apart by, and two factors share a reading wherever any choice in each does.
 *
 * <p><b>A fact about these cases, and nothing about others.</b> That a helper's readings are
 * chosen beside one another is read off the cases as they are. What its readings would come to
 * declared as a behavior, and how many ways the cases would be then, is another compilation, and
 * nothing here says it.
 *
 * <p>In the order the cases meet the parts: what every way holds is kept in the order its parts are
 * met, and the readings that made them are asked for in that order, which is the order they are
 * numbered and told in. Each reading by a number, as a bit of a set, so a reading is told apart
 * where it is made and not at every case it is carried through.
 */
final class ReadingsChosenOneBesideAnother {

    private ReadingsChosenOneBesideAnother() {
    }

    /**
     * The readings of each group {@code cases} choose among one beside another reading of the same
     * group, in the order the groups are first found.
     *
     * @param madeBy   the readings that made a part, by its spelling
     * @param groupOf  what a reading is a reading of, by its number: two readings of one thing
     *                 are what is told, and two of two things are not
     * @param mayBeOne whether two readings, by their numbers, may be one reading: the same, or
     *                 one said with less of where it was made than the other, which is all the
     *                 two choices they tell apart could need
     */
    static <G> Map<G, BitSet> of(DecidingCase.Cases cases, Function<Spelling, BitSet> madeBy,
                                 IntFunction<G> groupOf,
                                 BiPredicate<Integer, Integer> mayBeOne) {
        return multiplied(cases, heldOnEveryWay(cases), madeBy, groupOf, mayBeOne);
    }

    /**
     * What each case {@code cases} holds, itself and every case inside it, holds on every way of
     * choosing it with no choice made further, by the case: its own parts for a case, what any of
     * them holds for cases held together, what all of them hold for one of several, and nothing
     * for no case. Each part as the case holds it, in the order the parts are met.
     */
    static Map<DecidingCase.Cases, Set<Proposition>> heldOnEveryWay(DecidingCase.Cases cases) {
        Map<DecidingCase.Cases, Set<Proposition>> out = new IdentityHashMap<>();
        cases.fold(new DecidingCase.Cases.Fold<Set<Proposition>>() {

            @Override
            public Set<Proposition> one(DecidingCase.Cases.One one) {
                return inOrder(new LinkedHashSet<>(one.condition() instanceof Proposition.All all
                        ? all.parts() : List.of(one.condition())));
            }

            @Override
            public Set<Proposition> eachOf(DecidingCase.Cases.EachOf node,
                                           List<Set<Proposition>> alternatives) {
                if (alternatives.isEmpty()) {
                    return Set.of();
                }
                SequencedSet<Proposition> alike = new LinkedHashSet<>(alternatives.getFirst());
                alternatives.forEach(alike::retainAll);
                return inOrder(alike);
            }

            @Override
            public Set<Proposition> together(DecidingCase.Cases.Together node,
                                             List<Set<Proposition>> factors) {
                SequencedSet<Proposition> all = new LinkedHashSet<>();
                factors.forEach(all::addAll);
                return inOrder(all);
            }

            @Override
            public Set<Proposition> notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return Set.of();
            }
        }, out);
        return out;
    }

    /** {@code held} as it stands, kept in the order it was made in and changed by nobody. */
    private static Set<Proposition> inOrder(SequencedSet<Proposition> held) {
        return held.isEmpty() ? Set.of() : Collections.unmodifiableSequencedSet(held);
    }

    /**
     * The readings of each group two choices made together are told apart by, no reading of the
     * one maybe a reading of the other.
     *
     * @param held what each case holds on every way ({@link #heldOnEveryWay})
     */
    static <G> Map<G, BitSet> multiplied(DecidingCase.Cases cases,
                                         Map<DecidingCase.Cases, Set<Proposition>> held,
                                         Function<Spelling, BitSet> madeBy,
                                         IntFunction<G> groupOf,
                                         BiPredicate<Integer, Integer> mayBeOne) {
        Map<G, BitSet> found = new LinkedHashMap<>();
        Map<Proposition, BitSet> madeThe = new HashMap<>();
        Function<Set<Proposition>, BitSet> readingsOf = parts -> {
            BitSet out = new BitSet();
            for (Proposition part : parts) {
                out.or(madeThe.computeIfAbsent(part, one -> {
                    BitSet by = new BitSet();
                    WhereEachLineDecides.partsJoinedBy(one)
                            .forEach(spelling -> by.or(madeBy.apply(spelling)));
                    return by;
                }));
            }
            return out;
        };
        cases.fold(new DecidingCase.Cases.Fold<Chosen>() {

            @Override
            public Chosen one(DecidingCase.Cases.One one) {
                return new Chosen(1, new BitSet(), held.get(one));
            }

            @Override
            public Chosen eachOf(DecidingCase.Cases.EachOf node, List<Chosen> alternatives) {
                if (alternatives.size() == 1) {
                    return alternatives.getFirst();
                }
                Set<Proposition> alike = held.get(node);
                long ways = 0;
                BitSet chosen = new BitSet();
                // Each reading chosen among inside an alternative, with the alternatives that
                // choose among it again, by their place.
                Map<Integer, List<Integer>> past = new LinkedHashMap<>();
                for (int at = 0; at < alternatives.size(); at++) {
                    Chosen each = alternatives.get(at);
                    ways = Math.min(2, ways + each.ways());
                    chosen.or(readingsOf.apply(apart(each.held(), alike)));
                    chosen.or(each.chosen());
                    int place = at;
                    each.chosen().stream().forEach(again ->
                            past.computeIfAbsent(again, _ -> new ArrayList<>()).add(place));
                }
                past.forEach((again, those) -> {
                    if (those.size() > 1) {
                        List<Set<Proposition>> theirs = those.stream()
                                .map(at -> alternatives.get(at).held()).toList();
                        Set<Proposition> alikeThere = alike(theirs);
                        BitSet by = new BitSet();
                        theirs.forEach(each -> by.or(readingsOf.apply(apart(each, alikeThere))));
                        BitSet inner = new BitSet();
                        inner.set(again);
                        madeTogether(byGroup(by, groupOf), byGroup(inner, groupOf), mayBeOne,
                                found);
                    }
                });
                return new Chosen(ways, chosen, alike);
            }

            @Override
            public Chosen together(DecidingCase.Cases.Together node, List<Chosen> factors) {
                long ways = 1;
                BitSet chosen = new BitSet();
                List<Map<G, BitSet>> choices = new ArrayList<>();
                for (Chosen each : factors) {
                    ways = Math.min(2, ways * each.ways());
                    chosen.or(each.chosen());
                    if (each.ways() > 1 && !each.chosen().isEmpty()) {
                        choices.add(byGroup(each.chosen(), groupOf));
                    }
                }
                for (int one = 0; one < choices.size(); one++) {
                    for (int other = one + 1; other < choices.size(); other++) {
                        madeTogether(choices.get(one), choices.get(other), mayBeOne, found);
                    }
                }
                return new Chosen(ways, chosen, held.get(node));
            }

            @Override
            public Chosen notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return new Chosen(1, new BitSet(), held.get(notTakenApart));
            }
        });
        return found;
    }

    /** The parts every one of {@code held} holds alike. */
    private static Set<Proposition> alike(List<Set<Proposition>> held) {
        Set<Proposition> out = new LinkedHashSet<>(held.getFirst());
        held.forEach(out::retainAll);
        return out;
    }

    /** {@code held} less what is held {@code alike}: what this alternative is told apart by. */
    private static Set<Proposition> apart(Set<Proposition> held, Set<Proposition> alike) {
        if (alike.isEmpty()) {
            return held;
        }
        Set<Proposition> out = new LinkedHashSet<>(held);
        out.removeAll(alike);
        return out;
    }

    /**
     * Each group whose readings tell {@code one} apart and whose readings tell {@code other}
     * apart, no reading of the one maybe the same as one of the other, added to {@code found}
     * with all of them.
     */
    private static <G> void madeTogether(Map<G, BitSet> one, Map<G, BitSet> other,
                                         BiPredicate<Integer, Integer> mayBeOne,
                                         Map<G, BitSet> found) {
        one.forEach((group, these) -> {
            BitSet those = other.get(group);
            if (those != null && these.stream().noneMatch(here -> those.stream()
                    .anyMatch(there -> mayBeOne.test(here, there)))) {
                BitSet all = found.computeIfAbsent(group, _ -> new BitSet());
                all.or(these);
                all.or(those);
            }
        });
    }

    private static <G> Map<G, BitSet> byGroup(BitSet readings, IntFunction<G> groupOf) {
        Map<G, BitSet> out = new LinkedHashMap<>();
        readings.stream().forEach(reading ->
                out.computeIfAbsent(groupOf.apply(reading), _ -> new BitSet()).set(reading));
        return out;
    }

    /**
     * What is made of some cases for {@link #multiplied}: how many ways they are, counted as far
     * as two; the readings that tell apart some choice among more than one way inside them, no
     * more than the parts were made by however many ways lead here; and what they hold on every
     * way ({@link #heldOnEveryWay}), which is what a choice they are an alternative of reads of
     * them.
     */
    private record Chosen(long ways, BitSet chosen, Set<Proposition> held) {}
}
