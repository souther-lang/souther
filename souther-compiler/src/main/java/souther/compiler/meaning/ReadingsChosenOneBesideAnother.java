package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.IntFunction;

/**
 * Which readings some cases choose among one beside another.
 *
 * <p><b>What a choice is told apart by.</b> A choice is any one of several alternatives, and what
 * it chooses by is what its alternatives differ in: the parts one alternative holds outside any
 * further choice that some other alternative does not, held as the alternative holds them, so a
 * part and its denial are two. A part every alternative holds alike tells none apart, wherever
 * it was written. The readings that made the parts a choice chooses by are the readings that tell
 * it apart.
 *
 * <p><b>When two readings are chosen beside one another.</b> Two choices are made together, each
 * among more than one way, and the readings of one thing that tell one of them apart are none of
 * those that tell the other apart. Made together in two shapes, read off how
 * {@link DecidingCase.Cases#waysOfChoosing} counts: as two factors of a group, which multiply;
 * and as a choice made again past more than one alternative of another, which follows whichever of
 * those is taken, and so multiplies with the choice among them — the way a walk reaching a
 * candidate only past every way the one before it fails is taken apart. Alternatives among
 * themselves only add, and so does a choice past one alternative alone. No case is held nowhere
 * ({@link DecidingCase.Cases#NONE}), so every case here is some way of choosing.
 *
 * <p><b>Said only where it is shown.</b> A part some readings made together is theirs alike, and
 * where one reading may tell both choices apart — the same reading, or one said with less of
 * where it was made than the other — one reading is all the two need however it is declared, so
 * nothing is said of them. Where a choice gathers several, those of a factor are all
 * it is told apart by, and two factors share a reading wherever any choice in each does.
 *
 * <p>Each reading by a number, as a bit of a set, so a reading is told apart where it is made and
 * not at every case it is carried through.
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
        Map<G, BitSet> found = new LinkedHashMap<>();
        Map<Proposition, BitSet> madeThe = new HashMap<>();
        Function<Set<Proposition>, BitSet> readingsOf = parts -> {
            BitSet out = new BitSet();
            for (Proposition part : parts) {
                out.or(madeThe.computeIfAbsent(part, held -> {
                    BitSet by = new BitSet();
                    WhereEachLineDecides.partsJoinedBy(held)
                            .forEach(spelling -> by.or(madeBy.apply(spelling)));
                    return by;
                }));
            }
            return out;
        };
        cases.fold(new DecidingCase.Cases.Fold<Chosen>() {

            @Override
            public Chosen one(DecidingCase.Cases.One one) {
                return new Chosen(1, Set.copyOf(heldBy(one.condition())), new BitSet());
            }

            @Override
            public Chosen eachOf(DecidingCase.Cases.EachOf node, List<Chosen> alternatives) {
                if (alternatives.size() == 1) {
                    return alternatives.getFirst();
                }
                long ways = 0;
                BitSet chosen = new BitSet();
                Set<Proposition> alike = alike(alternatives);
                // Each reading chosen among inside an alternative, with the alternatives that
                // choose among it again.
                Map<Integer, List<Chosen>> past = new LinkedHashMap<>();
                for (Chosen each : alternatives) {
                    ways = Math.min(2, ways + each.ways());
                    chosen.or(readingsOf.apply(apart(each.direct(), alike)));
                    chosen.or(each.chosen());
                    each.chosen().stream().forEach(again ->
                            past.computeIfAbsent(again, _ -> new ArrayList<>()).add(each));
                }
                past.forEach((again, those) -> {
                    if (those.size() > 1) {
                        Set<Proposition> alikeThere = alike(those);
                        BitSet by = new BitSet();
                        those.forEach(each -> by.or(readingsOf.apply(
                                apart(each.direct(), alikeThere))));
                        BitSet inner = new BitSet();
                        inner.set(again);
                        madeTogether(by, inner, groupOf, mayBeOne, found);
                    }
                });
                return new Chosen(ways, Set.of(), chosen);
            }

            @Override
            public Chosen together(DecidingCase.Cases.Together node, List<Chosen> factors) {
                long ways = 1;
                Set<Proposition> direct = new LinkedHashSet<>();
                BitSet chosen = new BitSet();
                List<BitSet> choices = new ArrayList<>();
                for (Chosen each : factors) {
                    ways = Math.min(2, ways * each.ways());
                    direct.addAll(each.direct());
                    chosen.or(each.chosen());
                    if (each.ways() > 1) {
                        choices.add(each.chosen());
                    }
                }
                for (int one = 0; one < choices.size(); one++) {
                    for (int other = one + 1; other < choices.size(); other++) {
                        madeTogether(choices.get(one), choices.get(other), groupOf, mayBeOne,
                                found);
                    }
                }
                return new Chosen(ways, Set.copyOf(direct), chosen);
            }

            @Override
            public Chosen notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return new Chosen(1, Set.of(), new BitSet());
            }
        });
        return found;
    }

    /** The parts {@code condition} holds, each as it holds it. */
    private static List<Proposition> heldBy(Proposition condition) {
        return condition instanceof Proposition.All all ? all.parts() : List.of(condition);
    }

    /** The parts every one of {@code alternatives} holds alike. */
    private static Set<Proposition> alike(List<Chosen> alternatives) {
        Set<Proposition> out = new LinkedHashSet<>(alternatives.getFirst().direct());
        alternatives.forEach(each -> out.retainAll(each.direct()));
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
    private static <G> void madeTogether(BitSet one, BitSet other, IntFunction<G> groupOf,
                                         BiPredicate<Integer, Integer> mayBeOne,
                                         Map<G, BitSet> found) {
        Map<G, BitSet> ofOne = byGroup(one, groupOf);
        Map<G, BitSet> ofOther = byGroup(other, groupOf);
        ofOne.forEach((group, these) -> {
            BitSet those = ofOther.get(group);
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
     * What is made of some cases: how many ways they are, counted as far as two; the parts they
     * hold outside any choice, each as held, which a choice they are an alternative of is told
     * apart by; and the readings that tell apart some choice among more than one way inside them.
     * No more readings than the parts were made by, however many ways lead here.
     */
    private record Chosen(long ways, Set<Proposition> direct, BitSet chosen) {}
}
