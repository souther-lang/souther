package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.IntFunction;

/**
 * Which readings some cases choose among one beside another: two choices, each among more than
 * one way, made together on one way of choosing, one among parts some reading made and the other
 * among parts another reading of the same thing made.
 *
 * <p>Read off the cases as {@link DecidingCase.Cases#waysOfChoosing} counts them: any one of
 * several adds their ways, one of each of several multiplies them, and no case is held nowhere
 * ({@link DecidingCase.Cases#NONE}), so every case here is some way of choosing. Two choices are
 * made together in two shapes. As two factors of a group, each of more than one way: their ways
 * multiply. And as a choice made again past more than one alternative of another: whichever of
 * those alternatives is taken, the inner choice follows, so the two are as many ways as theirs
 * multiplied, which is how a walk that reaches a candidate only past every way the one before it
 * fails is taken apart. A choice made past one alternative alone only adds its ways to the
 * others', and so do the alternatives of one choice among themselves.
 *
 * <p>Of readings and not of the cases that hold them. The choice made again past several
 * alternatives is one choice by what it chooses among, though the cases it is held in past each
 * alternative may be cases of their own; and readings are what a reader names.
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
     * @param madeBy  the readings that made a part, by its spelling
     * @param groupOf what a reading is a reading of, by its number: two readings of one thing are
     *                what is told, and two of two things are not
     */
    static <G> Map<G, BitSet> of(DecidingCase.Cases cases, Function<Spelling, BitSet> madeBy,
                                 IntFunction<G> groupOf) {
        Map<G, BitSet> found = new LinkedHashMap<>();
        cases.fold(new DecidingCase.Cases.Fold<Chosen>() {

            @Override
            public Chosen one(DecidingCase.Cases.One one) {
                BitSet direct = new BitSet();
                for (Spelling part : WhereEachLineDecides.partsJoinedBy(one.condition())) {
                    direct.or(madeBy.apply(part));
                }
                return new Chosen(1, direct, new BitSet());
            }

            @Override
            public Chosen eachOf(DecidingCase.Cases.EachOf node, List<Chosen> alternatives) {
                if (alternatives.size() == 1) {
                    return alternatives.getFirst();
                }
                long ways = 0;
                BitSet chosen = new BitSet();
                // Each reading chosen among inside an alternative: how many alternatives choose
                // among it again, and what those alternatives are told apart by.
                Map<Integer, Integer> past = new HashMap<>();
                Map<Integer, BitSet> besideIt = new LinkedHashMap<>();
                for (Chosen each : alternatives) {
                    ways = Math.min(2, ways + each.ways());
                    chosen.or(each.direct());
                    chosen.or(each.chosen());
                    each.chosen().stream().forEach(again -> {
                        past.merge(again, 1, Integer::sum);
                        besideIt.computeIfAbsent(again, _ -> new BitSet()).or(each.direct());
                    });
                }
                besideIt.forEach((again, by) -> {
                    if (past.get(again) > 1) {
                        BitSet inner = new BitSet();
                        inner.set(again);
                        madeTogether(List.of(by, inner), groupOf, found);
                    }
                });
                return new Chosen(ways, new BitSet(), chosen);
            }

            @Override
            public Chosen together(DecidingCase.Cases.Together node, List<Chosen> factors) {
                long ways = 1;
                BitSet direct = new BitSet();
                BitSet chosen = new BitSet();
                List<BitSet> choices = new ArrayList<>();
                for (Chosen each : factors) {
                    ways = Math.min(2, ways * each.ways());
                    direct.or(each.direct());
                    chosen.or(each.chosen());
                    if (each.ways() > 1) {
                        choices.add(each.chosen());
                    }
                }
                madeTogether(choices, groupOf, found);
                return new Chosen(ways, direct, chosen);
            }

            @Override
            public Chosen notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return new Chosen(1, new BitSet(), new BitSet());
            }
        });
        return found;
    }

    /**
     * Each group two of {@code choices} choose among readings of, two different readings, added to
     * {@code found} with every reading of it they choose among. One reading in every choice is one
     * reading however it is declared.
     */
    private static <G> void madeTogether(List<BitSet> choices, IntFunction<G> groupOf,
                                         Map<G, BitSet> found) {
        if (choices.size() < 2) {
            return;
        }
        Map<G, BitSet> read = new LinkedHashMap<>();
        Map<G, Integer> choosing = new HashMap<>();
        for (BitSet choice : choices) {
            Set<G> here = new HashSet<>();
            choice.stream().forEach(reading -> {
                G group = groupOf.apply(reading);
                read.computeIfAbsent(group, _ -> new BitSet()).set(reading);
                if (here.add(group)) {
                    choosing.merge(group, 1, Integer::sum);
                }
            });
        }
        read.forEach((group, readings) -> {
            if (choosing.get(group) > 1 && readings.cardinality() > 1) {
                found.computeIfAbsent(group, _ -> new BitSet()).or(readings);
            }
        });
    }

    /**
     * What is made of some cases: how many ways they are, counted as far as two; the readings
     * whose parts they hold outside any choice, which a choice they are an alternative of is told
     * apart by; and the readings whose parts a choice among more than one way inside them chooses
     * among. No more readings than the parts were made by, however many ways lead here.
     */
    private record Chosen(long ways, BitSet direct, BitSet chosen) {}
}
