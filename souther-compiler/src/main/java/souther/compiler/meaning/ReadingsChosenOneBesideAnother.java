package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
 * <p><b>And only where saying a reading as its answer leaves fewer ways.</b> What naming a
 * helper tells an author is that declared as a behavior each reading of it is one answer, and the
 * cases are fewer: so a helper is named only where that is shown of one of its readings
 * ({@link #fewerAsAnswers}). Readings each chosen on one part of its own multiply, and are as many
 * ways said as answers as said in parts: each answer is chosen on where its part was.
 *
 * <p>Each reading by a number, as a bit of a set, so a reading is told apart where it is made and
 * not at every case it is carried through.
 */
final class ReadingsChosenOneBesideAnother {

    private ReadingsChosenOneBesideAnother() {
    }

    /**
     * The readings of each group {@code cases} choose among one beside another reading of the same
     * group, where saying one of them as its answer is shown to leave fewer ways, in the order the
     * groups are first found.
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
        Map<DecidingCase.Cases, Set<Proposition>> held = heldOnEveryWay(cases);
        Map<G, BitSet> found = multiplied(cases, held, madeBy, groupOf, mayBeOne);
        BitSet fewer = fewerAsAnswers(cases, held, madeBy, groupOf);
        found.keySet().removeIf(group -> fewer.stream()
                .noneMatch(reading -> groupOf.apply(reading).equals(group)));
        return found;
    }

    /**
     * What each case {@code cases} holds, itself and every case inside it, holds on every way of
     * choosing it with no choice made further, by the case: its own parts for a case, what any of
     * them holds for cases held together, what all of them hold for one of several, and nothing
     * for no case. Each part as the case holds it.
     */
    static Map<DecidingCase.Cases, Set<Proposition>> heldOnEveryWay(DecidingCase.Cases cases) {
        Map<DecidingCase.Cases, Set<Proposition>> out = new IdentityHashMap<>();
        cases.fold(new DecidingCase.Cases.Fold<Set<Proposition>>() {

            @Override
            public Set<Proposition> one(DecidingCase.Cases.One one) {
                return Set.copyOf(one.condition() instanceof Proposition.All all ? all.parts()
                        : List.of(one.condition()));
            }

            @Override
            public Set<Proposition> eachOf(DecidingCase.Cases.EachOf node,
                                           List<Set<Proposition>> alternatives) {
                if (alternatives.isEmpty()) {
                    return Set.of();
                }
                Set<Proposition> alike = new LinkedHashSet<>(alternatives.getFirst());
                alternatives.forEach(alike::retainAll);
                return Set.copyOf(alike);
            }

            @Override
            public Set<Proposition> together(DecidingCase.Cases.Together node,
                                             List<Set<Proposition>> factors) {
                Set<Proposition> all = new LinkedHashSet<>();
                factors.forEach(all::addAll);
                return Set.copyOf(all);
            }

            @Override
            public Set<Proposition> notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return Set.of();
            }
        }, out);
        return out;
    }

    /**
     * The readings of each group two choices made together are told apart by, no reading of the
     * one maybe a reading of the other, before anything is asked of their answers.
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

    /**
     * The readings each said as its answer — every part made by that reading alone held as the
     * answer is, holding where the part holds — leave the cases fewer ways, for what is shown
     * here; not every one that does.
     *
     * <p>Shown three ways, each where two ways come to one or a way comes to hold an answer both
     * ways. Two alternatives that differ only in parts the reading alone made, each held as held
     * on both, with the same beside them, are one alternative said as its answer. A choice made
     * on whether a part of the reading holds, with another part of it chosen on inside an
     * alternative holding that part one way or the other, holds the answer both ways on one of the
     * ways in there. And a choice made on whether a part of it holds, beside a part of it every way
     * past the choice holds alike, holds the answer both ways past one of the two.
     *
     * @param held what each case holds on every way ({@link #heldOnEveryWay})
     */
    static <G> BitSet fewerAsAnswers(DecidingCase.Cases cases,
                                     Map<DecidingCase.Cases, Set<Proposition>> held,
                                     Function<Spelling, BitSet> madeBy, IntFunction<G> groupOf) {
        BitSet out = new BitSet();
        Map<Proposition, Optional<Sole>> soleOnes = new HashMap<>();
        Function<Proposition, Optional<Sole>> sole =
                part -> soleOnes.computeIfAbsent(part, one -> soleSpelling(one, madeBy));
        cases.fold(new DecidingCase.Cases.Fold<Seen>() {

            @Override
            public Seen one(DecidingCase.Cases.One one) {
                return new Seen(Map.of(), held.get(one), heldBy(one.condition()), List.of(),
                        true);
            }

            @Override
            public Seen eachOf(DecidingCase.Cases.EachOf node, List<Seen> alternatives) {
                if (alternatives.size() == 1) {
                    return alternatives.getFirst();
                }
                Seen made = new Seen(new HashMap<>(), held.get(node), List.of(), null, false);
                if (alternatives.isEmpty()) {
                    return made;
                }
                List<Set<Proposition>> theirs = alternatives.stream().map(Seen::held).toList();
                Map<Integer, Set<Spelling>> split = made.split();
                alternatives.forEach(each -> each.split().forEach((reading, parts) ->
                        split.computeIfAbsent(reading, _ -> new LinkedHashSet<>())
                                .addAll(parts)));
                comingToOne(alternatives, sole, groupOf, out);
                // A choice on whether a part holds: held on every way of one alternative and
                // denied on every way of another, of one reading alone.
                Set<Proposition> alike = held.get(node);
                Map<Integer, Set<Spelling>> here = new HashMap<>();
                for (Set<Proposition> each : theirs) {
                    for (Proposition part : each) {
                        if (!alike.contains(part) && theirs.stream()
                                .anyMatch(other -> other.contains(part.denied()))) {
                            sole.apply(part).ifPresent(one -> here
                                    .computeIfAbsent(one.reading(), _ -> new LinkedHashSet<>())
                                    .add(one.spelling()));
                        }
                    }
                }
                Set<Proposition> everyWay = held.get(node);
                here.forEach((reading, parts) -> {
                    // Chosen on inside an alternative that holds the part chosen on, one way or
                    // the other.
                    for (int at = 0; at < theirs.size(); at++) {
                        Set<Spelling> holding = spellingsOf(theirs.get(at), reading, sole);
                        holding.retainAll(parts);
                        if (!holding.isEmpty()
                                && another(alternatives.get(at).split().get(reading), holding)) {
                            out.set(reading);
                        }
                    }
                    // Held alike on every way past the choice.
                    if (another(spellingsOf(everyWay, reading, sole), parts)) {
                        out.set(reading);
                    }
                    split.computeIfAbsent(reading, _ -> new LinkedHashSet<>()).addAll(parts);
                });
                return made;
            }

            @Override
            public Seen together(DecidingCase.Cases.Together node, List<Seen> factors) {
                Map<Integer, Set<Spelling>> split = new HashMap<>();
                List<Proposition> own = new ArrayList<>();
                List<Seen> beside = new ArrayList<>();
                for (Seen each : factors) {
                    each.split().forEach((reading, parts) ->
                            split.computeIfAbsent(reading, _ -> new LinkedHashSet<>())
                                    .addAll(parts));
                    if (each.one()) {
                        own.addAll(each.own());
                    } else {
                        beside.add(each);
                    }
                }
                // A choice on a part of a reading beside another part of it every way holds
                // alike, or beside another choice on one.
                for (int one = 0; one < factors.size(); one++) {
                    for (int other = 0; other < factors.size(); other++) {
                        if (one == other) {
                            continue;
                        }
                        Set<Proposition> besideIt = factors.get(other).held();
                        Map<Integer, Set<Spelling>> besideSplit = factors.get(other).split();
                        factors.get(one).split().forEach((reading, parts) -> {
                            if (another(spellingsOf(besideIt, reading, sole), parts)
                                    || another(besideSplit.get(reading), parts)) {
                                out.set(reading);
                            }
                        });
                    }
                }
                return new Seen(split, held.get(node), List.copyOf(own), List.copyOf(beside),
                        false);
            }

            @Override
            public Seen notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return new Seen(Map.of(), held.get(notTakenApart), List.of(), null, false);
            }
        });
        return out;
    }

    /**
     * The readings alternatives of one choice come to one by, said as answers, added to
     * {@code out}: two alternatives beside the same case whose own parts differ, and are the same
     * once each part a reading of one thing alone made is said as that reading's answer, held as
     * the part is held — all the readings of that thing said as answers at once, as declaring it
     * a behavior says them.
     *
     * <p>Each alternative put under what it comes to, and not held against each other one: the
     * same answer, as many times as there are alternatives. What an alternative holds beside its
     * own parts is told apart as the fold tells cases apart, by being the one worked out: a case
     * shared by two alternatives is the same one beside each.
     */
    private static <G> void comingToOne(List<Seen> alternatives,
                                        Function<Proposition, Optional<Sole>> sole,
                                        IntFunction<G> groupOf, BitSet out) {
        List<List<Proposition>> own = alternatives.stream().map(Seen::own).toList();
        Set<G> groups = new LinkedHashSet<>();
        own.forEach(parts -> parts.forEach(part -> sole.apply(part)
                .ifPresent(one -> groups.add(groupOf.apply(one.reading())))));
        for (G group : groups) {
            // What each alternative comes to, with the alternatives that do, by their place.
            Map<List<Object>, List<Integer>> comingTo = new HashMap<>();
            for (int at = 0; at < alternatives.size(); at++) {
                Set<Object> said = new LinkedHashSet<>();
                for (Proposition part : own.get(at)) {
                    Optional<Sole> by = sole.apply(part);
                    said.add(by.isPresent() && groupOf.apply(by.get().reading()).equals(group)
                            ? new Answer(by.get().reading(), by.get().holds()) : part);
                }
                comingTo.computeIfAbsent(List.of(alternatives.get(at).besideItsParts(), said),
                        _ -> new ArrayList<>()).add(at);
            }
            comingTo.values().forEach(those -> {
                if (those.stream().map(at -> Set.copyOf(own.get(at))).distinct().count() > 1) {
                    those.forEach(at -> own.get(at).forEach(part -> sole.apply(part)
                            .filter(one -> groupOf.apply(one.reading()).equals(group))
                            .ifPresent(one -> out.set(one.reading()))));
                }
            });
        }
    }

    /** A reading's answer, held where a part of it was held, or denied where one was denied. */
    private record Answer(int reading, boolean holds) {}

    /** The parts {@code condition} holds, each as it holds it. */
    private static List<Proposition> heldBy(Proposition condition) {
        return condition instanceof Proposition.All all ? all.parts() : List.of(condition);
    }

    /** One part one reading alone made: which reading, the part's spelling, and whether
     *  {@code part} holds it or denies it. */
    private record Sole(int reading, Spelling spelling, boolean holds) {}

    private static Optional<Sole> soleSpelling(Proposition part, Function<Spelling, BitSet> madeBy) {
        Map<Spelling, Proposition> held = WhereEachLineDecides.partsHeldBy(part);
        if (held.size() != 1) {
            return Optional.empty();
        }
        Map.Entry<Spelling, Proposition> only = held.entrySet().iterator().next();
        BitSet by = madeBy.apply(only.getKey());
        return by.cardinality() == 1
                ? Optional.of(new Sole(by.nextSetBit(0), only.getKey(),
                        only.getValue().equals(part)))
                : Optional.empty();
    }

    /** The spellings of the parts of {@code these} {@code reading} alone made. */
    private static Set<Spelling> spellingsOf(Set<Proposition> these, int reading,
                                             Function<Proposition, Optional<Sole>> sole) {
        Set<Spelling> out = new LinkedHashSet<>();
        for (Proposition part : these) {
            sole.apply(part).filter(one -> one.reading() == reading)
                    .ifPresent(one -> out.add(one.spelling()));
        }
        return out;
    }

    /** Whether some part of {@code these} is another than some part of {@code chosenOn}: two
     *  parts of one reading, one of them chosen on. */
    private static boolean another(Set<Spelling> these, Set<Spelling> chosenOn) {
        return these != null && these.stream()
                .anyMatch(part -> chosenOn.stream().anyMatch(on -> !on.equals(part)));
    }

    /**
     * What is seen of some cases for {@link #fewerAsAnswers}, each from what was seen of the
     * cases inside.
     *
     * <p>Told apart by being itself, as the fold tells the cases apart, and not by what it holds:
     * what a group holds beside its own parts is what was seen of the cases inside, which share
     * what follows from a choice, so comparing, hashing or writing out what it holds would walk
     * every way to them.
     */
    private static final class Seen {

        /** The parts of each reading alone some choice inside is made on, by whether it holds. */
        private final Map<Integer, Set<Spelling>> split;
        /** What is held on every way ({@link #heldOnEveryWay}). */
        private final Set<Proposition> held;
        /** The parts held of their own: a case's, or those of the cases a group holds together;
         *  none for a choice. */
        private final List<Proposition> own;
        /** What a group holds beside its own parts, as seen; null for a choice or cases nobody
         *  took apart, which hold themselves beside nothing. */
        private final List<Seen> beside;
        /** Whether this is one case, whose parts a group holds as its own. */
        private final boolean one;

        Seen(Map<Integer, Set<Spelling>> split, Set<Proposition> held, List<Proposition> own,
             List<Seen> beside, boolean one) {
            this.split = split;
            this.held = held;
            this.own = own;
            this.beside = beside;
            this.one = one;
        }

        Map<Integer, Set<Spelling>> split() {
            return split;
        }

        Set<Proposition> held() {
            return held;
        }

        List<Proposition> own() {
            return own;
        }

        boolean one() {
            return one;
        }

        /** What is held beside the own parts, each the very one seen. */
        List<Seen> besideItsParts() {
            if (one) {
                return List.of();
            }
            return beside == null ? List.of(this) : beside;
        }

        @Override
        public String toString() {
            return "Seen" + held;
        }
    }
}
