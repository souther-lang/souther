package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which readings some cases choose among one beside another is read off how the cases count:
 * choices held together multiply, alternatives add, and no case is nowhere.
 *
 * <p>Put to cases written here, each part made by a reading named after it: {@code h1} and
 * {@code h2} two readings of one helper, {@code g} a reading of another. What is checked is what the
 * cases make of the readings, so the cases are the smallest that have each shape.
 */
class ReadingsChosenOneBesideAnotherTest {

    /** The readings by number: two of the helper {@code H}, one of {@code G}, one of {@code I},
     *  and {@code h0}, which is {@code h1} said with less of where it was made. */
    private static final List<String> READINGS = List.of("h1", "h2", "g", "i", "h0");

    private static final List<String> GROUP = List.of("H", "H", "G", "I", "H");

    /** Whether two readings may be one: the same, or {@code h0} and {@code h1}. */
    private static boolean mayBeOne(int one, int other) {
        Set<Integer> coarseAndFine = Set.of(READINGS.indexOf("h0"), READINGS.indexOf("h1"));
        return one == other || (coarseAndFine.contains(one) && coarseAndFine.contains(other));
    }

    /** Every part, with the readings that made it: each by the reading its name starts with, and
     *  {@code s}, which both readings of {@code H} made alike. */
    private static final Map<String, List<String>> PARTS = Map.ofEntries(
            Map.entry("h1a", List.of("h1")), Map.entry("h1b", List.of("h1")),
            Map.entry("h1c", List.of("h1")), Map.entry("h2a", List.of("h2")),
            Map.entry("h2b", List.of("h2")), Map.entry("h2c", List.of("h2")),
            Map.entry("ga", List.of("g")), Map.entry("gb", List.of("g")),
            Map.entry("gc", List.of("g")), Map.entry("ia", List.of("i")),
            Map.entry("ib", List.of("i")), Map.entry("s", List.of("h1", "h2")),
            Map.entry("h0a", List.of("h0")));

    private static Proposition part(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    /** A case on the part {@code name}, made by the reading it starts with. */
    private static DecidingCase.Cases one(String name) {
        return new DecidingCase.Cases.One(part(name));
    }

    private static DecidingCase.Cases anyOf(DecidingCase.Cases... alternatives) {
        return new DecidingCase.Cases.EachOf(List.of(alternatives));
    }

    private static DecidingCase.Cases together(DecidingCase.Cases... factors) {
        return DecidingCase.Cases.together(List.of(factors));
    }

    private static DecidingCase.Cases not(String name) {
        return new DecidingCase.Cases.One(part(name).denied());
    }

    /** What made each part, by its spelling. */
    static Map<Spelling, BitSet> madeBy(Map<String, List<String>> parts, List<String> readings) {
        Map<Spelling, BitSet> out = new HashMap<>();
        parts.forEach((name, by) -> {
            BitSet these = new BitSet();
            by.forEach(reading -> these.set(readings.indexOf(reading)));
            WhereEachLineDecides.partsJoinedBy(part(name)).forEach(spelling ->
                    out.put(spelling, these));
        });
        return out;
    }

    /** The readings found for each group, by name. */
    private static Map<String, List<String>> found(DecidingCase.Cases cases) {
        Map<Spelling, BitSet> madeBy = madeBy(PARTS, READINGS);
        Map<String, List<String>> out = new HashMap<>();
        ReadingsChosenOneBesideAnother.of(cases,
                spelling -> madeBy.getOrDefault(spelling, new BitSet()), GROUP::get,
                ReadingsChosenOneBesideAnotherTest::mayBeOne)
                .forEach((group, readings) -> out.put(group,
                        readings.stream().mapToObj(READINGS::get).toList()));
        return out;
    }

    /** {@code h0} tells the first choice apart and {@code h1} the second: they may be one
     *  reading, so the two are not said to be two. */
    @Test
    void aReadingSaidWithLessMayBeTheOneSaidWithMore() {
        assertEquals(Map.of(), found(together(anyOf(one("h0a"), not("h0a")),
                anyOf(one("h1a"), one("h1b")))));
    }

    /**
     * A part every alternative holds alike tells none apart: here {@code h1a} beside each way of
     * the first choice and {@code h2a} beside each of the second, while {@code g} and {@code i}
     * are what the two choose by, and the helper's readings multiply nothing.
     */
    @Test
    void aPartEveryAlternativeHoldsAlikeTellsNoneOfThemApart() {
        assertEquals(Map.of(), found(together(
                anyOf(together(one("h1a"), one("ga")), together(one("h1a"), one("gb"))),
                anyOf(together(one("h2a"), one("ia")), together(one("h2a"), one("ib"))))));
    }

    /** Alike among the alternatives a choice is made again past, though not among all. */
    @Test
    void aPartAlikeAmongTheAlternativesTheChoiceFollowsTellsNoneOfThemApart() {
        DecidingCase.Cases next = anyOf(one("h2a"), one("h2b"));
        assertEquals(Map.of(), found(anyOf(
                together(one("h1a"), one("ga"), next),
                together(one("h1a"), one("gb"), next),
                one("gc"))));
    }

    /** A part and its denial are two: told apart by whether it holds. */
    @Test
    void aPartAndItsDenialTellTwoAlternativesApart() {
        DecidingCase.Cases next = anyOf(one("h2a"), not("h2a"));
        assertEquals(Map.of("H", List.of("h1", "h2")),
                found(anyOf(together(one("h1a"), next), together(not("h1a"), next))));
    }

    /** {@code s}, made by both readings alike, tells the first choice apart, and {@code h2}
     *  tells the second: one reading tells both apart, and nothing is said. */
    @Test
    void choicesOneReadingTellsApartAreNotSaidToMultiplyTwo() {
        assertEquals(Map.of(), found(together(anyOf(one("s"), not("s")),
                anyOf(one("h2a"), one("h2b")))));
    }

    @Test
    void twoChoicesHeldTogetherEachAmongReadingsOfOneHelperMultiply() {
        assertEquals(Map.of("H", List.of("h1", "h2")), found(together(
                anyOf(one("h1a"), one("h1b"), one("h1c")),
                anyOf(one("h2a"), one("h2b"), one("h2c")))));
    }

    @Test
    void aChoiceMadeAgainPastEveryAlternativeOfAnotherMultipliesWithIt() {
        DecidingCase.Cases next = anyOf(one("h2a"), one("h2b"));
        assertEquals(Map.of("H", List.of("h1", "h2")),
                found(anyOf(together(one("h1a"), next), together(one("h1b"), next))));
    }

    /** Held past each alternative by cases of its own, it is one choice by what it chooses
     *  among. */
    @Test
    void aChoiceMadeAgainPastTwoAlternativesMultipliesWhereverItIsHeld() {
        assertEquals(Map.of("H", List.of("h1", "h2")),
                found(anyOf(together(one("h1a"), anyOf(one("h2a"), one("h2b"))),
                        together(one("h1b"), anyOf(one("h2a"), one("h2c"))))));
    }

    @Test
    void readingsChosenAmongAsAlternativesAddAndMultiplyNothing() {
        assertEquals(Map.of(), found(anyOf(one("h1a"), one("h2a"))));
    }

    @Test
    void aChoiceInsideOneAlternativeAloneOnlyAddsItsWays() {
        assertEquals(Map.of(), found(anyOf(together(one("h1a"), anyOf(one("h2a"), one("h2b"))),
                one("h1b"))));
    }

    @Test
    void aChoiceHeldTogetherWithOneWayMultipliesNothing() {
        assertEquals(Map.of(), found(together(one("h1a"), anyOf(one("h2a"), one("h2b")))));
    }

    @Test
    void oneReadingOnEachSideIsOneReading() {
        assertEquals(Map.of(), found(together(anyOf(one("h1a"), one("h1b")),
                anyOf(one("h1c"), one("h1a")))));
    }

    @Test
    void readingsOfTwoThingsAreNotTwoReadingsOfOne() {
        assertEquals(Map.of(), found(together(anyOf(one("h1a"), one("h1b")),
                anyOf(one("ga"), one("gb")))));
    }

    /**
     * An alternative held together with no case is no case, and what is beside no case is in no
     * way of choosing: here the readings that would be chosen beside one another are past an
     * alternative that is none and one that is not, so they are chosen past one alone.
     */
    @Test
    void whatIsHeldBesideNoCaseIsChosenNowhere() {
        DecidingCase.Cases next = anyOf(one("h2a"), one("h2b"));
        DecidingCase.Cases cases = anyOf(
                together(DecidingCase.Cases.NONE, one("h1a"), next),
                together(one("h1b"), next));
        assertEquals(2, cases.waysOfChoosing(10), "the ways past the one that is a case");
        assertEquals(Map.of(), found(cases));
    }

    /** A choice on a way: the choice, and which of its alternatives the way took. */
    private record Taken(DecidingCase.Cases.EachOf choice, int alternative) {}

    /** Every way of choosing one case of {@code cases}, each the choices it made in order, or
     *  null past {@code most}: walked as a tree, nothing shared. */
    private static List<List<Taken>> ways(DecidingCase.Cases cases, int most) {
        List<List<Taken>> out = switch (cases) {
            case DecidingCase.Cases.One _, DecidingCase.Cases.NotTakenApart _ ->
                    List.of(List.of());
            case DecidingCase.Cases.EachOf each -> {
                List<List<Taken>> all = new ArrayList<>();
                for (int at = 0; at < each.alternatives().size(); at++) {
                    List<List<Taken>> those = ways(each.alternatives().get(at), most);
                    if (those == null) {
                        yield null;
                    }
                    for (List<Taken> way : those) {
                        List<Taken> longer = new ArrayList<>();
                        if (each.alternatives().size() > 1) {
                            longer.add(new Taken(each, at));
                        }
                        longer.addAll(way);
                        all.add(longer);
                    }
                }
                yield all;
            }
            case DecidingCase.Cases.Together group -> {
                List<List<Taken>> all = List.of(List.of());
                for (DecidingCase.Cases factor : group.factors()) {
                    List<List<Taken>> those = ways(factor, most);
                    if (those == null || (long) all.size() * those.size() > most) {
                        yield null;
                    }
                    List<List<Taken>> wider = new ArrayList<>();
                    for (List<Taken> way : all) {
                        for (List<Taken> more : those) {
                            List<Taken> both = new ArrayList<>(way);
                            both.addAll(more);
                            wider.add(both);
                        }
                    }
                    all = wider;
                }
                yield all;
            }
        };
        return out == null || out.size() > most ? null : out;
    }

    /** What {@code cases} holds outside any choice, each part as held: the definition's own
     *  words, worked out for each case asked and nothing kept. */
    private static Set<Proposition> heldOutsideAnyChoice(DecidingCase.Cases cases) {
        return switch (cases) {
            case DecidingCase.Cases.One(var condition) -> new LinkedHashSet<>(
                    condition instanceof Proposition.All all ? all.parts() : List.of(condition));
            case DecidingCase.Cases.NotTakenApart _ -> Set.of();
            case DecidingCase.Cases.EachOf each -> each.alternatives().size() == 1
                    ? heldOutsideAnyChoice(each.alternatives().getFirst()) : Set.of();
            case DecidingCase.Cases.Together group -> {
                Set<Proposition> out = new LinkedHashSet<>();
                group.factors().forEach(factor -> out.addAll(heldOutsideAnyChoice(factor)));
                yield out;
            }
        };
    }

    /** The readings that tell {@code choice} apart, by the definition. */
    private static BitSet tellingApart(DecidingCase.Cases.EachOf choice,
                                       Map<Spelling, BitSet> madeBy) {
        List<Set<Proposition>> held = choice.alternatives().stream()
                .map(ReadingsChosenOneBesideAnotherTest::heldOutsideAnyChoice).toList();
        Set<Proposition> alike = new LinkedHashSet<>(held.getFirst());
        held.forEach(alike::retainAll);
        BitSet out = new BitSet();
        for (Set<Proposition> each : held) {
            for (Proposition part : each) {
                if (!alike.contains(part)) {
                    WhereEachLineDecides.partsJoinedBy(part).forEach(spelling ->
                            out.or(madeBy.getOrDefault(spelling, new BitSet())));
                }
            }
        }
        return out;
    }

    /** Cases drawn at random from the parts above, each holding a few drawn before it. */
    private static DecidingCase.Cases drawn(Random dice, List<String> names) {
        List<DecidingCase.Cases> before = new ArrayList<>();
        for (int at = 0; at < 4; at++) {
            String name = names.get(dice.nextInt(names.size()));
            before.add(dice.nextBoolean() ? one(name) : not(name));
        }
        for (int at = 0; at < 8; at++) {
            List<DecidingCase.Cases> held = new ArrayList<>();
            int howMany = 1 + dice.nextInt(3);
            for (int i = 0; i < howMany; i++) {
                held.add(dice.nextInt(3) == 0
                        ? (dice.nextBoolean() ? one(names.get(dice.nextInt(names.size())))
                                : not(names.get(dice.nextInt(names.size()))))
                        : before.get(before.size() - 1 - dice.nextInt(Math.min(4,
                                before.size()))));
            }
            before.add(dice.nextBoolean() ? new DecidingCase.Cases.EachOf(held)
                    : DecidingCase.Cases.together(held));
        }
        return before.getLast();
    }

    /**
     * Held to the definition by cases drawn at random: each reading named tells some choice
     * apart, and some way of choosing makes two different choices told apart by two different
     * readings of what is named — worked out by walking every way, so a fold that keeps less
     * than it should, or names a reading for being there, is caught where it names one.
     */
    @Test
    void whatIsNamedIsTwoChoicesOnOneWayToldApartByTwoReadingsOfIt() {
        Random dice = new Random(3070);
        List<String> names = List.copyOf(PARTS.keySet().stream().sorted().toList());
        Map<Spelling, BitSet> madeBy = madeBy(PARTS, READINGS);
        int named = 0;
        int asked = 0;
        for (int round = 0; round < 4000; round++) {
            DecidingCase.Cases cases = drawn(dice, names);
            List<List<Taken>> all = ways(cases, 4000);
            if (all == null) {
                continue;
            }
            asked++;
            Map<String, BitSet> found = ReadingsChosenOneBesideAnother.of(cases,
                    spelling -> madeBy.getOrDefault(spelling, new BitSet()), GROUP::get,
                    ReadingsChosenOneBesideAnotherTest::mayBeOne);
            for (Map.Entry<String, BitSet> each : found.entrySet()) {
                named++;
                String group = each.getKey();
                BitSet tellsSome = new BitSet();
                boolean shown = false;
                for (List<Taken> way : all) {
                    for (int one = 0; one < way.size(); one++) {
                        BitSet first = ofGroup(tellingApart(way.get(one).choice(), madeBy), group);
                        tellsSome.or(first);
                        for (int other = one + 1; other < way.size() && !shown; other++) {
                            if (way.get(other).choice() == way.get(one).choice()) {
                                continue;
                            }
                            BitSet second = ofGroup(
                                    tellingApart(way.get(other).choice(), madeBy), group);
                            shown = twoDifferent(first, second);
                        }
                    }
                }
                BitSet beyond = (BitSet) each.getValue().clone();
                beyond.andNot(tellsSome);
                assertTrue(beyond.isEmpty(), "every reading named tells some choice apart: "
                        + beyond + " in " + cases);
                assertTrue(shown, "two choices on one way told apart by two readings of "
                        + group + ": " + cases);
            }
        }
        assertTrue(asked > 2000, "most of what is drawn is walked: " + asked);
        assertTrue(named > 50, "something is named, or this holds nothing to the definition: "
                + named);
    }

    private static BitSet ofGroup(BitSet readings, String group) {
        BitSet out = new BitSet();
        readings.stream().filter(reading -> GROUP.get(reading).equals(group)).forEach(out::set);
        return out;
    }

    private static boolean twoDifferent(BitSet one, BitSet other) {
        return one.stream().anyMatch(first -> other.stream()
                .anyMatch(second -> !mayBeOne(first, second)));
    }

    @Test
    void noCaseIsHeldTogetherWithAnother() {
        assertThrows(IllegalArgumentException.class, () -> new DecidingCase.Cases.Together(
                List.of(one("h1a"), DecidingCase.Cases.NONE)));
        assertEquals(DecidingCase.Cases.NONE, together(one("h1a"), DecidingCase.Cases.NONE));
        assertEquals(List.of(one("h1a")),
                ((DecidingCase.Cases.EachOf) anyOf(DecidingCase.Cases.NONE, one("h1a")))
                        .alternatives(), "an alternative that is no case is left out");
    }
}
