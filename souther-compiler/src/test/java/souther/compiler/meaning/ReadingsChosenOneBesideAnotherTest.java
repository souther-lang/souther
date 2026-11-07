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
import java.util.function.Function;

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

    /**
     * Two readings each chosen on one part of its own multiply, and said as their answers they
     * are as many ways: each answer is chosen on where its one part was. Nothing is said.
     */
    @Test
    void readingsEachChosenOnOnePartAreAsManyWaysSaidAsAnswers() {
        DecidingCase.Cases next = anyOf(one("h2a"), not("h2a"));
        assertEquals(Map.of(),
                found(anyOf(together(one("h1a"), next), together(not("h1a"), next))));
    }

    /**
     * Chosen on {@code h1a}, and on {@code h1b} only inside an alternative holding neither
     * {@code h1a} nor its denial: said as its answer, no way of {@code h1} holds it both ways,
     * and the ways are as many.
     */
    @Test
    void aChoiceOnAnotherPartPastNoSideOfTheFirstIsAsManyWaysAsAnswers() {
        assertEquals(Map.of(), found(together(
                anyOf(together(one("h1a"), one("ga")), together(not("h1a"), one("gb")),
                        together(one("gc"), anyOf(one("h1b"), not("h1b")))),
                anyOf(one("h2a"), not("h2a")))));
    }

    /**
     * Chosen on {@code h1a}, with {@code h1b} on both sides, held on one and denied on the other:
     * said as its answer, each side holds it one way, and the ways are as many.
     */
    @Test
    void aPartOnBothSidesOfAChoiceHeldOppositeWaysIsAsManyWaysAsAnswers() {
        assertEquals(Map.of(), found(together(
                anyOf(together(one("h1a"), one("h1b")), together(not("h1a"), not("h1b"))),
                anyOf(one("h2a"), not("h2a")))));
    }

    /**
     * Chosen on whether a part holds, and again on another part of the same reading inside one
     * side, as a walk that reaches the next candidate past every way the one before it fails:
     * said as its answer, one of the ways in there holds the answer both ways.
     */
    @Test
    void aReadingChosenOnTwoOfItsPartsAlongOneWayIsFewerWaysAsItsAnswer() {
        DecidingCase.Cases next = anyOf(together(one("h2a"), anyOf(one("h2b"), not("h2b"))),
                not("h2a"));
        DecidingCase.Cases failing = anyOf(together(one("h1b"), next), together(not("h1b"),
                next));
        assertEquals(Map.of("H", List.of("h1", "h2")),
                found(anyOf(together(one("h1a"), failing), together(not("h1a"), next))));
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

    /** The readings that tell {@code choice} apart, by the definition: what every way of one
     *  alternative holds that every way of another does not, each walked. */
    private static BitSet tellingApart(DecidingCase.Cases.EachOf choice,
                                       Map<Spelling, BitSet> madeBy) {
        List<Set<Proposition>> held = choice.alternatives().stream()
                .map(ReadingsChosenOneBesideAnotherTest::onEveryWay).toList();
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
            int kind = dice.nextInt(3);
            if (kind == 2) {
                // As the taking apart writes a choice on whether a part holds: the part on one
                // side and its denial on the other, each with what follows it.
                String name = names.get(dice.nextInt(names.size()));
                before.add(new DecidingCase.Cases.EachOf(List.of(
                        DecidingCase.Cases.together(List.of(one(name), held.getFirst())),
                        DecidingCase.Cases.together(List.of(not(name), held.getLast())))));
            } else {
                before.add(kind == 0 ? new DecidingCase.Cases.EachOf(held)
                        : DecidingCase.Cases.together(held));
            }
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

    /** One part as a way holds it: which part, or which reading's answer, and whether it holds. */
    private record Held(String what, boolean holds) {}

    /** Each part held and denied, by the proposition a case holds it as. */
    private static final Map<Proposition, Held> AS_HELD = asHeld();

    private static Map<Proposition, Held> asHeld() {
        Map<Proposition, Held> out = new HashMap<>();
        PARTS.keySet().forEach(name -> {
            out.put(part(name), new Held(name, true));
            out.put(part(name).denied(), new Held(name, false));
        });
        return out;
    }

    /** Every way of choosing, as the parts it holds, each said by {@code said}: a way holding a
     *  part both ways is no way, and two ways holding the same are one. */
    private static Set<Set<Held>> waysAsHeld(DecidingCase.Cases cases, Function<String, String> said) {
        Set<Set<Held>> out = new LinkedHashSet<>();
        for (List<Proposition> way : heldAlong(cases)) {
            Set<Held> held = new LinkedHashSet<>();
            for (Proposition part : way) {
                Held as = AS_HELD.get(part);
                if (as != null) {
                    held.add(new Held(said.apply(as.what()), as.holds()));
                }
            }
            if (held.stream().noneMatch(one -> held.contains(new Held(one.what(), !one.holds())))) {
                out.add(held);
            }
        }
        return out;
    }

    /** The parts each way of choosing holds, walked as a tree. */
    private static List<List<Proposition>> heldAlong(DecidingCase.Cases cases) {
        return switch (cases) {
            case DecidingCase.Cases.One(var condition) -> List.of(
                    condition instanceof Proposition.All all ? all.parts() : List.of(condition));
            case DecidingCase.Cases.NotTakenApart _ -> List.of(List.of());
            case DecidingCase.Cases.EachOf each -> each.alternatives().stream()
                    .flatMap(alternative -> heldAlong(alternative).stream()).toList();
            case DecidingCase.Cases.Together group -> {
                List<List<Proposition>> all = List.of(List.of());
                for (DecidingCase.Cases factor : group.factors()) {
                    List<List<Proposition>> wider = new ArrayList<>();
                    for (List<Proposition> way : all) {
                        for (List<Proposition> more : heldAlong(factor)) {
                            List<Proposition> both = new ArrayList<>(way);
                            both.addAll(more);
                            wider.add(both);
                        }
                    }
                    all = wider;
                }
                yield all;
            }
        };
    }

    /**
     * What naming a helper claims, held to what the cases would be: declared as a behavior, each
     * reading of it is one answer, so every part a reading of it alone made is that reading's
     * answer, held as the part was. Where the helper is named, the ways the cases are, told
     * apart by what they hold, are fewer with each reading said as its answer than with its
     * parts. Asked by walking every way and nothing the fold keeps, so a rule the fold reads that
     * names a helper declaring which leaves the cases as many is caught here.
     */
    @Test
    void whereAHelperIsNamedSayingEachReadingAsItsAnswerLeavesFewerWays() {
        Random dice = new Random(30701);
        List<String> names = List.copyOf(PARTS.keySet().stream().sorted().toList());
        Map<Spelling, BitSet> madeBy = madeBy(PARTS, READINGS);
        int named = 0;
        for (int round = 0; round < 12000; round++) {
            DecidingCase.Cases cases = drawn(dice, names);
            if (ways(cases, 4000) == null) {
                continue;
            }
            // Only cases the taking apart could write: no way holds a part both ways, and no
            // two hold the same.
            int as = waysAsHeld(cases, Function.identity()).size();
            if (as != heldAlong(cases).size()) {
                continue;
            }
            Map<String, BitSet> found = ReadingsChosenOneBesideAnother.of(cases,
                    spelling -> madeBy.getOrDefault(spelling, new BitSet()), GROUP::get,
                    ReadingsChosenOneBesideAnotherTest::mayBeOne);
            for (String group : found.keySet()) {
                named++;
                int answered = waysAsHeld(cases, name -> {
                    List<String> by = PARTS.get(name);
                    return by.size() == 1 && GROUP.get(READINGS.indexOf(by.getFirst()))
                            .equals(group) ? "answer of " + by.getFirst() : name;
                }).size();
                assertTrue(answered < as, group + " named, and said as its answers the cases are"
                        + " as many ways (" + as + " to " + answered + "): " + cases);
            }
        }
        assertTrue(named > 50, "something is named: " + named);
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

    /**
     * What every alternative of an inner choice holds alike tells none of them apart, and is
     * still what that choice holds on every way: here {@code h1a}, alike inside the first
     * alternative of the outer choice and in no way of the second, tells the outer one apart.
     */
    @Test
    void whatAChoiceHoldsAlikeTellsTheChoiceAroundItApart() {
        DecidingCase.Cases next = anyOf(one("h2a"), one("h2b"));
        assertEquals(Map.of("H", List.of("h1", "h2")), found(anyOf(
                together(anyOf(together(one("h1a"), one("ga")), together(one("h1a"), one("gb"))),
                        next),
                together(one("gc"), next))));
    }

    @Test
    void noCaseAtAllNamesNothing() {
        assertEquals(Map.of(), found(DecidingCase.Cases.NONE));
    }

    /** Every case held, from the one asked down, once each. */
    private static List<DecidingCase.Cases> everyCaseIn(DecidingCase.Cases cases) {
        Map<DecidingCase.Cases, Boolean> seen = new java.util.IdentityHashMap<>();
        List<DecidingCase.Cases> out = new ArrayList<>();
        List<DecidingCase.Cases> toVisit = new ArrayList<>(List.of(cases));
        while (!toVisit.isEmpty()) {
            DecidingCase.Cases each = toVisit.removeLast();
            if (seen.put(each, true) != null) {
                continue;
            }
            out.add(each);
            switch (each) {
                case DecidingCase.Cases.EachOf choice -> toVisit.addAll(choice.alternatives());
                case DecidingCase.Cases.Together group -> toVisit.addAll(group.factors());
                case DecidingCase.Cases.One _, DecidingCase.Cases.NotTakenApart _ -> { }
            }
        }
        return out;
    }

    /** What every way of {@code cases} holds, walked as a tree: no way, nothing. */
    private static Set<Proposition> onEveryWay(DecidingCase.Cases cases) {
        List<List<Proposition>> all = heldAlong(cases);
        if (all.isEmpty()) {
            return Set.of();
        }
        Set<Proposition> out = new LinkedHashSet<>(all.getFirst());
        all.forEach(out::retainAll);
        return out;
    }

    /** What the fold reads as held on every way is what every way holds, at every case. */
    @Test
    void whatEveryWayHoldsIsReadAtEveryCaseAsEveryWayHoldsIt() {
        Random dice = new Random(30702);
        List<String> names = List.copyOf(PARTS.keySet().stream().sorted().toList());
        int asked = 0;
        for (int round = 0; round < 3000; round++) {
            DecidingCase.Cases cases = drawn(dice, names);
            if (ways(cases, 4000) == null) {
                continue;
            }
            Map<DecidingCase.Cases, Set<Proposition>> held =
                    ReadingsChosenOneBesideAnother.heldOnEveryWay(cases);
            for (DecidingCase.Cases each : everyCaseIn(cases)) {
                asked++;
                assertEquals(onEveryWay(each), held.get(each), "at " + each);
            }
        }
        assertTrue(asked > 10000, "cases are asked: " + asked);
    }

    /**
     * The rules of being chosen beside one another, worked out as they are said with nothing
     * kept between cases: what an alternative holds is what every way of it holds, walked.
     */
    private static Map<String, BitSet> referenceMultiplied(DecidingCase.Cases cases,
                                                           Map<Spelling, BitSet> madeBy) {
        Map<String, BitSet> found = new HashMap<>();
        referenceChosen(cases, madeBy, found);
        return found;
    }

    /** How many ways (as far as two) and the readings telling apart some choice inside. */
    private record RefChosen(long ways, BitSet chosen) {}

    private static BitSet readingsOfParts(Set<Proposition> parts, Map<Spelling, BitSet> madeBy) {
        BitSet out = new BitSet();
        parts.forEach(part -> WhereEachLineDecides.partsJoinedBy(part).forEach(spelling ->
                out.or(madeBy.getOrDefault(spelling, new BitSet()))));
        return out;
    }

    private static RefChosen referenceChosen(DecidingCase.Cases cases,
                                             Map<Spelling, BitSet> madeBy,
                                             Map<String, BitSet> found) {
        return switch (cases) {
            case DecidingCase.Cases.One _, DecidingCase.Cases.NotTakenApart _ ->
                    new RefChosen(1, new BitSet());
            case DecidingCase.Cases.EachOf choice -> {
                List<DecidingCase.Cases> alternatives = choice.alternatives();
                if (alternatives.isEmpty()) {
                    yield new RefChosen(0, new BitSet());
                }
                if (alternatives.size() == 1) {
                    yield referenceChosen(alternatives.getFirst(), madeBy, found);
                }
                List<RefChosen> inside = alternatives.stream()
                        .map(each -> referenceChosen(each, madeBy, found)).toList();
                Set<Proposition> alike = onEveryWay(choice);
                long ways = 0;
                BitSet chosen = new BitSet();
                for (int at = 0; at < alternatives.size(); at++) {
                    ways = Math.min(2, ways + inside.get(at).ways());
                    Set<Proposition> apart = new LinkedHashSet<>(onEveryWay(alternatives.get(at)));
                    apart.removeAll(alike);
                    chosen.or(readingsOfParts(apart, madeBy));
                    chosen.or(inside.get(at).chosen());
                }
                BitSet again = new BitSet();
                inside.forEach(each -> again.or(each.chosen()));
                again.stream().forEach(reading -> {
                    List<Integer> those = new ArrayList<>();
                    for (int at = 0; at < inside.size(); at++) {
                        if (inside.get(at).chosen().get(reading)) {
                            those.add(at);
                        }
                    }
                    if (those.size() < 2) {
                        return;
                    }
                    Set<Proposition> alikeThere = new LinkedHashSet<>(
                            onEveryWay(alternatives.get(those.getFirst())));
                    those.forEach(at -> alikeThere.retainAll(onEveryWay(alternatives.get(at))));
                    BitSet by = new BitSet();
                    those.forEach(at -> {
                        Set<Proposition> apart = new LinkedHashSet<>(
                                onEveryWay(alternatives.get(at)));
                        apart.removeAll(alikeThere);
                        by.or(readingsOfParts(apart, madeBy));
                    });
                    BitSet inner = new BitSet();
                    inner.set(reading);
                    referenceTogether(by, inner, found);
                });
                yield new RefChosen(ways, chosen);
            }
            case DecidingCase.Cases.Together group -> {
                long ways = 1;
                BitSet chosen = new BitSet();
                List<BitSet> choices = new ArrayList<>();
                for (DecidingCase.Cases factor : group.factors()) {
                    RefChosen each = referenceChosen(factor, madeBy, found);
                    ways = Math.min(2, ways * each.ways());
                    chosen.or(each.chosen());
                    if (each.ways() > 1) {
                        choices.add(each.chosen());
                    }
                }
                for (int one = 0; one < choices.size(); one++) {
                    for (int other = one + 1; other < choices.size(); other++) {
                        referenceTogether(choices.get(one), choices.get(other), found);
                    }
                }
                yield new RefChosen(ways, chosen);
            }
        };
    }

    private static void referenceTogether(BitSet one, BitSet other, Map<String, BitSet> found) {
        for (String group : Set.copyOf(GROUP)) {
            BitSet these = ofGroup(one, group);
            BitSet those = ofGroup(other, group);
            if (!these.isEmpty() && !those.isEmpty() && these.stream().noneMatch(here ->
                    those.stream().anyMatch(there -> mayBeOne(here, there)))) {
                BitSet all = found.computeIfAbsent(group, _ -> new BitSet());
                all.or(these);
                all.or(those);
            }
        }
    }

    /**
     * What the fold finds chosen beside one another is what the rules find worked out as they
     * are said, both ways: a fold that keeps less of what a case holds than every way holds
     * names fewer, and one that keeps more names more, and either is caught here.
     */
    @Test
    void theFoldFindsWhatTheRulesWorkedOutAsSaidFind() {
        Random dice = new Random(30703);
        List<String> names = List.copyOf(PARTS.keySet().stream().sorted().toList());
        Map<Spelling, BitSet> madeBy = madeBy(PARTS, READINGS);
        int named = 0;
        for (int round = 0; round < 3000; round++) {
            DecidingCase.Cases cases = drawn(dice, names);
            if (ways(cases, 4000) == null) {
                continue;
            }
            Map<String, BitSet> folded = ReadingsChosenOneBesideAnother.multiplied(cases,
                    ReadingsChosenOneBesideAnother.heldOnEveryWay(cases),
                    spelling -> madeBy.getOrDefault(spelling, new BitSet()), GROUP::get,
                    ReadingsChosenOneBesideAnotherTest::mayBeOne);
            Map<String, BitSet> said = referenceMultiplied(cases, madeBy);
            assertEquals(said, folded, "for " + cases);
            named += folded.size();
        }
        assertTrue(named > 100, "something is found: " + named);
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
