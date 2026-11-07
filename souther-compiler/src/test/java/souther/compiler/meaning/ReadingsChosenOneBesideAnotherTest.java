package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which readings some cases choose among one beside another is read off how the cases count:
 * choices held together multiply, alternatives add, and no case is nowhere.
 *
 * <p>Put to cases written here, each part made by a reading named after it: {@code h1} and
 * {@code h2} two readings of one helper, {@code g} a reading of another. What is checked is what the
 * cases make of the readings, so the cases are the smallest that have each shape.
 */
class ReadingsChosenOneBesideAnotherTest {

    /** The readings by number: two of the helper {@code H}, one of {@code G}. */
    private static final List<String> READINGS = List.of("h1", "h2", "g");

    private static final List<String> GROUP = List.of("H", "H", "G");

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

    /** The readings found for each group, by name. */
    private static Map<String, List<String>> found(DecidingCase.Cases cases) {
        Map<Spelling, BitSet> madeBy = new HashMap<>();
        for (String name : List.of("h1a", "h1b", "h1c", "h2a", "h2b", "h2c", "ga", "gb")) {
            BitSet by = new BitSet();
            by.set(READINGS.indexOf(name.substring(0, name.length() - 1)));
            WhereEachLineDecides.partsJoinedBy(part(name)).forEach(spelling ->
                    madeBy.put(spelling, by));
        }
        Map<String, List<String>> out = new HashMap<>();
        ReadingsChosenOneBesideAnother.of(cases,
                spelling -> madeBy.getOrDefault(spelling, new BitSet()), GROUP::get)
                .forEach((group, readings) -> out.put(group,
                        readings.stream().mapToObj(READINGS::get).toList()));
        return out;
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
