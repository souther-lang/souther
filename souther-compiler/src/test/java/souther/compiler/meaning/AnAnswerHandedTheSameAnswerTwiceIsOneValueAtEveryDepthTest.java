package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.hash.ValueHash;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ValueName;
import souther.test.Growth;
import souther.test.Visits;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation answers of the answer before it twice is a graph of as many values as there
 * are calls, and what is asked of it follows each of them once: its hash, its equality, the
 * positions it is made of and what it spells are of the calls and not of the paths through them.
 */
class AnAnswerHandedTheSameAnswerTwiceIsOneValueAtEveryDepthTest {

    /** Deep enough that a visit to each way down is four thousand and ninety-six, which is well
     *  past what a visit to each call comes to. */
    private static final int DEEP = 12;

    private static final ValueName.Stdlib FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static final ValueName.Stdlib NEGATE = ValueName.Stdlib.operation("Int", "negate");

    private static DecisionAtom.OfTheInput input(String field) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("i").then(field)));
    }

    private static Quantity.WhatAnOperationAnswers twice(Quantity previous) {
        return new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(previous, previous));
    }

    private static Quantity chain(int depth, String field) {
        Quantity answer = input(field);
        for (int i = 0; i < depth; i++) {
            answer = twice(answer);
        }
        return answer;
    }

    /** The same shape made again by sharing nothing between the two arguments of a call. */
    private static Quantity unshared(int depth, String field) {
        Quantity answer = input(field);
        for (int i = 0; i < depth; i++) {
            Quantity left = answer;
            Quantity right = depth(i, field);
            answer = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(left, right));
        }
        return answer;
    }

    private static Quantity depth(int depth, String field) {
        return chain(depth, field);
    }

    /**
     * That how many times {@code asked} goes into the answers at {@link #DEEP} is no more than
     * eight times what it is at half of it. A reader that goes down the calls once each goes into
     * twice as many, and one that goes down every way goes into sixty-four times as many. Each
     * depth is asked of a chain made beforehand.
     */
    private static void assertCostIsOfTheCallsAndNotTheWays(IntFunction<Runnable> asked) {
        try (Visits visits = Visits.into(List.of(Quantity.class, Derivation.class))) {
            SequencedMap<Integer, Long> bySize = new LinkedHashMap<>();
            bySize.put(DEEP / 2, visits.duringLeast(asked.apply(DEEP / 2)));
            bySize.put(DEEP, visits.duringLeast(asked.apply(DEEP)));
            Growth.eachAtMost(bySize, 8, 1);
        }
    }

    @Test
    void twoChainsMadeSeparatelyAreOneValueWhateverIsSharedInThem() {
        Quantity shared = chain(DEEP, "x");
        Quantity unsharedAtEveryCall = unshared(12, "x");
        assertEquals(shared, chain(DEEP, "x"));
        assertEquals(shared.hashCode(), chain(DEEP, "x").hashCode());
        assertEquals(chain(12, "x"), unsharedAtEveryCall);
        assertEquals(chain(12, "x").spelling(), unsharedAtEveryCall.spelling());
        assertEquals(chain(12, "x").hashCode(), unsharedAtEveryCall.hashCode());

        assertCostIsOfTheCallsAndNotTheWays(depth -> {
            Quantity left = chain(depth, "x");
            Quantity right = chain(depth, "x");
            return () -> {
                assertEquals(left, right);
                assertEquals(left.hashCode(), right.hashCode());
            };
        });
    }

    @Test
    void whatTheyAreMadeOfTellsTwoApart() {
        assertNotEquals(chain(DEEP, "x"), chain(DEEP, "y"));
        assertNotEquals(chain(DEEP, "x"), chain(DEEP + 1, "x"));
        assertNotEquals(chain(DEEP, "x").spelling(), chain(DEEP, "y").spelling());
        assertNotEquals(chain(DEEP, "x").spelling(), chain(DEEP + 1, "x").spelling());
        Quantity a = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(chain(DEEP, "x"), input("y")));
        Quantity b = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(input("y"), chain(DEEP, "x")));
        assertNotEquals(a, b);
        Quantity negated = new Quantity.WhatAnOperationAnswers(NEGATE, List.of(chain(DEEP, "x")));
        Quantity floored = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(chain(DEEP, "x")));
        assertNotEquals(negated, floored);
        assertNotEquals(negated.spelling(), floored.spelling());
    }

    @Test
    void theInputsAnAnswerIsMadeOfAreEachOnceInTheOrderTheyAreHandedIn() {
        Quantity.WhatAnOperationAnswers deep = (Quantity.WhatAnOperationAnswers) chain(DEEP, "x");
        assertEquals(1, deep.positionsItIsMadeOf().size());
        Quantity.WhatAnOperationAnswers mixed = new Quantity.WhatAnOperationAnswers(FLOOR_MOD,
                List.of(chain(DEEP, "y"), input("x"), chain(DEEP, "z"), chain(DEEP, "y"),
                        input("x")));
        assertEquals(List.of(input("y").term(), input("x").term(), input("z").term()),
                mixed.positionsItIsMadeOf());

        assertCostIsOfTheCallsAndNotTheWays(depth -> {
            Quantity.WhatAnOperationAnswers answer = new Quantity.WhatAnOperationAnswers(FLOOR_MOD,
                    List.of(chain(depth, "y"), input("x"), chain(depth, "z"), chain(depth, "y")));
            return answer::positionsItIsMadeOf;
        });
    }

    @Test
    void aDeepAnswerSpellsInWhatGrowsWithItsCallsAndNotWithTheWaysThroughThem() {
        assertCostIsOfTheCallsAndNotTheWays(depth -> {
            Quantity answer = chain(depth, "x");
            return answer::spelling;
        });
        int spelledAtHalf = chain(DEEP / 2, "x").spelling().length();
        int spelled = chain(DEEP, "x").spelling().length();
        assertTrue(spelled <= 3 * spelledAtHalf, "spelled in " + spelledAtHalf + " at "
                + DEEP / 2 + " calls and " + spelled + " at " + DEEP);
    }

    /**
     * What a chain of answers is told apart by comes to no number it already had, however deep.
     * The same chain hashed as {@code int}s comes round after some tens of thousands of steps, and
     * from there every answer deeper hashes as one before it.
     */
    @Test
    void aChainDeeperThanAnIntHashCanTellApartIsStillTold() {
        Set<Long> states = new HashSet<>();
        Set<Integer> narrow = new HashSet<>();
        long state = 1;
        int number = 1;
        boolean cameRound = false;
        for (int depth = 0; depth < 400_000; depth++) {
            state = ValueHash.ofItsPartsWide(FLOOR_MOD.getClass(), state, state);
            assertTrue(states.add(state), "a state repeated at depth " + depth);
            number = ValueHash.ofItsParts(FLOOR_MOD.getClass(), number, number);
            cameRound |= !narrow.add(number);
        }
        assertTrue(cameRound, "the int chain this is compared with never came round");
        Quantity deep = chain(100_000, "x");
        assertEquals(deep.hashCode(), chain(100_000, "x").hashCode());
        assertNotEquals(deep, chain(100_001, "x"));
    }

    /** An answer that comes to {@code size} calls and numbers: the number, and a call each. */
    private static Quantity negations(int size) {
        Quantity answer = input("x");
        for (int i = 1; i < size; i++) {
            answer = new Quantity.WhatAnOperationAnswers(NEGATE, List.of(answer));
        }
        return answer;
    }

    /** Which form an answer is written in is where it comes to more calls than the figure. */
    @Test
    void anAnswerIsWrittenNestedUpToTheFigureAndListedPastIt() {
        int figure = Quantity.WhatAnOperationAnswers.WRITTEN_NESTED_UP_TO;
        assertFalse(negations(figure).spelled().contains("%"), "at the figure");
        assertTrue(negations(figure + 1).spelled().contains("%"), "one past it");
    }

    /** Either form says what the answer is: equal answers are written alike and the rest are not,
     *  whichever side of the figure they come to. */
    @Test
    void anAnswerIsWrittenAlikeWhereItIsEqualOnEverySideOfTheFigure() {
        int figure = Quantity.WhatAnOperationAnswers.WRITTEN_NESTED_UP_TO;
        for (int calls : new int[] {figure - 1, figure, figure + 1, figure + 2}) {
            assertEquals(negations(calls).spelling(), negations(calls).spelling(), "" + calls);
            assertNotEquals(negations(calls).spelling(), negations(calls + 1).spelling(),
                    "" + calls);
        }
        for (int depth : new int[] {5, 6, 7, 8}) {
            assertEquals(chain(depth, "x").spelling(), unshared(depth, "x").spelling(),
                    "shared and made again, depth " + depth);
            assertNotEquals(chain(depth, "x").spelling(), chain(depth, "y").spelling(),
                    "depth " + depth);
        }
    }

    @Test
    void aSmallAnswerIsSpelledAsTheCallsWrittenOneInsideAnother() {
        String x = input("x").spelling().toString();
        String inner = "Int.floorMod(" + x + ", " + x + ")";
        assertEquals("Int.floorMod(" + inner + ", " + inner + ")", chain(2, "x").spelled());
    }
}
