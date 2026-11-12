package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.hash.ValueHash;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ValueName;

import java.time.Duration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation answers of the answer before it twice is a graph of as many values as there
 * are calls, and what is asked of it follows each of them once: its hash, its equality, the
 * positions it is made of and what it spells are of the calls and not of the paths through them.
 */
class AnAnswerHandedTheSameAnswerTwiceIsOneValueAtEveryDepthTest {

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

    @Test
    void twoChainsMadeSeparatelyAreOneValueWhateverIsSharedInThem() {
        Quantity shared = chain(64, "x");
        Quantity unsharedAtEveryCall = unshared(12, "x");
        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            assertEquals(shared, chain(64, "x"));
            assertEquals(shared.hashCode(), chain(64, "x").hashCode());
            assertEquals(chain(12, "x"), unsharedAtEveryCall);
            assertEquals(chain(12, "x").spelling(), unsharedAtEveryCall.spelling());
            assertEquals(chain(12, "x").hashCode(), unsharedAtEveryCall.hashCode());
        });
    }

    @Test
    void whatTheyAreMadeOfTellsTwoApart() {
        assertNotEquals(chain(40, "x"), chain(40, "y"));
        assertNotEquals(chain(40, "x"), chain(41, "x"));
        assertNotEquals(chain(40, "x").spelling(), chain(40, "y").spelling());
        assertNotEquals(chain(40, "x").spelling(), chain(41, "x").spelling());
        Quantity a = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(chain(30, "x"), input("y")));
        Quantity b = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(input("y"), chain(30, "x")));
        assertNotEquals(a, b);
        Quantity negated = new Quantity.WhatAnOperationAnswers(NEGATE, List.of(chain(30, "x")));
        Quantity floored = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(chain(30, "x")));
        assertNotEquals(negated, floored);
        assertNotEquals(negated.spelling(), floored.spelling());
    }

    @Test
    void theInputsAnAnswerIsMadeOfAreEachOnceInTheOrderTheyAreHandedIn() {
        Quantity.WhatAnOperationAnswers deep = (Quantity.WhatAnOperationAnswers) chain(64, "x");
        assertEquals(1, deep.positionsItIsMadeOf().size());
        Quantity.WhatAnOperationAnswers mixed = new Quantity.WhatAnOperationAnswers(FLOOR_MOD,
                List.of(chain(50, "y"), input("x"), chain(50, "z"), chain(50, "y"), input("x")));
        assertEquals(List.of(input("y").term(), input("x").term(), input("z").term()),
                mixed.positionsItIsMadeOf());
    }

    @Test
    void aDeepAnswerSpellsInWhatGrowsWithItsCallsAndNotWithTheWaysThroughThem() {
        Spelling spelling = chain(200, "x").spelling();
        assertTrue(spelling.length() < 20_000, "spelled in " + spelling.length());
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
