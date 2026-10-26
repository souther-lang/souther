package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The choices of a group that stand in one state are stated as patterns that cover each of them
 * once and nothing else, and a set that is a product is one pattern.
 */
class AStateOfChoicesIsStatedExactlyAsPatternsTest {

    private static final String MADE = "made";
    private static final String MISSING = "missing";

    private static List<String> patterns(List<Integer> widths, List<String> states) {
        return ChoicePattern.of(widths, states, MISSING::equals).stream()
                .map(found -> found.pattern().fixed() + "x" + found.pattern().count())
                .toList();
    }

    @Test
    void twoBinaryFactorsWithOneChoiceMadeLeaveAChoiceAndAHalf() {
        // The first factor is the one that varies fastest: the choices are (0,0) (1,0) (0,1) (1,1).
        List<String> states = List.of(MADE, MISSING, MISSING, MISSING);

        assertEquals(List.of("[0, 1]x1", "[1, null]x2"), patterns(List.of(2, 2), states));
    }

    @Test
    void aChoiceNothingElseSharesAStateWithIsNotMergedWithItsNeighbours() {
        List<String> states = List.of(MISSING, MADE, MADE, MADE);

        assertEquals(List.of("[0, 0]x1"), patterns(List.of(2, 2), states));
    }

    @Test
    void tenBinaryFactorsWithOneChoiceMadeAreTenPatternsHoldingAllTheRest() {
        int size = 1 << 10;
        List<String> states = new ArrayList<>(Collections.nCopies(size, MISSING));
        states.set(0, MADE);

        List<ChoicePattern.Found<String>> found = ChoicePattern.of(
                Collections.nCopies(10, 2), states, MISSING::equals);

        assertEquals(10, found.size());
        assertEquals(size - 1, found.stream().mapToInt(each -> each.pattern().count()).sum());
        assertEquals(List.of(1, 2, 4, 8, 16, 32, 64, 128, 256, 512),
                found.stream().map(each -> each.pattern().count()).sorted().toList());
    }

    @Test
    void aChoiceTheFactorsLeaveNothingIsHeldByNoPattern() {
        // (1,1) is no choice: the second factor's second outcome cannot go with the first's.
        List<String> states = Arrays.asList(MISSING, MISSING, MISSING, null);

        assertEquals(List.of("[0, null]x2", "[1, 0]x1"), patterns(List.of(2, 2), states));
    }

    /**
     * How many patterns there are does not depend on the order the factors are in: the choices
     * missing wherever one factor came out one way are one pattern, whichever factor that is.
     */
    @Test
    void theNumberOfPatternsDoesNotDependOnWhichFactorTellsTheMissingFromTheMade() {
        for (int telling : new int[] {0, 4, 9}) {
            List<String> states = new ArrayList<>();
            for (int index = 0; index < 1 << 10; index++) {
                states.add(((index >> telling) & 1) == 1 ? MISSING : MADE);
            }

            List<ChoicePattern.Found<String>> found =
                    ChoicePattern.of(Collections.nCopies(10, 2), states, MISSING::equals);

            assertEquals(1, found.size(), () -> "missing where factor " + telling + " is 1");
            assertEquals(512, found.getFirst().pattern().count());
            for (int factor = 0; factor < 10; factor++) {
                assertEquals(factor == telling ? Integer.valueOf(1) : null,
                        found.getFirst().pattern().fixed().get(factor));
            }
        }
    }

    @Test
    void aFactorOfSeveralOutcomesJoinsWhenEveryOneOfThemIsMissing() {
        // idx = first + 3 * second: the second factor's outcome 1 is missing at all three firsts.
        List<String> states = List.of(MADE, MADE, MADE, MISSING, MISSING, MISSING);

        assertEquals(List.of("[null, 1]x3"), patterns(List.of(3, 2), states));
    }

    @Test
    void aFactorOfSeveralOutcomesDoesNotJoinWhileOneOfThemIsNotMissing() {
        List<String> states = List.of(MADE, MADE, MADE, MISSING, MISSING, MADE);

        assertEquals(List.of("[0, 1]x1", "[1, 1]x1"), patterns(List.of(3, 2), states));
    }

    @Test
    void aJoinCanMakeTwoOthersAlikeAtTheFactorThatNowDiffers() {
        // Missing wherever the third factor is 1: four choices, a square of the other two.
        List<String> states = new ArrayList<>();
        for (int index = 0; index < 8; index++) {
            states.add((index >> 2) == 1 ? MISSING : MADE);
        }

        assertEquals(List.of("[null, null, 1]x4"), patterns(List.of(2, 2, 2), states));
    }

    @Test
    void patternsOfDifferentStatesAreNotJoinedAtAFactor() {
        List<String> states = List.of("hedged", MISSING);

        assertEquals(List.of("[0]x1", "[1]x1"), ChoicePattern.of(List.of(2), states, each -> true)
                .stream().map(found -> found.pattern().fixed() + "x" + found.pattern().count())
                .toList());
    }

    @Test
    void choicesInDifferentStatesAreNotOnePattern() {
        List<String> states = List.of("hedged", MISSING, "hedged", MISSING);

        List<ChoicePattern.Found<String>> found =
                ChoicePattern.of(List.of(2, 2), states, each -> true);

        assertEquals(2, found.size());
        assertTrue(found.stream().allMatch(each -> each.pattern().count() == 2));
        assertEquals(List.of("hedged", MISSING),
                found.stream().map(ChoicePattern.Found::state).toList());
    }
}
