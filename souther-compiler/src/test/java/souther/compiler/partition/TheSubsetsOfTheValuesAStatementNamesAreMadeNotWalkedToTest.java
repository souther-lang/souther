package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The subsets of the values a statement names that a search builds are taken from the ends in —
 * none of them and all of them, then one and all but one — and made one after the next, so that
 * neither the stack nor the time grows with how many values are named beyond what is made.
 */
class TheSubsetsOfTheValuesAStatementNamesAreMadeNotWalkedToTest {

    private static List<FixtureTemplate> named(int many) {
        return IntStream.range(0, many).mapToObj(FixtureTemplate::integer).toList();
    }

    private static List<List<String>> textsOf(List<List<FixtureTemplate>> subsets) {
        return subsets.stream().map(each -> each.stream().map(FixtureTemplate::text).toList())
                .toList();
    }

    @Test
    void theSubsetsComeFromTheEndsInAndEachSizeInTheOrderTheMembersStand() {
        assertEquals(List.of(List.of(), List.of("0", "1", "2"), List.of("0"), List.of("1"),
                        List.of("2"), List.of("0", "1"), List.of("0", "2"), List.of("1", "2")),
                textsOf(CountWitnesses.subsetsFromTheEnds(named(3), 100)));
    }

    @Test
    void noMoreAreMadeThanAreAsked() {
        assertEquals(List.of(List.of(), List.of("0", "1", "2"), List.of("0")),
                textsOf(CountWitnesses.subsetsFromTheEnds(named(3), 3)));
    }

    /** All of a hundred thousand is one subset of a hundred thousand, made without a call for
     *  each of them standing on the stack. */
    @Test
    void aStatementNamingAHundredThousandValuesIsGivenAllOfThemWithoutDeepCalls() {
        List<List<FixtureTemplate>> made = CountWitnesses.subsetsFromTheEnds(named(100_000), 5);
        assertEquals(List.of(0, 100_000, 1, 1, 1), made.stream().map(List::size).toList());
        assertEquals(List.of("0", "1", "2"),
                made.subList(2, 5).stream().map(each -> each.getFirst().text()).toList());
    }
}
