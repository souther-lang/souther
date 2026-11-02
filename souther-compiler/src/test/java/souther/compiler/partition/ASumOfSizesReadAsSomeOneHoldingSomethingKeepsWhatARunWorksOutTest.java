package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StatedComparison;
import souther.compiler.meaning.Proposition;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A sum of sizes read as some one of the containers holding something says what a run works out
 * to get to it as the sum written says it, and not as the disjunction it is read as does.
 *
 * <p>The reading of what a comparison holds and the account of what a run works out to get to it
 * are two things read off the one comparison ({@link Pullback.OnTheInput}). A sum works out every
 * addend where a disjunction stops short at its left half, so a rule reading the first must leave
 * the second to the arithmetic of what was written.
 */
class ASumOfSizesReadAsSomeOneHoldingSomethingKeepsWhatARunWorksOutTest {

    private static final String SOURCE = """
            module g

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Yes
            data No

            behavior classify : (s: String, ys: List<Int>) -> Yes | No
                constructs Domain

            let classify (s, ys) =
                if %s then Yes else No
            """;

    private static final String LEFT =
            "List.length(List.flatMap(d -> if Domain(d) as name then [ name ] else [], "
                    + "List.drop(1, String.split(\"@\", s))))";

    /** A list whose closure works out an arithmetic operation a run may stop in. */
    private static final String RIGHT = "List.length(List.map(x -> x + 1, ys))";

    private static ReadComparisons readOf(String condition) {
        return ReadComparisons.ofTheAnalysis(SOURCE.formatted(condition), "classify");
    }

    private static Pullback.OnTheInput onTheInput(ReadComparisons read) {
        ComparisonReadings.Reading against = read.only();
        return Pullback.ofAComparisonOnTheInput(
                ((ComparisonReadings.Stated.AComparison) against.statement()).comparison(),
                against.reads(), read.inputs().reading(read.rules()));
    }

    /** What the arithmetic of the comparison as written says a run works out. */
    private static StopEvidence writtenArithmetic(ReadComparisons read) {
        ComparisonReadings.Reading against = read.only();
        StatedComparison comparison =
                ((ComparisonReadings.Stated.AComparison) against.statement()).comparison();
        return AffineReading.OfAComparison.worksOut(AffineReading.read(comparison,
                against.reads(), read.inputs().reading(read.rules()))).stops();
    }

    /**
     * Read as the lists holding something, and told what the sum written is told, whichever of
     * the spellings of the check it is.
     */
    @Test
    void whatARunWorksOutIsTheWrittenSumsWhateverTheCheckIsSpelt() {
        for (String bound : new String[] {">= 1", "> 0", "/= 0", "== 0"}) {
            ReadComparisons read = readOf(LEFT + " + " + RIGHT + " " + bound);
            Pullback.OnTheInput stated = onTheInput(read);
            assertFalse(Proposition.leavesSomethingUnread(stated.stated().proposition()),
                    bound + " is read as the lists holding something");
            assertEquals(writtenArithmetic(read), stated.stops().get(), bound);
        }
    }

    /**
     * What the sum is told does not depend on the rule that read it: the same sum held against a
     * bound that says how many, which that rule does not take, is told the same.
     */
    @Test
    void whatARunWorksOutIsNotWhatTheRuleThatReadTheSumSays() {
        assertEquals(onTheInput(readOf(LEFT + " + " + RIGHT + " >= 5")).stops().get(),
                onTheInput(readOf(LEFT + " + " + RIGHT + " >= 1")).stops().get());
    }

    /** Three addends and a sum given a name are read alike, and told the same. */
    @Test
    void aSumOfThreeAndASumGivenANameAreReadAsTheLists() {
        String three = LEFT + " + " + RIGHT + " + List.length(ys) >= 1";
        ReadComparisons readThree = readOf(three);
        assertFalse(Proposition.leavesSomethingUnread(
                onTheInput(readThree).stated().proposition()), three);
        assertEquals(writtenArithmetic(readThree), onTheInput(readThree).stops().get());
        String named = """
                { let total = %s + %s
                  total >= 1 }""".formatted(LEFT, RIGHT);
        ReadComparisons readNamed = readOf(named);
        assertFalse(Proposition.leavesSomethingUnread(
                onTheInput(readNamed).stated().proposition()), named);
    }
}
