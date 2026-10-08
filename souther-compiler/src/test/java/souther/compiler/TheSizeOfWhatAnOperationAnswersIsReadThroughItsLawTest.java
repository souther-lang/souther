package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fork on the size of what an operation answers is read through what the operation's law says of
 * its argument, and the rule it states is one about the argument.
 *
 * <p>{@code List.map} keeps the size of its list, {@code Set.map} keeps whether its set holds
 * anything, {@code Set.fromList} is empty exactly where its list is, and {@code String.lowercase} is
 * empty exactly where its string is. Each of these forks states a rule about the argument the
 * behavior was handed, and nothing about it is left unread.
 *
 * <p>Only as far as the law goes. Lowercasing may change how many characters a string has, so a
 * size other than nought held against the answer is still a rule about a value made from the string,
 * and what it says about the string itself is not worked out.
 */
class TheSizeOfWhatAnOperationAnswersIsReadThroughItsLawTest {

    private static final String MODEL = """
            module probe.w

            behavior viaListMap : (xs: List<Int>) -> Int
            let viaListMap (xs) = if List.length(List.map(x -> x + 1, xs)) >= 1 then 1 else 0

            behavior viaSetMap : (xs: Set<Int>) -> Int
            let viaSetMap (xs) = if Set.size(Set.map(x -> x + 1, xs)) >= 1 then 1 else 0

            behavior viaFromList : (xs: List<Int>) -> Int
            let viaFromList (xs) = if Set.size(Set.fromList(xs)) >= 1 then 1 else 0

            behavior viaLowercase : (s: String) -> Int
            let viaLowercase (s) = if String.length(String.lowercase(s)) >= 1 then 1 else 0

            behavior pastWhatLowercaseKeeps : (s: String) -> Int
            let pastWhatLowercaseKeeps (s) =
                if String.length(String.lowercase(s)) >= 2 then 1 else 0
            """;

    /** What was left unread about each position of {@code behavior}, as {@code position reason}. */
    private static List<String> notRead(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        for (AdequacyReport.BehaviorReport each
                : AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (each.name().equals(behavior)) {
                return each.partition().notRead().stream()
                        .map(one -> one.at() + " " + one.reason()).toList();
            }
        }
        throw new AssertionError("no behavior called " + behavior);
    }

    @Test
    void aMappedListKeepsItsSize() {
        assertEquals(List.of(), notRead("viaListMap"));
    }

    @Test
    void aMappedSetHoldsSomethingWhereItsSetDoes() {
        assertEquals(List.of(), notRead("viaSetMap"));
    }

    @Test
    void aSetMadeOfAListHoldsSomethingWhereTheListDoes() {
        assertEquals(List.of(), notRead("viaFromList"));
    }

    @Test
    void aLowercasedStringIsEmptyWhereTheStringIs() {
        assertEquals(List.of(), notRead("viaLowercase"));
    }

    @Test
    void aSizeOfALowercasedStringPastNoughtIsStillNotWorkedOut() {
        assertEquals(List.of("s RULE_ABOUT_A_DERIVED_VALUE"), notRead("pastWhatLowercaseKeeps"));
    }
}
