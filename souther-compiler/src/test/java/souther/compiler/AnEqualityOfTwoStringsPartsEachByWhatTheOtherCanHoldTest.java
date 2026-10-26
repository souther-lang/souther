package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An equality between the strings at two positions parts each by what the other can hold.
 *
 * <p>The equality is true at a string only if the other position can hold it, so the strings the
 * other cannot hold are a class of this position the rule tells from the rest, whatever is written
 * at the other. Nothing is said where the two are tied, where a way narrows either before the
 * equality, or where what the other can hold is not worked out exactly: a class that would be
 * counted there is one a row can be owed at that no row can be written for.
 */
class AnEqualityOfTwoStringsPartsEachByWhatTheOtherCanHoldTest {

    private static final String LETTERS = "[a-z]+";

    private static final String LETTERS_AND_DIGITS = "[a-z0-9]+";

    /** The classes of each position the model divides, by the path of the position. */
    private static Map<String, List<String>> classesOf(String first, String second,
                                                       String body) {
        Compilation compilation = Compilation.ofSource("""
                module example.equal

                data L = String
                    invariant String.matches("%s", value)

                data M = String
                    invariant String.matches("%s", value)

                behavior f : (a: L, b: M) -> Bool

                let f (a, b) = %s
                """.formatted(first, second, body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Map<String, List<String>> out = new java.util.TreeMap<>();
        all.get("f").axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The strings of {@code b} that {@code a} cannot hold are a class of {@code b}'s own. */
    @Test
    void theStringsThePartnerCannotHoldAreAClassOfTheOther() {
        assertEquals(Map.of("b", List.of("b/x can be a", "b/x is never a")),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"));
    }

    /** It is the wider side that is parted: the narrower one's strings are all the other's. */
    @Test
    void itIsTheWiderSideThatIsParted() {
        assertEquals(Map.of("a", List.of("a/x can be b", "a/x is never b")),
                classesOf(LETTERS_AND_DIGITS, LETTERS, "a.value == b.value"));
    }

    @Test
    void twoLanguagesThatOverlapPartEachOther() {
        assertEquals(Map.of("a", List.of("a/x can be b", "a/x is never b"),
                        "b", List.of("b/x can be a", "b/x is never a")),
                classesOf("[a-c]+", "[b-d]+", "a.value == b.value"));
    }

    @Test
    void oneLanguageOnBothSidesPartsNeither() {
        assertEquals(Map.of(), classesOf(LETTERS, LETTERS, "a.value == b.value"));
    }

    /** The order of the two operands is not what parts them. */
    @Test
    void theOperandsOfTheEqualityMayBeWrittenEitherWayRound() {
        assertEquals(classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "b.value == a.value"));
    }

    /** A rule that the strings are unequal is about the same strings. */
    @Test
    void anInequalityPartsTheSamePositionsTheSameWay() {
        assertEquals(classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value /= b.value"));
    }

    /** A position set against itself is tied to itself, and what it can hold parts nothing. */
    @Test
    void aPositionSetAgainstItselfPartsNothing() {
        assertEquals(Map.of(), classesOf(LETTERS, LETTERS_AND_DIGITS, "b.value == b.value"));
    }
}
