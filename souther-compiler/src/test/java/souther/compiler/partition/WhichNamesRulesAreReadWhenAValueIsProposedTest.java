package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of the names a value wears has its rules read when a value is proposed for it.
 *
 * <p>A value written under a name is written under every name the position wears, and each of those
 * names may carry rules of its own. What proposes a value from a rule about the characters of a
 * string reaches one name deep: it asks what the outermost name wraps, and reads that name's own
 * predicates only where what it wraps is the string itself. A name over a name therefore proposes
 * nothing of its own — the value comes out wearing both names, but only the innermost one's rules
 * were read for it.
 *
 * <p>Held here because it is the difference between two readings of one position. The names a value
 * wears and what is left under all of them are one answer; walking to what a single name wraps is
 * another, and the two part exactly where a name wraps a name. What this pins is which of them
 * decides today, so that a change to either is a change somebody chose.
 */
class WhichNamesRulesAreReadWhenAValueIsProposedTest {

    private static List<String> proposedFor(String declarations, String type) {
        RuleReadingSource rules = RuleReadings.ofSource("""
                module demo

                import String ( startsWith, endsWith )

                """ + declarations);
        TypeSymbol at = TypeSymbols.declared(new TypeKey(rules.symbols().module(), type));
        return Partitions.representativesOf(Type.ref(at), rules, ReadAs.THE_COMPILATION_DOES,
                        null, Set.of())
                .stream().map(FixtureTemplate::text).toList();
    }

    /** A rule on the name the string is directly under is read, and proposes what it asks for. */
    @Test
    void aRuleOnTheNameOverTheStringProposesAValue() {
        assertEquals(List.of("A(\"X\")", "A(\"x\")"), proposedFor("""
                data A = String
                    invariant tagged = startsWith("X", value)
                """, "A"));
    }

    /** The same rule under a second name: the value comes out under both, and the proposal is the
     *  inner name's. */
    @Test
    void aRuleOnTheInnerNameIsReadThroughTheOuterOne() {
        assertEquals(List.of("A(B(\"X\"))", "A(B(\"x\"))"), proposedFor("""
                data B = String
                    invariant tagged = startsWith("X", value)

                data A = B
                """, "A"));
    }

    /**
     * A rule on a name that wraps a name proposes nothing.
     *
     * <p>The walk that reads such a rule asks what the name wraps and finds another name rather than
     * the string, so the predicates written on it are not reached. What comes out is the value the
     * type would have offered with no rule written on it at all, under both names.
     */
    @Test
    void aRuleOnANameOverANameProposesNothing() {
        List<String> proposed = proposedFor("""
                data B = String

                data A = B
                    invariant tagged = startsWith("X", value)
                """, "A");

        assertEquals(List.of("A(B(\"x\"))"), proposed);
        assertTrue(proposed.stream().noneMatch(each -> each.contains("X")),
                "the outer name's rule reached no proposal: " + proposed);
    }

    /** Both names carrying a rule: the inner one's is proposed and the outer one's is not. */
    @Test
    void whereBothNamesCarryARuleOnlyTheInnerOneProposes() {
        List<String> proposed = proposedFor("""
                data B = String
                    invariant tagged = startsWith("X", value)

                data A = B
                    invariant ended = endsWith("Z", value)
                """, "A");

        assertEquals(List.of("A(B(\"X\"))", "A(B(\"x\"))"), proposed);
        assertTrue(proposed.stream().noneMatch(each -> each.endsWith("Z\"))")),
                "the outer name's rule reached no proposal: " + proposed);
    }

    /** And the names go back on in the order they were read off, however many there are. */
    @Test
    void theValueComesOutUnderEveryNameThePositionWears() {
        assertEquals(List.of("A(B(\"x\"))"), proposedFor("""
                data B = String

                data A = B
                """, "A"));
    }
}
