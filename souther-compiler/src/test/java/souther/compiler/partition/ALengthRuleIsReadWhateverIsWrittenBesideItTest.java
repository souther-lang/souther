package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.values.AdmissibleSet;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lengths a record's rule leaves its field {@code a} are read from what the rule says of
 * {@code a}, and from nothing beside it: a rule about another number is no reason to hold less of
 * it, and a rule that joins {@code a} to another place is a reason to hold nothing.
 *
 * <p>What is held is asked of every length a string of {@code a} may have, against the lengths the
 * rule's own words allow, so that a run the reader holds past what the rule says shows as one.
 */
class ALengthRuleIsReadWhateverIsWrittenBesideItTest {

    private static final int PAST_EVERY_END = 40;

    private static final String MODEL = """
            module beside

            data Pair = { a: String, b: String, xs: List<String> }
                invariant %s

            data Ok

            behavior read : (p: Pair) -> Ok
            """;

    /** What is held of the strings of {@code a}, where the record's rule is {@code rule}. */
    private static StringsHeld.Held heldBy(String rule) {
        Position at = positionOf(rule);
        return StringsHeld.held(at);
    }

    private static Position positionOf(String rule) {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL.formatted(rule)), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                Membership.none());
        Position at = input.at(TermPath.of("p").then("a"));
        assertNotNull(at, "the field is a position");
        return at;
    }

    /** Every length up to past the ends is held exactly where the rule allows it. */
    private static void assertHeldAre(String rule, IntPredicate allowed) {
        StringsHeld.Held held = heldBy(rule);
        assertNotNull(held, "the lengths " + rule + " leaves are read");
        for (int length = 0; length <= PAST_EVERY_END; length++) {
            assertEquals(allowed.test(length), held.lengths().holds(BigInteger.valueOf(length)),
                    "length " + length + " under " + rule);
        }
    }

    @Test
    void aHoleIsReadWhereAnotherNumberHasARuleOfItsOwn() {
        assertHeldAre("String.length(a) <= 10 && String.length(a) /= 7 && List.length(xs) >= 1",
                length -> length <= 10 && length != 7);
    }

    @Test
    void whatIsLeftOfALengthIsTheLengthsAndNotTheEndsTheRulesPlace() {
        // A length taken out past the ends changes nothing of the lengths, and a choice that
        // leaves every length is every length: both are read, as they are where they are not
        // written with a hole.
        assertHeldAre("String.length(a) <= 5 && String.length(a) /= 9", length -> length <= 5);
        assertHeldAre("String.length(a) <= 10 && (String.length(a) < 4 || String.length(a) > 6)",
                length -> length <= 10 && (length < 4 || length > 6));
    }

    /**
     * A set read whole and the ends of the lengths are not the rules where a choice takes a length
     * out from between them: the set holds the strings, the ends hold the hull of the choice, and
     * the length the choice refuses is a string of the set that no value is.
     */
    @Test
    void aSetIsNotTheWholeOfARuleWhoseChoiceTakesALengthOutOfIt() {
        String strings = "(a == \"abc\" || a == \"abcd\")";
        assertTrue(positionOf(strings).admitted().completeness()
                        instanceof AdmissibleSet.Completeness.Complete,
                "the strings alone are the whole of what is said");
        assertFalse(positionOf(strings
                + " && (String.length(a) == 4 || String.length(a) <= 2)").admitted().completeness()
                        instanceof AdmissibleSet.Completeness.Complete,
                "a length the choice takes out is a string the set still holds");
    }

    /**
     * A rule on the order of the strings is a bound the strings and the lengths do not hold, so
     * the lengths beside it are not read as the strings the position holds, whatever runs they
     * are.
     */
    @Test
    void aBoundOnTheOrderOfTheStringsLeavesTheLengthsUnread() {
        assertNull(heldBy("a < \"B\" && String.length(a) >= 1"));
        assertNull(heldBy("a < \"B\" && String.length(a) >= 1 && String.length(a) /= 3"));
    }

    @Test
    void aChoiceOneOfWhoseAlternativesLeavesNoLengthLeavesWhatTheOtherLeaves() {
        assertHeldAre("(String.length(a) > 5 && String.length(a) <= 0) || String.length(a) < 6",
                length -> length < 6);
    }

    @Test
    void aChoiceBetweenTwoStringsLengthsLeavesNoLengthsOfOne() {
        // A name and a code each shorter than three or each longer than five: the name may be of
        // either length, and with a code of the other it is no value. The lengths each may have
        // are not the choice.
        assertNull(heldBy("(String.length(a) < 3 && String.length(b) < 3)"
                + " || (String.length(a) > 5 && String.length(b) > 5)"));
    }

    @Test
    void aRuleThatJoinsTheLengthToAnotherPlaceLeavesNoLengthsOfIt() {
        assertNull(heldBy("String.length(a) <= 10 && String.length(a) /= 7"
                + " && String.length(a) == String.length(b)"));
    }
}
