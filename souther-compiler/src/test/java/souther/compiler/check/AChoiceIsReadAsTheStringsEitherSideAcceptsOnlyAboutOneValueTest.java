package souther.compiler.check;

import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A choice between two patterns is read as the strings either accepts where both are about one
 * value, and as nothing about the strings otherwise.
 *
 * <p>What a composer takes out of a reading is a value the rule admits, so a reading narrower than
 * the rule refuses values the author allowed. A choice about two values is no set of strings at
 * either, and a choice one side of which is no pattern admits strings the other side does not: read
 * as a set in either case, it would be that narrower reading.
 */
class AChoiceIsReadAsTheStringsEitherSideAcceptsOnlyAboutOneValueTest {

    private static StringPredicates.StatedOn statedOn(String declaration) {
        RuleReadingSource rules = RuleReadings.ofSource("module demo\n\n" + declaration);
        return StringPredicates.statedOn(
                TypeSymbols.declared(new TypeKey(rules.symbols().module(), "R")), rules);
    }

    private static List<StringPredicates.Reading> readings(StringPredicates.StatedOn stated) {
        return List.copyOf(stated.read().values());
    }

    @Test
    void aChoiceBetweenTwoPatternsAboutOneValueIsTheStringsEitherAccepts() {
        StringPredicates.StatedOn stated = statedOn("""
                data R = String
                    invariant String.matches("[A-Z]{2}", value) || String.matches("[0-9]{6}", value)
                """);

        List<StringPredicates.Reading> read = readings(stated);
        assertEquals(1, read.size(), "the rule is one part, read: " + read);
        StringPredicates.Reading.Accepting accepting =
                assertInstanceOf(StringPredicates.Reading.Accepting.class, read.get(0));
        PatternMeaning.EitherOf choice =
                assertInstanceOf(PatternMeaning.EitherOf.class, accepting.accepts());
        assertEquals(2, choice.arms().size(), "one arm for each pattern: " + choice);
    }

    @Test
    void aChoiceBetweenPatternsAboutTwoValuesIsNoSetOfStrings() {
        StringPredicates.StatedOn stated = statedOn("""
                data R = { a: String, b: String }
                    invariant String.matches("[A-Z]{2}", a) || String.matches("[0-9]{6}", b)
                """);

        assertTrue(readings(stated).isEmpty(),
                "nothing about the strings is read off a choice about two values: "
                        + readings(stated));
    }

    /** One side counts the characters, which is no pattern this reading takes a set out of, and the
     *  other side alone would refuse the strings of three characters the rule admits. */
    @Test
    void aChoiceOneSideOfWhichIsNoPatternIsNotReadAsTheOtherSide() {
        StringPredicates.StatedOn stated = statedOn("""
                data R = String
                    invariant String.length(value) == 3 || String.matches("[0-9]{6}", value)
                """);

        assertTrue(readings(stated).stream()
                        .noneMatch(StringPredicates.Reading.Accepting.class::isInstance),
                "no set of strings is read off half a choice: " + readings(stated));
    }
}
