package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a language writes of itself for an order is what its machine writes, the first time it is
 * asked and every time after, and it is the same for two spellings of one language and not for
 * two languages.
 */
class ALanguageIsWrittenOutAsItsMachineIsEveryTimeItIsAskedTest {

    private static Language language(String regex) {
        Language said = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(said, regex);
        return said;
    }

    private static String writtenBy(Language language) {
        StringBuilder out = new StringBuilder("before;");
        language.writtenInto(out);
        return out.toString();
    }

    @Test
    void theFirstAskAndTheOnesAfterWriteWhatTheMachineWrites() {
        Language language = language("[a-c]{2}");
        StringBuilder machine = new StringBuilder("before;");
        language.machine().writtenInto(machine);
        assertEquals(machine.toString(), writtenBy(language), "the first ask");
        assertEquals(machine.toString(), writtenBy(language), "and the next");
    }

    @Test
    void twoSpellingsOfOneLanguageWriteAlikeAndTwoLanguagesDoNot() {
        assertEquals(writtenBy(language("[a-c]")), writtenBy(language("a|b|c")));
        assertNotEquals(writtenBy(language("[a-c]")), writtenBy(language("[a-d]")));
    }
}
