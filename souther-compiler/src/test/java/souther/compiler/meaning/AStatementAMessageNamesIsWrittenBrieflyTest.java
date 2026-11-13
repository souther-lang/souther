package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a message says of a statement is its text where that is short, and where it is not the
 * first of it and its length ({@link Proposition#briefly}), so that a reader that is given what it
 * does not read says so in the time it takes to look, however many names the statement was made
 * through ({@link Spelling#beginning}).
 */
class AStatementAMessageNamesIsWrittenBrieflyTest {

    /** Each statement holds the one before it twice, in a conjunction and in the disjunction
     *  beside it, so its text holds the text of everything below it twice at each level; made
     *  until its text is longer than {@code chars}. */
    private static Proposition chainWhoseTextIsLongerThan(int chars) {
        String names = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(names + "0");
        for (int at = 1; held.spelling().length() <= chars; at++) {
            Proposition around = Proposition.any(List.of(held, CompoundSamples.truth(names + at)));
            held = Proposition.all(List.of(held, around));
        }
        return held;
    }

    private static Proposition chain(int length) {
        String names = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(names + "0");
        for (int at = 1; at <= length; at++) {
            Proposition around = Proposition.any(List.of(held, CompoundSamples.truth(names + at)));
            held = Proposition.all(List.of(held, around));
        }
        return held;
    }

    @Test
    void theBeginningOfASpellingIsWhatItsTextBeginsWith() {
        Spelling spelling = chain(5).spelling();
        String text = spelling.toString();

        for (int limit : new int[] {0, 1, 7, 50, text.length() - 1, text.length(),
                text.length() + 10}) {
            assertEquals(text.substring(0, Math.min(limit, text.length())),
                    spelling.beginning(limit), "the first " + limit);
        }
    }

    @Test
    void aShortStatementIsWrittenWhole() {
        Proposition statement = chain(2);

        assertEquals(statement.spelledOut(), statement.briefly());
    }

    @Test
    void aStatementAsLongAsTheWaysDownToItsPartsIsWrittenInItsFirstCharsAndItsLength() {
        Proposition statement = chainWhoseTextIsLongerThan(1_000_000);

        String said = assertTimeoutPreemptively(Duration.ofSeconds(10), statement::briefly);

        assertEquals(statement.spelling().beginning(Proposition.BRIEFLY_CHARS) + "... ("
                + statement.spelling().length() + " chars)", said);
        assertTrue(said.length() < Proposition.BRIEFLY_CHARS + 40, said.length() + " chars");
    }
}
