package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Localizable;
import souther.compiler.diag.Messages;
import souther.compiler.publish.WeakeningWord;
import souther.compiler.reading.WhyNotJoined;
import souther.test.ClosedWorldContract;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The page says each thing a measure went without, and each reason a meeting was not joined, in a
 * phrase of the catalog found by the value's name.
 *
 * <p>The phrases are entries and no code, so nothing the compiler checks says a value that is added
 * has one. This is what does, for the base catalog; that every other catalog defines the keys the
 * base does is {@code EveryShippedMessageCatalogIsCompleteAndValidTest}'s.
 */
@ClosedWorldContract
class EveryWordOfThePageHasAPhraseInEveryCatalogTest {

    @Test
    void everyWeakeningWordHasAPhrase() {
        List<String> missing = new ArrayList<>();
        for (WeakeningWord word : WeakeningWord.values()) {
            collectIfMissing("weakening", word, missing);
        }
        assertEquals(List.of(), missing, "a word of the document the page has no phrase for");
    }

    @Test
    void everyReasonAMeetingIsNotJoinedHasAPhrase() {
        List<String> missing = new ArrayList<>();
        for (WhyNotJoined why : WhyNotJoined.values()) {
            collectIfMissing("not-joined", why, missing);
        }
        assertEquals(List.of(), missing, "a reason the page has no phrase for");
    }

    private static void collectIfMissing(String family, Enum<?> value, List<String> missing) {
        Localizable phrase = AdequacyReport.phrase(family, value);
        if (!Messages.has(phrase.key(), Locale.ENGLISH)
                || Messages.get(phrase.key(), Locale.ENGLISH).isBlank()) {
            missing.add(phrase.key());
        }
    }
}
