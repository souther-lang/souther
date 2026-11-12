package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

import org.junit.jupiter.api.Test;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CaseMapping;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link CaseMaps#answeredAsTheyStand} says a string made only of code points one conversion
 * leaves alone, and held as a {@code String} holds it, is its own answer. That is a statement
 * about the run time's conversion, so each string drawn here is asked of the run time itself.
 */
class AStringACaseConversionLeavesAsItStandsIsItsOwnAnswerTest {

    private static final Meter METER = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();

    private static final int DRAWS = 200_000;

    private static List<Integer> codePointsOf(CodePoints set) {
        List<Integer> out = new ArrayList<>();
        for (CodePoints.Range range : set.ranges()) {
            for (int cp = range.from(); cp <= range.to(); cp++) {
                out.add(cp);
            }
        }
        return out;
    }

    /** Strings of one to four of the code points, a quarter of them drawn from those that combine
     *  with what stands before them so that the ones the form changes are asked as well. */
    private static List<String> drawn(List<Integer> from) {
        List<Integer> combining = from.stream()
                .filter(cp -> Normalization.combiningClass(cp) != 0).toList();
        Random random = new Random(3165);
        List<String> out = new ArrayList<>();
        for (int i = 0; i < DRAWS; i++) {
            int length = 1 + random.nextInt(4);
            StringBuilder text = new StringBuilder();
            for (int at = 0; at < length; at++) {
                List<Integer> pool = !combining.isEmpty() && random.nextInt(4) == 0
                        ? combining : from;
                text.appendCodePoint(pool.get(random.nextInt(pool.size())));
            }
            out.add(text.toString());
        }
        return out;
    }

    @Test
    void aStringOfTheCodePointsAConversionLeavesAloneThatIsHeldAsItIsIsItsOwnAnswer() {
        for (CaseMapping mapping : List.of(CaseMapping.LOWERCASE, CaseMapping.UPPERCASE)) {
            List<Integer> alone = codePointsOf(CaseMaps.of(mapping).leftAlone());
            Language stands = CaseMaps.answeredAsTheyStand(mapping, Language.EVERY_STRING, METER);
            int held = 0;
            for (String text : drawn(alone)) {
                assertTrue(stands.has(text), () -> mapping + " " + text);
                if (Normalization.nfc(text).equals(text)) {
                    held++;
                    assertEquals(text, BoundUnderEvaluation.mapped(mapping, text),
                            () -> mapping + " " + text);
                }
            }
            assertTrue(held > 0, () -> mapping + " drew no string a String holds");
        }
    }

    @Test
    void aCodePointANeighbourChangesIsNotOneTheConversionLeavesAlone() {
        CodePoints alone = CaseMaps.of(CaseMapping.LOWERCASE).leftAlone();
        assertFalse(alone.has('Σ'));
        assertFalse(alone.has('İ'));
        assertFalse(CaseMaps.answeredAsTheyStand(CaseMapping.LOWERCASE, Language.EVERY_STRING,
                METER).has("ΟΣ"));
    }

    /** The outer conversion leaves {@code ß} alone, and the two together answer {@code ss} of
     *  it: so nothing is answered as it stands for two. */
    @Test
    void twoConversionsAnswerNoStringAsItStands() {
        CaseMapping both = new CaseMapping.Lowercase(CaseMapping.UPPERCASE);
        assertEquals("ss", BoundUnderEvaluation.mapped(both, "ß"));
        assertTrue(CaseMaps.answeredAsTheyStand(both, Language.EVERY_STRING, METER).isEmpty());
    }

    /** Only the strings of the language asked of are answered as they stand. */
    @Test
    void onlyTheStringsOfTheLanguageAskedOfAreAnswered() {
        Language upper = Language.ofWords(List.of("ABC", "abc"), METER);
        Language stands = CaseMaps.answeredAsTheyStand(CaseMapping.LOWERCASE, upper, METER);
        assertTrue(stands.has("abc"));
        assertFalse(stands.has("ABC"));
    }
}
