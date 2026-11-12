package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Meter;

import org.junit.jupiter.api.Test;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.StringsInsideStrings;
import souther.compiler.semantics.CaseMapping;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a conversion answers of some strings, as far as it is shown, against what the run time
 * answers of them, asked of every value of up to three code points over an alphabet of the code
 * points the conversions turn on: the closing sigma, the dotted capital I, the sharp s in both
 * cases, combining marks, a titlecase letter, and the Kelvin sign.
 *
 * <p>Three things are held. A value shown ({@code canBe}) is the run time's answer of some value
 * of the strings. A value the run time answers is not outside what may be. And every string made
 * from the values to derive from, the strings inside them, is inside what the run time answers of
 * some value — which the strings left as they stand would break, since some are no value.
 */
class WhatAConversionAnswersAgreesWithTheRunTimeOnShortStringsTest {

    /** A meter of its own for each ask, as a reading is given one. */
    private static Meter meter() {
        return PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
    }

    private static final List<String> ALPHABET = List.of("a", "A", "z", "Σ", "σ", "ς", "İ", "i",
            "ß", "ẞ", "́", "̇", "̣", "ǅ", "K", "ᄀ", "ᅡ");

    private static final int PARTNERS = 100;

    private static boolean isAValue(String text) {
        return Normalization.nfc(text).equals(text);
    }

    private static List<String> valuesAmong(List<String> every) {
        return every.stream()
                .filter(WhatAConversionAnswersAgreesWithTheRunTimeOnShortStringsTest::isAValue)
                .toList();
    }

    private static List<String> strings(int upTo) {
        List<String> out = new ArrayList<>(List.of(""));
        int from = 0;
        for (int length = 1; length <= upTo; length++) {
            int to = out.size();
            for (int at = from; at < to; at++) {
                for (String each : ALPHABET) {
                    out.add(out.get(at) + each);
                }
            }
            from = to;
        }
        return out;
    }

    private static List<List<String>> partners(List<String> every) {
        Random random = new Random(3165);
        List<List<String>> out = new ArrayList<>();
        for (int i = 0; i < PARTNERS; i++) {
            Set<String> words = new LinkedHashSet<>();
            int count = 1 + random.nextInt(4);
            while (words.size() < count) {
                words.add(every.get(random.nextInt(every.size())));
            }
            out.add(List.copyOf(words));
        }
        return out;
    }

    private static final List<CaseMapping> MAPPINGS = List.of(CaseMapping.LOWERCASE,
            CaseMapping.UPPERCASE, new CaseMapping.Lowercase(CaseMapping.UPPERCASE),
            new CaseMapping.Uppercase(CaseMapping.LOWERCASE),
            new CaseMapping.Lowercase(CaseMapping.LOWERCASE));

    @Test
    void whatIsShownIsAnAnswerAndEveryAnswerIsAmongWhatMayBe() {
        List<String> every = strings(2);
        List<String> values = valuesAmong(every);
        for (CaseMapping mapping : MAPPINGS) {
            for (List<String> words : partners(every)) {
                Set<String> answers = new LinkedHashSet<>();
                for (String word : words) {
                    String answer = isAValue(word) ? BoundUnderEvaluation.mapped(mapping, word)
                            : null;
                    if (answer != null) {
                        answers.add(answer);
                    }
                }
                Meter meter = meter();
                Language partner = Language.ofWords(words, meter);
                WhatAConversionAnswers.Shown asked = WhatAConversionAnswers
                        .of(partner, mapping, meter).forEquality(meter);
                for (String value : values) {
                    boolean answered = answers.contains(value);
                    assertTrue(!asked.canBe().has(value) || answered,
                            () -> mapping + " " + words + " shows " + value + " that is no answer");
                    assertTrue(!answered || asked.mayBe().has(value),
                            () -> mapping + " " + words + " has the answer " + value
                                    + " outside what may be");
                }
            }
        }
    }

    /** A value of the side that is converted, asked as it stands: shown only where its answer is
     *  among the strings the other side holds. */
    @Test
    void aValueShownForTheConvertedSideHasItsAnswerAmongTheOthers() {
        List<String> values = valuesAmong(strings(2));
        for (CaseMapping mapping : MAPPINGS) {
            for (List<String> words : partners(strings(2))) {
                Meter meter = meter();
                Language answers = Language.ofWords(words, meter);
                Language shown = CaseMaps.answeringInto(mapping, answers, meter);
                for (String value : values) {
                    String answer = BoundUnderEvaluation.mapped(mapping, value);
                    assertTrue(!shown.has(value) || (answer != null && words.contains(answer)),
                            () -> mapping + " " + words + " shows " + value + " answered "
                                    + answer);
                }
            }
        }
    }

    @Test
    void everyStringMadeFromTheValuesToDeriveFromIsMadeFromAnAnswer() {
        List<String> every = strings(3);
        List<String> values = valuesAmong(every);
        for (CaseMapping mapping : MAPPINGS) {
            for (List<String> words : partners(every).subList(0, 30)) {
                List<String> answers = new ArrayList<>();
                for (String word : words) {
                    String answer = isAValue(word) ? BoundUnderEvaluation.mapped(mapping, word)
                            : null;
                    if (answer != null) {
                        answers.add(answer);
                    }
                }
                Meter meter = meter();
                Language partner = Language.ofWords(words, meter);
                Language derived = WhatAConversionAnswers.of(partner, mapping, meter)
                        .forDerivation();
                Language inside = StringsInsideStrings.standingIn(derived,
                        StringsInsideStrings.Where.ANYWHERE, meter);
                for (String value : values) {
                    assertTrue(!derived.has(value) || answers.contains(value),
                            () -> mapping + " " + words + " derives from " + value);
                    assertTrue(!inside.has(value)
                            || answers.stream().anyMatch(each -> each.contains(value)),
                            () -> mapping + " " + words + " has " + value
                                    + " inside no answer");
                }
            }
        }
    }
}
