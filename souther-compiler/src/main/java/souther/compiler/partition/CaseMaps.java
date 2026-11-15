package souther.compiler.partition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntPredicate;

import net.unit8.notation199x.CaseConversion;
import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.regex.ConversionAnswers;
import souther.compiler.regex.Language;
import souther.compiler.semantics.CaseMapping;

/**
 * A case conversion as the map on code points it is exactly one for ({@link CodeMap}), worked out
 * from the run time's own conversion the first time a conversion is asked of, and kept for the
 * rest: the map is a fact of the language and not of the model being read.
 */
public final class CaseMaps {

    private static final Map<CaseMapping, CodeMap> MADE = new ConcurrentHashMap<>();

    private CaseMaps() {
    }

    /**
     * The map {@code mapping} is on the code points it is exactly one for.
     *
     * <p>What it leaves be is what its outermost conversion leaves be. Converting what a
     * conversion answered changes nothing more only for the one conversion done again; of
     * {@code lowercase(uppercase(s))} that is not so ({@code ß} is what it answers of {@code ẞ},
     * and it answers {@code ss} of that), but every code point of its answer is one of the outer
     * conversion's.
     */
    static CodeMap of(CaseMapping mapping) {
        CodeMap had = MADE.get(mapping);
        if (had == null) {
            had = CodeMap.of(text -> BoundUnderEvaluation.mapped(mapping, text),
                    leftAloneEverywhere(mapping));
            CaseMapping outermost = lastDone(mapping);
            if (!outermost.equals(mapping) && !(mapping instanceof CaseMapping.None)) {
                had = had.leavingBe(of(outermost).leftAlone());
            }
            CodeMap raced = MADE.putIfAbsent(mapping, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }

    private static final Map<CaseMapping, ConversionAnswers> ANSWERED = new ConcurrentHashMap<>();

    /**
     * What {@code mapping} answers of each code point, read against the language a question is
     * about ({@link ConversionAnswers}), or null where it is made of more than one conversion: what
     * the second is handed is an answer of the first, which holds code points a question's
     * language does not, so its answers are not said code point by code point.
     */
    static ConversionAnswers answers(CaseMapping mapping) {
        return mapping instanceof CaseMapping.None || mapping.doneSoFar().size() != 1 ? null
                : answersOf(mapping);
    }

    /** What {@code mapping} answers of each code point, of however many conversions it is made. */
    private static ConversionAnswers answersOf(CaseMapping mapping) {
        return ANSWERED.computeIfAbsent(mapping, each -> ConversionAnswers.of(of(each),
                text -> BoundUnderEvaluation.mapped(each, text)));
    }

    /**
     * The strings of {@code over} that {@code mapping} answers as they stand, which are therefore
     * among its answers when it is asked of them: the strings whose code points it leaves alone.
     *
     * <p>Stated of each conversion a mapping is made of. A string of the code points a conversion
     * leaves alone is changed by nothing it does, whatever stands beside them — the code points
     * that depend on their neighbours are not among them — and the form it answers in is the
     * string's own, so a string a {@code String} holds comes back as it is. Of conversions done in
     * turn, a string of the code points every one of them leaves alone comes back from each, and
     * so from all of them. What the outermost leaves alone is not enough: {@code ß} is left alone
     * by an outer lowercase and is what it answers of {@code ẞ}, and the two together answer
     * {@code ss} of it — and the uppercase done first does not leave {@code ß} alone.
     *
     * <p>A language of the code points before the form is applied, as {@code over} is, so it holds
     * sequences that are no value: {@code a} followed by a combining acute is among them where
     * {@code over} holds it. It says of a value that it is an answer, and of nothing made from a
     * string of it: a string inside one of these, or one that converts to one, is made from a
     * sequence no value is and is not shown for that. Whoever derives strings from what is shown
     * leaves this out.
     *
     * @return the strings, which are every one of {@code over} where {@code mapping} converts
     *         nothing, or null past what {@code meter} allows
     */
    static Language answeredAsTheyStand(CaseMapping mapping, Language over, Meter meter) {
        CodePoints everyStep = null;
        for (CaseMapping step : mapping.doneSoFar()) {
            CodePoints alone = of(lastDone(step)).leftAlone();
            everyStep = everyStep == null ? alone : everyStep.and(alone);
        }
        if (everyStep == null) {
            return over;
        }
        Language alone = CodeMap.stringsOf(everyStep, meter);
        return alone == null ? null : over.and(alone, meter);
    }

    /**
     * Whether what {@code mapping} answers of a string holds {@code codePoint} no more times than
     * the string does: the conversion leaves it, sends no other code point of its map to it,
     * answers no code point outside its map with it alone or beside a letter
     * ({@link CodeMap#answeredOutsideTheDomain}) — {@code ŉ} is answered {@code ʼN} in uppercase —
     * and it is no composite a normalization could make of two code points answered apart.
     */
    public static boolean makesNoOccurrenceOf(CaseMapping mapping, int codePoint) {
        CodeMap map = of(mapping);
        CodePoints only = CodePoints.of(codePoint);
        String alone = Character.toString(codePoint);
        return map.domain().has(codePoint) && map.preimage(only).equals(only)
                && map.image(only).equals(only)
                && !map.answeredOutsideTheDomain().has(codePoint)
                && Normalization.normalize(Normalization.Form.NFD, alone).equals(alone);
    }

    /** The one conversion done last of what {@code mapping} makes of a string, done alone. */
    private static CaseMapping lastDone(CaseMapping mapping) {
        return switch (mapping) {
            case CaseMapping.None it -> it;
            case CaseMapping.Lowercase _ -> CaseMapping.LOWERCASE;
            case CaseMapping.Uppercase _ -> CaseMapping.UPPERCASE;
        };
    }

    /**
     * The strings of a side whose conversion by {@code mapping} is among {@code answers}, as far
     * as it is shown: the strings it is exactly a map on whose answer is among them, and the
     * strings it leaves as they stand ({@link #answeredAsTheyStand}) that are among them.
     *
     * <p>The second holds sequences that are no value, so what this says is of a value: that its
     * answer is among {@code answers}. Asked where a string is asked about as it stands, which is
     * an equality; where strings are made from the result, the first alone is values
     * ({@link CodeMap#stringsConvertedInto}).
     *
     * @return the strings, or null past what {@code meter} allows
     */
    static Language answeringInto(CaseMapping mapping, Language answers, Meter meter) {
        Language converted = of(mapping).stringsConvertedInto(answers, meter);
        Language standing = converted == null ? null : answeredAsTheyStand(mapping, answers, meter);
        Language joined = standing == null ? null : converted.or(standing, meter);
        return joined == null ? converted : joined;
    }

    /**
     * Whether {@code mapping} answers a code point as it is in every text, as the tables of the
     * case conversion the run time does it with say: where each conversion it is made of does.
     */
    static IntPredicate leftAloneEverywhere(CaseMapping mapping) {
        return switch (mapping) {
            case CaseMapping.None _ -> codePoint -> true;
            case CaseMapping.Lowercase(CaseMapping of) -> {
                IntPredicate inner = leftAloneEverywhere(of);
                yield codePoint -> CaseConversion.lowercaseLeavesAlone(codePoint)
                        && inner.test(codePoint);
            }
            case CaseMapping.Uppercase(CaseMapping of) -> {
                IntPredicate inner = leftAloneEverywhere(of);
                yield codePoint -> CaseConversion.uppercaseLeavesAlone(codePoint)
                        && inner.test(codePoint);
            }
        };
    }
}
