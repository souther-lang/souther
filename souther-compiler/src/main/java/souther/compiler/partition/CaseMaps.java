package souther.compiler.partition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntPredicate;

import net.unit8.notation199x.CaseConversion;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.regex.Language;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.values.TextExtents;

/**
 * A case conversion as the map on code points it is exactly one for ({@link CodeMap}), worked out
 * from the run time's own conversion the first time a conversion is asked of, and kept for the
 * rest: the map is a fact of the language and not of the model being read.
 */
final class CaseMaps {

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
     * The strings a run is shown to get past {@code mapping} at: the strings it is exactly a map
     * on, and the strings it leaves as they stand ({@link #answeredAsTheyStand}), whose answer is
     * the string itself and so is no longer than it. Every other string may stop the run there,
     * by the answer being longer than a {@code String} holds.
     *
     * <p>Asked whether the run gets past at a string, which is a question of a value: the second
     * kind holds sequences that are no value. A string a witness holds is chosen from
     * {@link CodeMap#strings}, which is values alone.
     *
     * @return the strings, or null past what {@code meter} allows
     */
    static Language gottenPastExactly(CaseMapping mapping, Meter meter) {
        Language exact = of(mapping).strings(meter);
        Language standing = exact == null ? null
                : answeredAsTheyStand(mapping, Language.EVERY_STRING, meter);
        Language joined = standing == null ? null : exact.or(standing, meter);
        return joined == null ? exact : joined;
    }

    /**
     * A length up to which a run is shown to get past {@code mapping} at every string, whatever
     * code points it holds: at a string of no more code points than this, none of its conversions
     * answers more than a {@code String} holds.
     *
     * <p>A bound and not the longest such length: a longer string may be gotten past as well, and
     * nothing here says one is not. A conversion's answer, in every canonical form, holds no more
     * code points than the text it is handed times what the run time's tables say one code point
     * comes to at most ({@link CaseConversion.Growth}), as written or decomposed. So a text of no
     * more than a {@code String} holds over that converts and is canonicalized within it, and of
     * conversions done in turn the factors multiply: each is handed what the one before answered.
     * The code points that come to the most in one conversion need not be the ones that do in the
     * next, so the product is a bound on what the conversions in turn make of a code point and may
     * be more than any comes to.
     */
    static long gottenPastAtEveryStringUpTo(CaseMapping mapping) {
        return switch (mapping) {
            case CaseMapping.None _ -> TextExtents.LONGEST_STRING;
            case CaseMapping.Lowercase(CaseMapping of) ->
                    gottenPastAtEveryStringUpTo(of) / most(CaseConversion.lowercaseGrowth());
            case CaseMapping.Uppercase(CaseMapping of) ->
                    gottenPastAtEveryStringUpTo(of) / most(CaseConversion.uppercaseGrowth());
        };
    }

    /** The most code points one code point comes to in a conversion's answer, in any form. */
    private static long most(CaseConversion.Growth growth) {
        return Math.max(growth.mapped(), growth.decomposed());
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
