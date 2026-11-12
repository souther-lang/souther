package souther.compiler.partition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import souther.compiler.evaluate.BoundUnderEvaluation;
import net.unit8.notation199x.pattern.Meter;

import souther.compiler.regex.CodeMap;
import souther.compiler.regex.Language;
import souther.compiler.semantics.CaseMapping;

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
            had = CodeMap.of(text -> BoundUnderEvaluation.mapped(mapping, text));
            CaseMapping outermost = switch (mapping) {
                case CaseMapping.None it -> it;
                case CaseMapping.Lowercase _ -> CaseMapping.LOWERCASE;
                case CaseMapping.Uppercase _ -> CaseMapping.UPPERCASE;
            };
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
     * <p>Stated of one conversion and not of two. A string of the code points a conversion leaves
     * alone is changed by nothing it does, whatever stands beside them — the code points that
     * depend on their neighbours are not among them — and the form it answers in is the string's
     * own, so a string a {@code String} holds comes back as it is. Of two conversions done in turn
     * that does not follow: {@code ß} is left alone by the outer lowercase and is what it answers
     * of {@code ẞ}, and the two together answer {@code ss} of it. So none is answered for those.
     *
     * <p>A language of the code points before the form is applied, as {@code over} is: the strings
     * of it that are no value are among these as they are among its own, and what is asked of the
     * values of a language is asked of those held as written.
     *
     * @return the strings, which are none where {@code mapping} is not one conversion, or null
     *         past what {@code meter} allows
     */
    static Language answeredAsTheyStand(CaseMapping mapping, Language over, Meter meter) {
        if (mapping.doneSoFar().size() != 1) {
            return Language.EVERY_STRING.not(meter);
        }
        Language alone = CodeMap.stringsOf(of(mapping).leftAlone(), meter);
        return alone == null ? null : over.and(alone, meter);
    }
}
