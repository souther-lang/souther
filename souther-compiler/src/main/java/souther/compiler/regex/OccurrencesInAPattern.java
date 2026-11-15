package souther.compiler.regex;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.OptionalLong;

/**
 * The most times one code point stands in a string a pattern accepts, read off the pattern.
 *
 * <p>Walked once, like {@link LengthsOfAPattern}, so what this costs is the size of the pattern and
 * no allowance is spent. The answer is a ceiling every accepted string keeps to. It is the exact
 * most wherever a part that can hold the code point can be taken as often as the pattern lets it be,
 * which is every pattern this is asked of in practice, and it is never below the most: a reader
 * that takes it as an upper bound is right whichever it is.
 *
 * <p>A repetition holds the code point as often as its body does, as many times over as it may be
 * repeated. What has no ceiling holds the code point without one only where its body can hold it
 * at all, so {@code [a-z]*@[a-z]*} holds {@code @} once, and {@code [a-z@]*} holds it without a
 * ceiling.
 */
public final class OccurrencesInAPattern {

    /** What the walk of a part comes to: no string at all, or a count that may have no ceiling. */
    private record Most(boolean accepts, boolean ceiling, long times) {

        static final Most NO_STRING = new Most(false, true, 0);
        static final Most NONE = new Most(true, true, 0);
        static final Most WITHOUT_A_CEILING = new Most(true, false, 0);

        static Most of(long times) {
            return new Most(true, true, times);
        }

        boolean holdsNone() {
            return ceiling && times == 0;
        }

        Most plus(Most other) {
            if (!accepts || !other.accepts) {
                return NO_STRING;
            }
            // A sum past what a long holds is no ceiling any string reaches.
            return ceiling && other.ceiling && times <= Long.MAX_VALUE - other.times
                    ? of(times + other.times) : WITHOUT_A_CEILING;
        }

        Most max(Most other) {
            if (!accepts) {
                return other;
            }
            if (!other.accepts) {
                return this;
            }
            if (!ceiling || !other.ceiling) {
                return WITHOUT_A_CEILING;
            }
            return of(Math.max(times, other.times));
        }
    }

    private OccurrencesInAPattern() {
    }

    /**
     * The most times {@code codePoint} stands in a string {@code meaning} accepts, or empty where
     * some accepted string holds it more often than any number says. Nought where the pattern
     * accepts no string, since no accepted string holds it at all.
     */
    public static OptionalLong most(PatternMeaning meaning, int codePoint) {
        Most out = of(meaning, codePoint);
        return out.accepts && !out.ceiling ? OptionalLong.empty() : OptionalLong.of(out.times);
    }

    /** The most symbols a set may hold for its symbols to be the ones a caller asks about: a
     *  written character or a short list of them, and not a class a code point is only one of. */
    private static final long SMALLEST_CLASS_ASKED_ABOUT = 8;

    /** How many code points are asked about, whatever the pattern. */
    private static final int MOST_ASKED_ABOUT = 16;

    /**
     * The code points a pattern writes out, each with the most times it stands in a string the
     * pattern accepts, where that has a ceiling: the symbols of every set of at most eight, which
     * is a character written in the pattern or a short list of them, and the first sixteen of them
     * in the order they are met. A code point a pattern does not write out is one the pattern
     * admits only as one of a larger class, and what a reader wants of it is asked with
     * {@link #most}.
     */
    public static Map<Integer, Long> writtenOutWithACeiling(PatternMeaning meaning) {
        Set<Integer> written = new LinkedHashSet<>();
        writtenOut(meaning, written);
        Map<Integer, Long> out = new LinkedHashMap<>();
        for (int each : written) {
            OptionalLong most = most(meaning, each);
            if (most.isPresent()) {
                out.put(each, most.getAsLong());
            }
        }
        return out;
    }

    private static void writtenOut(PatternMeaning meaning, Set<Integer> into) {
        switch (meaning) {
            case PatternMeaning.Nothing _, PatternMeaning.Never _ -> { }
            case PatternMeaning.Symbols symbols -> {
                if (symbols.held().size() <= SMALLEST_CLASS_ASKED_ABOUT) {
                    for (CodePoints.Range run : symbols.held().ranges()) {
                        for (int at = run.from(); at <= run.to()
                                && into.size() < MOST_ASKED_ABOUT; at++) {
                            into.add(at);
                        }
                    }
                }
            }
            case PatternMeaning.InTurn(List<PatternMeaning> parts) ->
                    parts.forEach(part -> writtenOut(part, into));
            case PatternMeaning.EitherOf(List<PatternMeaning> arms) ->
                    arms.forEach(arm -> writtenOut(arm, into));
            case PatternMeaning.Repeated(PatternMeaning what, int _, int _) ->
                    writtenOut(what, into);
        }
    }

    private static Most of(PatternMeaning meaning, int codePoint) {
        return switch (meaning) {
            case PatternMeaning.Nothing _ -> Most.NONE;
            case PatternMeaning.Never _ -> Most.NO_STRING;
            case PatternMeaning.Symbols symbols -> symbols.held().isEmpty() ? Most.NO_STRING
                    : Most.of(symbols.held().has(codePoint) ? 1 : 0);
            case PatternMeaning.InTurn(List<PatternMeaning> parts) -> {
                Most sum = Most.NONE;
                for (PatternMeaning part : parts) {
                    sum = sum.plus(of(part, codePoint));
                }
                yield sum;
            }
            case PatternMeaning.EitherOf(List<PatternMeaning> arms) -> {
                Most largest = Most.NO_STRING;
                for (PatternMeaning arm : arms) {
                    largest = largest.max(of(arm, codePoint));
                }
                yield largest;
            }
            case PatternMeaning.Repeated(PatternMeaning what, int least, int most) ->
                    repeated(of(what, codePoint), least, most);
        };
    }

    /** What the body comes to, repeated between {@code least} and {@code most} times. Nothing is
     *  a string, so a body no string satisfies is the empty string repeated none, and no string
     *  repeated more. */
    private static Most repeated(Most body, int least, int most) {
        if (!body.accepts) {
            return least == 0 ? Most.NONE : Most.NO_STRING;
        }
        if (body.holdsNone()) {
            return Most.NONE;
        }
        if (most == 0) {
            return Most.NONE;
        }
        if (!body.ceiling || most == PatternMeaning.Repeated.NO_CEILING) {
            return Most.WITHOUT_A_CEILING;
        }
        return body.times > Long.MAX_VALUE / most ? Most.WITHOUT_A_CEILING
                : Most.of(body.times * most);
    }
}
