package souther.compiler.regex;

import net.unit8.notation199x.pattern.PatternMeaning;
import souther.runtime.Strings;

import java.util.List;

/**
 * How many code points a string a pattern accepts holds, read off the pattern and not off the
 * machine that accepts its strings ({@link Language#lengths}).
 *
 * <p>The pattern is walked once, so what this costs is the size of the pattern and no allowance is
 * spent. What is answered is the fewest and the most code points a string it accepts holds, the
 * most being null where a repetition has no ceiling or the length passes what a {@code String}
 * holds. The empty string is accepted exactly where the fewest is nought.
 */
public final class LengthsOfAPattern {

    /** One more than the most code points a {@code String} holds: a length that is past it is held
     *  at it, since what is past it is no string. */
    private static final long PAST_A_STRING = Strings.LONGEST_TEXT + 1L;

    private LengthsOfAPattern() {
    }

    /**
     * The range of the lengths of the strings {@code meaning} accepts, or null where it accepts
     * none.
     */
    public static Language.Ends of(PatternMeaning meaning) {
        return switch (meaning) {
            case PatternMeaning.Nothing _ -> new Language.Ends(0, 0L);
            case PatternMeaning.Never _ -> null;
            case PatternMeaning.Symbols symbols ->
                    symbols.held().isEmpty() ? null : new Language.Ends(1, 1L);
            case PatternMeaning.InTurn(List<PatternMeaning> parts) -> inTurn(parts);
            case PatternMeaning.EitherOf(List<PatternMeaning> arms) -> eitherOf(arms);
            case PatternMeaning.Repeated(PatternMeaning what, int least, int most) ->
                    repeated(of(what), least, most);
        };
    }

    private static Language.Ends inTurn(List<PatternMeaning> parts) {
        long least = 0;
        Long most = 0L;
        for (PatternMeaning part : parts) {
            Language.Ends one = of(part);
            if (one == null) {
                return null;
            }
            least = held(least + one.least());
            most = most == null || one.most() == null ? null : heldOrNone(most + one.most());
        }
        return new Language.Ends(least, most);
    }

    private static Language.Ends eitherOf(List<PatternMeaning> arms) {
        Language.Ends out = null;
        for (PatternMeaning arm : arms) {
            Language.Ends one = of(arm);
            if (one == null) {
                continue;
            }
            out = out == null ? one : new Language.Ends(Math.min(out.least(), one.least()),
                    out.most() == null || one.most() == null ? null
                            : Math.max(out.most(), one.most()));
        }
        return out;
    }

    /** What is repeated between {@code least} and {@code most} times, where it is a string of
     *  {@code each}'s lengths each time. Nothing is a string, so repeating it none is the one
     *  empty string and repeating it more is no string. */
    private static Language.Ends repeated(Language.Ends each, int least, int most) {
        if (each == null) {
            return least == 0 ? new Language.Ends(0, 0L) : null;
        }
        boolean ceiling = most != PatternMeaning.Repeated.NO_CEILING;
        Long longest = each.most() == null ? (ceiling && most == 0 ? Long.valueOf(0) : null)
                : !ceiling ? (each.most() == 0 ? Long.valueOf(0) : null)
                : heldOrNone(times(most, each.most()));
        return new Language.Ends(held(times(least, each.least())), longest);
    }

    private static long times(long count, long length) {
        return length == 0 || count == 0 ? 0 : count > PAST_A_STRING / length
                ? PAST_A_STRING : count * length;
    }

    private static long held(long length) {
        return Math.min(length, PAST_A_STRING);
    }

    /** {@code length}, or null where it is past what a string holds, which is a ceiling nothing
     *  reaches. */
    private static Long heldOrNone(long length) {
        return length >= PAST_A_STRING ? null : length;
    }
}
