package souther.compiler.regex;

import net.unit8.notation199x.pattern.PatternMeaning;
import souther.runtime.Strings;

import java.util.List;

/**
 * How many code points a string a pattern accepts holds, read off the pattern and not off the
 * machine that accepts its strings ({@link Language#lengths}).
 *
 * <p>The pattern is walked once, so what this costs is the size of the pattern and no allowance is
 * spent. What is answered is a range every such string that a {@code String} can hold is in
 * ({@link Bounds}), which is the exact range of the machine of the pattern wherever the lengths
 * stay within what a {@code String} holds.
 */
public final class LengthsOfAPattern {

    /**
     * A range the lengths of the strings a pattern accepts lie in.
     *
     * <p>A bound and not the language's own ends: a length past what a {@code String} holds
     * ({@link Strings#LONGEST_TEXT}) is no length of any string, so the fewest is held at one past
     * it and the most is none. Every string a {@code String} can hold that the pattern accepts has
     * a length in the range, and the range is what the machine says wherever no length passes that
     * — which is the only thing a reader may take of it. The empty string is accepted exactly where
     * the fewest is nought.
     *
     * @param least the fewest code points, at most one past what a string holds
     * @param most  the most code points, or null where a repetition has no ceiling or the ceiling
     *              is past what a string holds
     */
    public record Bounds(long least, Long most) {}

    /** One more than the most code points a {@code String} holds: a length that is past it is held
     *  at it, since what is past it is no string. */
    private static final long PAST_A_STRING = Strings.LONGEST_TEXT + 1L;

    private LengthsOfAPattern() {
    }

    /**
     * The range of the lengths of the strings {@code meaning} accepts, or null where it accepts
     * none.
     */
    public static Bounds of(PatternMeaning meaning) {
        return switch (meaning) {
            case PatternMeaning.Nothing _ -> new Bounds(0, 0L);
            case PatternMeaning.Never _ -> null;
            case PatternMeaning.Symbols symbols ->
                    symbols.held().isEmpty() ? null : new Bounds(1, 1L);
            case PatternMeaning.InTurn(List<PatternMeaning> parts) -> inTurn(parts);
            case PatternMeaning.EitherOf(List<PatternMeaning> arms) -> eitherOf(arms);
            case PatternMeaning.Repeated(PatternMeaning what, int least, int most) ->
                    repeated(of(what), least, most);
        };
    }

    private static Bounds inTurn(List<PatternMeaning> parts) {
        long least = 0;
        Long most = 0L;
        for (PatternMeaning part : parts) {
            Bounds one = of(part);
            if (one == null) {
                return null;
            }
            least = held(least + one.least());
            most = most == null || one.most() == null ? null : heldOrNone(most + one.most());
        }
        return new Bounds(least, most);
    }

    private static Bounds eitherOf(List<PatternMeaning> arms) {
        Bounds out = null;
        for (PatternMeaning arm : arms) {
            Bounds one = of(arm);
            if (one == null) {
                continue;
            }
            out = out == null ? one : new Bounds(Math.min(out.least(), one.least()),
                    out.most() == null || one.most() == null ? null
                            : Math.max(out.most(), one.most()));
        }
        return out;
    }

    /** What is repeated between {@code least} and {@code most} times, where it is a string of
     *  {@code each}'s lengths each time. Nothing is a string, so repeating it none is the one
     *  empty string and repeating it more is no string. */
    private static Bounds repeated(Bounds each, int least, int most) {
        if (each == null) {
            return least == 0 ? new Bounds(0, 0L) : null;
        }
        boolean ceiling = most != PatternMeaning.Repeated.NO_CEILING;
        Long longest = each.most() == null ? (ceiling && most == 0 ? Long.valueOf(0) : null)
                : !ceiling ? (each.most() == 0 ? Long.valueOf(0) : null)
                : heldOrNone(times(most, each.most()));
        return new Bounds(held(times(least, each.least())), longest);
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
