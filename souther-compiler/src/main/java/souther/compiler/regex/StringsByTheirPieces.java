package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;

/**
 * The strings a language holds some piece of, or every piece of, when they are parted at one code
 * point.
 *
 * <p>Said of the whole string and not of a piece: the pieces are the stretches between the
 * separators, there is always at least one, and one may be empty. A piece holds no separator, so
 * it is in a language where it is in what that language leaves once the separator is taken out of
 * every set of symbols it names ({@link #withoutTheSeparator}) — the strings of the language that
 * hold none, which is the language met with the strings of no separator and needs no meet to say.
 *
 * <p>Of the pieces from index {@code from} up to, and not including, {@code until}: what dropping
 * {@code from} of them and taking {@code until - from} leaves. Where the string has none of
 * them, none is asked about: some of them is false and every one is true. {@link #TO_THE_LAST}
 * as {@code until} is no end.
 */
public final class StringsByTheirPieces {

    /** The window that runs to the last piece. */
    public static final int TO_THE_LAST = -1;

    private static final int NO_CEILING = PatternMeaning.Repeated.NO_CEILING;

    private StringsByTheirPieces() {
    }

    /** The strings with a piece, in the window, in {@code piece}. */
    public static PatternMeaning someIn(PatternMeaning piece, int separator, int from,
                                        int until) {
        requireAWindow(from, until);
        PatternMeaning field = fieldOf(separator);
        return new PatternMeaning.InTurn(List.of(
                new PatternMeaning.Repeated(followedBySeparator(field, separator), from,
                        until == TO_THE_LAST ? NO_CEILING : until - 1),
                withoutTheSeparator(piece, separator),
                restAfterASeparator(field, separator)));
    }

    /** The strings every piece of which, in the window, is in {@code piece}. */
    public static PatternMeaning everyIn(PatternMeaning piece, int separator, int from,
                                         int until) {
        requireAWindow(from, until);
        PatternMeaning field = fieldOf(separator);
        PatternMeaning inIt = withoutTheSeparator(piece, separator);
        PatternMeaning lead = new PatternMeaning.Repeated(
                followedBySeparator(field, separator), from, from);
        List<PatternMeaning> arms = new ArrayList<>();
        // Fewer pieces than the window starts at: none is asked about.
        if (from > 0) {
            arms.add(new PatternMeaning.InTurn(List.of(field,
                    new PatternMeaning.Repeated(separatedFrom(field, separator), 0, from - 1))));
        }
        if (until == TO_THE_LAST) {
            arms.add(new PatternMeaning.InTurn(List.of(lead, inIt,
                    new PatternMeaning.Repeated(separatedFrom(inIt, separator), 0, NO_CEILING))));
        } else {
            int width = until - from;
            // The string ends inside the window, every piece it has there in the language.
            if (width >= 2) {
                arms.add(new PatternMeaning.InTurn(List.of(lead, inIt,
                        new PatternMeaning.Repeated(separatedFrom(inIt, separator), 0,
                                width - 2))));
            }
            // The window is full, and what comes after it is anything.
            arms.add(new PatternMeaning.InTurn(List.of(lead, inIt,
                    new PatternMeaning.Repeated(separatedFrom(inIt, separator), width - 1,
                            width - 1),
                    restAfterASeparator(field, separator))));
        }
        return arms.size() == 1 ? arms.getFirst() : new PatternMeaning.EitherOf(arms);
    }

    private static void requireAWindow(int from, int until) {
        if (from < 0 || (until != TO_THE_LAST && until <= from)) {
            throw new IllegalArgumentException(
                    "a window holds a piece: " + from + " up to " + until);
        }
    }

    /** What {@code meaning} accepts of the strings that hold no {@code separator}. */
    static PatternMeaning withoutTheSeparator(PatternMeaning meaning, int separator) {
        return switch (meaning) {
            case PatternMeaning.Nothing _, PatternMeaning.Never _ -> meaning;
            case PatternMeaning.Symbols(CodePoints held) ->
                    new PatternMeaning.Symbols(held.and(CodePoints.of(separator).not()));
            case PatternMeaning.InTurn(List<PatternMeaning> parts) ->
                    new PatternMeaning.InTurn(parts.stream()
                            .map(part -> withoutTheSeparator(part, separator)).toList());
            case PatternMeaning.EitherOf(List<PatternMeaning> arms) ->
                    new PatternMeaning.EitherOf(arms.stream()
                            .map(arm -> withoutTheSeparator(arm, separator)).toList());
            case PatternMeaning.Repeated(PatternMeaning what, int least, int most) ->
                    new PatternMeaning.Repeated(withoutTheSeparator(what, separator), least, most);
        };
    }

    /** Any string that holds no separator: what a piece may be. */
    private static PatternMeaning fieldOf(int separator) {
        return new PatternMeaning.Repeated(
                new PatternMeaning.Symbols(CodePoints.of(separator).not()), 0, NO_CEILING);
    }

    private static PatternMeaning separatorOf(int separator) {
        return new PatternMeaning.Symbols(CodePoints.of(separator));
    }

    /** One piece and the separator after it. */
    private static PatternMeaning followedBySeparator(PatternMeaning piece, int separator) {
        return new PatternMeaning.InTurn(List.of(piece, separatorOf(separator)));
    }

    /** The separator and one piece after it. */
    private static PatternMeaning separatedFrom(PatternMeaning piece, int separator) {
        return new PatternMeaning.InTurn(List.of(separatorOf(separator), piece));
    }

    /** Any number of pieces after a separator, or none. */
    private static PatternMeaning restAfterASeparator(PatternMeaning field, int separator) {
        return new PatternMeaning.Repeated(separatedFrom(field, separator), 0, NO_CEILING);
    }
}
