package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * What the anchors in a pattern come to, given that the whole of it must match the whole string.
 *
 * <p>Whole-string matching is what gives an anchor an answer. {@code ^} asks to be at the start of
 * the string, so it is satisfied by every string where nothing before it can take a symbol and by
 * none where everything before it must — the empty string in the first case and
 * {@link PatternSyntax.Never} in the second. {@code $} is the same question about the end.
 *
 * <p><b>Null where neither holds.</b> {@code (a|)^b} has something before the anchor that sometimes
 * takes a symbol and sometimes does not, and the strings it accepts are the ones that took the
 * second way — an answer neither arm above gives, and one this compiler has no shape for. So the
 * pattern is not read at all rather than read as one of them. The same for an anchor under a
 * repetition, where how many copies precede it is not a thing the shape says.
 *
 * <p>Asked in one place because it is one rule. Whoever reads a pattern asks whether it can be
 * settled and whoever builds it asks what it comes to, and two spellings of the same rule would be
 * two answers to which strings a pattern accepts.
 */
final class Anchors {

    private Anchors() {
    }

    /** The same pattern with every anchor read as what it comes to, or null where one cannot be
     *  settled. */
    static PatternSyntax placed(PatternSyntax syntax) {
        return in(syntax, Where.YES, Where.YES);
    }

    /** Whether an anchor is at the end it is asking about, as far as the shape says. */
    private enum Where { YES, NO, UNSETTLED }

    private static PatternSyntax in(PatternSyntax syntax, Where atStart, Where atEnd) {
        return switch (syntax) {
            case PatternSyntax.Nothing _, PatternSyntax.Never _, PatternSyntax.Symbols _ -> syntax;
            case PatternSyntax.Anchor it -> switch (it.end() ? atEnd : atStart) {
                case YES -> new PatternSyntax.Nothing();
                // {@code ^} asks to be at the start of the string and there is one such place, so
                // anything that must take a symbol before it leaves no string at all. {@code $} is
                // not the mirror of that: it is satisfied at the end and also just before a line
                // terminator that ends the string, so {@code $[^a]} accepts the one string whose
                // only symbol is that terminator. This compiler has no shape for a place defined
                // by what comes after it, so the pattern is not read.
                case NO -> it.end() ? null : new PatternSyntax.Never();
                case UNSETTLED -> null;
            };
            // Every arm of a choice begins where the choice begins and ends where it ends.
            case PatternSyntax.EitherOf it -> {
                List<PatternSyntax> arms = new ArrayList<>();
                for (PatternSyntax each : it.arms()) {
                    PatternSyntax made = in(each, atStart, atEnd);
                    if (made == null) {
                        yield null;
                    }
                    arms.add(made);
                }
                yield new PatternSyntax.EitherOf(arms);
            }
            case PatternSyntax.InTurn it -> inTurn(it, atStart, atEnd);
            case PatternSyntax.Repeated it when !holdsOne(it.what()) -> it;
            // One copy is the thing itself and stands where the repetition stands. Any other count
            // leaves how many copies come before the anchor to the string being matched, which is
            // not a thing the shape of the pattern answers.
            case PatternSyntax.Repeated it when it.least() == 1 && it.most() == 1 ->
                    in(it.what(), atStart, atEnd);
            case PatternSyntax.Repeated _ -> null;
        };
    }

    private static PatternSyntax inTurn(PatternSyntax.InTurn it, Where atStart, Where atEnd) {
        List<PatternSyntax> parts = new ArrayList<>();
        for (int at = 0; at < it.parts().size(); at++) {
            PatternSyntax made = in(it.parts().get(at),
                    beyond(it.parts().subList(0, at), atStart),
                    beyond(it.parts().subList(at + 1, it.parts().size()), atEnd));
            if (made == null) {
                return null;
            }
            parts.add(made);
        }
        return new PatternSyntax.InTurn(parts);
    }

    /**
     * Where a part stands, given what is on that side of it and where they all stand together.
     *
     * <p>Nothing on that side takes a symbol, so the part stands where they all do. Everything on
     * that side must take one, so it does not. Anything in between and the answer belongs to a
     * string rather than to the pattern.
     */
    private static Where beyond(List<PatternSyntax> side, Where outer) {
        boolean anyTakes = false;
        boolean allTake = true;
        for (PatternSyntax each : side) {
            anyTakes = anyTakes || mayTake(each);
            allTake = allTake && mustTake(each);
        }
        if (!anyTakes) {
            return outer;
        }
        return allTake ? Where.NO : Where.UNSETTLED;
    }

    /** Whether it accepts any string of one symbol or more. */
    private static boolean mayTake(PatternSyntax syntax) {
        return switch (syntax) {
            case PatternSyntax.Nothing _, PatternSyntax.Never _, PatternSyntax.Anchor _ -> false;
            case PatternSyntax.Symbols _ -> true;
            case PatternSyntax.InTurn it -> it.parts().stream().anyMatch(Anchors::mayTake);
            case PatternSyntax.EitherOf it -> it.arms().stream().anyMatch(Anchors::mayTake);
            case PatternSyntax.Repeated it ->
                    (it.unbounded() || it.most() > 0) && mayTake(it.what());
        };
    }

    /** Whether every string it accepts has a symbol in it. */
    private static boolean mustTake(PatternSyntax syntax) {
        return switch (syntax) {
            case PatternSyntax.Nothing _, PatternSyntax.Anchor _ -> false;
            // It accepts no string, so none of the strings it accepts is the empty one — which is
            // the answer that leaves an anchor beyond it settled rather than unsettled.
            case PatternSyntax.Never _, PatternSyntax.Symbols _ -> true;
            case PatternSyntax.InTurn it -> it.parts().stream().anyMatch(Anchors::mustTake);
            case PatternSyntax.EitherOf it -> it.arms().stream().allMatch(Anchors::mustTake);
            case PatternSyntax.Repeated it -> it.least() > 0 && mustTake(it.what());
        };
    }

    private static boolean holdsOne(PatternSyntax syntax) {
        return switch (syntax) {
            case PatternSyntax.Nothing _, PatternSyntax.Never _, PatternSyntax.Symbols _ -> false;
            case PatternSyntax.Anchor _ -> true;
            case PatternSyntax.InTurn it -> it.parts().stream().anyMatch(Anchors::holdsOne);
            case PatternSyntax.EitherOf it -> it.arms().stream().anyMatch(Anchors::holdsOne);
            case PatternSyntax.Repeated it -> holdsOne(it.what());
        };
    }
}
