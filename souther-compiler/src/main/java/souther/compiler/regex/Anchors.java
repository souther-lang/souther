package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * What the anchors in a pattern come to, given that the whole of it must match the whole string.
 *
 * <p>Whole-string matching is what gives an anchor an answer. {@code ^} asks to be at the start of
 * the string, so it is satisfied by every string where nothing before it can take a symbol and by
 * none where everything before it must — the empty string in the first case and
 * {@link PatternMeaning.Never} in the second. {@code $} is the same question about the end.
 *
 * <p><b>Null where neither holds.</b> {@code (a|)^b} has something before the anchor that sometimes
 * takes a symbol and sometimes does not, and the strings it accepts are the ones that took the
 * second way — an answer neither arm above gives, and one the pattern language does not have. So
 * the pattern is refused rather than read as one of them. The same for an anchor under a
 * repetition, where how many copies precede it is not a thing the shape says.
 *
 * <p>Asked once, by the reader, because it is one rule. What leaves the reader is a
 * {@link PatternMeaning}, which has no anchor in it, so nothing downstream asks the question again.
 */
final class Anchors {

    private Anchors() {
    }

    /** The meaning of {@code written} with every anchor read as what it comes to, or null where one
     *  cannot be settled. */
    static PatternMeaning placed(WrittenPattern written) {
        return in(written, Where.YES, Where.YES);
    }

    /** Whether an anchor is at the end it is asking about, as far as the shape says. */
    private enum Where { YES, NO, UNSETTLED }

    private static PatternMeaning in(WrittenPattern written, Where atStart, Where atEnd) {
        return switch (written) {
            case WrittenPattern.Meant it -> it.meaning();
            case WrittenPattern.Anchor it -> switch (it.end() ? atEnd : atStart) {
                case YES -> new PatternMeaning.Nothing();
                // {@code ^} asks to be at the start of the string and there is one such place, so
                // anything that must take a symbol before it leaves no string at all. {@code $} is
                // not the mirror of that: it is satisfied at the end and also just before a line
                // terminator that ends the string, so {@code $[^a]} accepts the one string whose
                // only symbol is that terminator. The language has no shape for a place defined by
                // what comes after it, so the pattern is refused.
                case NO -> it.end() ? null : new PatternMeaning.Never();
                case UNSETTLED -> null;
            };
            // Every arm of a choice begins where the choice begins and ends where it ends.
            case WrittenPattern.EitherOf it -> {
                List<PatternMeaning> arms = new ArrayList<>();
                for (WrittenPattern each : it.arms()) {
                    PatternMeaning made = in(each, atStart, atEnd);
                    if (made == null) {
                        yield null;
                    }
                    arms.add(made);
                }
                yield new PatternMeaning.EitherOf(arms);
            }
            case WrittenPattern.InTurn it -> inTurn(it, atStart, atEnd);
            case WrittenPattern.Repeated it when !holdsOne(it.what()) ->
                    new PatternMeaning.Repeated(in(it.what(), atStart, atEnd), it.least(), it.most());
            // One copy is the thing itself and stands where the repetition stands. Any other count
            // leaves how many copies come before the anchor to the string being matched, which is
            // not a thing the shape of the pattern answers.
            case WrittenPattern.Repeated it when it.least() == 1 && it.most() == 1 ->
                    in(it.what(), atStart, atEnd);
            case WrittenPattern.Repeated _ -> null;
        };
    }

    private static PatternMeaning inTurn(WrittenPattern.InTurn it, Where atStart, Where atEnd) {
        int count = it.parts().size();
        // What stands before each part and after it, gathered once from each end. Asked afresh of
        // every part, the sides are read again for each of them, and a literal written out a
        // symbol at a time costs its length squared.
        boolean[] mayBefore = new boolean[count + 1];
        boolean[] mustBefore = new boolean[count + 1];
        mustBefore[0] = true;
        for (int at = 0; at < count; at++) {
            WrittenPattern part = it.parts().get(at);
            mayBefore[at + 1] = mayBefore[at] || mayTake(part);
            mustBefore[at + 1] = mustBefore[at] && mustTake(part);
        }
        boolean[] mayAfter = new boolean[count + 1];
        boolean[] mustAfter = new boolean[count + 1];
        mustAfter[count] = true;
        for (int at = count - 1; at >= 0; at--) {
            WrittenPattern part = it.parts().get(at);
            mayAfter[at] = mayAfter[at + 1] || mayTake(part);
            mustAfter[at] = mustAfter[at + 1] && mustTake(part);
        }
        List<PatternMeaning> parts = new ArrayList<>();
        for (int at = 0; at < count; at++) {
            PatternMeaning made = in(it.parts().get(at),
                    beyond(mayBefore[at], mustBefore[at], atStart),
                    beyond(mayAfter[at + 1], mustAfter[at + 1], atEnd));
            if (made == null) {
                return null;
            }
            // An anchor that asks for nothing leaves nothing in the sequence, so `^abc$` means what
            // `abc` means and is the same tree.
            if (!(made instanceof PatternMeaning.Nothing)) {
                parts.add(made);
            }
        }
        return switch (parts.size()) {
            case 0 -> new PatternMeaning.Nothing();
            case 1 -> parts.get(0);
            default -> new PatternMeaning.InTurn(parts);
        };
    }

    /**
     * Where a part stands, given what is on that side of it and where they all stand together.
     *
     * <p>Nothing on that side takes a symbol, so the part stands where they all do. Everything on
     * that side must take one, so it does not. Anything in between and the answer belongs to a
     * string rather than to the pattern.
     *
     * @param anyTakes whether something on that side may take a symbol
     * @param allTake  whether everything on that side must take one
     */
    private static Where beyond(boolean anyTakes, boolean allTake, Where outer) {
        if (!anyTakes) {
            return outer;
        }
        return allTake ? Where.NO : Where.UNSETTLED;
    }

    /** Whether it accepts any string of one symbol or more. */
    private static boolean mayTake(WrittenPattern written) {
        return switch (written) {
            case WrittenPattern.Meant it -> mayTake(it.meaning());
            case WrittenPattern.Anchor _ -> false;
            case WrittenPattern.InTurn it -> it.parts().stream().anyMatch(Anchors::mayTake);
            case WrittenPattern.EitherOf it -> it.arms().stream().anyMatch(Anchors::mayTake);
            case WrittenPattern.Repeated it ->
                    (it.most() == PatternMeaning.Repeated.NO_CEILING || it.most() > 0)
                            && mayTake(it.what());
        };
    }

    private static boolean mayTake(PatternMeaning meaning) {
        return switch (meaning) {
            case PatternMeaning.Nothing _, PatternMeaning.Never _ -> false;
            case PatternMeaning.Symbols _ -> true;
            case PatternMeaning.InTurn it -> it.parts().stream().anyMatch(Anchors::mayTake);
            case PatternMeaning.EitherOf it -> it.arms().stream().anyMatch(Anchors::mayTake);
            case PatternMeaning.Repeated it ->
                    (it.unbounded() || it.most() > 0) && mayTake(it.what());
        };
    }

    /** Whether every string it accepts has a symbol in it. */
    private static boolean mustTake(WrittenPattern written) {
        return switch (written) {
            case WrittenPattern.Meant it -> mustTake(it.meaning());
            case WrittenPattern.Anchor _ -> false;
            case WrittenPattern.InTurn it -> it.parts().stream().anyMatch(Anchors::mustTake);
            case WrittenPattern.EitherOf it -> it.arms().stream().allMatch(Anchors::mustTake);
            case WrittenPattern.Repeated it -> it.least() > 0 && mustTake(it.what());
        };
    }

    private static boolean mustTake(PatternMeaning meaning) {
        return switch (meaning) {
            case PatternMeaning.Nothing _ -> false;
            // It accepts no string, so none of the strings it accepts is the empty one — which is
            // the answer that leaves an anchor beyond it settled rather than unsettled.
            case PatternMeaning.Never _, PatternMeaning.Symbols _ -> true;
            case PatternMeaning.InTurn it -> it.parts().stream().anyMatch(Anchors::mustTake);
            case PatternMeaning.EitherOf it -> it.arms().stream().allMatch(Anchors::mustTake);
            case PatternMeaning.Repeated it -> it.least() > 0 && mustTake(it.what());
        };
    }

    private static boolean holdsOne(WrittenPattern written) {
        return switch (written) {
            case WrittenPattern.Meant _ -> false;
            case WrittenPattern.Anchor _ -> true;
            case WrittenPattern.InTurn it -> it.parts().stream().anyMatch(Anchors::holdsOne);
            case WrittenPattern.EitherOf it -> it.arms().stream().anyMatch(Anchors::holdsOne);
            case WrittenPattern.Repeated it -> holdsOne(it.what());
        };
    }
}
