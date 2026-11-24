package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The stable starters of a set are those of its code points that the normalization the run time
 * canonicalizes with says are stable starters, whichever way they are cut from the set: a large
 * set is cut with the table of every one, a small one is read a page at a time.
 */
class TheStableStartersOfASetAreTheSameCutOrReadTest {

    private static boolean stable(int codePoint) {
        return !CodePoints.isSurrogate(codePoint)
                && Normalization.isStableStarter(Normalization.Form.NFC, codePoint);
    }

    /** What the normalization says of each code point of {@code over}, asked one at a time. */
    private static CodePoints asked(CodePoints over) {
        List<CodePoints.Range> out = new ArrayList<>();
        int from = -1;
        for (CodePoints.Range range : over.ranges()) {
            for (int cp = range.from(); cp <= range.to(); cp++) {
                if (stable(cp)) {
                    if (from < 0) {
                        from = cp;
                    }
                } else if (from >= 0) {
                    out.add(new CodePoints.Range(from, cp - 1));
                    from = -1;
                }
            }
            if (from >= 0) {
                out.add(new CodePoints.Range(from, range.to()));
                from = -1;
            }
        }
        return new CodePoints(out);
    }

    private static List<CodePoints> sets() {
        List<CodePoints> sets = new ArrayList<>();
        sets.add(CodePoints.EVERYTHING);
        sets.add(CodePoints.of('@').or(CodePoints.SPACES).not());
        sets.add(CodePoints.between(0, 0x2FFFF));
        sets.add(CodePoints.between(0x300, 0x36F));
        sets.add(CodePoints.between(0x1100, 0x11FF));
        sets.add(CodePoints.of('a'));
        sets.add(CodePoints.EVERYTHING.not());
        Random random = new Random(3165);
        for (int i = 0; i < 20; i++) {
            CodePoints set = CodePoints.EVERYTHING.not();
            for (int each = 0; each < 1 + random.nextInt(6); each++) {
                int from = random.nextInt(CodePoints.LAST);
                int length = random.nextBoolean() ? random.nextInt(600)
                        : random.nextInt(300_000);
                set = set.or(CodePoints.between(from, Math.min(CodePoints.LAST, from + length)));
            }
            sets.add(set);
        }
        return sets;
    }

    @Test
    void theSetsAreCutTheSameWhateverTheirSize() {
        for (CodePoints set : sets()) {
            assertEquals(asked(set), StableStarters.within(set), () -> set.ranges().toString());
        }
    }
}
