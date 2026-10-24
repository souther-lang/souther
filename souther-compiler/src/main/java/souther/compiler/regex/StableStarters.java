package souther.compiler.regex;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

/**
 * The code points every string made of which is in Normalization Form C, whatever order they stand
 * in: what a {@code String} holds is canonicalized to NFC where it arrives, so a string of these is
 * held with each code point where it was written.
 *
 * <p>Unicode's quick check (UAX #15) says yes of a string whose every code point is a starter whose
 * quick check is yes, and that is what these are: a canonical combining class of nought, nothing
 * the code point alone turns into, and no composition it can be the later half of. Read off the
 * normalization the run time canonicalizes with, and not kept as a list beside it. A code point
 * standing after the first in what some composite decomposes to is taken out, whichever composite
 * that is, so every code point that can join the one before it is out, and some that cannot may be
 * out too: a string of the ones left is NFC, and a string of others may be NFC all the same.
 */
final class StableStarters {

    private StableStarters() {}

    /** Every such code point. Worked out once, when first asked. */
    static CodePoints all() {
        return Worked.ALL;
    }

    private static final class Worked {

        static final CodePoints ALL = worked();
    }

    private static CodePoints worked() {
        BitSet out = new BitSet(CodePoints.LAST + 1);
        for (int cp = 0; cp <= CodePoints.LAST; cp++) {
            if (CodePoints.isSurrogate(cp)) {
                out.set(cp);
                continue;
            }
            String one = Character.toString(cp);
            if (Normalization.combiningClass(cp) != 0 || !Normalization.nfc(one).equals(one)) {
                out.set(cp);
            }
            String parts = Normalization.normalize(Normalization.Form.NFD, one);
            if (parts.codePointCount(0, parts.length()) > 1
                    && Normalization.nfc(parts).equals(one)) {
                // The halves after the first of a composite: each joins what comes before it.
                parts.codePoints().skip(1).forEach(out::set);
            }
        }
        out.flip(0, CodePoints.LAST + 1);
        List<CodePoints.Range> ranges = new ArrayList<>();
        for (int from = out.nextSetBit(0); from >= 0; ) {
            int to = out.nextClearBit(from) - 1;
            ranges.add(new CodePoints.Range(from, to));
            from = out.nextSetBit(to + 1);
        }
        return new CodePoints(ranges);
    }
}
