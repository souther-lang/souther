package souther.compiler.regex;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicReferenceArray;

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
 *
 * <p>Worked out a page of code points at a time, as a page is first asked about: a format asks of
 * the code points its steps take, which are seldom more than a few pages. What a composite
 * decomposes to lies in pages of its own, so a page is worked out by reading every composite, once,
 * for the code points that join the one before them.
 */
final class StableStarters {

    private StableStarters() {}

    private static final int PAGE = 256;

    private static final int PAGES = (CodePoints.LAST + 1) / PAGE;

    /** For each page worked out, which of its code points are stable starters. */
    private static final AtomicReferenceArray<long[]> WORKED = new AtomicReferenceArray<>(PAGES);

    /** Every such code point. */
    static CodePoints all() {
        return within(CodePoints.EVERYTHING);
    }

    /** The code points of {@code over} that are such code points. */
    static CodePoints within(CodePoints over) {
        List<CodePoints.Range> out = new ArrayList<>();
        for (CodePoints.Range range : over.ranges()) {
            int cp = range.from();
            while (cp <= range.to()) {
                int from = next(cp, range.to(), true);
                if (from > range.to()) {
                    break;
                }
                int past = next(from, range.to(), false);
                out.add(new CodePoints.Range(from, past - 1));
                cp = past;
            }
        }
        return new CodePoints(out);
    }

    /**
     * The first code point from {@code cp} up to {@code last} that is a stable starter, or that
     * is not one where {@code stable} is false; one past {@code last} where there is none. Read a
     * word of the page's bits at a time.
     */
    private static int next(int cp, int last, boolean stable) {
        while (cp <= last) {
            long[] page = page(cp / PAGE);
            int at = cp % PAGE;
            long word = page[at / Long.SIZE];
            if (!stable) {
                word = ~word;
            }
            word &= -1L << (at % Long.SIZE);
            int start = cp - at % Long.SIZE;
            if (word != 0) {
                return Math.min(start + Long.numberOfTrailingZeros(word), last + 1);
            }
            cp = start + Long.SIZE;
        }
        return last + 1;
    }

    private static long[] page(int index) {
        long[] page = WORKED.get(index);
        if (page == null) {
            page = worked(index);
            WORKED.compareAndSet(index, null, page);
        }
        return page;
    }

    /** Which code points of page {@code index} are stable starters. */
    private static long[] worked(int index) {
        long[] out = new long[PAGE / Long.SIZE];
        int first = index * PAGE;
        for (int cp = first; cp < first + PAGE; cp++) {
            if (CodePoints.isSurrogate(cp) || JOINING.get(cp)) {
                continue;
            }
            String one = Character.toString(cp);
            if (Normalization.combiningClass(cp) == 0 && Normalization.nfc(one).equals(one)) {
                int at = cp - first;
                out[at / Long.SIZE] |= 1L << (at % Long.SIZE);
            }
        }
        return out;
    }

    /**
     * The code points standing after the first in what some composite decomposes to: each joins
     * the code point before it. Worked out once, when a page is first asked about, over every code
     * point that decomposes.
     */
    private static final BitSet JOINING = joining();

    private static BitSet joining() {
        BitSet out = new BitSet(CodePoints.LAST + 1);
        for (int cp = 0; cp <= CodePoints.LAST; cp++) {
            if (CodePoints.isSurrogate(cp)) {
                continue;
            }
            String one = Character.toString(cp);
            String parts = Normalization.normalize(Normalization.Form.NFD, one);
            if (!parts.equals(one) && parts.codePointCount(0, parts.length()) > 1
                    && Normalization.nfc(parts).equals(one)) {
                parts.codePoints().skip(1).forEach(out::set);
            }
        }
        return out;
    }
}
