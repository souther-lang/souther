package souther.compiler.regex;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;

import java.util.ArrayList;
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
 * tables of the normalization the run time canonicalizes with
 * ({@link Normalization#isStableStarter}), and not kept as a list beside it.
 *
 * <p>Worked out a page of code points at a time, as a page is first asked about: a format asks of
 * the code points its steps take, which are seldom more than a few pages.
 */
final class StableStarters {

    private StableStarters() {}

    private static final int PAGE = 256;

    private static final int PAGES = (CodePoints.LAST + 1) / PAGE;

    /** For each page worked out, which of its code points are stable starters. */
    private static final AtomicReferenceArray<long[]> WORKED = new AtomicReferenceArray<>(PAGES);

    /** Every such code point, worked out once. */
    static CodePoints all() {
        return Every.THEM;
    }

    /** Held apart so that the pages are not all worked out until the first ask for every one. */
    private static final class Every {
        static final CodePoints THEM = readOff(CodePoints.EVERYTHING);
    }

    /**
     * The least number of code points a set holds for {@link #within} to cut it with
     * {@link #all} instead of reading its pages: a page walk costs a word for each
     * {@code Long.SIZE} code points of the set, and the cut one comparison for each range of
     * either set, so a set of a few planes is cheaper cut, and one of a few pages is cheaper
     * read, which also leaves the pages it does not ask about unworked.
     */
    private static final long CUT_FROM = 1L << 16;

    /** Whether {@code over} holds such a code point, which stops at the first one. */
    static boolean anyWithin(CodePoints over) {
        for (CodePoints.Range range : over.ranges()) {
            if (next(range.from(), range.to(), true) <= range.to()) {
                return true;
            }
        }
        return false;
    }

    /** The code points of {@code over} that are such code points. */
    static CodePoints within(CodePoints over) {
        return over.size() >= CUT_FROM ? all().and(over) : readOff(over);
    }

    /** The same, read a page at a time off the pages worked out. */
    private static CodePoints readOff(CodePoints over) {
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
            int pageStart = cp - cp % PAGE;
            for (int index = cp % PAGE / Long.SIZE; index < page.length; index++) {
                long word = stable ? page[index] : ~page[index];
                int start = pageStart + index * Long.SIZE;
                if (start < cp) {
                    word &= -1L << (cp - start);
                }
                if (word != 0) {
                    return Math.min(start + Long.numberOfTrailingZeros(word), last + 1);
                }
                if (start + Long.SIZE > last) {
                    return last + 1;
                }
            }
            cp = pageStart + PAGE;
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
            if (!CodePoints.isSurrogate(cp)
                    && Normalization.isStableStarter(Normalization.Form.NFC, cp)) {
                int at = cp - first;
                out[at / Long.SIZE] |= 1L << (at % Long.SIZE);
            }
        }
        return out;
    }
}
