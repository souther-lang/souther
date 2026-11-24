package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.CodePoints;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The image of a set of code points under a {@link CodeMap} is the set of what each of its code
 * points in the domain is sent to, and the preimage of a set is the set of the domain's code points
 * sent into it — whichever ranges the set is made of, including ranges between, across and beyond
 * the runs the map is made of, and images of several runs that overlap.
 */
class TheImageAndPreimageOfACodeMapAreThoseOfEachCodePointTest {

    private static final CodeMap LOWER = CodeMap.of(text -> text.toLowerCase(Locale.ROOT));

    /** The code points of the domain, and those among them sent somewhere else. */
    private static final BitSet IN_DOMAIN = new BitSet();
    private static final BitSet MOVED = new BitSet();

    static {
        for (CodePoints.Range range : LOWER.domain().ranges()) {
            IN_DOMAIN.set(range.from(), range.to() + 1);
        }
        for (int codePoint = IN_DOMAIN.nextSetBit(0); codePoint >= 0;
                codePoint = IN_DOMAIN.nextSetBit(codePoint + 1)) {
            if (Character.toLowerCase(codePoint) != codePoint) {
                MOVED.set(codePoint);
            }
        }
    }

    /** The code points of {@code over} that are in the domain. */
    private static BitSet inDomain(CodePoints over) {
        BitSet out = new BitSet();
        for (CodePoints.Range range : over.ranges()) {
            out.set(range.from(), range.to() + 1);
        }
        out.and(IN_DOMAIN);
        return out;
    }

    private static CodePoints of(int... fromTo) {
        List<CodePoints.Range> ranges = new ArrayList<>();
        for (int i = 0; i < fromTo.length; i += 2) {
            ranges.add(new CodePoints.Range(fromTo[i], fromTo[i + 1]));
        }
        return new CodePoints(ranges);
    }

    private static CodePoints ofBits(BitSet bits) {
        List<CodePoints.Range> ranges = new ArrayList<>();
        for (int from = bits.nextSetBit(0); from >= 0; from = bits.nextSetBit(from)) {
            int end = bits.nextClearBit(from);
            ranges.add(new CodePoints.Range(from, end - 1));
            from = end;
        }
        return new CodePoints(ranges);
    }

    private static final List<CodePoints> SETS = List.of(
            of(0, 0xD7FF, 0xE000, CodePoints.LAST),
            of('A', 'Z'),
            of('a', 'z'),
            of('K', 'K'),
            // Starting where a run's images end, and ending where one starts.
            of('z', 'z'),
            of('Z', 'Z'),
            of('z', 'z', 0xFF, 0xFF),
            of('a', 'a'),
            of(0x10428, 0x10428),
            of(0x10427, 0x10427),
            of(0x212A, 0x212A),
            of('k', 'k', 0x212A, 0x212A),
            of('A', 'Z', 'a', 'z'),
            of(0xC0, 0x17F),
            of(0x100, 0x100),
            of(0x370, 0x3FF, 0x400, 0x4FF),
            of(0x1C4, 0x1CC),
            of(0x10400, 0x1044F),
            of(0xE000, 0xF8FF),
            of(0x10FFFE, CodePoints.LAST),
            of(0x41, 0x41, 0x61, 0x61, 0x391, 0x391, 0x3B1, 0x3B1, 0x10400, 0x10400));

    @Test
    void theImageIsTheSetOfWhatEachCodePointOfTheDomainIsSentTo() {
        for (CodePoints over : SETS) {
            BitSet held = inDomain(over);
            BitSet expected = new BitSet();
            // What stays is held as it is; what is moved is held where it goes.
            BitSet moved = (BitSet) held.clone();
            moved.and(MOVED);
            expected.or(held);
            expected.andNot(moved);
            for (int codePoint = moved.nextSetBit(0); codePoint >= 0;
                    codePoint = moved.nextSetBit(codePoint + 1)) {
                expected.set(Character.toLowerCase(codePoint));
            }
            assertEquals(ofBits(expected).ranges(), LOWER.image(over).ranges(),
                    () -> "image of " + over.ranges());
        }
    }

    @Test
    void thePreimageIsTheSetOfTheDomainsCodePointsSentIntoIt() {
        for (CodePoints over : SETS) {
            // What stays is sent into the set where it is in it; what is moved where its target is.
            BitSet expected = inDomain(over);
            expected.andNot(MOVED);
            for (int codePoint = MOVED.nextSetBit(0); codePoint >= 0;
                    codePoint = MOVED.nextSetBit(codePoint + 1)) {
                if (over.has(Character.toLowerCase(codePoint))) {
                    expected.set(codePoint);
                }
            }
            assertEquals(ofBits(expected).ranges(), LOWER.preimage(over).ranges(),
                    () -> "preimage of " + over.ranges());
        }
    }
}
