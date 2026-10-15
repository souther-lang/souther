package souther.compiler.partition;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * The members of a class of whole numbers that a run holds, in the order a search is to try them.
 *
 * <p><b>Where a class is part of what is searched.</b> A value held to a class is a value of the
 * class, and every search that chooses one draws its candidates from the class and not from the run
 * and asks afterwards. Asked afterwards, the first candidate the class admits is the only one a
 * search can hold on to: whatever else refuses it — a rule about another remainder, a place already
 * tried — leaves the next member of the class unreached by anything that walks the run.
 *
 * <p>Whole numbers only. A run with an end that is no whole number is cut inward to the whole numbers
 * it holds, and an end that cannot be read as one leaves the run as it was, which is wider and so
 * sound for a search.
 *
 * @param values the members to try, nearest the end the search starts from first
 * @param stoppedShort whether the run holds members past the last of these
 */
record ClassMembers(List<BigInteger> values, boolean stoppedShort) {

    ClassMembers {
        values = List.copyOf(values);
    }

    /**
     * The members of {@code members} inside {@code run}, at most {@code most} of them, from the end
     * of the run nearest the line the item is named for.
     *
     * <p>That is the lower end where the item lies above its line and the upper end where it lies
     * below it; with neither said, the lower end where the run has one. A run with neither end is
     * walked outward from nought, one side and then the other.
     *
     * @param away which side of its line the run lies on, or null where no end is the near one
     */
    static ClassMembers within(Congruences members, NumericDomain.Bounds run, Towards away,
                               int most) {
        BigInteger low = run.min() == null ? null : wholeEnd(run.min(), true);
        BigInteger high = run.max() == null ? null : wholeEnd(run.max(), false);
        List<BigInteger> out = new ArrayList<>();
        BigInteger step = members.modulus();
        if (low == null && high == null) {
            BigInteger up = members.leastAtOrAbove(BigInteger.ZERO);
            BigInteger down = members.greatestAtOrBelow(BigInteger.ONE.negate());
            for (int i = 0; out.size() < most; i++) {
                BigInteger turns = step.multiply(BigInteger.valueOf(i));
                out.add(up.add(turns));
                if (out.size() < most) {
                    out.add(down.subtract(turns));
                }
            }
            return new ClassMembers(out, true);
        }
        boolean fromBelow = low != null && (away != Towards.BELOW || high == null);
        if (fromBelow) {
            BigInteger at = members.leastAtOrAbove(low);
            while ((high == null || at.compareTo(high) <= 0) && out.size() < most) {
                out.add(at);
                at = at.add(step);
            }
            return new ClassMembers(out, high == null || at.compareTo(high) <= 0);
        }
        BigInteger at = members.greatestAtOrBelow(high);
        while ((low == null || at.compareTo(low) >= 0) && out.size() < most) {
            out.add(at);
            at = at.subtract(step);
        }
        return new ClassMembers(out, low == null || at.compareTo(low) >= 0);
    }

    /** The places among these that none of {@code apart} is, as places of a carrier's own. */
    List<Place> notApart(PlacesApart apart) {
        List<Place> out = new ArrayList<>();
        for (BigInteger each : values) {
            Place place = new Count(new BigDecimal(each));
            if (!apart.has(place)) {
                out.add(place);
            }
        }
        return out;
    }

    /**
     * The whole number an end admits: the end itself where it is a whole number it includes, one
     * inside it where it is a whole number it excludes, and the next whole number inward where it is
     * between two. Null where the end names no number this reads.
     */
    private static BigInteger wholeEnd(Endpoint end, boolean lower) {
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        ExactAnswer<BigInteger> whole = lower ? count.exactly().ceiling() : count.exactly().floor();
        if (!(whole instanceof ExactAnswer.Held<BigInteger> held)) {
            return null;
        }
        boolean excluded = count.exactly().isWhole() && !end.inclusive();
        return excluded ? held.value().add(lower ? BigInteger.ONE : BigInteger.ONE.negate())
                : held.value();
    }
}
