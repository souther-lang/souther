package souther.compiler.partition;

import souther.compiler.numeric.Towards;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Where every rule about one quantity parts its values, and the runs they leave between them.
 *
 * <p><b>One arrangement per quantity, made once.</b> What the classes of a position are, what a
 * border owes at each of its points and what the generator offers rows for are three readings of
 * this and not three derivations of it. Derived separately, the partition merged every threshold on
 * a position into one set of ranges while a border was built from one rule at a time — so a border
 * knew nothing of the lines beside it, and the run its {@code IN} point asked for ran past them to
 * the end of the order.
 *
 * <p><b>Built from seams and never from thresholds.</b> Several rules can part a quantity's values
 * in one place, and they are one place however they were written: {@code n <= 4} and {@code n < 5}
 * divide the whole numbers once. Keyed on the numbers the rules carry, they leave a run above four
 * and below five that no row can be written in, and a report counts a class nothing can reach
 * ({@link Seam}).
 *
 * @param seams where the values part, in the order the values are in
 * @param bands the runs between them, one more than there are seams
 */
public record QuantityArrangement(List<Parting> partings, List<Band> bands) {

    public QuantityArrangement {
        partings = List.copyOf(partings);
        bands = List.copyOf(bands);
    }

    /**
     * The arrangement {@code parted} come to on {@code space}.
     *
     * <p>Ordered here rather than by the caller, and deduplicated by where the values part rather
     * than by which rule parted them: the rules that drew a place are a property of the place and
     * are kept beside it, while what the quantity is divided into is a property of the quantity.
     */
    public static QuantityArrangement of(LevelSpace space, List<Parting> parted) {
        return of(space, parted, null, null);
    }

    /**
     * The same, where the rules leave the quantity only what runs from {@code from} to {@code to}.
     *
     * <p>The ends are not seams and never become runs of their own. Nothing outside a bound can be
     * constructed, so there is no run on the far side of one to cover (ADR-0090); what a bound does
     * is stop the run beside it, which is why the two either side of a line at ten run from the
     * bound rather than from the order's own extent.
     *
     * @param from where the rules leave off at the low end and whether they keep the place they
     *             leave off at, or null where they leave it everything that way. Not the first value
     *             in the run: a strict bound on a carrier with no step leaves no first value, and
     *             read as one such a run either had no end at all or held the value its bound
     *             refuses
     * @param to   the same at the high end
     */
    public static QuantityArrangement of(LevelSpace space, List<Parting> parted, Bound from,
                                         Bound to) {
        Map<String, Parting> distinct = new LinkedHashMap<>();
        for (Parting each : parted) {
            // A place the rules leave nothing at divides nothing. The values it would tell apart are
            // values no row can be written at, so it is dropped rather than kept as a run holding
            // none — which is a class an author would be told to write a row for and could not.
            if (outside(each.geometry(), from, to)) {
                continue;
            }
            // One place, and every line the model wrote there against it. Which is the whole of what
            // this being the one canonicaliser buys: a producer that told two candidates apart for
            // itself kept whichever it read first, and the other line went unsaid.
            distinct.merge(each.key(), each, Parting::and);
        }
        List<Parting> ordered = new ArrayList<>(distinct.values());
        ordered.sort(QuantityArrangement::inOrderOfTheValues);

        List<Band> bands = new ArrayList<>();
        Parting under = null;
        for (Parting parting : ordered) {
            keep(space, bands, runBetween(under, parting, from, to));
            under = parting;
        }
        keep(space, bands, runBetween(under, null, from, to));
        return new QuantityArrangement(ordered, bands);
    }

    /** The run between two of the places the values part, held to what the rules leave either
     *  side. */
    private static Band runBetween(Parting under, Parting over, Bound from, Bound to) {
        // The places and not the lines against them. What a run asks a row for is the same however
        // many rules wrote a line where it stops, and which of them did is this arrangement's answer
        // to a different question ({@link Parting#alternatives}) — carried into the run, it would be
        // inside every value that says what is asked of a row.
        return new Band(Band.endAt(under == null ? null : under.geometry(), from, Towards.ABOVE),
                Band.endAt(over == null ? null : over.geometry(), to, Towards.BELOW));
    }

    /**
     * Which of two seams parts the values first.
     *
     * <p>Where the lines fall, and where two fall in one place, the one that gives that place away
     * before the one that keeps it. Two rules can part a carrier whose values fill at one number —
     * {@code <= 0.5} and {@code < 0.5} — and what they leave between them is that number and nothing
     * else. Ordered by a value either of them names, both name it, and one of the two readings put
     * the number in the runs on both sides of itself.
     *
     * <p>Asked of the line and not of the values beside it, because a line the quantity names no
     * value beside has none to be asked about.
     */
    private static int inOrderOfTheValues(Parting one, Parting other) {
        int where = one.geometry().at().compareTo(other.geometry().at());
        return where != 0 ? where : Boolean.compare(one.geometry().keepsItsOwnValueBelow(),
                other.geometry().keepsItsOwnValueBelow());
    }

    /**
     * The run just above {@code seam}, or null where the rules leave none there.
     *
     * <p>What the {@code IN} point of a border on the upper side asks for. Null is a run the rules
     * leave nothing in, which is a point nobody is owed a row at rather than one nothing has got
     * to.
     */
    public Band above(Parting parting) {
        return bands.stream().filter(each -> is(each.lower().seam(), parting)).findFirst()
                .orElse(null);
    }

    /** The run just below it, on the same reading. */
    public Band below(Parting parting) {
        return bands.stream().filter(each -> is(each.upper().seam(), parting)).findFirst()
                .orElse(null);
    }

    /** The run one value of the quantity is in, or null where the rules leave it in none. */
    public Band holding(Level at) {
        return bands.stream().filter(each -> each.holds(at)).findFirst().orElse(null);
    }

    /**
     * The run at one end of what the rules leave: the one nothing parts below it, or nothing parts
     * above it.
     *
     * <p>What a bound bounds. A bound's line is where what it leaves stops, so the run it bounds is
     * the one against that end — and it is found by being the endmost rather than by holding the
     * line's own value, which a bound that stops short of that value does not leave in any run at
     * all. Null where the rules leave no run there, which is a point nobody is owed a row at.
     */
    public Band endmost(Towards inward) {
        return bands.stream()
                .filter(each -> (inward == Towards.ABOVE ? each.lower() : each.upper())
                        .seam() == null)
                .findFirst().orElse(null);
    }

    private static boolean is(Seam one, Parting other) {
        return one != null && other != null && one.key().equals(other.key());
    }

    /** A run, unless what the rules leave has nothing in it. */
    private static void keep(LevelSpace space, List<Band> bands, Band band) {
        Level first = band.first();
        Level last = band.last();
        if (first != null && last != null && space.compare(first, last) > 0) {
            return;
        }
        bands.add(band);
    }

    /**
     * Whether the rules leave nothing at the place this seam parts the values.
     *
     * <p>Asked of the place and not of the values either side of it. A line at the very edge of what
     * the rules leave has one of its two values outside them and parts what is left all the same —
     * read off that value, a bound's own line was dropped from the arrangement and the run it starts
     * belonged to no seam at all.
     */
    private static boolean outside(Seam seam, Bound from, Bound to) {
        return from != null && seam.at().compareTo(from.at()) < 0
                || to != null && seam.at().compareTo(to.at()) > 0;
    }
}
