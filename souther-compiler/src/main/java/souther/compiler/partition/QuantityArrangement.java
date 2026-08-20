package souther.compiler.partition;

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
public record QuantityArrangement(List<Seam> seams, List<Band> bands) {

    public QuantityArrangement {
        seams = List.copyOf(seams);
        bands = List.copyOf(bands);
    }

    /**
     * The arrangement {@code parted} come to on {@code space}.
     *
     * <p>Ordered here rather than by the caller, and deduplicated by where the values part rather
     * than by which rule parted them: the rules that drew a place are a property of the place and
     * are kept beside it, while what the quantity is divided into is a property of the quantity.
     */
    public static QuantityArrangement of(LevelSpace space, List<Seam> parted) {
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
     * @param from the first value the rules leave the quantity, or null where they leave it
     *             everything that way. A value the quantity takes, and not the number a bound was
     *             written with: which of those two it is belongs to whoever holds the bound
     * @param to   the last, on the same reading
     */
    public static QuantityArrangement of(LevelSpace space, List<Seam> parted, Level from,
                                         Level to) {
        Map<String, Seam> distinct = new LinkedHashMap<>();
        for (Seam each : parted) {
            // A place the rules leave nothing at divides nothing. The values it would tell apart are
            // values no row can be written at, so it is dropped rather than kept as a run holding
            // none — which is a class an author would be told to write a row for and could not.
            if (outside(each, from, to)) {
                continue;
            }
            distinct.putIfAbsent(each.key(), each);
        }
        List<Seam> ordered = new ArrayList<>(distinct.values());
        ordered.sort((l, r) -> space.compare(l.somewhere(), r.somewhere()));

        List<Band> bands = new ArrayList<>();
        Seam under = null;
        for (Seam seam : ordered) {
            keep(space, bands, new Band(under, seam, from, to));
            under = seam;
        }
        keep(space, bands, new Band(under, null, from, to));
        return new QuantityArrangement(ordered, bands);
    }

    /**
     * The run just above {@code seam}, or null where the rules leave none there.
     *
     * <p>What the {@code IN} point of a border on the upper side asks for. Null is a run the rules
     * leave nothing in, which is a point nobody is owed a row at rather than one nothing has got
     * to.
     */
    public Band above(Seam seam) {
        return bands.stream().filter(each -> is(each.under(), seam)).findFirst().orElse(null);
    }

    /** The run just below it, on the same reading. */
    public Band below(Seam seam) {
        return bands.stream().filter(each -> is(each.over(), seam)).findFirst().orElse(null);
    }

    /** The run one value of the quantity is in, or null where the rules leave it in none. */
    public Band holding(LevelSpace space, Level at) {
        return bands.stream().filter(each -> each.holds(space, at)).findFirst().orElse(null);
    }

    private static boolean is(Seam one, Seam other) {
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
    private static boolean outside(Seam seam, Level from, Level to) {
        return from != null && seam.at().compare(from) > 0
                || to != null && seam.at().compare(to) < 0;
    }
}
