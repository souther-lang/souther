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
        Map<String, Seam> distinct = new LinkedHashMap<>();
        for (Seam each : parted) {
            distinct.putIfAbsent(each.key(), each);
        }
        List<Seam> ordered = new ArrayList<>(distinct.values());
        ordered.sort((l, r) -> space.compare(l.somewhere(), r.somewhere()));

        List<Band> bands = new ArrayList<>();
        Seam under = null;
        for (Seam seam : ordered) {
            bands.add(new Band(under, seam));
            under = seam;
        }
        bands.add(new Band(under, null));
        return new QuantityArrangement(ordered, bands);
    }
}
