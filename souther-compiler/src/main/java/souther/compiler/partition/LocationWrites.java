package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a row being composed has been asked to write at each of its locations.
 *
 * <p>A row writes one value at a location. Two numbers taken of one location — how long a string is
 * and the string itself, which hour of a time it is and which minute — are two things to ask a row
 * for and one place to write, so a search fixing both has been asked for something a row may not
 * be able to be.
 *
 * <p><b>And a location holding another is not a second one.</b> A container written whole and a
 * position inside it are one value asked for twice: what a total demands is every element of a
 * sequence, and what a line at an element demands is one of them. Told apart by the spelling, both
 * asks are taken and the composer writes whichever it plans — which is the half-answered point
 * above, reached by two paths that are not equal.
 *
 * <p><b>What is refused is not the second ask.</b> Two asks at one location is a shape the model
 * has, and a search that composed one value satisfying both would be answering it. What cannot
 * happen is taking one of them and writing it as though it were the whole: the row then stands
 * where one number said and says nothing about the other, and the point it was composed for is
 * offered half-answered. So an ask that does not agree with what is already here comes back as
 * {@link Written#CONFLICTING}, and a caller says {@code NOTHING_COMPOSES_ONE} — which is what that
 * reason is for: not that the model has no such value, but that this compiler composed none.
 *
 * <p>The same ask twice is one ask. What is held here is what will be written, and asking for what
 * is already going to be written changes nothing about the row.
 */
final class LocationWrites {

    /** What an ask came to. */
    enum Written {
        /** Nothing had been asked for here, and this is what will be written. */
        FIRST,
        /** What is already going to be written is what was asked for. */
        AGAIN,
        /** Something else is already going to be written here, and nothing composes the two. */
        CONFLICTING
    }

    private final Map<TermPath, List<FixtureTemplate>> written = new LinkedHashMap<>();

    /**
     * What asking for {@code values} at {@code at} came to.
     *
     * <p>The one place a write is told from a write already here, so the two ways of being one
     * location are answered by one reader. Asked as two questions — the same path, and a path inside
     * a path — the second would be answered wherever somebody remembered to.
     */
    Written write(TermPath at, List<FixtureTemplate> values) {
        List<FixtureTemplate> already = written.get(at);
        if (already != null) {
            return already.equals(values) ? Written.AGAIN : Written.CONFLICTING;
        }
        for (TermPath other : written.keySet()) {
            if (at.isAtOrUnder(other) || other.isAtOrUnder(at)) {
                return Written.CONFLICTING;
            }
        }
        written.put(at, values);
        return Written.FIRST;
    }

    /** What is to be written exactly here, or null where nothing is. Where a value inside this one
     *  is written, this is null and {@link #write} is what says the two are one location. */
    List<FixtureTemplate> at(TermPath path) {
        return written.get(path);
    }

    /** What is to be written, for the walk that composes each parameter out of it. */
    Map<TermPath, List<FixtureTemplate>> all() {
        return written;
    }
}
