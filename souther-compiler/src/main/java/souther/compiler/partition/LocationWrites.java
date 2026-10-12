package souther.compiler.partition;

import souther.compiler.check.DeclaredBounds;
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
 * container, and what a line at an element demands is one of them. Told apart by the spelling, both
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
     * How many each of these containers is to hold, where that is what was asked of it and not a
     * value of it.
     *
     * <p>Kept apart from {@link #written} because it says less. A container written whole settles
     * every position inside it; one asked to hold so many settles none of them, so what is asked
     * at a position inside it is one more thing the container is built to hold rather than a
     * second ask at one location.
     */
    private final Map<TermPath, DeclaredBounds.CountRange> sized = new LinkedHashMap<>();

    /**
     * The same asks, to go on asking in for one way of writing the row.
     *
     * <p>A row tried under one case and given up is not the row: what that way wrote at a position
     * under its case is nothing the next way, under another, is asked for.
     */
    LocationWrites copy() {
        LocationWrites out = new LocationWrites();
        out.written.putAll(written);
        out.sized.putAll(sized);
        return out;
    }

    /**
     * What asking the container at {@code at} to hold as many as {@code holds} says came to.
     *
     * <p>Refused where a value is written at it or at a value it is inside: that value already says
     * how many the container holds. Taken beside whatever is asked inside it, which the container
     * is built to hold.
     */
    Written size(TermPath at, DeclaredBounds.CountRange holds) {
        for (TermPath whole : written.keySet()) {
            if (at.isAtOrUnder(whole)) {
                return Written.CONFLICTING;
            }
        }
        DeclaredBounds.CountRange already = sized.get(at);
        if (already != null) {
            return already.equals(holds) ? Written.AGAIN : Written.CONFLICTING;
        }
        sized.put(at, holds);
        return Written.FIRST;
    }

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
            if (oneLocation(at, other)) {
                return Written.CONFLICTING;
            }
        }
        // A value written whole at a container asked to hold so many, or at a value around it,
        // would say again how many it holds.
        for (TermPath counted : sized.keySet()) {
            if (counted.isAtOrUnder(at)) {
                return Written.CONFLICTING;
            }
        }
        written.put(at, values);
        return Written.FIRST;
    }

    /**
     * Whether two asks reach one value, which is what makes them one location.
     *
     * <p>The same path, or a path inside a path: what is written at a container is written at every
     * position under it. Asked here by everything that asks it — a reader keeping its own account of
     * which locations are spoken for parts from this one over exactly the pair that is not spelled
     * alike, which is the pair a total brings.
     */
    static boolean oneLocation(TermPath one, TermPath other) {
        return one.isAtOrUnder(other) || other.isAtOrUnder(one);
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

    /** How many the containers asked to hold so many are to hold, for the same walk. */
    Map<TermPath, DeclaredBounds.CountRange> sizes() {
        return sized;
    }
}
