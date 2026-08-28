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

    Written write(TermPath at, List<FixtureTemplate> values) {
        List<FixtureTemplate> already = written.get(at);
        if (already == null) {
            written.put(at, values);
            return Written.FIRST;
        }
        return already.equals(values) ? Written.AGAIN : Written.CONFLICTING;
    }

    boolean holds(TermPath at) {
        return written.containsKey(at);
    }

    List<FixtureTemplate> at(TermPath path) {
        return written.get(path);
    }

    /** What is to be written, for the walk that composes each parameter out of it. */
    Map<TermPath, List<FixtureTemplate>> all() {
        return written;
    }
}
