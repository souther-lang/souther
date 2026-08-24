package souther.compiler.partition;

import java.util.Map;
import java.util.Set;

/**
 * One reading of what a combination asks of a row.
 *
 * <p>A class apiece at the positions the combination is about, and nothing said about the rest.
 * Which positions those are is the combination's to answer: a row filling it has to sit in these
 * classes, and where it stands anywhere else is the search's own choice rather than something the
 * combination asked for.
 *
 * <p><b>What a search counts, and what it does not.</b> How many readings one combination has is how
 * many different things it can be asking, and a bound on the search is a bound on those. Counted
 * over whole assignments instead, most of what a search tried differed only at positions the
 * combination says nothing about — so a bound meant to stop a wrong reading from walking the space
 * was spent before the reading's second meaning was ever tried.
 *
 * @param pins the class each position the combination is about must hold, by the index of the
 *             position in the order the axes are ordered
 */
public record Interpretation(Map<Integer, Integer> pins) {

    public Interpretation {
        pins = Map.copyOf(pins);
    }

    /** The positions this is about. */
    public Set<Integer> at() {
        return pins.keySet();
    }

    /** Which parameters this is about, which is what an origin either states a value of or does
     *  not. */
    public Set<String> heads(java.util.List<Axis> axes) {
        java.util.Set<String> out = new java.util.LinkedHashSet<>();
        for (int i : pins.keySet()) {
            out.add(axes.get(i).path().head());
        }
        return out;
    }
}
