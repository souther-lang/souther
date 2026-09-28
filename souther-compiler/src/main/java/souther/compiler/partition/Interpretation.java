package souther.compiler.partition;

import souther.compiler.carrier.Lookup;

import java.util.LinkedHashSet;
import java.util.List;
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
 *             position among the axes. What this answers is which position a class is pinned at and
 *             what that class is — a reader wanting the positions in the axes' own order asks the
 *             axes, one index at a time, rather than walking this.
 */
public record Interpretation(Lookup<Integer, Integer> pins) {

    /** Which parameters this is about, which is what an origin either states a value of or does
     *  not. Asked of the axes, one at a time, rather than of {@code pins} — {@code pins} answers
     *  what is bound to a position and not which positions there are. */
    public Set<String> heads(List<Axis> axes) {
        Set<String> out = new LinkedHashSet<>();
        for (int i = 0; i < axes.size(); i++) {
            if (pins.containsKey(i)) {
                out.add(axes.get(i).path().head());
            }
        }
        return out;
    }
}
