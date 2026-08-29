package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;

/**
 * What a row has to satisfy to stand at one coverage item, in the words a search can solve.
 *
 * <p><b>The solver's input language, and not a second listing of the quantities.</b> What these name
 * is the kind of constraint a search has to answer — one position pinned or confined, two positions
 * held a fixed distance apart, a form held at a value — and a quantity added later adds one of these
 * only where it needs a kind of search that is not here. A quantity whose items lower onto a
 * constraint that already exists brings no new shape.
 *
 * <p>Which is why this is apart from {@link BorderQuantity}. What a border means and how a row at one
 * of its points is found are two questions; answered by one type, every reader that only wanted the
 * first was holding the second, and the search that answers the second was written once per shape of
 * line.
 *
 * <p>Nothing here holds what the rules leave. The region a row has to be written inside is the
 * caller's — it comes from the reading of the declarations and is the same for every item of a
 * behavior — so a constraint is what the <em>border</em> asks and is handed to {@link LevelRealizer}
 * beside what the model admits.
 */
public sealed interface Standing {

    /**
     * One position's own value, at a level of its carrier or anywhere in a side of it.
     *
     * <p>The whole of what a border on one coordinate asks. Which of the two it is is the criterion's
     * to say, and both are answered by the same search: a place the carrier names that the criterion
     * accepts.
     */
    record OfOneCoordinate(NumericTerm.FromOnePosition term, Carrier of, Criterion where)
            implements Standing {}

    /**
     * Two positions on one carrier, standing the criterion's number of that carrier's steps apart.
     *
     * <p>Both are fixed at once, which is the whole of what makes the row one on the line. A search
     * that settled one and left the other to its own range would produce a row beside the line as
     * readily as one on it.
     *
     * <p>The place they are apart <em>from</em> is not here. Where the line is is a relation the row
     * satisfies and the pair a search happens to find is a witness rather than the item: written
     * here, one row on the line would name every other row on it a different item.
     */
    record OfTwoOnOneCarrier(NumericTerm.FromOnePosition on, NumericTerm.FromOnePosition against,
                             Carrier of, Criterion where)
            implements Standing {}

    /**
     * An arithmetic form over several positions, held at a value of the form or past one.
     *
     * <p>The one constraint here that has to be searched for. A level of a form is reached by many
     * assignments and by none, and which it is depends on what every rule leaves each position — so
     * this names the equation and the caller hands in the box.
     *
     * <p>The order the form's own values sit on comes with it. Which levels a form takes is the
     * quantity's answer, and a search that worked it out again from the coefficients would be the
     * quantity's reading written a second time, free to disagree with it about where the next level
     * is.
     *
     * <p>And an order per position beside it. Which order a position is read and written on is a
     * question about that position, and a form may be over positions that answer it differently —
     * handed one order for all of them, a search walked every position over the values of whichever
     * order it was given.
     */
    record OfAForm(souther.compiler.numeric.NumericDomain.LinearForm<NumericTerm> form,
                   java.util.Map<NumericTerm, Carrier> on, LevelSpace levels, Criterion where)
            implements Standing {

        public OfAForm {
            on = java.util.Map.copyOf(on);
            if (!on.keySet().equals(form.coefs().keySet())) {
                throw new IllegalArgumentException("a form stands over the positions it names, each"
                        + " on one order: " + form.coefs().keySet() + " against " + on.keySet());
            }
        }
    }
}
