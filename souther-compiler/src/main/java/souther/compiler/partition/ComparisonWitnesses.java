package souther.compiler.partition;

import souther.compiler.meaning.Quantity;
import souther.compiler.types.ConstructOccurrence;

/**
 * Where the reading of one comparison asks for the rows shown to get to it: a row showing a count
 * it reads takes every value beside how many its container holds ({@link CountWitnesses}), and a
 * row a run of which gets to the comparison past whatever the way to it works out
 * ({@link ReachWitnesses}). Each is found by running what the compile produced, which the
 * reading of an input is not made of, so it is handed to a reading and not kept in what it reads.
 */
public final class ComparisonWitnesses {

    private ComparisonWitnesses() {}

    /** Where the reading of one comparison asks for the rows shown to get to it. */
    public interface AtAComparison {

        /** What the search for a witness of {@code count} whose row gets to the comparison came
         *  to. */
        CountWitnesses.Sought of(Quantity.HowManyMeet count);

        /** What the search for a row that gets to the comparison came to. */
        default ReachWitnesses.Sought reached() {
            return ReachWitnesses.Sought.NOTHING;
        }

        /** Nothing found: nothing more is shown than the reading shows alone. */
        AtAComparison NONE = _ -> CountWitnesses.Sought.NOTHING;
    }

    /** Where the reading of a body asks for the witnesses of the comparison it reads, by which
     *  comparison of the body it is. */
    public interface AtComparisons {

        /** Where the reading of {@code comparison} asks for its witnesses. */
        AtAComparison at(ConstructOccurrence comparison);

        /** Nothing found for any comparison. */
        AtComparisons NONE = _ -> AtAComparison.NONE;
    }
}
