package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.types.ConstructOccurrence;

import java.util.List;

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

        /**
         * Whether two values of a type are the same value, as the language says: what a row found
         * by {@link #reached} is compared with, which a row does not carry because it holds no
         * function. Never the same where nothing was found to compare.
         */
        default BehaviorInputs.SameValue sameValue() {
            return (_, _, _) -> false;
        }

        /**
         * The same, a run of each row found getting to the comparison shown to make it on every
         * element of each of {@code elements} ({@link ReachWitnesses.Witness#madeOnEvery}): a
         * fact about where the comparison stands, which the search for the row does not know.
         */
        default AtAComparison madeOnEveryElementOf(List<TermPath> elements) {
            if (elements.isEmpty()) {
                return this;
            }
            AtAComparison found = this;
            return new AtAComparison() {
                @Override
                public CountWitnesses.Sought of(Quantity.HowManyMeet count) {
                    return found.of(count);
                }

                @Override
                public ReachWitnesses.Sought reached() {
                    return found.reached().madeOnEveryElementOf(elements);
                }

                @Override
                public BehaviorInputs.SameValue sameValue() {
                    return found.sameValue();
                }
            };
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
