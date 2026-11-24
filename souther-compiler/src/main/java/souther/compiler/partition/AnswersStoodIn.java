package souther.compiler.partition;

import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

/**
 * What a row takes to stand its target's dependencies in with, or why nothing does.
 *
 * <p>An answer and never an absence. A behavior that requires nothing is stood in by nothing and a
 * behavior whose stand-in nothing composed has rows that cannot go out, and the two read alike as
 * an empty list — after which a reader downstream decides for itself which it had, and the one that
 * decided wrongly offered a row nothing applies.
 *
 * <p>Carried from where a row is composed to where the block is written, so that what a block says
 * about work it did not offer is what the composition came to rather than something read off the
 * absence of a row.
 */
public sealed interface AnswersStoodIn {

    /**
     * What a behavior requiring nothing hands its rows.
     *
     * <p>An answer and not an empty one. Every dependency of nothing is answered, so a row of such
     * a behavior is complete with nothing standing in — which is the composition having succeeded
     * and is what a caller with no dependencies to supply says.
     */
    AnswersStoodIn REQUIRING_NOTHING = new Stood(List.of());

    /**
     * Every dependency answered, in the order they are required.
     *
     * @param answers   what each is stood in with
     * @param answering for each dependency whose answer is one value of a type a position stands
     *                  at, that position: where a search can put an answer of its own in the place
     *                  of what a dependency answers, as it puts a value in the place of an input
     */
    record Stood(List<StoodInAnswer> answers, Map<ValueName.Behavior, MeasuredInput> answering)
            implements AnswersStoodIn {

        public Stood {
            answers = List.copyOf(answers);
            answering = Map.copyOf(answering);
        }

        /** Every dependency answered, with no position to move an answer at. */
        public Stood(List<StoodInAnswer> answers) {
            this(answers, Map.of());
        }
    }

    /**
     * Nothing came of it, in the words a search comes back with.
     *
     * <p>Never a statement that no row exists: what a dependency answers may be a shape nothing
     * here writes a value of, and an author writes one by hand.
     */
    record NothingComposed(Generator.UnresolvedCombination.Reason why) implements AnswersStoodIn {

        public NothingComposed {
            if (why == null) {
                throw new IllegalArgumentException("a composition that came to nothing says what of");
            }
        }
    }
}
