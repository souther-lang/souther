package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

import java.util.Set;

/**
 * Something the rules state exactly, about several of a row's numbers at once.
 *
 * <p><b>What keeps a term from being a set of its own.</b> A condition over a form of two positions
 * and a border of how far two of them stand apart are each one statement about the several; which
 * numbers either leaves one of those terms is whatever the others took. So a search of that term
 * walks what is known of it and has not walked the question, however far it went.
 *
 * <p>Not sealed, and nothing switches on which of these it is holding. What a reader here does is
 * the same thing whichever one it is — decline to call a walk finished — and a reader that asked
 * would be deciding that from where the condition came, which is what the two halves of
 * {@link NumbersAskedFor} exist to stop being the question. The arms are here so that each of the
 * things that states one can say it in the words it already has, rather than being translated into
 * another shape's spelling on the way in.
 */
public interface JointDemand {

    /**
     * Every number of the row this is about.
     *
     * <p>Which is how a reader finds the ones it bears on, and the whole of what a reader asks it.
     */
    Set<NumericTerm> terms();
}
