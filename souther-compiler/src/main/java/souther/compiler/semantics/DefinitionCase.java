package souther.compiler.semantics;

import java.util.List;

/**
 * One case of a piecewise definition: the argument it answers, and what the arguments stand as for
 * it to be reached.
 *
 * <p>Generic in the word for an argument, as {@link ElementLineage} is: authored, a case names its
 * arguments as the fact writes them; held to the library, as the declaration has them.
 *
 * @param <A> the word for an argument of the operation
 */
public record DefinitionCase<A>(A answers, List<ArgumentsStand<A>> given) {

    public DefinitionCase {
        java.util.Objects.requireNonNull(answers, "a case answers an argument");
        given = List.copyOf(given);
    }
}
