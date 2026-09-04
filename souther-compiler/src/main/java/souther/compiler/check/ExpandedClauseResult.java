package souther.compiler.check;

import souther.compiler.types.TypeKey;

/**
 * What a lookup says about one declaration's clauses in the expanded representation.
 *
 * <p>Three answers and not two, because a reading that got no clauses has to know which of the two
 * happened. A declaration that states nothing and a declaration whose clauses could not be worked
 * out are the same empty list and opposite facts; handed the list alone, a reader reports the second
 * as the first — which is the shape this arrangement exists to remove, and which reappears one rung
 * down the moment an absence is allowed to be an empty answer.
 *
 * <p>The fourth state is no answer of this kind at all. A module whose expansion did come out has an
 * entry for every declaration it wrote, so one missing from it is this compiler having failed to hand
 * its own reading over, and it is refused where the expansion is read.
 */
public sealed interface ExpandedClauseResult {

    /**
     * Its clauses, expanded — empty where the declaration wrote none, and empty where its kind has
     * no {@code invariant} to write.
     *
     * <p>Those two are one answer on purpose. What a reader needs to know is that every rule about
     * the declaration has been read and there are none; why the producer had none to give is the
     * producer's, and a reader that could tell a sum from a clause-free product would be reading the
     * declaration's kind through a question about its rules.
     */
    record Found(ExpandedClauses clauses) implements ExpandedClauseResult {

        public Found {
            if (clauses == null) {
                throw new IllegalArgumentException("a found answer is some clauses");
            }
        }
    }

    /**
     * The declaration exists and its clauses could not be worked out — its module does not compile,
     * its imports form a cycle, or expanding it failed.
     *
     * <p>Never widened to no clauses. A reading turns this into a rule about the position that went
     * unreached, which it already has a word for; a code generator does not generate, because a
     * decoder built from clauses nobody read constrains less than the model says and says nothing
     * about having done so.
     */
    record Unavailable(TypeKey declaration) implements ExpandedClauseResult {}

    /** Nothing in this compilation declares one. */
    record NotDeclared(TypeKey declaration) implements ExpandedClauseResult {}
}
