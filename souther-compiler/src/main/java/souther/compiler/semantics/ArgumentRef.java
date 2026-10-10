package souther.compiler.semantics;

import java.util.List;

/**
 * Which argument of an operation a fact about that operation names.
 *
 * <p>A word and nothing more. Either the position the declaration writes, or the part the argument
 * plays in what the operation hands its closure. A fact says which argument it is about by writing
 * one of these, and says nothing about how to find that argument in a particular call.
 *
 * <p><b>What this cannot answer is which position {@link TheContainer} and {@link TheClosure}
 * are.</b> That is read off the library's declaration, which is the frontend's to interpret, and
 * asking it here would bring the whole of name resolution into a package that is supposed to hold
 * propositions about operations. Resolving one of these is {@code check.OperationFactBinder}'s,
 * which has both this word and the declaration it takes to read it, and does it once: what it
 * answers with is the declaration's own argument ({@code check.DeclaredArgument}), position and
 * all, and that is what every reader below holds. Nothing below the binding holds one of these.
 */
public sealed interface ArgumentRef {

    /** The argument at a written position. */
    record At(int position) implements ArgumentRef {}

    /** The argument holding what the operation hands its closure. */
    record TheContainer() implements ArgumentRef {}

    /** The argument the operation applies to what a container holds. */
    record TheClosure() implements ArgumentRef {}

    /**
     * The part at {@code path} of what a walk in the operation's body carries — named only in what
     * a lemma states the walk carries, and never in a law.
     */
    record Carried(List<Integer> path) implements ArgumentRef {

        public Carried {
            path = List.copyOf(path);
        }
    }

    /** The part of the list a walk in the operation's body has walked so far — named only where
     *  {@link Carried} may be. */
    record Walked() implements ArgumentRef {}

    /**
     * Any value at all, the same wherever {@code which} names it in one statement: a statement
     * naming it holds of every value — named only where {@link Carried} may be, and in what is
     * stated of kernels beside one another.
     */
    record Every(int which) implements ArgumentRef {}
}
