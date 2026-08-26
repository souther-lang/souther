package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.SequencedSet;

/**
 * What an expansion produced, and what it could not remove.
 *
 * <p>Expanding a tree answers with the tree, and with the recursive helpers it left calls to
 * standing. The second is a requirement: a call left standing is a call to a method, and the method
 * has to be emitted wherever the tree ends up. It is made by the expansion — the decision to leave a
 * call standing is the moment it becomes true — so it is carried out of the expansion beside what
 * the expansion produced, rather than worked out again by a reader looking at the module the tree
 * came from.
 *
 * <p>Only what this expansion met. A helper left standing has a body of its own that may reach
 * further recursions; a caller that wants those expands that body and asks it the same question.
 * Two answers, because what a tree holds and what is reachable from what it holds are two
 * questions, and only the first is this one's to know — and the second is not a graph's to answer
 * either, since a body reaches a recursion by reading a value as well as by calling it.
 *
 * <p>{@code standing} is a {@link SequencedSet} so that a walk over it happens in the order the
 * expansion met them, which is what keeps a walk driven by several of these from depending on hash
 * order. It is not what decides how anything is reported: two of these compare as sets, and a reader
 * that reports in declaration order puts them in it.
 *
 * @param value what the expansion produced
 * @param standing every recursive helper it left a call to, in the order they were met
 * @param supplied which rule each expansion was handed, by the parameter it was handed to. Read
 *                 where the call site still stands, for the same reason the element provenance is
 */
public record Expansion<T>(T value, SequencedSet<souther.compiler.types.ReachName> standing,
                          ElementProvenance provenance,
                          souther.compiler.coverage.SuppliedRules supplied) {

    /** The same, of an expansion nothing needs what the calls inside it were handed. */
    public Expansion(T value, SequencedSet<souther.compiler.types.ReachName> standing) {
        this(value, standing, ElementProvenance.NONE, souther.compiler.coverage.SuppliedRules.NONE);
    }

    /** The same, of one nothing needs the rules of. */
    public Expansion(T value, SequencedSet<souther.compiler.types.ReachName> standing, ElementProvenance provenance) {
        this(value, standing, provenance, souther.compiler.coverage.SuppliedRules.NONE);
    }

    public Expansion {
        standing = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(standing));
    }
}
