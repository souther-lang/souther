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
 * further recursions; following that is the call graph's ({@link HelperGraph#reachedFrom}), and a
 * caller that wants the closure asks for it there. Two answers, because what a tree holds and what
 * is reachable from what it holds are two questions, and only the first is this one's to know.
 *
 * <p>{@code standing} is a {@link SequencedSet} because the order is part of what it says: a reader
 * reporting one of a mutually-recursive group reports the one it reached first.
 *
 * @param value what the expansion produced
 * @param standing every recursive helper it left a call to, in the order they were met
 */
public record Expansion<T>(T value, SequencedSet<String> standing) {

    public Expansion {
        standing = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(standing));
    }

    /** An expansion that left nothing standing — what a caller with nothing to expand answers. */
    public static <T> Expansion<T> of(T value) {
        return new Expansion<>(value, new LinkedHashSet<>());
    }

    /** The same value, with {@code more} joined to what this left standing. */
    public Expansion<T> and(SequencedSet<String> more) {
        SequencedSet<String> joined = new LinkedHashSet<>(standing);
        joined.addAll(more);
        return new Expansion<>(value, joined);
    }
}
