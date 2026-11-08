package souther.compiler.proof;

import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Objects;
import java.util.Set;

/**
 * What is asked of the sites of a library operation's body that may end a run, about where it
 * reaches them ({@link LibraryProver#whereReached}).
 *
 * @param operation    the operation
 * @param body         its body, whose terms the sites are, each by where it is written
 * @param sites        the sites asked whether the body reaches them at all
 * @param divisions    those of them that divide, asked whether the divisor is ever nought where
 *                     they are reached
 * @param mostElements how many elements every collection the operation is handed holds at most
 */
public record AskedWhereReached(ValueName.Stdlib.Operation operation, LibraryTerm body,
                                Set<LibraryTerm> sites, Set<LibraryTerm> divisions,
                                BigInteger mostElements) {

    public AskedWhereReached {
        Objects.requireNonNull(operation, "of some operation");
        Objects.requireNonNull(body, "of its body");
        Objects.requireNonNull(mostElements, "with what a collection holds at most");
        sites = byWhereItIsWritten(sites);
        divisions = byWhereItIsWritten(divisions);
        if (!sites.containsAll(divisions)) {
            throw new IllegalArgumentException("a division asked of is a site asked of");
        }
    }

    /** {@code sites}, each kept as the term it is, since two places writing one thing are two. */
    private static Set<LibraryTerm> byWhereItIsWritten(Set<LibraryTerm> sites) {
        Set<LibraryTerm> out = Collections.newSetFromMap(new IdentityHashMap<>());
        out.addAll(sites);
        return Collections.unmodifiableSet(out);
    }
}
