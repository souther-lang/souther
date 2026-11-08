package souther.compiler.proof;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

/**
 * Where a library operation's body reaches the sites asked of, proved against the body
 * ({@link LibraryProver#whereReached}).
 *
 * <p>About the sites asked of and nothing else, and each said only where it is proved: a site in
 * neither set is reached as far as this says, and divides by whatever it may.
 *
 * @param onNoWay       the sites the body reaches on no way, which end no run
 * @param neverByNought the divisions reached whose divisor is never nought where they are
 */
public record WhereReached(Set<LibraryTerm> onNoWay, Set<LibraryTerm> neverByNought) {

    /** Nothing proved of any site. */
    public static final WhereReached NOTHING_SHOWN = new WhereReached(Set.of(), Set.of());

    public WhereReached {
        onNoWay = byWhereItIsWritten(onNoWay);
        neverByNought = byWhereItIsWritten(neverByNought);
    }

    private static Set<LibraryTerm> byWhereItIsWritten(Set<LibraryTerm> sites) {
        Set<LibraryTerm> out = Collections.newSetFromMap(new IdentityHashMap<>());
        out.addAll(sites);
        return Collections.unmodifiableSet(out);
    }
}
