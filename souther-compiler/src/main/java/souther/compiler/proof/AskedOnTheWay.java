package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What is asked of the sites of a library operation's body that may hold too much on the way
 * ({@link LibraryProver#heldOnTheWay}).
 *
 * @param operation      the operation
 * @param body           its body, whose terms the sites are, each by where it is written
 * @param collections    the sites that build a collection, which end a run only where it holds
 *                       more than {@code mostElements}
 * @param numbers        the sites that work out a whole number, which end a run only where it
 *                       lies outside {@code least} to {@code greatest}
 * @param alsoNoMoreThan what the owners of the sites say each holds at most, over the operation's
 *                       arguments by place, where that is a number of them
 */
public record AskedOnTheWay(ValueName.Stdlib.Operation operation, LibraryTerm body,
                            Set<LibraryTerm> collections, Set<LibraryTerm> numbers,
                            List<LinearForm<LawNumber<Integer>>> alsoNoMoreThan,
                            BigInteger least, BigInteger greatest, BigInteger mostElements) {

    public AskedOnTheWay {
        Objects.requireNonNull(operation, "of some operation");
        Objects.requireNonNull(body, "of its body");
        collections = byWhereItIsWritten(collections);
        numbers = byWhereItIsWritten(numbers);
        alsoNoMoreThan = List.copyOf(alsoNoMoreThan);
    }

    /** {@code sites}, each kept as the term it is, since two places writing one thing are two. */
    private static Set<LibraryTerm> byWhereItIsWritten(Set<LibraryTerm> sites) {
        Set<LibraryTerm> out = Collections.newSetFromMap(new IdentityHashMap<>());
        out.addAll(sites);
        return Collections.unmodifiableSet(out);
    }
}
