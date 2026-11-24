package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What is asked of the sites of a library operation's body that may end a run, about the way to
 * each of them ({@link LibraryProver#onTheWay}).
 *
 * @param operation      the operation
 * @param body           its body, whose terms the sites are, each by where it is written
 * @param reaching       the sites asked whether the body reaches them at all
 * @param divisions      those of them that divide, asked whether the divisor is ever nought where
 *                       they are reached
 * @param collections    the sites that build a collection, which end a run for holding too much
 *                       only where it holds more than {@code mostElements}
 * @param numbers        the sites that work out a whole number, which end a run for holding too
 *                       much only where it lies outside {@code least} to {@code greatest}
 * @param alsoNoMoreThan what the owners of the sites say each holds at most, over the operation's
 *                       arguments by place, where that is a number of them
 */
public record AskedOnTheWay(ValueName.Stdlib.Operation operation, LibraryTerm body,
                            Set<LibraryTerm> reaching, Set<LibraryTerm> divisions,
                            Set<LibraryTerm> collections, Set<LibraryTerm> numbers,
                            List<LinearForm<LawNumber<Integer>>> alsoNoMoreThan,
                            BigInteger least, BigInteger greatest, BigInteger mostElements) {

    public AskedOnTheWay {
        Objects.requireNonNull(operation, "of some operation");
        Objects.requireNonNull(body, "of its body");
        Objects.requireNonNull(least, "the least a whole number holds");
        Objects.requireNonNull(greatest, "the greatest a whole number holds");
        Objects.requireNonNull(mostElements, "how many elements a collection holds at most");
        reaching = LibraryTerm.placesOf(reaching);
        divisions = LibraryTerm.placesOf(divisions);
        collections = LibraryTerm.placesOf(collections);
        numbers = LibraryTerm.placesOf(numbers);
        alsoNoMoreThan = List.copyOf(alsoNoMoreThan);
        if (!reaching.containsAll(divisions)) {
            throw new IllegalArgumentException("a division asked of is a site asked of");
        }
    }
}
