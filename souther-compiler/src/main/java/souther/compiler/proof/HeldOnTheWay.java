package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;

import java.util.Objects;

/**
 * How much the collections a library operation's body builds on the way hold, and where the whole
 * numbers it works out on the way lie, proved against the body ({@link LibraryProver#heldOnTheWay}).
 *
 * <p>About the sites asked of and nothing else: what a site ends a run for besides holding too
 * much, and every site not asked of, is the asker's.
 */
public sealed interface HeldOnTheWay {

    /** Every collection asked of holds no more than some collection the operation is handed, and
     *  every number asked of lies where its type holds it. */
    record WithinWhatItIsHanded() implements HeldOnTheWay {}

    /**
     * Every collection asked of holds no more than {@code most}, a number of the operation's
     * arguments by place, and every number asked of lies where its type holds it.
     */
    record NoMoreThan(LinearForm<LawNumber<Integer>> most) implements HeldOnTheWay {

        public NoMoreThan {
            Objects.requireNonNull(most, "no more than some number of what it is handed");
        }
    }

    /** Not proved of some site asked of. */
    record NotShown() implements HeldOnTheWay {}
}
