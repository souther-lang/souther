package souther.compiler.proof;

import java.util.Objects;

/**
 * What is proved of the way to the sites of a library operation's body asked of
 * ({@link LibraryProver#onTheWay}): where it reaches them, and how much those that may hold too
 * much hold there. Both read off one reading of the ways through the body.
 *
 * @param reached where the body reaches the sites asked whether it does
 * @param held    how much the collections and the whole numbers asked of hold
 */
public record OnTheWay(WhereReached reached, HeldOnTheWay held) {

    /** Nothing proved of any site. */
    public static final OnTheWay NOTHING_SHOWN =
            new OnTheWay(WhereReached.NOTHING_SHOWN, new HeldOnTheWay.NotShown());

    public OnTheWay {
        Objects.requireNonNull(reached, "where the sites are reached, or nothing shown");
        Objects.requireNonNull(held, "how much they hold, or not shown");
    }
}
