package souther.compiler.inputs;

/**
 * A position whose values are read from a product this reading cannot show the rules admit.
 *
 * <p>Not {@link UnreadRule} and not {@link PositionReadingBlocked}. Every rule about the position
 * arrived and every one of them was taken in, so there is no rule to name and nothing was left
 * unreached; what happened is that a choice reaching across positions is held one position at a
 * time, and a clause met with it afterwards can leave the values wider than the rules are. Said as
 * either of those, an author is sent to look for a limit that is not there.
 *
 * <p>Carries the position and nothing else. What would lift it is not a reader for a form or a walk
 * that reaches further but a reading that keeps the alternatives apart, which is one fact about this
 * compiler and needs no word to tell it from another.
 *
 * <p>Said whether or not the position came back divided, which is what tells it from a stop. A stop
 * is what a position is left with where nothing answered for it; this qualifies the classes
 * themselves — a class made out of a set wider than the rules leave is one no value can be in.
 */
public record PositionValuesNotSeparated(TermPath at) {

    public PositionValuesNotSeparated {
        if (at == null) {
            throw new IllegalArgumentException("a reading held a product somewhere");
        }
    }
}
