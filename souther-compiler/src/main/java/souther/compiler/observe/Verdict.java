package souther.compiler.observe;

/**
 * Whether an answer is what was stated of it.
 *
 * <p>Two answers and not three. A value that could not be read back is not a third state here: the
 * language settles a statement by whether the answer is the value it states, and an answer nothing
 * can be read out of has not been shown to be that value. So it does not hold, and
 * {@link Mismatch.Reason#UNREADABLE} is why — which keeps this the same verdict a compile reaches
 * about the same answer, rather than one the reader of a snapshot has to decide for itself.
 */
public sealed interface Verdict {

    /** The answer is the value that was stated. */
    record Held() implements Verdict {}

    /** It was not shown to be, and this is where the two part. */
    record NotHeld(Mismatch differs) implements Verdict {

        public NotHeld {
            if (differs == null) {
                throw new IllegalArgumentException("a verdict that does not hold says where");
            }
        }
    }

    Verdict HELD = new Held();
}
