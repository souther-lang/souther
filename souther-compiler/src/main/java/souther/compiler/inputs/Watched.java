package souther.compiler.inputs;

/**
 * What a reading came to, with what it asked of the values handed on the way to it.
 *
 * <p>The reading may have come to nothing, so the result is not a payload that is lost by being
 * absent; what was asked is always said, as {@link HandedAnswers#UNTOLD} where the reading is not
 * to be told from another by it.
 */
public final class Watched<T> {

    private final T result;
    private final HandedAnswers asked;

    Watched(T result, HandedAnswers asked) {
        this.result = result;
        this.asked = java.util.Objects.requireNonNull(asked,
                "a watched reading says what it asked, if only that it is not to be told by it");
    }

    /** What the reading came to. */
    public T result() {
        return result;
    }

    /** What it asked of what was handed. */
    public HandedAnswers asked() {
        return asked;
    }
}
