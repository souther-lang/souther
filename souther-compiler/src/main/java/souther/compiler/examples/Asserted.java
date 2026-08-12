package souther.compiler.examples;

import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeName;

import java.util.List;
import java.util.Map;

/**
 * What an {@code example} row states, as the row states it.
 *
 * <p>Not an {@link ObservedValue}. That is what a value turned out to be, read back from one that a
 * behavior produced, and it leaves out what the value it was read from no longer needs to carry: a
 * {@code List} and a {@code Set} are one sequence there, because the type that produced it says which
 * one it was. A row's expectation has no such type behind it. It stands at a position it is free to
 * disagree with, so what it wrote is the only thing that says what it wrote.
 *
 * <p>So the two are held apart. This is built from the row's text; an {@link ObservedValue} is read
 * from what came out; {@link ValueMatch} compares one against the other and neither is read as the
 * other. Sharing one type for both was how the position came to answer for the row: a written
 * {@code Set.fromList([1])} at a {@code List} became the sequence a list is, and the row held.
 */
sealed interface Asserted {

    /**
     * A value with no parts, exactly as it was written: a scalar, a unit case, absence. Its type is
     * in the value, so nothing more has to be kept beside it.
     */
    record Value(ObservedValue value) implements Asserted {}

    /** A construction, under the name the row wrote and with the parts it wrote. */
    record Built(TypeName type, Map<String, Asserted> fields) implements Asserted {}

    /**
     * A sequence, and which sequence the row said it was.
     *
     * <p>{@code [ 1 ]} says nothing — it is how a list and a set are both written — and the position
     * answers for it, which is the one thing a position may answer. {@code Set.fromList([ 1 ])},
     * {@code Set.empty} and a helper answering with a set say it themselves.
     */
    record Elements(Container stated, List<Asserted> elements) implements Asserted {}

    /** A map's entries, in the order the row wrote them, which is not part of the value. */
    record Entries(boolean stated, List<Entry> entries) implements Asserted {}

    record Entry(Asserted key, Asserted value) {}

    /** Which sequence a row wrote, where it wrote which. */
    enum Container {
        /** Written as `[ … ]`, which a list and a set share, so the position says which. */
        UNSTATED,
        LIST,
        SET
    }
}
