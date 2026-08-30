package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;

/**
 * A value stated by source text, in a form that names nothing of the compiler that read it.
 *
 * <p>The other half of the pair {@link ObservedValue} is one of. A value is either what someone
 * wrote down or what an execution turned out to hold, and the two are not one kind of thing: an
 * observation leaves out what the value it was read from no longer needs to carry — a {@code List}
 * and a {@code Set} are one sequence there, because the type that produced it says which one it was.
 * A stated value has no such type behind it. It stands at a position it is free to disagree with, so
 * what it wrote is the only thing that says what it wrote.
 *
 * <p>So the two are held apart, and neither is read as the other. This is built from what was
 * written, an {@link ObservedValue} is read from what came out, and whether the two are the same
 * value is a question asked of both. Sharing one type for them was how the position came to answer
 * for what was written: a {@code Set.fromList([1])} stated at a {@code List} became the sequence a
 * list is, and what stated it held.
 *
 * <p>Here rather than beside whatever reads a source text, because what a text stated is a fact
 * about the text and not about the reading: an output outside this compiler is handed one of these
 * for a row it did not read, and holds the same value the compile held.
 */
public sealed interface Asserted {

    /**
     * A value with no parts, exactly as it was written: a scalar, a unit case, absence. Its type is
     * in the value, so nothing more has to be kept beside it.
     */
    record Value(ObservedValue value) implements Asserted {}

    /** A construction, under the name the text wrote and with the parts it wrote. */
    record Built(TypeSymbol type, Map<String, Asserted> fields) implements Asserted {}

    /**
     * A sequence, and which sequence the text said it was.
     *
     * <p>{@code [ 1 ]} says nothing — it is how a list and a set are both written — and the position
     * answers for it, which is the one thing a position may answer. {@code Set.fromList([ 1 ])},
     * {@code Set.empty} and a helper answering with a set say it themselves.
     */
    record Elements(Container stated, List<Asserted> elements) implements Asserted {}

    /** A map's entries, in the order they were written, which is not part of the value. */
    record Entries(boolean stated, List<Entry> entries) implements Asserted {}

    record Entry(Asserted key, Asserted value) {}

    /** Which sequence was written, where the text says which. */
    enum Container {
        /** Written as `[ … ]`, which a list and a set share, so the position says which. */
        UNSTATED,
        LIST,
        SET
    }
}
