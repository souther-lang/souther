package souther.compiler.types;

/**
 * What a value turns out to be once a case has been selected, and where the selected value is read
 * from — the carrier is tested, and this says what stands under it.
 *
 * <p>Written by whoever builds a {@link CaseSelector} and read by everything downstream. Which of
 * these a case takes is decided once, where the cases of a subject are worked out, so no later stage
 * asks whether a subject is an {@code Option}, whether an arm named one case or several, or whether a
 * case is a primitive. Those questions have one answer each and it is recorded here.
 *
 * <p>The arms are named for what the carrier holds rather than for the case that happens to take
 * them today. {@code Some} and {@code None} are the two carriers an optional is represented by, and
 * naming the arms after them would make a reader look up an {@code Option} to know what to emit.
 */
public sealed interface Refinement {

    /** What the case binds, or null where nothing readable stands under the carrier. */
    Type bound();

    /**
     * The carrier is the value. Testing it is testing the case's own class, and the value read is
     * that class's instance — a declared data as its own type, a primitive-named case (the
     * {@code Int} of {@code Int | DivisionByZero}) as that primitive.
     *
     * <p>{@code bound} is null for a case that denotes no type at all, which is what a name outside
     * the spelling table answers; nothing readable stands under such a carrier either.
     */
    record Itself(Type bound) implements Refinement {}

    /** The carrier wraps the value: an optional's present carrier, under which its element stands. */
    record Wrapped(Type bound) implements Refinement {
        public Wrapped {
            if (bound == null) {
                throw new IllegalArgumentException("a wrapping carrier holds something");
            }
        }
    }

    /** The carrier has nothing under it: an optional's absent carrier. */
    record Absent() implements Refinement {

        @Override
        public Type bound() {
            return null;
        }
    }
}
