package souther.compiler.semantics;

/**
 * What an operation that walks a container answers: a value it starts from, and one step it repeats
 * over what it has so far and an element.
 *
 * <p>A proposition about the operation, so it is declared here rather than kept beside whichever
 * check happened to want it first. Two readers want it and they want different halves: the discharge
 * procedure reads it forwards, building the arithmetic a call comes to, and a reading of what a
 * model measures reads it as how a number is taken off a container. Written down beside one of them,
 * the other would state it again in its own words — and then a sum is nought and addition to one of
 * them and something else to the other, with nothing bringing the two together to disagree.
 *
 * <p>A recipe and not a value. {@code List.concat} starts from the empty list of a type its
 * declaration does not name, and {@code List.sum} starts from a nought that is an {@code Int} at one
 * call and a {@code Decimal} at the next (ADR-0082) — so what it starts from is named as the value
 * it is, and instantiated at the type the call answers by whoever needs one.
 *
 * <p>Nothing here is about numbers. {@code String.concat} accumulates exactly as {@code List.concat}
 * does, and that the domain reading bounds carries no strings is a fact about that reader. What may
 * be read as a number is asked after this, by whoever needs it to be one.
 */
public record Accumulation(Identity identity, Combine combine) {

    public Accumulation {
        java.util.Objects.requireNonNull(identity, "an accumulation starts from something");
        java.util.Objects.requireNonNull(combine, "and repeats one step");
    }

    /** What it starts from, as the value it is rather than as a term of some type. */
    public enum Identity {
        ZERO,
        ONE,
        EMPTY
    }

    /** The step it repeats over what it has so far and an element. */
    public enum Combine {
        ADD,
        MULTIPLY,
        APPEND
    }
}
