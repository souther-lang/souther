package souther.compiler.check;

/**
 * Where a behavior's body comes from.
 *
 * <p>A behavior with no {@code let} is one of two things. To the rows, no {@code let} means the body
 * has not been written yet, and to the emitter it means Java supplies it. The two are separate
 * states here, and what tells them apart is the clause: a behavior that declares
 * {@code depends on} takes those dependencies as arguments of a {@code let} (spec §depends-on),
 * which is a Souther implementation, so with no {@code let} it is a Souther implementation nobody
 * has written. A behavior declaring nothing to depend on and writing no {@code let} is what Java
 * supplies (spec §injected-behavior).
 *
 * <p>The state is a fact about a module, decided once and held in {@link BehaviorBodies}. It is not
 * derived from a tree, and not from whether a definition is at hand: a module read from the path
 * publishes no {@code let}, so a reader that worked it out again would have only two states to put
 * three declarations into.
 */
public enum BehaviorImplementation {

    /** A {@code let} of its name, or a {@code >->} composition, which is its own implementation. */
    IMPLEMENTED,

    /** Souther's to write, and not written. Its rows wait; nothing that needs the body is emitted. */
    UNIMPLEMENTED,

    /** Java's to supply. An abstract base is emitted for an implementation to extend. */
    INJECTION_TARGET;

    /** Whether Java supplies this one, so an abstract base is emitted and a caller injects it. */
    public boolean isInjectionTarget() {
        return this == INJECTION_TARGET;
    }

    /** Whether there is a body here to run, to compile a row against, and to generate from. */
    public boolean hasBody() {
        return this == IMPLEMENTED;
    }

    /** The word a report and the published metadata write it under. */
    public String written() {
        return switch (this) {
            case IMPLEMENTED -> "implemented";
            case UNIMPLEMENTED -> "unimplemented";
            case INJECTION_TARGET -> "injected";
        };
    }

    /** The state that word names, for a reader of what was published. */
    public static BehaviorImplementation readingWritten(String word) {
        for (BehaviorImplementation each : values()) {
            if (each.written().equals(word)) {
                return each;
            }
        }
        throw new IllegalArgumentException("no implementation state is written `" + word + "`");
    }
}
