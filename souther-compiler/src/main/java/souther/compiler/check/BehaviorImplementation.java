package souther.compiler.check;

/**
 * Where a behavior's body comes from.
 *
 * <p>One reading of the declarations, made here and nowhere else. Whether a behavior has a
 * {@code let} used to be asked separately by the requirement walk, by the signatures a
 * {@code depends on} may name, by the emitter, by the rows and by the report, and each of them put
 * its own meaning on the answer. Two of those meanings disagree: to the rows, no {@code let} means
 * the body has not been written yet, and to the emitter it means Java supplies it. The disagreement
 * surfaces at {@code depends on}, which an injection target may not declare and an author writing a
 * model example-first has to (issue #936).
 *
 * <p>So the two are separate states here, and what tells them apart is the clause. A behavior that
 * declares {@code depends on} takes those dependencies as arguments of a {@code let}
 * (spec §depends-on), which is a Souther implementation; with no {@code let} it is a Souther
 * implementation nobody has written. A behavior declaring nothing to depend on and writing no
 * {@code let} is what Java supplies (spec §injected-behavior).
 *
 * <p>Carried across a module boundary rather than worked out again there: a module read from the
 * path publishes no {@code let}, so an importer that re-derived would have only two states to put
 * three declarations into, which is the conflation this exists to remove.
 */
public enum BehaviorImplementation {

    /** A {@code let} of its name, or a {@code >->} composition, which is its own implementation. */
    IMPLEMENTED,

    /** Souther's to write, and not written. Its rows wait; nothing that needs the body is emitted. */
    UNIMPLEMENTED,

    /** Java's to supply. An abstract base is emitted for an implementation to extend. */
    INJECTION_TARGET;

    /**
     * The one rule.
     *
     * <p>Two questions about the declaration and nothing else — no name to look up and no module to
     * consult — so that the two representations a behavior is read in cannot answer differently.
     *
     * @param hasBody whether an implementation of this behavior is written here: a {@code let} of
     *                its name, or the {@code >->} the behavior is declared as
     * @param declaresDependsOn whether the declaration writes a {@code depends on} clause
     */
    public static BehaviorImplementation of(boolean hasBody, boolean declaresDependsOn) {
        if (hasBody) {
            return IMPLEMENTED;
        }
        return declaresDependsOn ? UNIMPLEMENTED : INJECTION_TARGET;
    }

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
