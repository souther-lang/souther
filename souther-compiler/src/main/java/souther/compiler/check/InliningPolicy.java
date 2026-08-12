package souther.compiler.check;

/**
 * Which abstractions an expansion resolves, and so what an expanded tree is a representation
 * <em>of</em>.
 *
 * <p>Expansion is not one thing done once. The backend needs every call it cannot emit to be gone,
 * and reads a tree of algorithms. A static analysis needs the operations it has rules about to still
 * be operations, and reads a tree of meanings. Asking for one and getting the other is what made the
 * invariant-discharge check's combinator rules unreachable: it was written against
 * {@code List.map(f, xs)} and handed the fold that is.
 *
 * <p>The line is not "the standard library is special". It is whether the language defines what an
 * operation does to the properties the analysis tracks. A standard-library operation has such a
 * definition and every module already has it, so it survives as a call. A module's own helper has
 * none — nothing could be derived from leaving it standing — and it does not travel to an importer
 * either, so it is expanded.
 */
public enum InliningPolicy {

    /** Expand everything expandable: what the backend emits from. */
    FULL,

    /** Expand a module's own helpers; leave the language's own operations standing. What the
     * invariant-discharge analysis reads (spec §invariant-discharge). */
    DISCHARGE
}
