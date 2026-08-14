package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.util.Map;

/**
 * What stays fixed while one definition is checked: the module's symbol table, the {@code data} an
 * invariant or a codec is written against, the injected behaviors a body may call, and whether the
 * expression being checked is a value being given to a {@code ?} field — the one place an optional is
 * made (ADR-0011).
 *
 * <p>None of them changes as the walk descends into an expression, so they travel together rather than
 * as separate parameters threaded through every method. What does change — the variable environment and
 * the expected type pushed down from the surrounding context — is passed separately.
 */
public record CheckContext(Symbols symbols, Hir.Data data, Map<String, ReqSig> reqs,
                           Map<String, ReqSig> callees, boolean makingAnOptional,
                           Preserved preserved) {

    public CheckContext(Symbols symbols, Hir.Data data, Map<String, ReqSig> reqs,
                        Map<String, ReqSig> callees, boolean makingAnOptional) {
        this(symbols, data, reqs, callees, makingAnOptional, Preserved.NONE);
    }

    /** A context with no behavior callable by name — every construction that predates the
     *  distinction, and every position where only injected behaviors are in sight. */
    public CheckContext(Symbols symbols, Hir.Data data, Map<String, ReqSig> reqs) {
        this(symbols, data, reqs, Map.of());
    }

    public CheckContext(Symbols symbols, Hir.Data data, Map<String, ReqSig> reqs,
                        Map<String, ReqSig> callees) {
        this(symbols, data, reqs, callees, false);
    }

    /** No {@code data} in scope and no behaviors — the context an invariant-free, injection-free
     *  expression is checked in. */
    public static CheckContext of(Symbols symbols) {
        return new CheckContext(symbols, null, Map.of(), Map.of());
    }

    /** The same context checking a different {@code data}'s invariant, decoder, or encoder. */
    public CheckContext forData(Hir.Data other) {
        return new CheckContext(symbols, other, reqs, callees, makingAnOptional, preserved);
    }

    /** The same context with the behaviors a body may call in scope. */
    public CheckContext withReqs(Map<String, ReqSig> required) {
        return new CheckContext(symbols, data, required, callees, makingAnOptional, preserved);
    }

    /** The same context with the behaviors a body may call by name in scope — the ones that require
     *  nothing (spec {@code [#calling-a-behavior]}). */
    public CheckContext withCallees(Map<String, ReqSig> callable) {
        return new CheckContext(symbols, data, reqs, callable, makingAnOptional, preserved);
    }

    /**
     * The same context, checking the value a {@code ?} field is being given.
     *
     * <p>This is what says an optional may be *made* here, rather than the expected type saying it: a
     * model can now write the type's name (issue #202), so an expected optional no longer means a field
     * asked for one. It travels with the context because the permission reaches the branches of the
     * value — a field may be given one thing or nothing by a rule — and stops at anything that is not
     * that value.
     */
    public CheckContext makingAnOptional(boolean making) {
        return new CheckContext(symbols, data, reqs, callees, making, preserved);
    }

    /**
     * The same context, typing a representation that keeps some calls standing.
     *
     * <p>Here rather than passed where a call is typed, because it does not change as the walk
     * descends: which representation is being typed is decided before any of it, and a body does not
     * become another representation part-way down.
     */
    public CheckContext preserving(Preserved kept) {
        return new CheckContext(symbols, data, reqs, callees, makingAnOptional, kept);
    }

    /**
     * The same context, typing the representation the invariant-discharge analysis reads: the
     * language's own operations kept standing, because that is what the analysis has rules about.
     *
     * <p>Said once, though two trees are typed that way — a behavior's body and the invariants of the
     * declarations it builds. They are two halves of one representation, and a line drawn in one of
     * them and not the other is an analysis that quietly sees less.
     */
    public CheckContext forDischarge() {
        return preserving(Preserved.byTheLanguagesOwnOperations());
    }

    /**
     * The same context, starting a tree that belongs to another representation.
     *
     * <p>What a representation keeps standing does not travel to a tree that is not it. A body
     * reaching a declaration's invariant reaches another tree, built by another question and holding
     * whatever that question decided to keep — which is that representation's to say at its own
     * entry, not something it receives by having been reached from here.
     *
     * <p>Named as the boundary rather than folded into {@link #forData}: which {@code data} is being
     * checked changes within one representation too, and joining the two would make "a data is in
     * scope" quietly mean "the permission is gone".
     */
    public CheckContext inAnotherRepresentation() {
        return preserved == Preserved.NONE ? this : preserving(Preserved.NONE);
    }
}
