package souther.compiler.abort;

import souther.compiler.types.TypeSymbol;

/**
 * A declared type a construction builds, and whether it holds what it builds to an invariant.
 *
 * <p>One of these for every such declaration, the ones with no invariant included, so that
 * {@link AbortSites} can tell a type it was told has none from a type nobody told it about. A list of
 * only the types that have one would answer the second as the first.
 *
 * @param type the declaration
 * @param holdsInvariants whether at least one {@code invariant} clause names it — the answer
 *     {@link souther.compiler.program.CheckedData.WithFields#invariants} gives, read off the
 *     declaration rather than re-derived by a reader of it
 */
public record Constructible(TypeSymbol.AtModule type, boolean holdsInvariants) {

    public Constructible {
        if (type == null) {
            throw new IllegalArgumentException("a constructible type is named by its identity");
        }
    }
}
