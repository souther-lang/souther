package souther.compiler.check;

import souther.compiler.types.TypeName;

/**
 * Where a declaration's identity comes into existence.
 *
 * <p>A declaration says which module wrote it and what it is called there, and those two are what it
 * is. Putting them together is a mint rather than a reading, so it happens here and the answer is
 * carried: a {@link souther.compiler.ast.Hir.Def} holds the identity it was given, and a reader asks
 * the declaration rather than assembling the pair again.
 *
 * <p>Two callers, and they are the two places an identity is needed before one exists. {@code
 * Resolve} mints one per declaration as it answers it, which is what puts it in the tree. The scope
 * a module is resolved against mints one per declaration it has, which is what a spelling written
 * here resolves to.
 *
 * <p>Held apart so that there is one call to change when a declaration's identity becomes a symbol
 * an authority issues rather than a pair anything can assemble.
 */
public final class DeclaredIdentity {

    private DeclaredIdentity() {
    }

    /** The identity of a declaration {@code declaredIn} wrote under {@code name}. */
    public static TypeName of(String declaredIn, String name) {
        return new TypeName(declaredIn, name);
    }
}
