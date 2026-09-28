package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;

/**
 * What each name in force was given, for the readers that ask what an expression comes to.
 *
 * <p>The other environment at a lexical position. What a name's <em>type</em> is is {@link Scope}'s
 * bindings; what it <em>denotes</em> is this. Held apart because they are two questions: a reader
 * that had one map for both would answer what a name means from the table that says what it types
 * as, which is what ADR-0106 took apart.
 *
 * <p>What is here is a denotation and never an interpretation. A caller may say which expression
 * stands where a name stands; it may not say what that expression comes to. Whether the expression
 * is a constant is the constant folder's answer, whether it is a linear form is the affine walk's,
 * and a result kept here would be one reader's offered to all of them (ADR-0111).
 *
 * <p>The environment travels with the value. A value stands for the name in the environment the
 * binding was made in, which is not always the one the name was read in — an expansion elaborates
 * an argument outside the bindings its own parameters make, and reading that argument under them
 * would answer it against names it was never written against.
 */
public final class BoundValues {

    /** Nothing is in force: what a root is read under, and what a walk that entered no binding
     *  has. */
    public static final BoundValues NONE = new BoundValues(null, null, null);

    /** What a name stands for: the expression it was given, and the environment that expression is
     *  read in. */
    public record Bound(Hir.Expr value, BoundValues at) {}

    private final BindingId binding;
    private final Bound bound;
    private final BoundValues outer;

    private BoundValues(BindingId binding, Bound bound, BoundValues outer) {
        this.binding = binding;
        this.bound = bound;
        this.outer = outer;
    }

    /**
     * These, with {@code binder} standing for {@code value} as read here.
     *
     * <p>For a binding whose value was written where the binding is — a {@code let}, whose
     * initializer is read under everything outside it and nothing inside it.
     */
    public BoundValues binding(Hir.Binder binder, Hir.Expr value) {
        return binding(binder, value, this);
    }

    /**
     * The same, where the value was written somewhere other than here.
     *
     * <p>An expansion's argument is elaborated outside the bindings the expansion makes, so what it
     * is read under is the environment of the call and not of the body it is bound into. Told to
     * read it here instead, a name it was written against would be answered by whatever the body
     * binds under that spelling.
     */
    public BoundValues binding(Hir.Binder binder, Hir.Expr value, BoundValues definedAt) {
        // What a name was given is the value it computes: which build of it was bound is no part of
        // what a reader that folds it asks.
        return binder == null || value == null ? this
                : new BoundValues(binder.id(),
                        new Bound(Hir.Materialised.stripped(value), definedAt), this);
    }

    /** What {@code binding} was given and where to read it, or null where nothing in force is
     *  it. */
    public Bound read(BindingId binding) {
        for (BoundValues each = this; each != null; each = each.outer) {
            if (binding.equals(each.binding)) {
                return each.bound;
            }
        }
        return null;
    }

    /** Whether nothing at all is in force, which is what a reader handed a root has. */
    public boolean isEmpty() {
        return binding == null && outer == null;
    }
}
