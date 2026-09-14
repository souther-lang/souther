package souther.compiler.check;

import souther.compiler.core.DeclaredOperation;
import souther.compiler.types.Type;

/**
 * One argument of a declaration, as the declaration has it: which operation, which position, and
 * what stands there.
 *
 * <p>The word a fact writes for an argument ({@link souther.compiler.semantics.ArgumentRef}) says
 * which argument it means and nothing about where that argument is in a call — the position of
 * "the container" is the library's to say. This is that word once it has been read against the
 * declaration: the position is settled, the type at it is settled, and the operation it is an
 * argument of is part of the value rather than something a reader pairs it with. A reader holding
 * one has nothing left to resolve, and nothing to resolve it with.
 *
 * <p>Made in one place, {@link OperationFactBinder}, which is the one reader of the authoring word
 * and the library together. The constructor is this package's for the same reason
 * {@link DeclaredOperation}'s is its own: who may make one is answered by counting callers, and a
 * name a package can reach is a name that package can call.
 *
 * <p><b>The type is not the identity.</b> Two of these are the same argument when they are the same
 * position of the same declaration; what stands there is a fact the library settled about it, and a
 * second reading of one declaration that disagreed about the type would be a binding that has come
 * apart rather than a different argument. So a {@link souther.compiler.numeric.LinearForm} keyed on
 * these keys on the position, as it should.
 */
public final class DeclaredArgument {

    private final DeclaredOperation of;
    private final int position;
    private final Type stands;

    DeclaredArgument(DeclaredOperation of, int position, Type stands) {
        if (of == null) {
            throw new IllegalArgumentException("a declared argument is an argument of something");
        }
        if (position < 0 || position >= of.arity()) {
            throw new IllegalArgumentException("`" + of + "` takes " + of.arity()
                    + " argument(s), and argument " + (position + 1) + " was read against it");
        }
        if (stands == null) {
            throw new IllegalArgumentException("argument " + (position + 1) + " of `" + of
                    + "` stands at some type");
        }
        this.of = of;
        this.position = position;
        this.stands = stands;
    }

    /** The declaration this is an argument of. */
    public DeclaredOperation of() {
        return of;
    }

    /** Where in that declaration's parameters it stands, from nought. */
    public int position() {
        return position;
    }

    /** The type the declaration has at that position. */
    public Type stands() {
        return stands;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof DeclaredArgument each
                && of.equals(each.of) && position == each.position;
    }

    @Override
    public int hashCode() {
        return of.hashCode() * 31 + position;
    }

    @Override
    public String toString() {
        return of + "#" + (position + 1);
    }
}
