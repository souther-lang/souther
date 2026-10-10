package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which operations the library writes are read through their body where the analysis reads a tree
 * of meanings ({@link InliningPolicy#DISCHARGE}).
 *
 * <p>The analysis keeps the language's operations as calls because it has rules about them. An
 * operation it has a rule for stays a call, since the reader of that rule looks for the call. One it
 * has none for is held to nothing but its body, so the body is the whole of what the analysis can
 * know of it, and keeping the call would make a program and the same program written out two
 * programs to it.
 *
 * <p>Only a body written in the language's own constructs: no call of another operation and no
 * closure. Applying a closure is a call, so a body that walks, or that hands a closure what a
 * container holds, is not read through however little is stated of it; reading one through would
 * put a walk into every tree that mentions it.
 *
 * <p>A pure function of a library and the facts held to it, and the shipped pair is held once. That
 * is the pattern {@link Combinators} follows: what depends on which compilation is running takes a
 * library as a value, and a table that is the same for every compilation is derived from the
 * shipped one in one place.
 */
final class LibraryReadThrough {

    private LibraryReadThrough() {
    }

    /** The operations of {@code stdlib} read through, given the facts stated of its operations. */
    static Set<ValueName.Stdlib.Operation> of(Stdlib stdlib, BoundOperationFacts facts) {
        Set<ValueName.Stdlib.Operation> out = new LinkedHashSet<>();
        stdlib.helpers().forEach((operation, body) -> {
            if (!facts.statesAnythingOf(operation) && callsNothingAndWalksNothing(body.writtenBody())) {
                out.add(operation);
            }
        });
        return Collections.unmodifiableSet(out);
    }

    /** The operations of the shipped library read through, which is the same for every compilation. */
    static Set<ValueName.Stdlib.Operation> shipped() {
        return Shipped.READ_THROUGH;
    }

    private static final class Shipped {
        private static final Set<ValueName.Stdlib.Operation> READ_THROUGH =
                of(DefaultStdlib.get(), DefaultBoundOperationFacts.get());
    }

    /** Whether {@code e} is written in the language's own constructs alone. */
    private static boolean callsNothingAndWalksNothing(Hir.Expr e) {
        if (e instanceof Hir.Apply || e instanceof Hir.Block) {
            return false;
        }
        boolean[] plain = {true};
        Hir.forEachChild(e, child -> plain[0] = plain[0] && callsNothingAndWalksNothing(child));
        return plain[0];
    }
}
