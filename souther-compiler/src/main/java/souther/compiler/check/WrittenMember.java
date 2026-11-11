package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.values.Value;

/**
 * The value a rule writes where it asks a container for a member that is no place of the value.
 *
 * <p>The one place such a member is read as the value it is, so that every reader of what a rule
 * asks a container to hold — the places a clause reads, the entries a record's builders keep —
 * says the same of it. A rule writes a primitive: a newtype's constructor is a construction, which
 * a rule cannot make, and a case is no value a member is asked to be.
 */
final class WrittenMember {

    private WrittenMember() {}

    /** The value {@code e} writes, or null where it is not a constant a value stands for. */
    static Value of(Core e, Symbols symbols) {
        return Value.folded(CoreConstantEval.against(symbols, Denotations.none()).eval(e)
                .orElse(null));
    }
}
