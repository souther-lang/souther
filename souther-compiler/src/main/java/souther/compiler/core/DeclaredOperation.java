package souther.compiler.core;

import souther.compiler.types.ValueName;

/**
 * A name that has been read against the declaration it reaches: what it denotes, and how many
 * arguments that declaration takes.
 *
 * <p>{@link ValueName} is an identity and says nothing about what stands behind it — two modules'
 * same-named values are two values, and that is the whole of what it answers. This is that identity
 * where a declaration has been read for it, so a reader holding one is holding a name the
 * declaration world knows. {@link souther.compiler.types.TypeSymbol} is the same step in the type
 * namespace: a structural key, and the key where an authority has settled what it stands for.
 *
 * <p>Made nowhere but {@link CompleteSignature}, which is the value a declaration comes to when it
 * has been read whole. The constructor is this package's for that reason: what may mint one is a
 * question about who has read a declaration, and it is answered by counting the callers of a
 * constructor rather than by an access modifier, since a name a package can reach is a name that
 * package can call.
 *
 * <p><b>The arity is not the identity.</b> Two of these are the same operation when they name the
 * same declaration; what that declaration takes is a fact the authority settled about it, not a
 * second thing to tell two apart by. Were it part of the identity, two readings of one declaration
 * that disagreed about its arity would be two operations rather than a minting authority that has
 * come apart, and the disagreement would travel as a distinction instead of being found.
 */
public final class DeclaredOperation {

    private final ValueName operation;
    private final int arity;

    DeclaredOperation(ValueName operation, int arity) {
        if (operation == null) {
            throw new IllegalArgumentException("a declared operation names what it was read for");
        }
        if (arity < 0) {
            throw new IllegalArgumentException(
                    "`" + operation + "` is declared to take " + arity + " arguments");
        }
        this.operation = operation;
        this.arity = arity;
    }

    /** What the name was resolved to. What a reader with a rule about an operation asks by. */
    public ValueName operation() {
        return operation;
    }

    /** How many arguments the declaration takes. A value declares none. */
    public int arity() {
        return arity;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof DeclaredOperation each && operation.equals(each.operation);
    }

    @Override
    public int hashCode() {
        return operation.hashCode();
    }

    @Override
    public String toString() {
        return String.valueOf(operation);
    }
}
