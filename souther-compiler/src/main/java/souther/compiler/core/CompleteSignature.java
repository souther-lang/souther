package souther.compiler.core;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Objects;

/**
 * A declaration that says what it answers as well as what it takes.
 *
 * <p>The condition a call has to meet to be kept standing. A declaration may leave its result to its
 * body — most do, and nothing is wrong with that — but a call typed without expanding it has only
 * what the declaration says, so an operation a representation keeps must say all of it. The
 * requirement is on being kept, not on being a library function or a helper: it is the same
 * condition whichever namespace the name is in, because it is the same thing being asked of it.
 *
 * <p>A type rather than a check, so the incompleteness cannot travel. Were the result allowed to be
 * absent here, every reader of a kept call would have to answer for a result that is not there, and
 * the first one that did not would fail somewhere with nothing to say about which operation or which
 * representation was at fault.
 *
 * <p>The operation is held here rather than beside this. What a signature is the signature of, and
 * what it says, are one fact: passed as two values, a signature could be paired with an operation it
 * is not the signature of, and everything downstream that types a call against it would be typing it
 * against another declaration with nothing to say so. {@link souther.compiler.types.ReachName} holds
 * a route and a denotation together for the same reason.
 *
 * <p>So this is where a {@link DeclaredOperation} is minted, once, as this comes to be. What may
 * make one of those is then the question of what may make one of these, and the two ways in below
 * are the whole of the answer.
 *
 * <p><b>Not a record, and the canonical constructor is not reachable.</b> A record publishes a
 * constructor taking whatever its components are, and a language that lets one be narrowed would
 * still be answering the question with a modifier — anything in this package could call it. What
 * holds this to its two ways in is that both are named and both are counted.
 */
public final class CompleteSignature {

    private final DeclaredOperation declared;
    private final List<Type> params;
    private final Type result;

    private CompleteSignature(ValueName operation, List<Type> params, Type result) {
        if (result == null) {
            throw new IllegalStateException("`" + operation + "` is kept standing by a representation"
                    + " that reads it, so it must declare what it answers: a call kept unexpanded is"
                    + " typed from its declaration alone");
        }
        this.params = List.copyOf(params);
        this.result = result;
        this.declared = new DeclaredOperation(operation, this.params.size());
    }

    /**
     * The signature {@code operation} was declared with, refusing one that leaves its result to its
     * body.
     *
     * <p>Raised where a representation says what it keeps, so an operation that cannot be typed
     * without expanding it is answered for once, by name, rather than as a failure at whichever call
     * happened to be reached first.
     *
     * <p>What the parameters are is the declaration's own: this is the way in for a name whose
     * declaration states both halves of its signature, which is what the library's operations do.
     */
    public static CompleteSignature ofDeclaration(ValueName operation, List<Type> params,
                                                  Type result) {
        return new CompleteSignature(operation, params, result);
    }

    /**
     * The signature of a value: no parameters, and what its own check settled it as.
     *
     * <p>A second way in and not a shorthand for the first. A value's declaration does not state
     * what it answers — a value is written as a body and the check works its type out — so the
     * result comes from having checked it, while the empty parameter list is the declaration's:
     * being written with no parameters is what makes it a value rather than a helper. The caller is
     * the one place that has both, and it has them at the same moment.
     *
     * <p>Held to the same condition as a declared operation's, so a reader that keeps a reference to
     * a value standing and one that keeps a call standing are answered by the same thing. A value
     * reference is an application of no arguments, and nothing downstream has to learn that a name
     * can stand for one.
     */
    public static CompleteSignature ofSettledValue(ValueName value, Type result) {
        return new CompleteSignature(value, List.of(), result);
    }

    /** The operation this is the signature of, read against this declaration. */
    public DeclaredOperation declaring() {
        return declared;
    }

    /** What the declaration takes. */
    public List<Type> params() {
        return params;
    }

    /** What the declaration answers. */
    public Type result() {
        return result;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CompleteSignature each
                && declared.equals(each.declared)
                && params.equals(each.params)
                && result.equals(each.result);
    }

    @Override
    public int hashCode() {
        return Objects.hash(declared, params, result);
    }

    @Override
    public String toString() {
        return declared + params.toString() + " -> " + result;
    }
}
