package souther.compiler.types;

/**
 * Which binding a name is. A parameter, a {@code let}, a lambda's parameter, a {@code match} arm's
 * binding: each is one of these, and two of them are the same binding when they are equal.
 *
 * <p>What a binding is cannot be worked out from how it was spelled — a body may bind a name a
 * module declares, and two bodies may bind one spelling — nor from where it was written, since a
 * pass that expands a helper stamps the call site over the positions in the copy. So the binder
 * carries this, every name that resolves to it carries the same value, and asking whether a name is
 * that binding is asking whether the two are equal. There is nothing else to compare.
 *
 * <p>It is a value, not a token: the query database decides that an answer is unchanged by comparing
 * it, and an {@code Ast.Module} is what many keys answer, so an identity that differed between two
 * readings of one source would make every edit look like a change to everything downstream.
 *
 * <p>{@code ordinal} counts the bindings of {@code owner} in the order they are written. It is not
 * stable against an edit — binding something ahead of it moves it — but the movement stops at the
 * definition, which is the unit the queries already ask in.
 */
public record BindingId(BindingOwner owner, int ordinal) {

    public BindingId {
        if (owner == null) {
            throw new IllegalArgumentException("a binding belongs to something: " + ordinal);
        }
    }

    @Override
    public String toString() {
        return owner + "." + ordinal;
    }
}
