package souther.compiler.types;

import java.util.Objects;

/**
 * A call of one of the language's operations some source wrote: which operation, and where the
 * call stands.
 *
 * <p>What a closure's applications are the applications of. The closure's body is one construct
 * however many times it is applied, so a reader naming the construct of the model that applied it
 * names this call, and the operation is what that reader calls it by.
 *
 * @param operation the operation of the language called
 * @param at        where the call stands, in the copy of the body it stands in
 */
public record ACallOfAnOperation(ValueName.Stdlib operation, ConstructOccurrence at) {

    public ACallOfAnOperation {
        Objects.requireNonNull(operation, "a call is of some operation");
        Objects.requireNonNull(at, "and stands somewhere");
        if (!at.isWritten()) {
            throw new IllegalArgumentException("a call some source wrote: " + at);
        }
    }
}
