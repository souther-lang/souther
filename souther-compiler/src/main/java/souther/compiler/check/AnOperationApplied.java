package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * An application of one of the language's operations, in any shape a tree gives one: the operation
 * standing as itself, a call to what its name reached, or the operator the library declares it as.
 *
 * <p>One reading of all of them. A reader that knew one shape answered for an operation in that
 * shape and said nothing — or something else — of the same operation in the other, and two readers
 * of one application that knew different shapes read it two ways. {@code a ++ b} is
 * {@code List.append(a, b)} over lists and {@code String.append(a, b)} over strings, so what either
 * operation says is said of the operator too.
 *
 * @param operation which operation is applied
 * @param args      what it is handed, in the order the declaration takes them
 */
public record AnOperationApplied(ValueName operation, List<Core> args) {

    /** {@code e} read as an application of an operation, or null where it applies none. */
    public static AnOperationApplied of(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.PreservedCall kept ->
                    new AnOperationApplied(kept.declared().operation(), kept.args());
            case Core.Call call when call.fn() instanceof Core.Reached reached ->
                    new AnOperationApplied(reached.denotes(), call.args());
            // The checker types the operator over two strings or two lists and refuses it over
            // anything else, so a join that is no string's is a list's: the string's append and the
            // list's are the two operations it can be.
            case Core.Binary joined when joined.op() == BinOp.CONCAT -> new AnOperationApplied(
                    ValueName.Stdlib.operation(Type.STRING.equals(joined.type()) ? "String" : "List",
                            "append"), List.of(joined.left(), joined.right()));
            case null, default -> null;
        };
    }

    /** What it passes where {@code which} stands, or null where it passes nothing there. */
    public Core argument(DeclaredArgument which) {
        int at = CallArguments.positionOf(which, operation);
        return at < 0 || at >= args.size() ? null : args.get(at);
    }
}
