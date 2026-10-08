package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * An application of one of the language's operations, in either shape a tree gives one: the
 * operation standing as itself, or a call to what its name reached.
 *
 * <p>One reading of both. A reader that knew one shape answered for an operation in that shape
 * and said nothing — or something else — of the same operation in the other, and two readers of
 * one application that knew different shapes read it two ways.
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
            case null, default -> null;
        };
    }

    /** What it passes where {@code which} stands, or null where it passes nothing there. */
    public Core argument(DeclaredArgument which) {
        int at = CallArguments.positionOf(which, operation);
        return at < 0 || at >= args.size() ? null : args.get(at);
    }
}
