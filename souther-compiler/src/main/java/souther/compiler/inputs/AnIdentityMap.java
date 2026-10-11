package souther.compiler.inputs;

import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.core.Core;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.function.Function;

/**
 * A call of an operation answering one value per element of a container, handed a closure that
 * answers each element as it is.
 *
 * <p>What it answers is the container's own values, each as often as the container holds it:
 * {@code List.map(k -> k, ks)} is {@code ks}. Both halves are needed. That the operation answers one
 * value per element ({@link BuiltFrom#mapsEachElementOf}) says nothing of what the values are, and a
 * closure that returns its parameter says nothing of how many answers there are — handed to a
 * {@code Set.map} it would leave the values and lose their count.
 *
 * <p>The closure's body is its parameter itself and not the parameter standing as a wider type: a
 * value widened is another value of another type, and what is said of the answer would be said of
 * values the container does not hold.
 */
public final class AnIdentityMap {

    /**
     * The argument {@code operation}, applied to {@code args}, answers as it is, or null where it
     * answers anything else.
     *
     * @param blockOf the block a closure argument stands for, or null where it stands for none
     */
    public static DeclaredArgument of(ValueName operation, List<Core> args,
                                      Function<Core, Core.Block> blockOf) {
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        DeclaredArgument mapped = built == null ? null : built.mapsEachElementOf();
        if (mapped == null) {
            return null;
        }
        Core.Block closure = closureBeside(args, mapped.position(), blockOf);
        return closure != null && answersItsParameter(closure) ? mapped : null;
    }

    /**
     * The one closure among {@code args} other than the container at {@code container}, or null
     * where there is none or more than one.
     */
    static Core.Block closureBeside(List<Core> args, int container,
                                    Function<Core, Core.Block> blockOf) {
        Core.Block closure = null;
        for (int i = 0; i < args.size(); i++) {
            Core.Block block = i == container ? null : blockOf.apply(args.get(i));
            if (block != null) {
                if (closure != null) {
                    return null;
                }
                closure = block;
            }
        }
        return closure;
    }

    /** Whether {@code closure} takes one value and answers that value. */
    private static boolean answersItsParameter(Core.Block closure) {
        if (closure.params().size() != 1 || closure.params().getFirst().binding() == null) {
            return false;
        }
        return switch (closure.body()) {
            case Core.Read read -> read.binding().equals(closure.params().getFirst().binding());
            // The parameter standing as a wider type is another value of another type.
            case Core.Widen _ -> false;
            default -> false;
        };
    }

    private AnIdentityMap() {}
}
