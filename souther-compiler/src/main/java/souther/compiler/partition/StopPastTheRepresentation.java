package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * An operation of a behavior's body that ends a run only where what it makes would be more than
 * the representation holds ({@link GetsPast#endsOnlyPastTheRepresentation}): a text longer than a
 * {@code String} holds, or a collection holding more elements than one holds.
 *
 * <p>The classes of a behavior are drawn as though a run gets past such an operation
 * ({@link WorkedOutToReachIt#completionOfARowsRun}), since where the representation stops is no
 * distinction a model made. That a run stops there is still so, and it is said once, of the
 * operation, rather than as a reason some values of every relation past it are open.
 *
 * @param operation the operation as the library names it, or the operator as it is written
 * @param at        where it is written
 */
public record StopPastTheRepresentation(String operation, SourcePos at) {

    public StopPastTheRepresentation {
        Objects.requireNonNull(operation, "a stop is at some operation");
        Objects.requireNonNull(at, "written somewhere");
    }

    /**
     * Every such operation {@code body} works out, each once, in the order they are written: in
     * its root, and in the template of each value it builds, whose operations a run works out
     * where the value is built.
     */
    public static List<StopPastTheRepresentation> in(AnalysisBody body) {
        Set<StopPastTheRepresentation> out = new LinkedHashSet<>();
        collect(body.core(), out);
        body.templatesAfterTheirBuilders().forEach(template -> collect(template, out));
        return List.copyOf(out);
    }

    private static void collect(Core e, Set<StopPastTheRepresentation> out) {
        Core bare = Core.withoutStanding(e);
        for (Core each : Core.subexpressionsAt(bare)) {
            String named = WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(each)
                    .endsOnlyPastTheRepresentation() ? nameOf(each) : null;
            if (named != null && each.pos() != null) {
                out.add(new StopPastTheRepresentation(named, each.pos()));
            }
        }
        List<Core> children = new ArrayList<>();
        Core.forEachChild(bare, children::add);
        children.forEach(child -> collect(child, out));
    }

    /**
     * What a reader is shown the operation as, or null where it is neither an operation of the
     * library kept as the model wrote it nor an operator. A call the library's own body makes,
     * where an operation is worked out in the language, is the library's and stands nowhere the
     * model wrote; the operation it is part of is the one said.
     */
    private static String nameOf(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Binary binary -> binary.op() == BinOp.CONCAT ? "++" : null;
            case Core.PreservedCall kept ->
                    AnOperationApplied.of(kept) instanceof AnOperationApplied applied
                            && applied.operation() instanceof ValueName.Stdlib.Operation operation
                            ? operation.qualified() : null;
            default -> null;
        };
    }
}
