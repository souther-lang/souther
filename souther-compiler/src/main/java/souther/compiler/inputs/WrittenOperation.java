package souther.compiler.inputs;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.util.List;

/**
 * A sum, a difference or a product of two whole numbers or two decimals as the program writes it:
 * with the operator, or as the library's operation called by name ({@code Decimal.add(a, b)}).
 * The two are one operation and stop a run at the same numbers, so a reader of what a step works
 * out takes either.
 */
public final class WrittenOperation {

    private WrittenOperation() {
    }

    /** The two operands of {@code e}, where it is {@code op} of two whole numbers or two
     *  decimals, written as the operator or as the library's operation the library declares to
     *  compute it; null otherwise. */
    public static List<Core> operandsOf(Core e, BinOp op) {
        return switch (Core.withoutStanding(e)) {
            case Core.Binary binary when binary.op() == op
                    && (binary.type() == Type.INT || binary.type() == Type.DECIMAL) ->
                    List.of(binary.left(), binary.right());
            case Core.PreservedCall call when call.args().size() == 2
                    && AnOperationApplied.of(call) instanceof AnOperationApplied applied
                    && applied.theOperatorItComputes() == op -> call.args();
            default -> null;
        };
    }
}
