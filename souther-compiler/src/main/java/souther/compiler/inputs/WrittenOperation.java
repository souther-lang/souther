package souther.compiler.inputs;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A sum, a difference or a product of two whole numbers or two decimals as the program writes it:
 * with the operator, or as the library's operation called by name ({@code Decimal.add(a, b)}).
 * The two are one operation and stop a run at the same numbers, so a reader of what a step works
 * out takes either.
 */
public final class WrittenOperation {

    private WrittenOperation() {
    }

    /** The kernels of the library each operator is written as. */
    private static final Map<BinOp, Set<Kernel>> AS_THE_LIBRARYS = Map.of(
            BinOp.ADD, Set.of(Kernel.INT_ADD, Kernel.DECIMAL_ADD),
            BinOp.SUB, Set.of(Kernel.INT_SUBTRACT, Kernel.DECIMAL_SUBTRACT),
            BinOp.MUL, Set.of(Kernel.INT_MULTIPLY, Kernel.DECIMAL_MULTIPLY));

    /** The two operands of {@code e}, where it is {@code op} of two whole numbers or two
     *  decimals, written as the operator or as the library's operation; null otherwise. */
    public static List<Core> operandsOf(Core e, BinOp op, Symbols symbols) {
        return switch (Core.withoutStanding(e)) {
            case Core.Binary binary when binary.op() == op
                    && (binary.type() == Type.INT || binary.type() == Type.DECIMAL) ->
                    List.of(binary.left(), binary.right());
            case Core.PreservedCall call when call.args().size() == 2
                    && call.operation() instanceof ValueName.Stdlib.Operation operation
                    && isTheLibrarys(op, symbols.kernelOf(operation)) -> call.args();
            default -> null;
        };
    }

    /** Whether {@code kernel} is the library's {@code op}; a kernel of none is no operator. */
    private static boolean isTheLibrarys(BinOp op, Kernel kernel) {
        return kernel != null && AS_THE_LIBRARYS.get(op).contains(kernel);
    }
}
