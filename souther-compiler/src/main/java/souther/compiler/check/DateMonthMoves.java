package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

/**
 * A call that moves a date by a number of months written out, read through what the library says
 * of the operation.
 *
 * <p>Not a match on {@code Date.addMonths}. What makes a call a move by months is that the library
 * says the operation is one ({@code OperationFacts}), and any operation declared so is.
 *
 * <p>One step, as a shift by days is read ({@link DateShifts}): which expression the date inside
 * stands for is the reading's to follow. And no chain of them is made here, since two moves by
 * months are not the move by their sum.
 */
public final class DateMonthMoves {

    private DateMonthMoves() {
    }

    /**
     * One move: the months it moves a date by, the date it moves, and what the library says of it.
     *
     * @param months the count of months written out
     * @param date   the date the call was given
     * @param law    the library's account of the move
     */
    public record Step(long months, Core date, BoundOperationFact.MovesADateByMonths law) {
    }

    /**
     * {@code e} as a date moved by a count of months the source wrote out, or null where it is not
     * one: a call that is no move by months, or one whose count is not written out, is not a whole
     * number, or is more than a count holds. The count is folded where the asker reads the call
     * ({@code folded}), so a count given a name is the number it was given.
     */
    public static Step stepOf(Core e, Function<Core, Optional<Object>> folded) {
        ValueName operation = Terms.operationOf(e);
        BoundOperationFact.MovesADateByMonths law = operation == null ? null
                : DefaultBoundOperationFacts.get().movesADateByMonths(operation);
        if (law == null) {
            return null;
        }
        List<Core> args = Terms.argsOf(e);
        int months = CallArguments.positionOf(law.months(), operation);
        int date = CallArguments.positionOf(law.date(), operation);
        if (months < 0 || months >= args.size() || date < 0 || date >= args.size()) {
            return null;
        }
        BigDecimal count = FoldedValue.number(folded.apply(args.get(months)));
        if (count == null || count.stripTrailingZeros().scale() > 0) {
            return null;
        }
        try {
            return new Step(count.longValueExact(), args.get(date), law);
        } catch (ArithmeticException _) {
            return null;
        }
    }
}
