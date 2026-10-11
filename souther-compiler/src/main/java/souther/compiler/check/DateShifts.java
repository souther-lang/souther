package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

/**
 * A call that moves a date by a number of days written out, read through what the library says of
 * the operation.
 *
 * <p>Not a match on {@code Date.addDays}. What makes a call a shift is the form the library says it
 * answers ({@code OperationFacts}): a date weighed one and a count of days beside it, and nothing
 * else added. Any operation declared that way is a shift, and one that is not declared that way is
 * not, whatever it is called.
 *
 * <p>One step at a time. Which expression the date inside a step stands for — a name, a binding, a
 * position — is the reading's, so a caller that holds one asks for the next step of whatever it
 * found there rather than being handed a chain this walk made out of the syntax.
 */
public final class DateShifts {

    private DateShifts() {
    }

    /**
     * One shift: the days it moves a date by, and the date it moves.
     *
     * @param days the count of days written out, times what the library weighs it by
     * @param date the date the call was given
     */
    public record Step(long days, Core date) {
    }

    /**
     * {@code e} as a date moved by a count of days the source wrote out, or null where it is not
     * one.
     *
     * <p>Null both for a call that is no shift and for one whose count is not written out or is not
     * a whole number of days: a count another input supplies is a number of two inputs, and no
     * chain of constant shifts of one.
     */
    public static Step stepOf(Core e, Symbols symbols) {
        ValueName operation = Terms.operationOf(e);
        if (operation == null) {
            return null;
        }
        LinearForm<DeclaredArgument> says =
                DefaultBoundOperationFacts.get().answersAFormOfItsArguments(operation);
        if (says == null || says.constant().signum() != 0 || says.coefs().size() != 2) {
            return null;
        }
        List<Core> args = Terms.argsOf(e);
        Core date = null;
        Long days = null;
        for (Map.Entry<DeclaredArgument, ExactRatio> each : says.coefs().entrySet()) {
            int at = CallArguments.positionOf(each.getKey(), operation);
            if (at < 0 || at >= args.size()) {
                return null;
            }
            if (each.getKey().stands() == Type.Prim.DATE
                    && each.getValue().compareTo(ExactRatio.ONE) == 0) {
                date = args.get(at);
            } else if (each.getKey().stands() == Type.Prim.INT) {
                days = daysOf(args.get(at), each.getValue(), symbols);
            } else {
                return null;
            }
        }
        return date == null || days == null ? null : new Step(days, date);
    }

    /** What {@code written}, weighed by {@code weight}, comes to as a whole count of days, or null
     *  where it is not written out or does not come to one. */
    private static Long daysOf(Core written, ExactRatio weight, Symbols symbols) {
        BigDecimal folded = StatedComparison.foldedNumber(written, symbols);
        if (folded == null
                || !(weight.times(ExactRatio.of(folded))
                        instanceof ExactAnswer.Held<ExactRatio> product)
                || !product.value().isWhole()
                || !(product.value().truncated() instanceof ExactAnswer.Held<BigInteger> whole)) {
            return null;
        }
        return whole.value().bitLength() < Long.SIZE ? whole.value().longValue() : null;
    }
}
