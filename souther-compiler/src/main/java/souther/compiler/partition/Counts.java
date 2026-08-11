package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Place;

import java.math.BigDecimal;

/**
 * A count read as how many of something there are.
 *
 * <p>Not every count is one. A size is a count on the whole-number carrier, and a count on that
 * carrier is still not a size where it has a fraction in it or names more things than can be
 * counted — so the two questions are asked apart, here, rather than at each place that wants to build
 * a collection of that many.
 */
final class Counts {

    /**
     * The count a fixture settles its position at, reaching through the newtype it may be wrapped
     * in, or null where it settles none.
     *
     * <p>Only a written number. A temporal fixture carries its text and not its count, and it stays
     * unsettled rather than being read back: what a settled position is for is asking the record's
     * rules what is left beside it, and those rules are read over the positions the projection
     * holds — which the temporal ones are not yet.
     *
     * <p>Here rather than beside either walk. Both of them settle a field before choosing the next,
     * and two readings of what a written value counts as are two chances to settle different
     * things.
     */
    static Place writtenIn(Ast.Expr written) {
        return switch (written) {
            case Ast.IntLit i -> Count.of(i.value());
            case Ast.DecimalLit d -> Count.of(d.value());
            case Ast.Neg n -> {
                Place inner = writtenIn(n.operand());
                yield inner == null ? null : Count.number(inner).negate();
            }
            case Ast.Apply a when a.args().size() == 1 -> writtenIn(a.args().get(0));
            case null, default -> null;
        };
    }

    /**
     * How many {@code min} says there are at least, or 0 where it says nothing about that.
     *
     * <p>One reading, because a floor is written on a type and on the record that has a value of it
     * as a field, and the two have to come to the same number from the same end. An end the range
     * stops short of is the next count up: a rule reading {@code > 3} is met by four and not by
     * three, and a caller reading the number and dropping whether the end is one of the range's own
     * has a floor one short of what was written.
     */
    static int leastFrom(Endpoint min) {
        if (min == null) {
            return 0;
        }
        int at = asSize(min.at());
        if (at < 0) {
            return 0;
        }
        return min.inclusive() ? at : at + 1;
    }

    /** {@code at} as a number of things, or -1 where it is not one. A count is whole and no larger
     * than the values there are to count, so a number outside that is a size nothing carries. */
    static int asSize(Place at) {
        if (!(at instanceof Count count) || !count.whole()
                || count.at().compareTo(BigDecimal.valueOf(Integer.MAX_VALUE)) > 0
                || count.signum() < 0) {
            return -1;
        }
        return count.at().intValue();
    }

    private Counts() {}
}
