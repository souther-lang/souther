package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Objects;

/**
 * A comparison of a quotient by a value with a number, read as what it states of the dividend and
 * the divisor on each side of nought.
 *
 * <p>A quotient by a value is no form of what it divides ({@link Terms#quotient}), so no reading of
 * it is arithmetic over them. What a comparison of it with a number states is a line all the same,
 * on each sign of the divisor: above nought {@code n / d >= k} is {@code n >= k * d}, and below
 * nought the relation turns. The quotient is exact, so nothing is dropped between the two
 * statements.
 *
 * <p><b>The comparison states something only where the divisor is not nought.</b> At nought the
 * division aborts and the run stops before the comparison comes out either way, so the statement is
 * read only where the division answers ({@link Read#answers}) and a row at nought is a row of neither
 * outcome. There, the two sides are the divisor above
 * nought and its denial: read as one atom and its denial, a case of either knows the other
 * excludes; read as two atoms, above and below nought, a case where one side's line decides could
 * ask a row to stand on the other side's line as well.
 *
 * <p><b>Both signs are read, and which a run is on is not this reader's.</b> Where a guard on the
 * way keeps the divisor above nought, or its type is declared so, the side below has no row, as any
 * line a path has already left behind has none. The sign is then a fact about the inputs that
 * reach the comparison however it was written, and the comparison means one thing on every path
 * to it.
 *
 * <p><b>The number is written as the source would write it.</b> {@code k} times the divisor is
 * {@code (p * d) / q} for {@code k} in lowest terms, each literal of the type the elaborator's rule
 * for the operator takes beside the value ({@link ArithmeticCheck}), so a half over a whole divisor
 * is {@code (1 * d) / 2} and not a product no source could write.
 */
public final class QuotientByAValue {

    private QuotientByAValue() {}

    /**
     * What a comparison of a quotient by a value states, on each sign of the divisor.
     *
     * @param <E>     the environment the dividend and the divisor are read in
     * @param at      where the quotient was written, which is where its operands are read
     * @param answers the divisor away from nought, which is where the division answers
     * @param signed  the divisor above nought, whose denial is the other side there
     * @param above   the dividend against the number times the divisor, which holds exactly where
     *                the comparison of the quotient does where the divisor is above nought
     * @param below   the same, turned, where it is below
     */
    public record Read<E>(E at, StatedComparison answers, StatedComparison signed,
                          StatedComparison above, StatedComparison below) {

        public Read {
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(answers, "a division answers somewhere");
            Objects.requireNonNull(signed, "the divisor stands on a side of nought");
            Objects.requireNonNull(above, "the comparison is stated above nought");
            Objects.requireNonNull(below, "and below it");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the dividend and the divisor of a
     * quotient on one of its sides — or null where neither side is a quotient by a value that is
     * not the same on every run, the other side is no number the same on every run, or a statement
     * of it is no comparison a source could write.
     *
     * <p>A quotient by a number the same on every run is arithmetic over the dividend, and is the
     * arithmetic's to read. A quotient by a value on one side leaves nothing to try on the other:
     * the quotient is no number the same on every run, so the other side is never the quotient
     * and this one the number.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides, Symbols symbols) {
        for (boolean quotientFirst : List.of(true, false)) {
            ValueStanding.ReadThrough<E> side = ACallAgainstANumber.under(
                    quotientFirst ? comparison.left() : comparison.right(), at, sides);
            if (!(Core.withoutStanding(side.value()) instanceof Core.Binary quotient)
                    || quotient.op() != BinOp.DIV
                    || sides.constant(quotient.right(), side.at()) != null) {
                continue;
            }
            ExactRatio against =
                    sides.constant(quotientFirst ? comparison.right() : comparison.left(), at);
            if (against == null) {
                return null;
            }
            Rel written = (quotientFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            Core dividend = quotient.left();
            Core divisor = quotient.right();
            StatedComparison answers =
                    ConstantComparison.stated(Rel.NE, divisor, ExactRatio.ZERO);
            StatedComparison signed = ConstantComparison.stated(Rel.GT, divisor, ExactRatio.ZERO);
            Core times = timesTheDivisor(against, divisor, symbols);
            Core.BinaryReading reading = times == null ? null
                    : ConstantComparison.comparedAs(dividend.type(), times.type());
            return answers == null || signed == null || reading == null ? null
                    : new Read<>(side.at(), answers, signed,
                    new StatedComparison(ComparisonClaim.stating(written), dividend, times,
                            reading),
                    new StatedComparison(ComparisonClaim.stating(written.turned()), dividend,
                            times, reading));
        }
        return null;
    }

    /** {@code k} times {@code divisor}, as {@code (p * divisor) / q} for {@code k} at {@code p/q}. */
    private static Core timesTheDivisor(ExactRatio k, Core divisor, Symbols symbols) {
        ExactRatio.Terms terms = k.asTerms();
        Core product = operated(BinOp.MUL, terms.comesTo(), divisor, true, symbols);
        return product == null || terms.per().equals(ExactRatio.ONE) ? product
                : operated(BinOp.DIV, terms.per(), product, false, symbols);
    }

    /**
     * {@code value} and {@code number} under {@code op}, the number on the left where
     * {@code numberFirst} says so and written as the first literal the rule for {@code op} takes
     * there — or null where it takes none.
     */
    private static Core operated(BinOp op, ExactRatio number, Core value, boolean numberFirst,
                                 Symbols symbols) {
        for (Core literal : ConstantComparison.literalsOf(number, value.pos())) {
            Core left = numberFirst ? literal : value;
            Core right = numberFirst ? value : literal;
            if (ArithmeticCheck.of(op, left.type(), right.type(), numberFirst, !numberFirst,
                    symbols) instanceof ArithmeticCheck.Allowed(Type type,
                                                                Core.BinaryReading reading)) {
                return new Core.Binary(op, left, right, reading, ConstructOccurrence.unwritten(),
                        type, value.pos());
            }
        }
        return null;
    }
}
