package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.ast.Hir;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * Where one conjunct of a numeric newtype's invariant leaves its value able to stop.
 *
 * <p>Read off the comparison. What a report measures a position at is where the rules about it stop,
 * and that is not the same question as which runtime check the rule becomes: the runtime states a
 * decimal above zero directly and has no word for a decimal above five, so a reader written for it
 * answers "no bound" to a rule that plainly draws one. Asked here of an ordering of
 * {@code value} against a literal, and of one end at a time. An equality states both ends at once
 * and is not read: it was not read before either, and giving a position one value is a different
 * answer from bounding it, which the report has nowhere to put yet.
 *
 * <p>Over whole numbers a strict comparison names the adjacent value, and the end lands on a value
 * the rule admits. Over decimals there is no adjacent value, so the end stays on the literal and says
 * that the literal is not one of its own.
 *
 * @param lower whether this bounds the value below; otherwise above
 */
public record InvariantBound(boolean lower, Endpoint end) {

    private static final String VALUE = "value";

    /**
     * What a reading of one ordered rule came to.
     *
     * <p>Three answers and not two. A rule either places an end, or states none this reads, or
     * states one the order does not reach — and the third was being given the second's answer. They
     * are opposite facts: nothing follows about a position from a rule nobody read, and everything
     * follows from a rule that steps past the last value there is. Told apart here, at the one place
     * an ordered rule is read, so that a reader cannot arrive at the wrong one by leaving a case out.
     */
    public sealed interface Read {

        /** The end the rule places. */
        record AnEnd(InvariantBound bound) implements Read {}

        /**
         * The rule states no end this reading has a word for.
         *
         * <p>An equality states both ends at once and a disequality states neither; a literal the
         * order does not read is not an end either. What they share is that this says nothing about
         * where the position stops, and a reader may narrow nothing by them.
         */
        record NoEnd() implements Read {}

        /**
         * The rule states an end past the last value of the order, so it admits nothing.
         *
         * <p>Reached where a strict end is sharpened onto the value beside the one named and the
         * order has none there: one past the last case of an enumeration, one past the last day a
         * calendar reaches, one past the greatest whole number. The position holds no value, which
         * is a fact about the rule and not a limit of this reading.
         */
        record PastWhereTheOrderStops() implements Read {}
    }

    private static final Read NO_END = new Read.NoEnd();
    private static final Read PAST_THE_END = new Read.PastWhereTheOrderStops();

    /**
     * What {@code clause} says about a value on {@code carrier}.
     *
     * <p>The one reading of an ordered rule. Which literals a rule may be bounded by and how its
     * values are spaced are facts about the order the value sits on, so both come from the carrier; the
     * shape of the clause, which side of it the value is on, and where a strict comparison leaves the
     * end are the same questions whatever the values are.
     *
     * <p>A second reader used to answer this for the sites that generate code, keyed on a list of
     * types that did not include the temporal ones. So a bound a report read perfectly was a rule
     * another reader called unreadable, and every boundary of the value it sat in — its siblings'
     * included — was downgraded to one nothing promises is writable.
     */
    public static Read of(Hir.Expr clause, Carrier carrier) {
        if (carrier == null || !(clause instanceof Hir.Binary bin)) {
            return NO_END;
        }
        // `0 <= value` says what `value >= 0` says: read the value-bearing side as the left one.
        Hir.Expr left = bin.left();
        Hir.Expr right = bin.right();
        BinOp op = bin.op();
        if (!isValue(left) && isValue(right)) {
            Hir.Expr swap = left;
            left = right;
            right = swap;
            op = mirrored(op);
        }
        if (!isValue(left)) {
            return NO_END;
        }
        Place bound = carrier.literalOf(right);
        if (bound == null) {
            return NO_END;
        }
        return ordered(op, bound, carrier);
    }

    /**
     * What {@code clause} says about the number {@code measure} takes of the value.
     *
     * <p>The same reading one operand in. A size is a whole number, so a strict bound names the
     * adjacent one exactly as an {@code Int}'s does, and which size call this is does not come into
     * it — every one of them counts something.
     */
    public static Read ofSize(Hir.Expr clause, ValueName measure) {
        // A size is a whole number whatever it is a size of, so it steps like an `Int` and stops
        // where one does.
        return sizeComparedIn(clause, measure, VALUE)
                .map(read -> ordered(read.op(), Count.of(read.count()), Carrier.WHOLE))
                .orElse(NO_END);
    }

    /**
     * A comparison of a counted number against a literal, as it was written.
     *
     * @param op    the operator, with the count on the left however the clause was spelled
     * @param count what it is compared against
     */
    public record SizeComparison(BinOp op, BigDecimal count) {}

    /**
     * The comparison {@code clause} makes about {@code measure} taken of {@code subject}, or empty
     * where it makes none.
     *
     * <p>Before any reading of what it means. {@link #ofSize} turns one of these into an end of a
     * range and answers nothing for the comparisons that are not ends — an equality states both ends
     * at once and a disequality states neither, so a range has nowhere to put them. A reader asking
     * something a range cannot hold, such as whether a count of none is refused, needs the comparison
     * itself. Recognised here so that the shape is read in one place and what it means in as many as
     * there are questions.
     */
    public static Optional<SizeComparison> sizeComparedIn(Hir.Expr clause, ValueName measure,
                                                          String subject) {
        if (!(clause instanceof Hir.Binary bin)) {
            return Optional.empty();
        }
        Hir.Expr left = bin.left();
        Hir.Expr right = bin.right();
        BinOp op = bin.op();
        if (!takesSizeOf(left, measure, subject) && takesSizeOf(right, measure, subject)) {
            Hir.Expr swap = left;
            left = right;
            right = swap;
            op = mirrored(op);
        }
        if (!takesSizeOf(left, measure, subject)) {
            return Optional.empty();
        }
        BigDecimal count = wholeLiteral(right);
        return count == null ? Optional.empty() : Optional.of(new SizeComparison(op, count));
    }

    /**
     * The end an ordering places on a coordinate already recognised, or empty where the comparison
     * places none.
     *
     * <p>The same reading {@link #of} finishes with, entered one step later. {@link #of} recognises
     * its coordinate by the word {@code value}, which is the only name a newtype's own clause can use
     * for it; a clause written on the record holding a field names the field, or a size of it, or a
     * field of a field, and which of those it named is settled before this by the naming the
     * discharge check already does. What is left is where the comparison leaves the end, and that is
     * one question with one answer whatever recognised the coordinate — asked again here, a strict
     * bound would land on the neighbour in one reader and on the literal in the other.
     *
     * @param op    the comparison, with the coordinate on its left
     * @param bound what the coordinate is compared against
     */
    static Read at(BinOp op, Hir.Expr bound, Carrier carrier) {
        if (carrier == null || bound == null) {
            return NO_END;
        }
        Place at = carrier.literalOf(bound);
        return at == null ? NO_END : ordered(op, at, carrier);
    }

    /** Which comparison an operand on the right states of one on the left. */
    static BinOp flipped(BinOp op) {
        return mirrored(op);
    }

    /** Whether {@code op} says where values stop rather than which one a value is. */
    static boolean ordering(BinOp op) {
        return ComparisonPlacement.orders(op);
    }

    /** One end, from the comparison and how the carrier's counts are spaced. */
    private static Read ordered(BinOp op, Place bound, Carrier carrier) {
        boolean steps = carrier.spacing() == Granularity.DISCRETE;
        return switch (op) {
            case GE -> placed(true, Endpoint.inclusive(bound));
            case LE -> placed(false, Endpoint.inclusive(bound));
            case GT -> steps ? stepped(true, carrier.onTheGrid(Count.number(bound).plus(1)))
                    : placed(true, Endpoint.exclusive(bound));
            case LT -> steps ? stepped(false, carrier.onTheGrid(Count.number(bound).minus(1)))
                    : placed(false, Endpoint.exclusive(bound));
            default -> NO_END;
        };
    }

    private static Read placed(boolean lower, Endpoint end) {
        return new Read.AnEnd(new InvariantBound(lower, end));
    }

    /**
     * Whether {@code e} is {@code measure} applied to the named subject: {@code value} inside a
     * newtype's rule, a field's name inside the rule of the record that has it.
     *
     * <p>Asked of the name the application resolved to, not of how it was spelled: an import lets a
     * library operation be written without its qualifier, and a reader comparing text would miss
     * every clause written that way while looking as though it had read them.
     */
    private static boolean takesSizeOf(Hir.Expr e, ValueName measure, String subject) {
        return e instanceof Hir.Apply call && call.args().size() == 1
                && call.args().get(0) instanceof Hir.Var arg && arg.name().equals(subject)
                && call.function() instanceof Hir.Var.Denoting fn && measure.equals(fn.denotes());
    }

    /**
     * A strict bound moved onto the count beside it — where the carrier has one there.
     *
     * <p>Asked of the carrier, which is the one place that knows where its counts stop. Read off the
     * range of a {@code long} instead, an end one step past the last case of an enumeration was a
     * count no case is at: it reached a cut, an obligation, and the reader that writes an obligation
     * as the value it stands for, which asked the carrier for a case that is not there.
     *
     * <p>Where the carrier has no count there, the rule admits nothing. That is said as itself. It was
     * answered "no end this reading could make of it", which is what a rule of another shape gets —
     * so a position the rules leave empty read exactly like a position nothing was written about,
     * and the count deciding whether the type has any value never heard of the rule.
     */
    private static Read stepped(boolean lower, Place onto) {
        return onto == null ? PAST_THE_END
                : placed(lower, Endpoint.inclusive(onto));
    }

    private static boolean isValue(Hir.Expr e) {
        return e instanceof Hir.Var v && v.name().equals(VALUE);
    }

    private static BinOp mirrored(BinOp op) {
        return switch (op) {
            case LT -> BinOp.GT;
            case LE -> BinOp.GE;
            case GT -> BinOp.LT;
            case GE -> BinOp.LE;
            default -> op;
        };
    }

    /** A whole number a literal names, or null where it names one with a fraction: a value that
     *  steps one at a time is not bounded at a place between two of its values. */
    public static BigDecimal wholeLiteral(Hir.Expr e) {
        BigDecimal read = literalOf(e);
        return read == null || read.stripTrailingZeros().scale() > 0 ? null : read;
    }

    /** A numeric literal, negation included. A bare integer counts against a decimal, since a literal
     * takes the other side's type. */
    public static BigDecimal literalOf(Hir.Expr e) {
        return switch (e) {
            case Hir.IntLit lit -> BigDecimal.valueOf(lit.value());
            case Hir.DecimalLit lit -> normalized(lit.value());
            case Hir.Neg neg -> negated(literalOf(neg.operand()));
            case null, default -> null;
        };
    }

    /**
     * The number a literal names, without how many places it was written to.
     *
     * <p>{@code 5.0m} and {@code 5.00m} are one constraint, so they have to reach a range as one
     * number: two spellings of an end would be two lines through a position, both holding the same
     * values, and one boundary owed twice under one printed figure. Trailing zeros left of the point
     * are put back, so a hundred is written as one.
     */
    private static BigDecimal normalized(BigDecimal value) {
        BigDecimal bare = value.stripTrailingZeros();
        return bare.scale() < 0 ? bare.setScale(0) : bare;
    }

    private static BigDecimal negated(BigDecimal value) {
        return value == null ? null : value.negate();
    }
}
