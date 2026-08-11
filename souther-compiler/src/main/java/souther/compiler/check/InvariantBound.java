package souther.compiler.check;

import souther.compiler.ast.Ast;
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
     * What {@code clause} says about a value on {@code carrier}, or empty where it says nothing a
     * range can hold.
     *
     * <p>The one reading of an ordered rule. Which literals a rule may be bounded by and how its
     * values are spaced are facts about what carries the value, so both come from the carrier; the
     * shape of the clause, which side of it the value is on, and where a strict comparison leaves the
     * end are the same questions whatever the values are.
     *
     * <p>A second reader used to answer this for the sites that generate code, keyed on a list of
     * types that did not include the temporal ones. So a bound a report read perfectly was a rule
     * another reader called unreadable, and every boundary of the value it sat in — its siblings'
     * included — was downgraded to one nothing promises is writable.
     */
    public static Optional<InvariantBound> of(Ast.Expr clause, Carrier carrier) {
        if (carrier == null || !(clause instanceof Ast.Binary bin)) {
            return Optional.empty();
        }
        // `0 <= value` says what `value >= 0` says: read the value-bearing side as the left one.
        Ast.Expr left = bin.left();
        Ast.Expr right = bin.right();
        Ast.BinOp op = bin.op();
        if (!isValue(left) && isValue(right)) {
            Ast.Expr swap = left;
            left = right;
            right = swap;
            op = mirrored(op);
        }
        if (!isValue(left)) {
            return Optional.empty();
        }
        Place bound = carrier.literalOf(right);
        if (bound == null) {
            return Optional.empty();
        }
        return ordered(op, bound, carrier);
    }

    /**
     * What {@code clause} says about the number {@code measure} takes of the value, or empty where it
     * says nothing a range can hold.
     *
     * <p>The same reading one operand in. A size is a whole number, so a strict bound names the
     * adjacent one exactly as an {@code Int}'s does, and which size call this is does not come into
     * it — every one of them counts something.
     */
    public static Optional<InvariantBound> ofSize(Ast.Expr clause, ValueName measure) {
        // A size is a whole number whatever it is a size of, so it steps like an `Int` and stops
        // where one does.
        return sizeComparedIn(clause, measure, VALUE)
                .flatMap(read -> ordered(read.op(), Count.of(read.count()), Carrier.WHOLE));
    }

    /**
     * A comparison of a counted number against a literal, as it was written.
     *
     * @param op    the operator, with the count on the left however the clause was spelled
     * @param count what it is compared against
     */
    public record SizeComparison(Ast.BinOp op, BigDecimal count) {}

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
    public static Optional<SizeComparison> sizeComparedIn(Ast.Expr clause, ValueName measure,
                                                          String subject) {
        if (!(clause instanceof Ast.Binary bin)) {
            return Optional.empty();
        }
        Ast.Expr left = bin.left();
        Ast.Expr right = bin.right();
        Ast.BinOp op = bin.op();
        if (!takesSizeOf(left, measure, subject) && takesSizeOf(right, measure, subject)) {
            Ast.Expr swap = left;
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
     * Whether {@code clause} says where the value stops, however this reading turned out.
     *
     * <p>Two questions, and only the second was being asked. Whether a bound was read is
     * {@link #of}'s; whether the model states one at all is this, and a caller with only the first
     * answer reports "the model bounds this position no way" about a declaration two lines above it.
     * A rule of another shape — a format, a quantifier over what the value holds — is not one of
     * these: it says which values exist and not where they stop, and naming it as a line nothing read
     * would send an author after a boundary nobody wrote.
     *
     * <p>An equality is not one either. It names a value rather than an end, is not read by
     * {@link #of}, and a report has nowhere to put one — so saying it went unread would state an
     * obligation that does not exist yet.
     *
     * @param measure the operation the number is taken by, or null where the number is the value
     *                itself
     */
    public static boolean statesAnEnd(Ast.Expr clause, ValueName measure) {
        if (!(clause instanceof Ast.Binary bin) || !orders(bin.op())) {
            return false;
        }
        return measure == null
                ? isValue(bin.left()) || isValue(bin.right())
                : takesSizeOfValue(bin.left(), measure) || takesSizeOfValue(bin.right(), measure);
    }

    /** Whether an operator says where values stop rather than which one a value is. */
    private static boolean orders(Ast.BinOp op) {
        return switch (op) {
            case LT, LE, GT, GE -> true;
            case EQ, NE, AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /** One end, from the comparison and how the carrier's counts are spaced. */
    private static Optional<InvariantBound> ordered(Ast.BinOp op, Place bound, Carrier carrier) {
        boolean steps = carrier.spacing() == Granularity.DISCRETE;
        return switch (op) {
            case GE -> Optional.of(new InvariantBound(true, Endpoint.inclusive(bound)));
            case LE -> Optional.of(new InvariantBound(false, Endpoint.inclusive(bound)));
            case GT -> steps ? stepped(true, carrier.onTheGrid(Count.number(bound).plus(1)))
                    : Optional.of(new InvariantBound(true, Endpoint.exclusive(bound)));
            case LT -> steps ? stepped(false, carrier.onTheGrid(Count.number(bound).minus(1)))
                    : Optional.of(new InvariantBound(false, Endpoint.exclusive(bound)));
            default -> Optional.empty();
        };
    }

    /**
     * Whether the expression is {@code measure} applied to the newtype's value.
     *
     * <p>Asked of the name the application resolved to, not of how it was spelled: an import lets a
     * library operation be written without its qualifier, and a reader comparing text would miss
     * every clause written that way while looking as though it had read them.
     */
    private static boolean takesSizeOfValue(Ast.Expr e, ValueName measure) {
        return takesSizeOf(e, measure, VALUE);
    }

    /** The same of a named subject: {@code value} inside a newtype's rule, a field's name inside the
     * rule of the record that has it. */
    private static boolean takesSizeOf(Ast.Expr e, ValueName measure, String subject) {
        return e instanceof Ast.Apply call && call.args().size() == 1
                && call.args().get(0) instanceof Ast.Var arg && arg.name().equals(subject)
                && call.function() instanceof Ast.Var fn && measure.equals(fn.denotes());
    }

    /**
     * A strict bound moved onto the count beside it — where the carrier has one there.
     *
     * <p>Asked of the carrier, which is the one place that knows where its counts stop. Read off the
     * range of a {@code long} instead, an end one step past the last case of an enumeration was a
     * count no case is at: it reached a cut, an obligation, and the reader that writes an obligation
     * as the value it stands for, which asked the carrier for a case that is not there.
     *
     * <p>No end where the carrier has no count there. Which is not the same as the rule being
     * unsatisfiable, and this does not say which — the two look alike from here, and an end nothing
     * can be written at is the one thing that must not be claimed.
     */
    private static Optional<InvariantBound> stepped(boolean lower, Place onto) {
        return onto == null ? Optional.empty()
                : Optional.of(new InvariantBound(lower, Endpoint.inclusive(onto)));
    }

    private static boolean isValue(Ast.Expr e) {
        return e instanceof Ast.Var v && v.name().equals(VALUE);
    }

    private static Ast.BinOp mirrored(Ast.BinOp op) {
        return switch (op) {
            case LT -> Ast.BinOp.GT;
            case LE -> Ast.BinOp.GE;
            case GT -> Ast.BinOp.LT;
            case GE -> Ast.BinOp.LE;
            default -> op;
        };
    }

    /** A whole number a literal names, or null where it names one with a fraction: a value that
     *  steps one at a time is not bounded at a place between two of its values. */
    public static BigDecimal wholeLiteral(Ast.Expr e) {
        BigDecimal read = literalOf(e);
        return read == null || read.stripTrailingZeros().scale() > 0 ? null : read;
    }

    /** A numeric literal, negation included. A bare integer counts against a decimal, since a literal
     * takes the other side's type. */
    public static BigDecimal literalOf(Ast.Expr e) {
        return switch (e) {
            case Ast.IntLit lit -> BigDecimal.valueOf(lit.value());
            case Ast.DecimalLit lit -> normalized(lit.value());
            case Ast.Neg neg -> negated(literalOf(neg.operand()));
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
