package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The clauses reaching a value, read for where each of its positions stops.
 *
 * <p>Beside the reading that turns those same clauses into bounds for the report, and beside the one
 * that reads them for which values a position may hold — over the same list, at the same moment.
 * Which clauses reach a value is settled once, by the walk that gathers them; what each reading
 * makes of a clause is its own.
 *
 * <p><b>Why it is not the interval algebra.</b> That one carries one number per position and relates
 * positions to each other by differences, which is worth having and is available only where a model
 * adds and subtracts — so it holds an {@code Int} and a {@code Decimal} and nothing else. This holds
 * every order there is and relates no two positions. Both may read one rule about an {@code Int},
 * and neither is the other's copy: what each can show is its own.
 *
 * <p><b>Why it is not the value sets.</b> Those name which values a position may take, as a finite
 * set or a finite exclusion, and an ordering names no finite set — there are as many dates below a
 * date as anyone likes. Pushing orderings into them would make one finite-set evaluator answer for
 * enum equality, enum ordering, numeric ordering and date ordering at once, which is four readings
 * wearing one name.
 *
 * <p><b>Every range this puts on a position is inside what the order holds.</b> Not an unbounded
 * range narrowed at the end: what is below the empty string is nothing, and a reading open below
 * would take {@code value < ""} for a rule leaving room underneath. The extent is the scale's
 * ({@link OrderScale#extent}) and it is applied where a rule becomes a range, which is the one place
 * a position is spoken about.
 *
 * <p>Applied there and not once around the whole reading, because whether an <em>alternative</em>
 * admits anything is asked of each branch. A branch left short of the order's own ends is a branch
 * whose emptiness nothing can see, and the choice between two such branches then turned on whether
 * they happened to be empty at the same position: {@code a < "" || a < ""} was refused and
 * {@code a < "" || b < ""} was not.
 *
 * <p><b>Equalities are read and disequalities are not.</b> An equality states both ends at once,
 * which is a range with one value in it and is exactly what this holds; {@code /=} states neither
 * end, and the values a denial leaves are a set rather than a range. Under a denial the two swap
 * places, which is the same rule read once.
 */
final class OrderedReading {

    private final Terms terms;
    private final Denotations at;
    /** What each position's values are ordered on, for the positions that are ordered at all. */
    private final Map<Term, OrderScale> scales;

    private OrderedReading(Terms terms, Denotations at, Map<Term, OrderScale> scales) {
        this.terms = terms;
        this.at = at;
        this.scales = scales;
    }

    /**
     * Where {@code clauses} leave each position able to stop, all of them holding at once.
     *
     * @param byName the type at each position, keyed by what that position is called
     */
    static OrderedIntervals<Term> of(List<Core> clauses, Terms terms, Denotations at,
                                     Map<Term, Type> byName, Symbols symbols) {
        Map<Term, OrderScale> scales = new LinkedHashMap<>();
        byName.forEach((name, type) -> {
            OrderScale scale = OrderScale.ofValue(type, symbols);
            if (scale != null) {
                scales.put(name, scale);
            }
        });
        OrderedReading reading = new OrderedReading(terms, at, scales);
        OrderedIntervals<Term> out = OrderedIntervals.top();
        for (Core clause : clauses) {
            out = out.meet(reading.read(clause, true));
        }
        return out;
    }

    /**
     * Where {@code e} leaves each position, stated where {@code positive} and denied where it is not.
     *
     * <p>A denial is carried to the leaves rather than applied to what a branch came to. What a state
     * says is a range per position, and the denial of that is not one — the values a conjunction
     * rules out are a choice between the positions it named, which no map of ranges holds. Carried
     * down, every denial meets a comparison, where it is the comparison the other way round.
     */
    private OrderedIntervals<Term> read(Core e, boolean positive) {
        Core under = Predicates.negated(e);
        if (under != null) {
            return read(under, !positive);
        }
        if (e instanceof Core.Binary bin) {
            if (bin.op() == Hir.BinOp.AND) {
                return positive ? read(bin.left(), true).meet(read(bin.right(), true))
                        : read(bin.left(), false).join(read(bin.right(), false));
            }
            if (bin.op() == Hir.BinOp.OR) {
                return positive ? read(bin.left(), true).join(read(bin.right(), true))
                        : read(bin.left(), false).meet(read(bin.right(), false));
            }
            return comparison(bin, positive);
        }
        // A rule of another shape says nothing here, and nothing is what it contributes. It is not
        // recorded as something that went unread: which positions this reading can speak for is the
        // value sets' answer, and a second account of it kept here would be a second thing to hold
        // in step.
        return OrderedIntervals.top();
    }

    /** Where one comparison leaves the position it names, or nothing where it names none. */
    private OrderedIntervals<Term> comparison(Core.Binary bin, boolean positive) {
        // The position-bearing side read as the left one, as `0 <= value` says what `value >= 0`
        // says.
        Term position = positionIn(bin.left());
        Core bound = bin.right();
        Hir.BinOp op = bin.op();
        if (position == null) {
            position = positionIn(bin.right());
            bound = bin.left();
            op = InvariantBound.flipped(op);
        }
        OrderScale scale = position == null ? null : scales.get(position);
        if (scale == null) {
            return OrderedIntervals.top();
        }
        Hir.Expr written = Terms.asWrittenValue(bound);
        // Denied, a comparison is the one that leaves what it leaves out. `!(value /= x)` is an
        // equality and is read; `!(value == x)` is a disequality and is not, which is the same
        // answer the disequality gets when it is written directly.
        Hir.BinOp said = positive ? op : denied(op);
        if (said == Hir.BinOp.EQ) {
            Place only = written == null ? null : scale.literalOf(written);
            return only == null ? OrderedIntervals.top()
                    : leaves(position, scale, new OrderedInterval(
                            Endpoint.inclusive(only), Endpoint.inclusive(only)));
        }
        if (!InvariantBound.ordering(said)) {
            return OrderedIntervals.top();
        }
        return switch (InvariantBound.at(said, written, scale)) {
            case InvariantBound.Read.AnEnd it -> leaves(position, scale, it.bound().lower()
                    ? new OrderedInterval(it.bound().end(), null)
                    : new OrderedInterval(null, it.bound().end()));
            // The rule names an end the order does not reach, so the position holds nothing. Said as
            // a range of this order with no value in it, which is the same kind of answer two rules
            // whose ends cross come to.
            case InvariantBound.Read.PastWhereTheOrderStops _ ->
                    leaves(position, scale, scale.nothing());
            case InvariantBound.Read.NoEnd _ -> OrderedIntervals.top();
        };
    }

    /**
     * What one rule leaves a position, inside what the order itself holds.
     *
     * <p>The one place a position is spoken about, which is what makes the order's own ends part of
     * every answer rather than something applied once at the end. A reader adding a second such
     * place has to remember the extent; this one cannot forget it.
     */
    private static OrderedIntervals<Term> leaves(Term position, OrderScale scale,
                                                 OrderedInterval range) {
        return OrderedIntervals.at(position, scale.extent().meet(range));
    }

    /** The comparison that holds exactly where {@code op} does not. */
    private static Hir.BinOp denied(Hir.BinOp op) {
        return switch (op) {
            case EQ -> Hir.BinOp.NE;
            case NE -> Hir.BinOp.EQ;
            case LT -> Hir.BinOp.GE;
            case LE -> Hir.BinOp.GT;
            case GT -> Hir.BinOp.LE;
            case GE -> Hir.BinOp.LT;
            // Not a comparison. Denied or stated, it says nothing about where a position stops, and
            // answering it with itself lets the caller find that out the one way it does.
            default -> op;
        };
    }

    /** The position {@code e} is, or null where it is not one this is reading for. */
    private Term positionIn(Core e) {
        Term named = terms.atomOf(e, at);
        if (named == null) {
            named = terms.bodyKey(e, at);
        }
        return named != null && scales.containsKey(named) ? named : null;
    }
}
