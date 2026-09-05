package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
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
 * would take {@code value < ""} for a rule leaving room underneath. The extent is the carrier's
 * ({@link Carrier#extent}) and it is applied where a rule becomes a range, which is the one place
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
final class OrderedReading implements ClauseReading<OrderedIntervals<FactSubject>, Denotations> {

    private final Terms terms;
    /** What each position's values are ordered on, for the positions that are ordered at all. */
    private final Map<FactSubject, Carrier> carriers;

    private OrderedReading(Terms terms, Map<FactSubject, Carrier> carriers) {
        this.terms = terms;
        this.carriers = carriers;
    }

    /** The reading of one value's positions, for {@link StatedByClauses} to take the leaves of.
     *
     *  <p>No environment is held. Which environment a leaf is read at is where the leaf stands,
     *  which the fold hands down — kept here, a rule under a binding would be read at the names the
     *  clause began with. */
    static OrderedReading of(Terms terms, Map<FactSubject, Type> byName, Symbols symbols) {
        Map<FactSubject, Carrier> carriers = new LinkedHashMap<>();
        byName.forEach((name, type) -> {
            Carrier carrier = Carrier.ofValue(type, symbols);
            if (carrier != null) {
                carriers.put(name, carrier);
            }
        });
        return new OrderedReading(terms, carriers);
    }

    /**
     * What each position's values are ordered on, for a reader putting a range together with a set
     * of values.
     *
     * <p>The table this reading already worked out, handed on rather than built again. Which order a
     * position is counted by is settled where its type is read, and a second table would be a second
     * answer to that question.
     */
    Map<FactSubject, Carrier> carriers() {
        return carriers;
    }

    @Override
    public OrderedIntervals<FactSubject> nothingSaid() {
        return OrderedIntervals.top();
    }

    @Override
    public OrderedIntervals<FactSubject> both(OrderedIntervals<FactSubject> one, OrderedIntervals<FactSubject> other) {
        return one.meet(other);
    }

    @Override
    public OrderedIntervals<FactSubject> either(Core writtenAt,
                                                OrderedIntervals<FactSubject> one,
                                                OrderedIntervals<FactSubject> other) {
        return joined(one, other);
    }

    /**
     * The same join, for a caller with no {@code ||} in hand.
     *
     * <p>Where two alternatives leave a position is this reading's rule and turns on nothing an
     * author wrote, so branches already settled are joined by it as a clause's own were.
     */
    OrderedIntervals<FactSubject> joined(OrderedIntervals<FactSubject> one,
                                         OrderedIntervals<FactSubject> other) {
        return one.join(other);
    }

    /**
     * A comparison places an end; nothing else here is read.
     *
     * <p>A rule of another shape says nothing here, and nothing is what it contributes. It is not
     * recorded as something that went unread: which positions this reading can speak for is the
     * value sets' answer, and a second account of it kept here would be a second thing to hold in
     * step.
     */
    @Override
    public OrderedIntervals<FactSubject> leaf(Core e, boolean positive, Denotations at) {
        return e instanceof Core.Binary bin ? comparison(bin, positive, at) : OrderedIntervals.top();
    }

    /** Where one comparison leaves the position it names, or nothing where it names none. */
    private OrderedIntervals<FactSubject> comparison(Core.Binary bin, boolean positive,
                                                     Denotations at) {
        Comparison read = Comparison.of(bin).orElse(null);
        if (read == null) {
            return OrderedIntervals.top();
        }
        // The position-bearing side read as the left one, as `0 <= value` says what `value >= 0`
        // says.
        FactSubject position = positionIn(bin.left(), at);
        Core bound = bin.right();
        ComparisonClaim claim = read.claim();
        if (position == null) {
            position = positionIn(bin.right(), at);
            bound = bin.left();
            claim = claim.turned();
        }
        Carrier carrier = position == null ? null : carriers.get(position);
        if (carrier == null) {
            return OrderedIntervals.top();
        }
        Hir.Expr written = Terms.asWrittenValue(bound, at);
        // Denied, a comparison is the one that leaves what it leaves out. `!(value /= x)` is an
        // equality and is read; `!(value == x)` is a disequality and is not, which is the same
        // answer the disequality gets when it is written directly.
        ComparisonClaim said = positive ? claim : claim.denied();
        return switch (said) {
            // The value the rule is met at, which is a range with one value in it. What a denial
            // leaves is every other value, and that is a set rather than a range, so this says
            // nothing about it.
            case ComparisonClaim.Singled singled -> singled.holdsAtTheValue()
                    ? onlyTheValue(position, carrier, written)
                    : OrderedIntervals.top();
            case ComparisonClaim.Cut cut -> ends(position, carrier,
                    InvariantBound.at(cut, written, carrier));
        };
    }

    /** The range of one value, or nothing where the rule names none this order reads. */
    private OrderedIntervals<FactSubject> onlyTheValue(FactSubject position, Carrier carrier,
                                                       Hir.Expr written) {
        Place only = written == null ? null : carrier.literalOf(written);
        return only == null ? OrderedIntervals.top()
                : leaves(position, carrier, new OrderedInterval(
                        Endpoint.inclusive(only), Endpoint.inclusive(only)));
    }

    /** What the end an ordering placed leaves the position. */
    private OrderedIntervals<FactSubject> ends(FactSubject position, Carrier carrier,
                                               InvariantBound.Read read) {
        return switch (read) {
            case InvariantBound.Read.AnEnd it -> leaves(position, carrier, it.bound().lower()
                    ? new OrderedInterval(it.bound().end(), null)
                    : new OrderedInterval(null, it.bound().end()));
            // The rule names an end the order does not reach, so the position holds nothing. Said as
            // a range of this order with no value in it, which is the same kind of answer two rules
            // whose ends cross come to.
            case InvariantBound.Read.PastWhereTheOrderStops _ ->
                    leaves(position, carrier, carrier.nothing());
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
    private static OrderedIntervals<FactSubject> leaves(FactSubject position, Carrier carrier,
                                                 OrderedInterval range) {
        return OrderedIntervals.at(position, carrier.extent().meet(range));
    }

    /** The position {@code e} is, or null where it is not one this is reading for. */
    private FactSubject positionIn(Core e, Denotations at) {
        FactSubject named = terms.subjectOf(e, at);
        return named != null && carriers.containsKey(named) ? named : null;
    }
}
