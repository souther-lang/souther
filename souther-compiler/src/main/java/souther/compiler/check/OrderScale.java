package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Instants;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Times;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * An order a rule can be read against: what a literal is on it, how its values are spaced, and where
 * it stops.
 *
 * <p>Everything reading a rule needs of a type, and nothing writing a value needs. The two were one
 * type, and the smaller question was answered with the larger one's answer: whether an invariant's
 * ends can both hold is settled by comparing them on the order, and it went unsettled at a
 * {@code Time} and an {@code Instant} because settling it asked for a {@link Carrier} — which owes a
 * way back from its counts and a spacing of its own besides. A rule went unread for want of
 * machinery no reading of it uses.
 *
 * <p>So the capability is cut where the direction is. Reading is here; writing a value at a
 * position — a row, a cut, a fixture, a report's label — is {@link Carrier}, which is one of these
 * with the way back added. A type gaining an order does not thereby gain a line drawn at it, and a
 * type is refused for rules that cannot hold whether or not anything can be written at it.
 *
 * <p><b>Sealed, so a scale added is one every reader has to answer for.</b> Each switch below is
 * over these eight and nothing else. {@link Carrier}'s are over its six, and the two that are only
 * scales fall outside them by construction rather than by a reader remembering to leave them out.
 *
 * <p><b>Which types have one</b> is {@link #ofValue}, which is where every such question is settled:
 * {@link Carrier#ofValue} narrows this rather than deciding again. Deciding twice is what left a
 * {@code Date} a carrier to one reader and not to another (see {@link Carrier}), and a second answer
 * one level up would be that again.
 */
public sealed interface OrderScale permits Carrier, OrderScale.TimeOfDay, OrderScale.InstantNanos {

    /**
     * A second of the day, standing for a time of day.
     *
     * <p>A scale and not a carrier. A {@code Time} is ordered and held to the second, so where its
     * values stop is as plain as any other's; what it has not been given is the way back from a
     * count, and the report says as much — a rule written over one is named as not read (spec
     * §a-line-is-drawn-where-the-values-can-carry-one).
     */
    record TimeOfDay() implements OrderScale {}

    /**
     * A nanosecond from the epoch, standing for a moment.
     *
     * <p>Apart from {@link Carrier.Seconds} because the units differ: an {@code Instant} is held to
     * the nanosecond and a {@code DateTime} to the second (spec §an-instant-carries-what-a-timestamp-said),
     * and two units in one scale would leave a rule read at one of them with nothing saying which.
     */
    record InstantNanos() implements OrderScale {}

    OrderScale TIME_OF_DAY = new TimeOfDay();
    OrderScale INSTANT_NANOS = new InstantNanos();

    /**
     * The order a location's own content is read on, or null where nothing here orders it.
     *
     * <p>Asked of what the names wrap, so a newtype answers as the value it carries — which is what
     * makes {@code data Cutoff = Date} the same scale as a bare {@code Date}, and
     * {@code data StageN = Stage} the same scale as a bare {@code Stage}.
     */
    static OrderScale ofValue(Type type, Symbols symbols) {
        Type base = TypeOps.base(type, symbols);
        if (base instanceof Type.Prim prim) {
            return switch (prim) {
                case INT -> Carrier.WHOLE;
                case DECIMAL -> Carrier.DENSE;
                case DATE -> Carrier.DATE;
                case DATETIME -> Carrier.MOMENT;
                // Ordered and read, and written back at by nothing. Each has a count that embeds and
                // neither has the way back a line drawn at it would need, which is the difference
                // between these two arms and the four above.
                case TIME -> TIME_OF_DAY;
                case INSTANT -> INSTANT_NANOS;
                // `String` is ordered lexicographically and stands for itself, having no count to
                // embed into and needing none. `Bool` and `Raw` are not ordered at all.
                case STRING -> Carrier.TEXT;
                case BOOL, RAW -> null;
            };
        }
        // The enumeration itself, and not an order a value of it can be compared on. Which order
        // two operands are comparable by is a wider question and has its own answer
        // ({@link TypeOps#comparisonEnumeration}): a case and a union of cases are both comparable
        // on their sum's order without ranging over it. Answered with that wider order, a position
        // declared as one case took the whole enumeration's counts, and the line drawn on it asked
        // for a row at a value the position cannot hold.
        if (!(base instanceof Type.Ref ref)
                || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.SumData sum)
                || !TypeOps.isUnitOnlySum(base, symbols)) {
            return null;
        }
        List<souther.compiler.types.TypeSymbol> cases = TypeOps.leafCases(sum, symbols);
        return cases.isEmpty() ? null : new Carrier.Ordinal(ref.name(), cases);
    }

    /** How the counts on this scale are spaced, which is what decides whether a strict bound has a
     * next count to step to. */
    default Granularity spacing() {
        return switch (this) {
            // A date-time steps too: it is held to the second (spec
            // §a-local-temporal-is-held-to-the-second), which is the decision `DateTimes` recorded
            // as nobody's, so a strict bound on one has a count to sharpen onto. A time of day and a
            // moment step for the same reason, each at its own unit.
            case Carrier.Whole _, Carrier.Days _, Carrier.Ordinal _, Carrier.Seconds _,
                 TimeOfDay _, InstantNanos _ -> Granularity.DISCRETE;
            // No smallest step this language names. A strict bound then leaves its end on the count
            // it names and says that count is not one of its own, rather than inventing a step in.
            // A string has no next string this language names — naming it means choosing a
            // character this language does not name either — so a strict bound leaves its end on the
            // value it names and the row beside a line is not asked for.
            case Carrier.Dense _, Carrier.Text _ -> Granularity.DENSE;
        };
    }

    /**
     * Every value this scale has, as the ends it runs between.
     *
     * <p>Where a reading of the rules starts, and the third thing it needs of a type. Neither the
     * spacing nor the literals say it, and a reading that started every position unbounded has no
     * way to find out that a rule states an end the order does not reach: {@code value < ""} leaves
     * a range open below, and what is below the empty string is nothing.
     *
     * <p>Not the same as where a value can be <em>written</em>. This says which values the order
     * has, and it is asked to decide whether any is left — a question every ordered type answers,
     * including the two that write nothing back.
     */
    default OrderedInterval extent() {
        return switch (this) {
            case Carrier.Whole _ -> between(Count.of(Long.MIN_VALUE), Count.of(Long.MAX_VALUE));
            // Every number, so no end either way.
            case Carrier.Dense _ -> OrderedInterval.OPEN;
            case Carrier.Days _ -> between(Count.of(java.time.LocalDate.MIN.toEpochDay()),
                    Count.of(java.time.LocalDate.MAX.toEpochDay()));
            case Carrier.Seconds _ -> between(DateTimes.MIN, DateTimes.MAX);
            case TimeOfDay _ -> between(Times.MIN, Times.MAX);
            case InstantNanos _ -> between(Instants.MIN, Instants.MAX);
            // Every string is at or above the empty one, and there is no longest string.
            case Carrier.Text _ -> new OrderedInterval(
                    Endpoint.inclusive(souther.compiler.numeric.Text.of("")), null);
            case Carrier.Ordinal ordinal ->
                    between(Count.of(0), Count.of(ordinal.cases().size() - 1L));
        };
    }

    private static OrderedInterval between(Place low, Place high) {
        return new OrderedInterval(Endpoint.inclusive(low), Endpoint.inclusive(high));
    }

    /**
     * A range of this order with no value in it, which is what a rule stepping past its end leaves.
     *
     * <p>Written as ends of this order rather than as a flag on the range, so that a range holding
     * nothing is the same kind of thing however it was arrived at: two rules whose ends cross leave
     * one of these, and so does one rule naming an end the order does not reach.
     *
     * <p>Only a stepping order can be stepped off, and every stepping order this has stops at both
     * ends — there is no last decimal and no last string, and neither steps. So the end is there to
     * be named, and a scale that reached here without one is a mistake in this compiler.
     */
    default OrderedInterval nothing() {
        OrderedInterval extent = extent();
        Endpoint end = extent.high() != null ? extent.high() : extent.low();
        if (end == null) {
            throw new IllegalStateException(
                    "an order with no end was stepped off: " + this);
        }
        // Open at one place, on both sides of it: nothing is above a value and below it at once.
        return new OrderedInterval(Endpoint.exclusive(end.at()), Endpoint.exclusive(end.at()));
    }

    /**
     * The count as this scale can actually hold it, or null where it holds nothing there.
     *
     * <p>Not every number between two of this scale's counts is one of them. Halfway between two
     * adjacent moments is a number and not a date-time, because what a date-time can be written as
     * sits on a grid at the second.
     *
     * <p>Asked wherever a count is about to stand for a value. Left unasked, a class open at both
     * ends between two adjacent moments offered the count between them, which was written back as one
     * of the ends — a row labelled for a class it is not in.
     */
    default Place onTheGrid(Place count) {
        if (count == null) {
            return null;
        }
        return switch (this) {
            // A decimal holds every number and a string is every string: the ranges and the values
            // are the same things. Its own, though — this is where a scale says which places are
            // its, so a place of some other scale is not one of them however little else would
            // have noticed.
            case Carrier.Dense _ -> count instanceof Count ? count : null;
            case Carrier.Text _ -> count instanceof souther.compiler.numeric.Text ? count : null;
            // A whole number, a day count, an ordinal, a second of the day and a nanosecond step, so
            // a number between two of them is neither, and each stops where what carries it stops.
            // Asked here rather than at each place that steps one, because a step off the end is the
            // same non-value however it was reached — and an enumeration's ends are the nearest of
            // them all, one step past its last case.
            case Carrier.Whole _, Carrier.Ordinal _, Carrier.Days _, TimeOfDay _, InstantNanos _ ->
                    whole(count) && extent().admits(count) ? count : null;
            // Where the calendar stops first, and then on the grid inside it. A date-time is
            // bounded at both ends and spaced besides, and asking the writer alone would be asking
            // it to answer for a count it exists to write — which it does by throwing, out of a
            // question whose whole job is to answer no.
            //
            // Round-tripped and then held to itself. The writer floors a count onto the second, so
            // returning what came back would answer "the nearest count this scale holds" to a
            // question that asks whether it holds this one. A caller reading that as a yes offers a
            // value between two moments as one of them.
            case Carrier.Seconds _ -> {
                if (!(count instanceof Count) || !DateTimes.holds(count)) {
                    yield null;
                }
                Place written = DateTimes.secondOf(DateTimes.written(count));
                yield written != null && written.sameAs(count) ? count : null;
            }
        };
    }

    /** Whether a place counts to a whole number, which is what a stepping scale's order is made
     * of. A place that is not a number is not one. */
    private static boolean whole(Place at) {
        return at instanceof Count count && count.whole();
    }

    /**
     * The count a rule's literal names on this scale, or null where the expression names none.
     *
     * <p>Which literals a rule may be bounded by is a fact about what carries the value and not about
     * the reader that wants one, so it is answered here. It was being answered separately by each
     * reader instead, and an invariant and a {@code guard} at one position admitted different rules
     * with only one of them saying so.
     */
    default Place literalOf(Hir.Expr e) {
        return switch (this) {
            case Carrier.Whole _ -> Count.of(InvariantBound.wholeLiteral(e));
            case Carrier.Dense _ -> Count.of(InvariantBound.literalOf(e));
            case Carrier.Days _ -> temporal(e, "Date", Dates::dayOf);
            case Carrier.Seconds _ -> temporal(e, "DateTime", DateTimes::secondOf);
            case TimeOfDay _ -> temporal(e, "Time", Times::secondOf);
            case InstantNanos _ -> temporal(e, "Instant", Instants::nanoOf);
            // A case is named rather than written, so the literal is a name and what it denotes says
            // which case it is. Read off the denotation and not the text: a case is reachable under
            // an alias, and two enumerations may declare cases spelled the same way.
            case Carrier.Ordinal ordinal -> e instanceof Hir.Var.Denoting v
                    && v.denotes() instanceof ValueName.OfType named
                    ? ordinal.at(named.type()) : null;
            case Carrier.Text _ -> e instanceof Hir.StringLit lit
                    ? souther.compiler.numeric.Text.of(lit.value()) : null;
        };
    }

    /** The count a written temporal is, or null where the expression is not one of that kind. A
     *  temporal is written as a literal with its text spelled out (spec
     *  §a-temporal-value-is-written-as-a-literal), so it is read here rather than run. */
    private static Count temporal(Hir.Expr e, String written,
                                  java.util.function.Function<String, Count> countOf) {
        return e instanceof Hir.Apply call && call.answered() != null
                && written.equals(call.answered().reaches())
                && call.args().size() == 1 && call.args().get(0) instanceof Hir.StringLit iso
                ? countOf.apply(iso.value()) : null;
    }
}
