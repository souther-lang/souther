package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;

/**
 * The number a rule compares, and where that number is read from.
 *
 * <p>Not the position. A boundary is drawn on a number, and the number a rule names is sometimes the
 * content of a location and sometimes something taken of it — the length of a string, the size of a
 * container. The two were one thing here, so a position holding a string was a position holding no
 * number, and every rule written about its length came back as a rule the model had not written. The
 * discharge procedure has always kept them apart (spec §invariant-discharge-terms); this is the same
 * separation on the side that measures.
 *
 * <p>Three properties, asked separately, because they are three different questions about a number.
 * How its values are spaced decides what lies beside a boundary. What its own values are decides
 * which of those exist — a size is never negative whatever the rules about it happen to say. How it
 * is read off an observation decides whether a row is at the line. Answering all three from the
 * position's type is what made a length unreadable at each of them.
 */
public sealed interface NumericTerm {

    /** The number a location holds: a numeric parameter, a field of one, a numeric newtype's value. */
    record ValueOf(TermPath path) implements NumericTerm {

        @Override
        public String toString() {
            return path.toString();
        }
    }

    /**
     * A number taken of what a location holds: {@code String.length}, {@code List.length},
     * {@code Set.size}, {@code Map.size}.
     *
     * <p>Keyed by the operation the call resolved to rather than by how it was written, so a term
     * here and an atom in the discharge procedure are the same term when they are the same operation
     * over the same location.
     *
     * <p><b>The operation and the location agree, by construction.</b> Both places that make one of
     * these guarantee it: an invariant's term is the operation that counts the position's own type
     * ({@code NumericMeasures.takenOf}), and a guard's is a call the type checker has already held
     * to its argument. So {@link #read} counts what the observation is without asking which
     * operation was named.
     *
     * <p>Not a check that was skipped for being cheap. A {@code List} and a {@code Set} are one
     * observation — which of the two it was is the declared type's to say, not the value's — so
     * comparing the operation against the shape would tell a string from a collection and leave the
     * one pair a reader might actually confuse undistinguished. A check that looks total and is
     * blind in the middle is worse than a stated premise, so the premise is stated.
     */
    record SizeOf(ValueName.Stdlib measure, TermPath path) implements NumericTerm {

        @Override
        public String toString() {
            return measure.qualified() + "(" + path + ")";
        }
    }

    /** Where the value this is taken of sits. Never the identity of the term: two terms can be taken
     * of one location, and reading one as the other is what this type exists to stop. */
    TermPath path();

    /**
     * The number at an observation of {@link #path()}, or why there is none.
     *
     * <p>The one reader. What a class asks of a row, what a boundary asks of it, and what a report
     * prints were three walks down a value that agreed only because they were written the same way.
     */
    default Reading read(ObservedValue at) {
        Membership.Incomplete unread = Membership.unread(at);
        if (unread != null) {
            return new Reading.Missing(unread.code());
        }
        // A newtype is not a step in a path, so what sits at the position may be the construction and
        // the value one inside it. Asked again of what is inside rather than walked into: a limit
        // reached one layer down leaves a construction that reads perfectly well with nothing where
        // the value should be, and a walk that only looked at the outside would call that a value
        // this term does not hold.
        if (at instanceof ObservedValue.Constructed c && c.field("value") != null) {
            return read(c.field("value"));
        }
        return switch (this) {
            case ValueOf _ -> number(at);
            case SizeOf _ -> size(at);
        };
    }

    /**
     * Whether this term's values are decimals, which is a question about the term and only sometimes
     * about the position: a size is a whole number whatever it is a size of.
     *
     * @param positionType what {@link #path()} is declared as
     */
    default boolean decimal(Type positionType, Symbols symbols) {
        return Carrier.of(this, positionType, symbols) == Carrier.DENSE;
    }

    /** How the values beside a boundary on this term are found. A size steps like an {@code Int}. */
    default BoundaryDomain intervals(Type positionType, Symbols symbols) {
        Carrier carrier = Carrier.of(this, positionType, symbols);
        return carrier == null ? BoundaryDomain.NONE : carrier.intervals();
    }

    /**
     * What this term's values are, before any rule is read.
     *
     * <p>Null where the term is a location's own content: what an {@code Int} holds is what its type
     * holds, and a position nobody bounded is one the model draws no line through (ADR-0090). A size
     * is not that — it is never negative, and the procedure knows that much without being told
     * (spec §invariant-discharge-terms), which is what keeps a guard at zero from asking for a row
     * one below it.
     */
    default NumericDomain.Bounds ownBounds() {
        return this instanceof SizeOf
                ? new NumericDomain.Bounds(Endpoint.inclusive(BigDecimal.ZERO), null) : null;
    }

    /** The number at a value, keeping why there is none where there is none. */
    sealed interface Reading {

        record Number(BigDecimal value) implements Reading {}

        /** There was no value to read, and this is what stopped there being one. */
        record Missing(Incompleteness.Code code) implements Reading {}

        /** The value was read and this term is not a number of it. An answer about the value and not
         * about the observation: a {@code Text} where a number was expected is a class nothing holds,
         * and calling it unreadable would report a partition that does not fit its position as a row
         * nobody could read. */
        record NotNumber() implements Reading {}
    }

    /**
     * The number a value is, or null where it is not one.
     *
     * <p>For a value that is a number by construction — a boundary's own — rather than one read off
     * a row, where why there is none is the question and {@link #read} is what asks it.
     */
    static BigDecimal numberOf(ObservedValue at) {
        return switch (at) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            // Which of the two counts a written temporal is on is decided by its own text, and the
            // two do not overlap: a date-time carries its time and a date does not, so each reader
            // declines the other's. What makes that safe is the declared type — a position holding
            // dates never holds a date-time — so the count here and the count a line was drawn on
            // are on one carrier without this having to be told which.
            case ObservedValue.Temporal t -> t.iso() != null && t.iso().indexOf('T') >= 0
                    ? DateTimes.secondOf(t.iso()) : Dates.dayOf(t.iso());
            case ObservedValue.Constructed c when c.field("value") != null -> numberOf(c.field("value"));
            case null, default -> null;
        };
    }

    /** The number an observation already unwrapped is. */
    private static Reading number(ObservedValue at) {
        BigDecimal read = numberOf(at);
        return read == null ? new Reading.NotNumber() : new Reading.Number(read);
    }

    /**
     * How much an observation holds.
     *
     * <p>Read off the observation under the premise {@link SizeOf} states: the operation and what it
     * is applied to agree, so counting what is there counts what was asked for. A string counts in
     * code points, as {@code Strings.length} does — counting UTF-16 units here would put a boundary
     * one place away from the rule that drew it for every string outside the basic plane.
     */
    private static Reading size(ObservedValue at) {
        return switch (at) {
            case ObservedValue.Text t -> new Reading.Number(
                    BigDecimal.valueOf(t.value().codePointCount(0, t.value().length())));
            case ObservedValue.Sequence s -> new Reading.Number(
                    BigDecimal.valueOf(s.elements().size()));
            case ObservedValue.Mapping m -> new Reading.Number(
                    BigDecimal.valueOf(m.entries().size()));
            case null, default -> new Reading.NotNumber();
        };
    }
}
