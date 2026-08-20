package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

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
     * The carrier this term's counts are on, or null where it has none.
     *
     * <p>A size is a whole number whatever it is a size of, so the term answers this and not the
     * position: a rule about the length of a string is counted as an {@code Int} at a position no
     * line is drawn on.
     */
    default Carrier carrierAt(Type positionType, Symbols symbols) {
        return this instanceof SizeOf ? Carrier.WHOLE : Carrier.ofValue(positionType, symbols);
    }

    /**
     * The count at an observation of {@link #path()}, or why there is none.
     *
     * <p>The one reader. What a class asks of a row, what a boundary asks of it, and what a report
     * prints were three walks down a value that agreed only because they were written the same way.
     *
     * <p>The carrier is handed in rather than guessed at from the observation. A written temporal
     * says nothing about whether the position counts days or seconds — the declared type says it —
     * and a reader that sniffed the text for a {@code T} answered a question that was already
     * answered, differently.
     */
    default Reading read(ObservedValue at, Carrier carrier) {
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
            return read(c.field("value"), carrier);
        }
        if (this instanceof SizeOf) {
            return size(at);
        }
        if (carrier == null) {
            return new Reading.NotNumber();
        }
        Place read = carrier.placeOf(at);
        return read == null ? new Reading.NotNumber() : new Reading.Number(read);
    }

    /** How the values beside a boundary on this term are found. A size steps like an {@code Int}. */
    default BoundaryDomain intervals(Type positionType, Symbols symbols) {
        return BoundaryDomain.on(carrierAt(positionType, symbols));
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
                ? new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null) : null;
    }

    /** The count at a value, keeping why there is none where there is none. */
    sealed interface Reading {

        record Number(Place value) implements Reading {}

        /** There was no value to read, and this is what stopped there being one. */
        record Missing(Incompleteness.Code code) implements Reading {}

        /** The value was read and this term is not a number of it. An answer about the value and not
         * about the observation: a {@code Text} where a number was expected is a class nothing holds,
         * and calling it unreadable would report a partition that does not fit its position as a row
         * nobody could read. */
        record NotNumber() implements Reading {}
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
                    Count.of(t.value().codePointCount(0, t.value().length())));
            case ObservedValue.Sequence s -> new Reading.Number(Count.of(s.elements().size()));
            case ObservedValue.Mapping m -> new Reading.Number(Count.of(m.entries().size()));
            case null, default -> new Reading.NotNumber();
        };
    }
}
