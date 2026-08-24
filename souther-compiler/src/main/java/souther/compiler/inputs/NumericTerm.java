package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
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

    /**
     * A term that is what an operation answered, rather than what a location holds.
     *
     * <p>Here so that what is true of such a number is asked of the operation that answered it and
     * not of which kind of term this is. The two were one thing while a size was the only such term:
     * a size is never negative was written as a property of {@link SizeOf}, and the same proposition
     * about {@code Int.abs} — declared beside it in {@code semantics} — was unreachable from here
     * because the term said the fact rather than naming who says it (#1016).
     *
     * <p>What a term of this kind adds is the name of the operation. Everything true of the number
     * follows from that, so a second such term answers with what its own operation declares on the
     * day it is written, and nothing here is edited for it.
     */
    sealed interface ResultOfOperation extends NumericTerm {

        /** The operation whose answer this is. */
        ValueName.Stdlib operation();
    }

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
    record SizeOf(ValueName.Stdlib measure, TermPath path) implements ResultOfOperation {

        /** The measure, under the name every term of this kind answers what answered it by. */
        @Override
        public ValueName.Stdlib operation() {
            return measure;
        }

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
     *
     * <p>Which is why {@code positionType} may be absent. A caller reading a term under more steps
     * than the walk that finds an input's positions goes down has no position to ask, and a size
     * there is a whole number all the same — asked for the type first, a caller would either have
     * nothing to pass or would write out the rule above a second time, at whichever call site
     * noticed. What is null there is a term measured by its own values, which is the one case the
     * position was the answer to.
     */
    default Carrier carrierAt(Type positionType, Symbols symbols) {
        if (this instanceof SizeOf) {
            return Carrier.WHOLE;
        }
        return positionType == null ? null : Carrier.ofValue(positionType, symbols);
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
     * <p>Open where the term is a location's own content: what an {@code Int} holds is what its type
     * holds, and a position nobody bounded is one the model draws no line through (ADR-0090). A term
     * that is what an operation answered is not that — a size is never negative, which is what keeps
     * a guard at zero from asking for a row one below it (spec §invariant-discharge-terms).
     *
     * <p><b>Asked of the operation, not answered here.</b> That a size is at or above nought is one
     * proposition with {@code Int.abs(x) >= 0}, and both are declared where what is true of the
     * language's operations is declared. Written out here instead, it was the same sentence in a
     * second vocabulary, and the half declared in {@code semantics} could not be reached from a term
     * (#1016).
     *
     * <p>Read with nothing said about the arguments, because a term of this kind carries none: what
     * a size is taken of is a container, and a bound may only name an argument that is a number
     * ({@code check.DischargeRules.holdBound}), so an operation like these declares no row that
     * names one. A term whose operation does take numbers would have to answer them here rather than
     * be read the same way and quietly come back wider.
     */
    default NumericDomain.Bounds intrinsicBounds() {
        return this instanceof ResultOfOperation answered
                ? ResultRange.of(answered.operation(), ConstantArguments.NONE)
                : NumericDomain.Bounds.OPEN;
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
