package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Carrier;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What the rules written on a type leave a value of it between, and which of the names it wears
 * said so.
 *
 * <p>Read here rather than by whoever needs it, because two things need it and they are not the
 * same reader: what a position is divided and bounded at, and what values can be produced to stand
 * for it. Each working it out for itself is how a reading of one invariant came to mean two things.
 */
final class TypeBounds {

    /**
     * One end of a range, and every name that put it there.
     *
     * <p>Names, plural. Two layers can state the same bound — a wrapper repeating what it wraps — and
     * they are two rules a row could be owed to, which is the accounting a cut already keeps. Holding
     * one would drop an obligation rather than a line of text.
     */
    record End(Endpoint at, List<TypeName> from) {

        Place value() {
            return at.at();
        }

        /**
         * This end, or {@code other} where it is the stronger, or both where they agree.
         *
         * <p>Which number survives and whether the value is one of the range's own are the same
         * question asked of {@link Endpoint}, so that this and the domain cannot disagree about it.
         * Where the two are at one number both names are kept: each is a rule the line is owed to,
         * however far into the range each of them reaches.
         */
        static End tighter(End had, End one, boolean upper) {
            if (one == null) {
                return had;
            }
            if (had == null) {
                return one;
            }
            Endpoint at = upper ? Endpoint.upper(had.at(), one.at()) : Endpoint.lower(had.at(), one.at());
            if (had.value().compareTo(one.value()) != 0) {
                return at == had.at() ? had : one;
            }
            List<TypeName> both = new ArrayList<>(had.from());
            one.from().stream().filter(n -> !both.contains(n)).forEach(both::add);
            return new End(at, List.copyOf(both));
        }
    }

    /**
     * What a newtype's rules leave the value between, and which of the names it wears said so.
     *
     * <p>The layer is kept because a boundary is reported by the rule that drew it, and a value
     * wearing two names is bounded by rules written on either. Read off the outermost name, an edge
     * that `Minute` drew would be reported as `StartMinute`'s.
     */
    record Bounds(End min, End max, Carrier carrier) {

        boolean isEmpty() {
            return min == null && max == null;
        }
    }

    /** What a numeric newtype's own rules leave its value between, for a caller that is asking about
     * the value and not about anything taken of it. */
    static Bounds of(Type type, Symbols symbols) {
        return of(type, symbols, Carrier.ofValue(type, symbols), null);
    }

    /**
     * @param carrier what the clauses' values are read on, or null where nothing here reads them
     * @param measure the operation the number is taken by, or null where the number is the value
     *                itself
     */
    static Bounds of(Type type, Symbols symbols, Carrier carrier, ValueName measure) {
        if (carrier == null) {
            return null;
        }
        End min = null;
        End max = null;
        // Every name the value wears, not the outermost one. A rule written on the type a newtype
        // wraps bounds the value as much as one written on the newtype does, and the two intersect:
        // `Inner: value >= 0` under `Outer: value <= 10` is a range of `[0, 10]`, and neither layer
        // alone says so. How far that reaches is asked of `TypeOps` rather than walked again here,
        // and every layer that put an end where it is is kept, because each is a rule a row is owed.
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    InvariantBound read = (measure == null ? InvariantBound.of(each, carrier)
                            : InvariantBound.ofSize(each, measure)).orElse(null);
                    if (read == null) {
                        continue;
                    }
                    End end = new End(read.end(), List.of(layer.named()));
                    if (read.lower()) {
                        min = End.tighter(min, end, false);
                    } else {
                        max = End.tighter(max, end, true);
                    }
                }
            }
        }
        return new Bounds(min, max, carrier);
    }

    /**
     * The ends {@code placed} puts on one coordinate, or null where it puts none there.
     *
     * <p>The clauses of the record a position sits in, read as what they are: a clause naming one
     * coordinate and a constant places an end exactly as one written on that coordinate's own type
     * does, and which declaration held it is what the line is named by (ADR-0090).
     *
     * @param measured which of the position's coordinates these are wanted for — the count taken of
     *                 it, or its value
     */
    static Bounds placed(List<souther.compiler.check.FieldDomains.Placed> placed, boolean measured,
                         Carrier carrier) {
        End min = null;
        End max = null;
        for (souther.compiler.check.FieldDomains.Placed each : placed) {
            if (each.measured() != measured) {
                continue;
            }
            End end = new End(each.end(), List.of(each.from()));
            if (each.lower()) {
                min = End.tighter(min, end, false);
            } else {
                max = End.tighter(max, end, true);
            }
        }
        return min == null && max == null ? null : new Bounds(min, max, carrier);
    }

    /**
     * Both, intersected, with every declaration that put an end where it is kept.
     *
     * <p>One coordinate can be bounded from either side of the same rule set — a newtype's own clause
     * and the record holding a field of it — and neither is the other's context. Which number
     * survives is {@link End#tighter}'s, the same answer two layers of newtype already get.
     */
    static Bounds and(Bounds had, Bounds one) {
        if (one == null) {
            return had;
        }
        if (had == null) {
            return one;
        }
        return new Bounds(End.tighter(had.min(), one.min(), false),
                End.tighter(had.max(), one.max(), true),
                had.carrier() == null ? one.carrier() : had.carrier());
    }

    /**
     * What the position can hold: every rule reaching it, intersected, with what the term itself
     * guarantees taken in.
     *
     * <p>An end survives from whichever side has one, because a value outside it is refused whether
     * the type said so or the record did. That is the difference from {@link LocalInspection}'s axis bounds: a cap the
     * record alone imposes is not a line dividing this position, and it is still where its values
     * stop — so a guard beyond it divides nothing and is no edge either.
     *
     * <p>Numbers and no names. An end here says where the values stop; which rule put it there is a
     * cut's question, and answering it from a projection would name a rule that never mentioned this
     * position on its own.
     *
     * <p>A size is never negative and nothing has to write that down (spec
     * §invariant-discharge-terms). Kept here with the rules rather than at the boundary that reads
     * them, so that a guard at zero is refused its neighbour below by the same intersection that
     * refuses one outside an invariant.
     */
    static NumericDomain.Bounds admissible(Bounds own, NumericDomain.Bounds projected,
                                           NumericTerm term) {
        NumericDomain.Bounds intrinsic = term == null ? null : term.ownBounds();
        if (own == null) {
            return intrinsic;   // not a number of its own, so only what the term guarantees
        }
        Endpoint min = own.min() == null ? null : own.min().at();
        Endpoint max = own.max() == null ? null : own.max().at();
        NumericDomain.Bounds read = projected == null ? new NumericDomain.Bounds(min, max)
                : new NumericDomain.Bounds(Endpoint.lower(min, projected.min()),
                        Endpoint.upper(max, projected.max()));
        return intrinsic == null ? read
                : new NumericDomain.Bounds(Endpoint.lower(read.min(), intrinsic.min()),
                        Endpoint.upper(read.max(), intrinsic.max()));
    }

    /** The same, of a position no term of its own is measured at. */
    static NumericDomain.Bounds admissible(Bounds own, NumericDomain.Bounds projected) {
        return admissible(own, projected, null);
    }

    private TypeBounds() {}
}
