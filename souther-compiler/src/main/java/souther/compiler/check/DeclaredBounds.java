package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
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
 * <p>Read here rather than by whoever needs it, because more than one thing needs it and they are
 * not the same reader: what a position is divided and bounded at, and what values can be produced to
 * stand for it. Each working it out for itself is how a reading of one invariant came to mean two
 * things.
 *
 * <p>A range, and only what a range can hold. What the rules leave out between their ends is not
 * here — a caller asking whether some particular value is admitted is asking the domain the rules
 * seed ({@link FieldDomains#mayHoldNothingAt}) and not this.
 *
 * <p>Below whoever composes it with anything else. What a declaration's rules say is a fact about the
 * declaration, and a reader that had to reach a generator to ask it would be reaching past the
 * question.
 */
public final class DeclaredBounds {

    /**
     * One end of a range, and every name that put it there.
     *
     * <p>Names, plural. Two layers can state the same bound — a wrapper repeating what it wraps — and
     * they are two rules a row could be owed to, which is the accounting a cut already keeps. Holding
     * one would drop an obligation rather than a line of text.
     */
    public record End(Endpoint at, List<TypeName> from) {

        public Place value() {
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
        public static End tighter(End had, End one, boolean upper) {
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
    public record Bounds(End min, End max, Carrier carrier) {

        public boolean isEmpty() {
            return min == null && max == null;
        }
    }

    /** What a numeric newtype's own rules leave its value between, for a caller that is asking about
     * the value and not about anything taken of it. */
    public static Bounds of(Type type, Symbols symbols) {
        return of(type, symbols, Carrier.ofValue(type, symbols), null);
    }

    /**
     * @param carrier what the clauses' values are read on, or null where nothing here reads them
     * @param measure the operation the number is taken by, or null where the number is the value
     *                itself
     */
    public static Bounds of(Type type, Symbols symbols, Carrier carrier, ValueName measure) {
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
                for (Ast.Expr each : HelperInvariants.conjunctsOf(clause.expr())) {
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
     * How many of whatever counts a value the rules on its type require it to hold, or 0 where they
     * require none.
     *
     * <p>Which operation counts it is asked of {@link NumericMeasures}, the one list of them, so that
     * a rule this reads and a rule a boundary is drawn on are read off the same call. Not asked of the
     * decoder's constraints: Raoh has no entry for a set's size — a set crosses the boundary as a list
     * and a size chained after the mapping that drops duplicates would count the wrong things — and
     * that absence is a fact about the decoder rather than about what the rule says.
     *
     * <p>What is being counted follows from the type. A string's rule reaches this as readily as a
     * list's, and comes back a floor on characters; a caller reading every floor above zero as a
     * collection that cannot be empty would be answering a question this did not.
     */
    public static int leastCountOf(Type type, Symbols symbols) {
        ValueName.Stdlib counts = NumericMeasures.takenOf(type, symbols);
        if (counts == null) {
            return 0;
        }
        Bounds sized = of(type, symbols, Carrier.WHOLE, counts);
        if (sized == null || sized.min() == null) {
            return 0;
        }
        return CountDomain.leastFrom(sized.min().at());
    }

    /**
     * The same, where the record the position sits in has a rule about it too.
     *
     * <p>The higher of the two, because both are rules the construction has to satisfy. A value
     * clearing one and not the other is refused as surely as one clearing neither, so a reader taking
     * either alone offers a position a value something refuses: ask only the type and a field whose
     * floor is its record's is handed the value that holds nothing.
     *
     * <p>Both readings end at {@link CountDomain#leastFrom}, so what a floor comes to as a count is
     * settled once. A second reading here could put a record's {@code > 3} at three while the type's
     * came to four, and the two would disagree about one rule written twice.
     */
    public static int leastCountOf(Type type, Symbols symbols, FieldDomains.Held held) {
        return Math.max(leastCountOf(type, symbols),
                held == null ? 0 : CountDomain.leastFrom(held.bounds().min()));
    }

    private DeclaredBounds() {}
}
