package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;
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
     * One end of a range, and every rule that put it there.
     *
     * <p>Rules, plural. Two layers can state the same bound — a wrapper repeating what it wraps — and
     * they are two rules a row could be owed to, which is the accounting a cut already keeps. Holding
     * one would drop an obligation rather than a line of text.
     *
     * <p>The clauses and not the declarations they are written on. Held as declarations, two clauses
     * of one declaration at one value came out as one rule, and a report owed one line for a
     * boundary two rules had drawn ({@link Clause}).
     *
     * <p>Each as the rule a report names it by. An end here is read by the measure that turns it
     * into lines to write rows at, and that measure names the rule that drew it — handed the clause
     * reference, it built the identity back for itself, which is a decision about what a rule is
     * being taken by whoever happened to consume one.
     */
    public record End(Endpoint at, List<RuleRef.Invariant> from) {

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
            List<RuleRef.Invariant> both = new ArrayList<>(had.from());
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
            // The clauses with the declaration each was written on, which is what names the line
            // (ADR-0090). Read flat, every clause a spread brought in was named after the type that
            // spread it, and two clauses of one declaration were one rule.
            for (TypeOps.Declared declared
                    : TypeOps.declaredInvariants(layer.named(), layer.data(), symbols, _ -> null)) {
                RuleRef.Invariant rule = new RuleRef.Invariant(Clause.Ref.of(declared));
                for (Hir.Expr each : ClauseHelpers.conjunctsOf(declared.clause().expr())) {
                    // An end and nothing else. A rule this reads no end from narrows nothing here,
                    // and a rule stepping past the last value of the order states an end no value is
                    // at — which is a declaration with no value, answered where counts are and not
                    // by a bound written at a place nothing can be.
                    if (!((measure == null ? InvariantBound.of(each, carrier)
                            : InvariantBound.ofSize(each, measure))
                            instanceof InvariantBound.Read.AnEnd placed)) {
                        continue;
                    }
                    InvariantBound read = placed.bound();
                    End end = new End(read.end(), List.of(rule));
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
     * <p>The clauses of the value a position sits in, read as what they are: a clause naming one
     * coordinate and a constant places an end exactly as one written on that coordinate's own type
     * does, and which declaration held it is what the line is named by (ADR-0090). Here with the
     * rules a type states rather than beside the reader of them, because an end is an end whichever
     * declaration wrote it and both come out as the same {@link Bounds}.
     *
     * @param measured which of the position's coordinates these are wanted for — the count taken of
     *                 it, or its value
     */
    public static Bounds placed(List<FieldDomains.Placed> placed, boolean measured,
                                Carrier carrier) {
        End min = null;
        End max = null;
        for (FieldDomains.Placed each : placed) {
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
    public static Bounds and(Bounds had, Bounds one) {
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

    /**
     * How many of whatever counts a value of {@code type} the rules on it allow it to hold, or every
     * number where they cap it in no way.
     *
     * <p>The dual of {@link #leastCountOf} and asked for the same reason: a rule capping a value at
     * none is written on the type as readily as on the record holding one, and a reader finding only
     * the second offered a value at a position the first leaves no room for.
     */
    public static int mostCountOf(Type type, Symbols symbols) {
        ValueName.Stdlib counts = NumericMeasures.takenOf(type, symbols);
        if (counts == null) {
            return Integer.MAX_VALUE;
        }
        Bounds sized = of(type, symbols, Carrier.WHOLE, counts);
        return sized == null || sized.max() == null ? Integer.MAX_VALUE
                : CountDomain.mostFrom(sized.max().at());
    }

    /**
     * The same, where the record the position sits in has a rule about it too.
     *
     * <p>The lower of the two, because both are rules the construction has to satisfy -- which is
     * {@link #leastCountOf}'s argument at the other end.
     */
    public static int mostCountOf(Type type, Symbols symbols, FieldDomains.Held held) {
        return Math.min(mostCountOf(type, symbols),
                held == null ? Integer.MAX_VALUE : CountDomain.mostFrom(held.bounds().max()));
    }

    private DeclaredBounds() {}
}
