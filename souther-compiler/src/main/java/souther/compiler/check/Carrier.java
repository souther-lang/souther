package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What a position's counts stand for, and the only place either direction is crossed.
 *
 * <p>The interval algebra holds one number per position, so a type takes part in it by having an
 * order-preserving count and a way back. Whether a type has one is this question, asked here and
 * nowhere else: it was answered in three places that disagreed — a predicate deciding what a report
 * said, a reader deciding what an invariant bounded, and a table deciding how a value was written
 * back — so a {@code Date} was a carrier to one of them and not to another, and the disagreement
 * showed up as a bound that vanished without a word.
 *
 * <p><b>Closed both ways.</b> Everything that turns a value into a {@link Count} and everything that
 * turns a {@link Count} back into a value is a method here. Outside this type nothing may read a
 * count as a number a model wrote, or build a value out of one: those were the leaks, and each of
 * them was a reader that had a carrier available and did not ask it. A reader that sniffed a written
 * temporal for a {@code T} to decide whether it was counting days or seconds is the shape they all
 * had — the declared type says which, and guessing from the text is a second answer to a question
 * already answered.
 *
 * <p><b>Sealed, so a carrier added is one every reader has to answer for.</b> Each switch below is
 * over these cases and nothing else, which is what makes a sixth one a build failure rather than a
 * wrong value. That mattered least while every carrier's counts looked like numbers a model might
 * write; an ordinal is a small integer, which is the most plausible-looking wrong value of the five
 * and the one a report is least likely to give away.
 *
 * <p><b>Which types have one</b> is {@link #ofValue}. The primitives are matched exhaustively, so
 * one added to the language stops the build; an enumeration is the sum itself, checked as one
 * ({@link TypeOps#isUnitOnlySum}). Which order two operands can be compared on is a wider question
 * with its own answer ({@link TypeOps#comparisonEnumeration}) — it holds of a case and of a union of
 * cases as well — and this one was being answered with it, which gave a position declared as one
 * case the whole enumeration's counts and a line at a value that position cannot hold.
 */
public sealed interface Carrier {

    /** A whole number: an {@code Int}, and every size. */
    record Whole() implements Carrier {}

    /** A decimal. */
    record Dense() implements Carrier {}

    /** A day count, standing for a date. */
    record Days() implements Carrier {}

    /** A second count, standing for a date-time. Apart from {@link Days}: two units in one carrier
     *  would leave a line drawn on a day beside one drawn on a second with nothing saying which. */
    record Seconds() implements Carrier {}

    /**
     * The place a case takes in its enumeration's declaration, standing for the case.
     *
     * <p>Carries the cases because the count means nothing without them: 1 is a day, a second, a
     * number and {@code Qualified} depending on what is being counted, and only here is that ever
     * decided. Which enumeration a value is ordered by belongs to the sum rather than to the case —
     * a unit data may be listed by two sums that place it differently — so the sum is named as well.
     *
     * @param enumeration the sum whose declaration order this counts in
     * @param cases       its leaf cases, in that order
     */
    record Ordinal(TypeName enumeration, List<TypeName> cases) implements Carrier {

        public Ordinal {
            cases = List.copyOf(cases);
        }

        /** Where {@code name} comes in the declaration, or null where this enumeration has no such
         * case — which is a value of some other type and not a place on this order. */
        public Place at(TypeName name) {
            int index = cases.indexOf(name);
            return index < 0 ? null : Count.of(index);
        }

        /** The case at a count. Only ever asked of a count this carrier holds, which is what
         * {@link Carrier#onTheGrid} is for. */
        public TypeName caseAt(Place count) {
            return cases.get(Count.number(count).at().intValueExact());
        }
    }

    Carrier WHOLE = new Whole();
    Carrier DENSE = new Dense();
    Carrier DATE = new Days();
    Carrier MOMENT = new Seconds();

    /**
     * The carrier a location's own content is counted on, or null where nothing here draws a line on
     * it.
     *
     * <p>Asked of what the names wrap, so a newtype answers as the value it carries — which is what
     * makes {@code data Cutoff = Date} the same carrier as a bare {@code Date}, and
     * {@code data StageN = Stage} the same carrier as a bare {@code Stage}.
     */
    static Carrier ofValue(Type type, Symbols symbols) {
        Type base = TypeOps.base(type, symbols);
        if (base instanceof Type.Prim prim) {
            return switch (prim) {
                case INT -> WHOLE;
                case DECIMAL -> DENSE;
                case DATE -> DATE;
                case DATETIME -> MOMENT;
                // `String` is ordered and has no count to embed into, so nothing here draws a line
                // on it. `Bool` and `Raw` are not ordered at all.
                case STRING, BOOL, RAW -> null;
            };
        }
        // The enumeration itself, and not an order a value of it can be compared on. Which order
        // two operands are comparable by is a wider question and has its own answer
        // ({@link TypeOps#comparisonEnumeration}): a case and a union of cases are both comparable
        // on their sum's order without ranging over it. Answered with that wider order, a position
        // declared as one case took the whole enumeration's counts, and the line drawn on it asked
        // for a row at a value the position cannot hold.
        if (!(base instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.SumData sum)
                || !TypeOps.isUnitOnlySum(base, symbols)) {
            return null;
        }
        List<TypeName> cases = TypeOps.leafCases(sum, symbols);
        return cases.isEmpty() ? null : new Ordinal(ref.name(), cases);
    }

    /** How the counts on this carrier are spaced, which is what decides whether a strict bound has a
     * next count to step to. */
    default Granularity spacing() {
        return switch (this) {
            case Whole _, Days _, Ordinal _ -> Granularity.DISCRETE;
            // No smallest step this language names. A strict bound then leaves its end on the count
            // it names and says that count is not one of its own, rather than inventing a step in.
            case Dense _, Seconds _ -> Granularity.DENSE;
        };
    }

    /**
     * The count as this carrier can actually hold it, or null where it holds nothing there.
     *
     * <p>Not every number between two of this carrier's counts is one of them. A date-time is dense
     * in the sense that matters to a strict bound — there is no step to sharpen one onto — and the
     * counts it can be written as still sit on a grid, at the nanosecond. Halfway between two
     * adjacent ones is a number and not a date-time.
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
            // A decimal holds every number: the ranges and the values are the same numbers.
            case Dense _ -> count;
            // A whole number, a day count and an ordinal step, so a number between two of them is
            // neither, and each stops where what carries it stops. Asked here rather than at each
            // place that steps one, because a step off the end is the same non-value however it was
            // reached — and an enumeration's ends are the nearest of the five, one step past its
            // last case.
            case Whole _ -> whole(count) && within(count, Long.MIN_VALUE, Long.MAX_VALUE)
                    ? count : null;
            case Days _ -> whole(count)
                    && within(count, java.time.LocalDate.MIN.toEpochDay(),
                            java.time.LocalDate.MAX.toEpochDay())
                    ? count : null;
            case Ordinal ordinal -> whole(count) && within(count, 0, ordinal.cases().size() - 1)
                    ? count : null;
            // Round-tripped and then held to itself. What a date-time can be written as sits on a
            // grid at the nanosecond, and the writer rounds onto it — so returning what came back
            // would answer "the nearest count this carrier holds" to a question that asks whether it
            // holds this one. A caller reading that as a yes offers a value between two moments as
            // one of them.
            // Where the calendar stops first, and then on the grid inside it. A date-time is the
            // one carrier whose counts are bounded at both ends and spaced besides, and asking the
            // writer would be asking it to answer for a count it exists to write — which it does by
            // throwing, out of a question whose whole job is to answer no.
            //
            // Round-tripped and then held to itself. What a date-time can be written as sits on a
            // grid at the nanosecond, and the writer rounds onto it, so returning what came back
            // would answer "the nearest count this carrier holds" to a question that asks whether
            // it holds this one. A caller reading that as a yes offers a value between two moments
            // as one of them.
            case Seconds _ -> {
                if (!DateTimes.holds(count)) {
                    yield null;
                }
                Place written = DateTimes.secondOf(DateTimes.written(count));
                yield written != null && written.sameAs(count) ? count : null;
            }
        };
    }

    /** Whether a place counts to a whole number, which is what a stepping carrier's order is made
     * of. A place that is not a number is not one. */
    private static boolean whole(Place at) {
        return at instanceof Count count && count.whole();
    }

    private static boolean within(Place count, long low, long high) {
        return count.compareTo(Count.of(low)) >= 0 && count.compareTo(Count.of(high)) <= 0;
    }

    /**
     * A place inside a pair of ends, or null where they hold none.
     *
     * <p>The one way a range gives up a value, so that nothing deciding what to write reads an end
     * and loses whether the range holds it. An end the range holds is the place taken: it is inside
     * whatever other end there is, and it is what a boundary wants written anyway. An end the range
     * stops short of is not one, and over a carrier whose values do not step there is nothing beside
     * it to take instead — so the place comes from inside, between the ends where both are known and
     * a step in from the only one where there is one.
     *
     * <p>Asked of the carrier because the answer is the carrier's arithmetic. It sat on the ends
     * themselves, which is where it could only ever be a number's answer, and a carrier whose values
     * are not numbers had nothing to say through it.
     */
    default Place somethingInside(Endpoint low, Endpoint high) {
        Granularity spacing = spacing();
        if (spacing == Granularity.DISCRETE) {
            Endpoint lo = whole(low, true);
            Endpoint hi = whole(high, false);
            if (!Endpoint.someValueLiesBetween(lo, hi)) {
                return null;
            }
            return lo != null ? lo.at() : hi != null ? hi.at() : Count.ZERO;
        }
        if (!Endpoint.someValueLiesBetween(low, high)) {
            return null;
        }
        if (low == null) {
            return high == null ? Count.ZERO
                    : high.inclusive() ? high.at() : count(high).minus(1);
        }
        if (low.inclusive()) {
            return low.at();
        }
        // Open below, so the place is not the end. Halfway to the other end where there is one — a
        // count the dense carrier holds, and inside both — and a step in where there is not.
        return high == null ? count(low).plus(1)
                : count(low).halfwayTo(count(high), Granularity.DENSE);
    }

    /** An end moved onto the nearest whole count the range holds, which is always one it holds. */
    private static Endpoint whole(Endpoint end, boolean lower) {
        if (end == null) {
            return null;
        }
        java.math.RoundingMode away = lower ? java.math.RoundingMode.CEILING
                : java.math.RoundingMode.FLOOR;
        if (end.inclusive()) {
            return Endpoint.inclusive(count(end).rounded(away));
        }
        java.math.RoundingMode into = lower ? java.math.RoundingMode.FLOOR
                : java.math.RoundingMode.CEILING;
        Count step = count(end).rounded(into);
        return Endpoint.inclusive(lower ? step.plus(1) : step.minus(1));
    }

    /** The count an end is at. Only reached from the arithmetic above, which every carrier that has
     * none skips before it gets here. */
    private static Count count(Endpoint end) {
        if (!(end.at() instanceof Count at)) {
            throw new IllegalStateException("a carrier with no counts reached the arithmetic: " + end);
        }
        return at;
    }

    /**
     * A place the position holds that is none of {@code singled}, or null where this found none.
     *
     * <p>Where the values step, the one beside a singled-out value is the nearest thing to it and is
     * tried first. Over a carrier whose values do not step there is no step to take: a value bounded
     * to `+[0, 1]+` and singled out at `+0.5+` steps to `+1.5+` and `+-0.5+`, both outside, and
     * neither says anything about whether the class has values — it holds `+0+`, `+1+` and everything
     * between. So the ends of what the position admits are asked, and a value between them, before
     * any step is.
     *
     * <p>Null is this having found none and never the class being empty. Nothing here enumerates a
     * range, so what a caller may say about an empty answer is that it composed nothing.
     */
    default Place somethingOtherThan(java.util.List<Place> singled, NumericDomain.Bounds within) {
        java.util.List<Place> stepped = new java.util.ArrayList<>();
        for (Place from : singled) {
            if (from instanceof Count count) {
                stepped.add(count.plus(1));
                stepped.add(count.minus(1));
            }
        }
        java.util.List<Place> inside = new java.util.ArrayList<>();
        if (within != null) {
            for (Endpoint end : java.util.Arrays.asList(within.min(), within.max())) {
                if (end != null && end.inclusive()) {
                    inside.add(end.at());
                }
            }
            inside.add(somethingInside(within.min(), within.max()));
            // Between the place singled out and each end, which is where a range with no step still
            // has room once the ends themselves are singled out too.
            for (Place from : singled) {
                for (Endpoint end : java.util.Arrays.asList(within.min(), within.max())) {
                    if (end != null) {
                        inside.add(somethingInside(Endpoint.exclusive(from), end));
                        inside.add(somethingInside(end, Endpoint.exclusive(from)));
                    }
                }
            }
        }
        java.util.List<Place> tried = new java.util.ArrayList<>();
        if (spacing() == Granularity.DENSE) {
            tried.addAll(inside);
            tried.addAll(stepped);
        } else {
            tried.addAll(stepped);
            tried.addAll(inside);
        }
        for (Place candidate : tried) {
            // On the carrier's grid before it is asked anything. Halfway between two adjacent moments
            // is neither of them as a number and is one of them once written, so a class of
            // everything else was offered one of the values it exists to exclude.
            Place each = onTheGrid(candidate);
            if (each != null && (within == null || within.admits(each))
                    && singled.stream().noneMatch(each::sameAs)) {
                return each;
            }
        }
        return null;
    }

    /**
     * The count a rule's literal names on this carrier, or null where the expression names none.
     *
     * <p>Which literals a rule may be bounded by is a fact about what carries the value and not about
     * the reader that wants one, so it is answered here. It was being answered separately by each
     * reader instead, and an invariant and a {@code guard} at one position admitted different rules
     * with only one of them saying so.
     */
    default Place literalOf(Ast.Expr e) {
        return switch (this) {
            case Whole _ -> Count.of(InvariantBound.wholeLiteral(e));
            case Dense _ -> Count.of(InvariantBound.literalOf(e));
            case Days _ -> temporal(e, "Date", Dates::dayOf);
            case Seconds _ -> temporal(e, "DateTime", DateTimes::secondOf);
            // A case is named rather than written, so the literal is a name and what it denotes says
            // which case it is. Read off the denotation and not the text: a case is reachable under
            // an alias, and two enumerations may declare cases spelled the same way.
            case Ordinal ordinal -> e instanceof Ast.Var v
                    && v.denotes() instanceof ValueName.OfType named
                    ? ordinal.at(named.type()) : null;
        };
    }

    /** The count a written temporal is, or null where the expression is not one of that kind. A
     *  temporal is written as a literal with its text spelled out (spec
     *  §a-temporal-value-is-written-as-a-literal), so it is read here rather than run. */
    private static Count temporal(Ast.Expr e, String written,
                                  java.util.function.Function<String, Count> countOf) {
        return e instanceof Ast.Apply call && written.equals(call.reaches())
                && call.args().size() == 1 && call.args().get(0) instanceof Ast.StringLit iso
                ? countOf.apply(iso.value()) : null;
    }

    /**
     * The count an observed value is on this carrier, or null where the value is not one of this
     * carrier's.
     *
     * <p>Null is about the value and not about this: a {@code Text} where a date was expected is a
     * value the position does not hold, and a caller with a reason to keep is the one that has it.
     *
     * <p>A newtype is not a step in a path, so what sits at a position may be the construction with
     * the value one inside it. Reached through rather than refused, which is how a wrapped number and
     * a bare one are the same count.
     */
    default Place placeOf(ObservedValue value) {
        ObservedValue at = value instanceof ObservedValue.Constructed c && c.field("value") != null
                ? c.field("value") : value;
        return switch (this) {
            // A whole number written as a decimal is the same count; whether the position admits a
            // fraction is the range's question and not this one's.
            case Whole _, Dense _ -> switch (at) {
                case ObservedValue.Integer i -> Count.of(i.value());
                case ObservedValue.Decimal d -> Count.of(d.value());
                case null, default -> null;
            };
            case Days _ -> at instanceof ObservedValue.Temporal t ? Dates.dayOf(t.iso()) : null;
            case Seconds _ ->
                    at instanceof ObservedValue.Temporal t ? DateTimes.secondOf(t.iso()) : null;
            // A case carries nothing but which case it is, so the observation is its name.
            case Ordinal ordinal ->
                    at instanceof ObservedValue.Unit u ? ordinal.at(u.type()) : null;
        };
    }

    /**
     * The value a count stands for, as an observation of it would look.
     *
     * <p>The one place a count leaves the algebra. A date is a day count inside the ranges and a date
     * everywhere a person reads it, and the conversion sitting here is what keeps a cut, a report and
     * a fixture from disagreeing about which of the two a line is drawn at.
     */
    default ObservedValue valueOf(Place count) {
        return switch (this) {
            case Whole _ -> new ObservedValue.Integer(Count.number(count).at().longValueExact());
            case Dense _ -> new ObservedValue.Decimal(Count.number(count).at());
            case Days _ -> new ObservedValue.Temporal(Dates.written(count));
            case Seconds _ -> new ObservedValue.Temporal(DateTimes.written(count));
            case Ordinal ordinal -> new ObservedValue.Unit(ordinal.caseAt(count));
        };
    }

    /**
     * A count as an author would write the value it stands for. A report that printed the count
     * itself would name a line at a number nobody wrote.
     *
     * <p>The number and not how many places it was written to, which is the same thing that makes
     * two cuts one cut ({@link Count#key()}). A line an invariant and a {@code guard} both draw is
     * one line recorded once, and the spelling it keeps is whichever rule reached it first — so a
     * label that preserved places would print one line two ways depending on the order the rules
     * were read in.
     */
    default String written(Place count) {
        return switch (this) {
            case Whole _, Dense _ -> count.key();
            case Days _ -> Dates.written(count);
            case Seconds _ -> DateTimes.written(count);
            // The case's name, which is the only thing a person ever writes at such a position. An
            // ordinal in a report would name a line at a number the model does not contain.
            case Ordinal ordinal -> ordinal.caseAt(count).name();
        };
    }
}
