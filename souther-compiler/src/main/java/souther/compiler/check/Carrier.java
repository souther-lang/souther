package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Granularity;
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
 * <p><b>Which types have one</b> is {@link #ofValue}, and it is not a second list: the primitives are
 * matched exhaustively so that one added to the language stops the build, and an enumeration is asked
 * of {@link TypeOps#orderingEnumeration}, which already knows that the order belongs to the sum
 * rather than to a case a second sum may also list.
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
        public Count at(TypeName name) {
            int index = cases.indexOf(name);
            return index < 0 ? null : Count.of(index);
        }

        /** The case at a count. Only ever asked of a count this carrier holds, which is what
         * {@link Carrier#onTheGrid} is for. */
        public TypeName caseAt(Count count) {
            return cases.get(count.at().intValueExact());
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
    default Count onTheGrid(Count count) {
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
            case Whole _ -> count.whole() && within(count, Long.MIN_VALUE, Long.MAX_VALUE)
                    ? count : null;
            case Days _ -> count.whole()
                    && within(count, java.time.LocalDate.MIN.toEpochDay(),
                            java.time.LocalDate.MAX.toEpochDay())
                    ? count : null;
            case Ordinal ordinal -> count.whole() && within(count, 0, ordinal.cases().size() - 1)
                    ? count : null;
            // Round-tripped and then held to itself. What a date-time can be written as sits on a
            // grid at the nanosecond, and the writer rounds onto it — so returning what came back
            // would answer "the nearest count this carrier holds" to a question that asks whether it
            // holds this one. A caller reading that as a yes offers a value between two moments as
            // one of them.
            case Seconds _ -> {
                Count written = DateTimes.secondOf(DateTimes.written(count));
                yield written != null && written.sameAs(count) ? count : null;
            }
        };
    }

    private static boolean within(Count count, long low, long high) {
        return count.at().compareTo(java.math.BigDecimal.valueOf(low)) >= 0
                && count.at().compareTo(java.math.BigDecimal.valueOf(high)) <= 0;
    }

    /**
     * The count a rule's literal names on this carrier, or null where the expression names none.
     *
     * <p>Which literals a rule may be bounded by is a fact about what carries the value and not about
     * the reader that wants one, so it is answered here. It was being answered separately by each
     * reader instead, and an invariant and a {@code guard} at one position admitted different rules
     * with only one of them saying so.
     */
    default Count literalOf(Ast.Expr e) {
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
    default Count countOf(ObservedValue value) {
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
    default ObservedValue valueOf(Count count) {
        return switch (this) {
            case Whole _ -> new ObservedValue.Integer(count.at().longValueExact());
            case Dense _ -> new ObservedValue.Decimal(count.at());
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
    default String written(Count count) {
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
