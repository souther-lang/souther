package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * The numbers a form of the input's numbers can come to, from the ends of the places it is over:
 * what the order a place is counted on holds, and what the language says of the number
 * ({@link NumericTerm#reachBounds}). Whether an operation can stop a run at all is asked of it.
 *
 * @param least    the least the form comes to
 * @param greatest the greatest
 */
record FormRange(ExactRatio least, ExactRatio greatest) {

    /** The range of {@code form} over places of the input alone, or null where some place has no
     *  end to give. */
    static FormRange of(LinearForm<NumericTerm> form, InputReading read) {
        return of(form, read, Map.of());
    }

    /**
     * The range of {@code form}, where {@code standIns} names the atoms that are no place of the
     * input — each an expression held aside — with the range of the numbers it comes to, null
     * where that is not known. Null where some atom has no range to give.
     */
    static FormRange of(LinearForm<NumericTerm> form, InputReading read,
                        Map<NumericTerm, FormRange> standIns) {
        return of(form, term -> standIns.containsKey(term) ? standIns.get(term)
                : endsOf(term, read));
    }

    /**
     * The range of {@code form}, worked out as it is written and before any type holds it, over
     * numbers each of which says where it lies whatever the declarations say: a number of the
     * input as it is worked out ({@link #asWorkedOut}), a remainder between the ends its
     * operation states by its divisor ({@link #ofARemainder}), a count of the elements meeting
     * something ({@link #OF_A_COUNT}), and a name {@code named} answers a range of, which it
     * holds where it is read: a name is no number of the input and no remainder, so this is asked
     * of it and of nothing else. The name itself only, and not a field read off it. Null where
     * some number is anything else.
     */
    static FormRange ofNumbers(LinearForm<Quantity> form, InputReading read,
                               Function<BindingId, FormRange> named) {
        return of(form, quantity -> switch (quantity) {
            case DecisionAtom.OfTheInput(var term, var _) -> asWorkedOut(term, read);
            case Quantity.OfABinding bound when bound.steps().isEmpty() ->
                    named.apply(bound.binding());
            case Quantity.HowManyMeet _ -> OF_A_COUNT;
            default -> ofARemainder(quantity);
        });
    }

    /**
     * This, the range of {@code form} {@link #ofNumbers} answered, held to what the declarations
     * say of the form as a whole ({@link #within}) where every number it is over is a number of
     * the input: a value of the input exists only where its rules held, so the numbers a run works
     * out of it lie where they leave them. This as it is where some number is anything else.
     */
    FormRange heldWhereItIsOfTheInput(LinearForm<Quantity> form, InputReading read) {
        Map<NumericTerm, ExactRatio> terms = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof DecisionAtom.OfTheInput(var term, var _))
                    || terms.put(term, each.getValue()) != null) {
                return this;
            }
        }
        return within(new LinearForm<>(form.constant(), terms), read, Map.of());
    }

    /** How many elements of a container meet something: none at the fewest, and no more than a
     *  container holds ({@link GetsPast#MOST_ELEMENTS}). */
    private static final FormRange OF_A_COUNT = new FormRange(ExactRatio.ZERO,
            ExactRatio.of(GetsPast.MOST_ELEMENTS));

    /**
     * The numbers {@code term} comes to as a run works it out: a product, what its two factors
     * come to multiplied, since the type it is answered in is what is being asked of it; a total,
     * not known, for the same reason ({@link #aTotal}); anything else, the ends of its place
     * ({@link #endsOf}), which a value there is held to. Null where the reading answers nothing
     * of the term ({@link Quantities#answersFor}).
     */
    private static FormRange asWorkedOut(NumericTerm term, InputReading read) {
        if (term instanceof NumericTerm.ProductOf product) {
            Function<NumericTerm, FormRange> factor = each -> asWorkedOut(each, read);
            return combined(BinOp.MUL, of(product.one(), factor), of(product.other(), factor));
        }
        if (aTotal(term)) {
            return null;
        }
        return read.quantities().answersFor(term) ? endsOf(term, read) : null;
    }

    /**
     * Whether {@code term} is what the values a container holds add up to. The ends of its place
     * are those its type holds the total to once it is worked out, and a total is worked out
     * exactly before that, so they say nothing of the number it comes to: the exact total of
     * many numbers of a type is past the ends of the type on some runs. A count is not one, and
     * comes to no more than a container holds.
     */
    private static boolean aTotal(NumericTerm term) {
        return switch (term) {
            case NumericTerm.TakenOver over -> over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
            case NumericTerm.TakenOf of -> of.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
            default -> false;
        };
    }

    /**
     * The whole numbers {@code quantity} comes to, where it is what a division by a written number
     * leaves: where its operation states its answers lie by its divisor
     * ({@link Quantity.RemainderOfADividend#whatTheOperationStates}), whatever its dividend comes
     * to. Null where it is no such remainder.
     */
    static FormRange ofARemainder(Quantity quantity) {
        return quantity instanceof Quantity.RemainderOfADividend remainder
                ? ofTheWholeNumbersIn(remainder.whatTheOperationStates()) : null;
    }

    /**
     * The whole numbers {@code runs} holds, from the least to the greatest — or null where it has
     * no end on a side. A remainder is whole, so {@code r < 7} is {@code r <= 6}.
     */
    static FormRange ofTheWholeNumbersIn(NumericDomain.Bounds runs) {
        ExactRatio least = onAWholeNumber(runs.min(), false);
        ExactRatio greatest = onAWholeNumber(runs.max(), true);
        return least == null || greatest == null ? null : new FormRange(least, greatest);
    }

    /**
     * The numbers the rules a position wears leave its value, from the least to the greatest — or
     * null where they have no end on a side. Whole numbers where the position counts in them
     * ({@link #ofTheWholeNumbersIn}); anywhere else an end the rules do not reach is taken as
     * reached, which holds the numbers the rules leave and no fewer.
     */
    static FormRange ofWhatTheRulesLeave(DeclaredBounds.Range rules) {
        NumericDomain.Bounds runs = new NumericDomain.Bounds(rules.min(), rules.max());
        if (rules.carrier() != null && rules.carrier().countsInWholeNumbers()) {
            return ofTheWholeNumbersIn(runs);
        }
        return rules.min() == null || rules.max() == null ? null
                : new FormRange(Count.number(rules.min().at()).exactly(),
                        Count.number(rules.max().at()).exactly());
    }

    /** {@code end} of a run of whole numbers, as the whole number nearest it the run reaches —
     *  or null, where it has no end. */
    private static ExactRatio onAWholeNumber(Endpoint end, boolean upper) {
        if (end == null) {
            return null;
        }
        ExactRatio at = Count.number(end.at()).exactly();
        if (!((upper ? at.floor() : at.ceiling()) instanceof ExactAnswer.Held<BigInteger>(
                BigInteger whole))) {
            return null;
        }
        return ExactRatio.of(end.inclusive() || ExactRatio.of(whole).compareTo(at) != 0 ? whole
                : upper ? whole.subtract(BigInteger.ONE) : whole.add(BigInteger.ONE));
    }

    /** The range of {@code form} over atoms each of whose range {@code rangeOf} answers, null
     *  where that is not known; null where some atom has no range to give. */
    static <A> FormRange of(LinearForm<A> form, Function<A, FormRange> rangeOf) {
        ExactRatio low = form.constant();
        ExactRatio high = low;
        for (Map.Entry<A, ExactRatio> each : form.coefs().entrySet()) {
            FormRange ends = rangeOf.apply(each.getKey());
            if (ends == null) {
                return null;
            }
            boolean rising = each.getValue().signum() >= 0;
            ExactRatio atLeast = each.getValue().times(rising ? ends.least : ends.greatest)
                    .flatMap(low::plus).orNull();
            ExactRatio atMost = each.getValue().times(rising ? ends.greatest : ends.least)
                    .flatMap(high::plus).orNull();
            if (atLeast == null || atMost == null) {
                return null;
            }
            low = atLeast;
            high = atMost;
        }
        return new FormRange(low, high);
    }

    /**
     * The range of {@code form} held to what the declarations say of it as a whole, or null where
     * some place has no end to give ({@link #of}).
     *
     * <p>Asked of the declarations, which relate the places a form is over: the ends of the places
     * added one by one say less than the declarations say of their sum, and a bound written in a
     * clause of a record is seen only there.
     */
    static FormRange held(LinearForm<NumericTerm> form, InputReading read,
                          Map<NumericTerm, FormRange> standIns) {
        FormRange ends = of(form, read, standIns);
        return ends == null ? null : ends.within(form, read, standIns);
    }

    /**
     * Whether every number {@code form} comes to lies from {@code leastAllowed} to
     * {@code greatestAllowed}: by the ends of its places where those show it, and by what the
     * declarations say of the form as a whole where they do not. The declarations are asked only
     * then, since asking them is the dearer question.
     */
    static boolean liesWithin(LinearForm<NumericTerm> form, InputReading read,
                              Map<NumericTerm, FormRange> standIns, BigInteger leastAllowed,
                              BigInteger greatestAllowed) {
        FormRange ends = of(form, read, standIns);
        return ends != null && (ends.liesWithin(leastAllowed, greatestAllowed)
                || ends.within(form, read, standIns).liesWithin(leastAllowed, greatestAllowed));
    }

    /**
     * This, held to what the rules say of the form as a whole, where every atom of it is a place of
     * the input.
     */
    private FormRange within(LinearForm<NumericTerm> form, InputReading read,
                             Map<NumericTerm, FormRange> standIns) {
        if (form.coefs().isEmpty()
                || form.coefs().keySet().stream().anyMatch(standIns::containsKey)) {
            return this;
        }
        NumericDomain.Bounds runs = read.quantities().runsBetween(form);
        if (runs == null) {
            return this;
        }
        ExactRatio from = tighter(least, runs.min(), true);
        ExactRatio to = tighter(greatest, runs.max(), false);
        return new FormRange(from, to);
    }

    /** The ends of the place {@code term} stands at, or null where it has none at either end. */
    static FormRange endsOf(NumericTerm term, InputReading read) {
        TermOrders orders = read.quantities().ordersOf(term);
        Carrier carrier = orders == null ? null : orders.answered();
        NumericDomain.Bounds reach = term.reachBounds();
        ExactRatio least = tighter(wholeEnd(carrier == null ? null : carrier.leastWholeNumber()),
                reach.min(), true);
        ExactRatio greatest = tighter(
                wholeEnd(carrier == null ? null : carrier.greatestWholeNumber()), reach.max(),
                false);
        return least == null || greatest == null ? null : new FormRange(least, greatest);
    }

    /** The numbers {@code range} holds, negated — or null where it is not known. */
    static FormRange negated(FormRange range) {
        return range == null ? null
                : new FormRange(range.greatest.negated(), range.least.negated());
    }

    /**
     * The numbers {@code op}, a sum, a difference or a product, comes to of a number {@code left}
     * holds and one {@code right} holds, exactly and whatever type would hold them — or null where
     * either is not known, or an end has no number the exact arithmetic holds.
     */
    static FormRange combined(BinOp op, FormRange left, FormRange right) {
        if (left == null || right == null) {
            return null;
        }
        List<ExactAnswer<ExactRatio>> ends = switch (op) {
            case ADD -> List.of(left.least.plus(right.least), left.greatest.plus(right.greatest));
            case SUB -> List.of(left.least.minus(right.greatest),
                    left.greatest.minus(right.least));
            case MUL -> List.of(left.least.times(right.least), left.least.times(right.greatest),
                    left.greatest.times(right.least), left.greatest.times(right.greatest));
            default -> List.of();
        };
        ExactRatio least = null;
        ExactRatio greatest = null;
        for (ExactAnswer<ExactRatio> each : ends) {
            if (!(each instanceof ExactAnswer.Held<ExactRatio>(ExactRatio end))) {
                return null;
            }
            least = least == null || end.compareTo(least) < 0 ? end : least;
            greatest = greatest == null || end.compareTo(greatest) > 0 ? end : greatest;
        }
        return least == null ? null : new FormRange(least, greatest);
    }

    /**
     * The numbers a quotient by a whole number comes to where {@code dividend} holds what it
     * divides, or null where those are not known. A whole number other than nought is at least one
     * from nought, so no quotient lies farther from nought than the dividend does; a run whose
     * divisor is nought stops and comes to none.
     */
    static FormRange quotientByAWholeNumber(FormRange dividend) {
        if (dividend == null) {
            return null;
        }
        ExactRatio below = dividend.least.negated();
        ExactRatio farthest = below.compareTo(dividend.greatest) > 0 ? below : dividend.greatest;
        return new FormRange(farthest.negated(), farthest);
    }

    /** Whether every number this holds lies from {@code least} to {@code greatest}. */
    boolean liesWithin(BigInteger leastAllowed, BigInteger greatestAllowed) {
        return least.compareTo(ExactRatio.of(leastAllowed)) >= 0
                && greatest.compareTo(ExactRatio.of(greatestAllowed)) <= 0;
    }

    /** The numbers both this and {@code other} hold, or null where there are none. */
    FormRange meet(FormRange other) {
        ExactRatio from = least.compareTo(other.least) >= 0 ? least : other.least;
        ExactRatio to = greatest.compareTo(other.greatest) <= 0 ? greatest : other.greatest;
        return from.compareTo(to) > 0 ? null : new FormRange(from, to);
    }

    /** The smallest range holding this and {@code other}. */
    FormRange hull(FormRange other) {
        return new FormRange(least.compareTo(other.least) <= 0 ? least : other.least,
                greatest.compareTo(other.greatest) >= 0 ? greatest : other.greatest);
    }

    private static ExactRatio wholeEnd(BigInteger end) {
        return end == null ? null : ExactRatio.of(end);
    }

    /** Whichever of {@code carried} and {@code reached} lies nearer the inside, or the one there
     *  is; null where neither is a number. */
    private static ExactRatio tighter(ExactRatio carried, Endpoint reached, boolean fromBelow) {
        ExactRatio stated = reached != null && reached.at() instanceof Count count
                ? count.exactly() : null;
        if (carried == null || stated == null) {
            return carried != null ? carried : stated;
        }
        return (carried.compareTo(stated) < 0) == fromBelow ? stated : carried;
    }
}
