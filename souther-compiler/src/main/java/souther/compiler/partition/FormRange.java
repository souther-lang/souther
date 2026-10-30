package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.Map;

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
        ExactRatio low = form.constant();
        ExactRatio high = low;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            FormRange ends = standIns.containsKey(each.getKey()) ? standIns.get(each.getKey())
                    : endsOf(each.getKey(), read);
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
        return new FormRange(low, high).within(form, read, standIns);
    }

    /**
     * This, held to what the rules say of the form as a whole, where every atom of it is a place of
     * the input. The ends of the places added one by one say less than the rules say of their sum
     * whenever a rule relates the places: two amounts that together stay within a bound are
     * together within it, and each alone is only within the bound.
     */
    private FormRange within(LinearForm<NumericTerm> form, InputReading read,
                             Map<NumericTerm, FormRange> standIns) {
        if (form.coefs().isEmpty() || form.coefs().keySet().stream().anyMatch(standIns::containsKey)) {
            return this;
        }
        NumericDomain.Bounds runs = read.quantities().runsBetween(form);        if (runs == null) {
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

    /** Whether every number this holds lies from {@code least} to {@code greatest}. */
    boolean liesWithin(BigInteger leastAllowed, BigInteger greatestAllowed) {
        return least.compareTo(ExactRatio.of(leastAllowed)) >= 0
                && greatest.compareTo(ExactRatio.of(greatestAllowed)) <= 0;
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
