package souther.compiler.query;

import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.function.Supplier;

/**
 * Whether the rows fix how each position weighs into the value a computation derives from several
 * positions.
 *
 * <p>A weight is a fault of the computation and not of one threshold: the value is computed once
 * and every threshold of its table reads it, so a position left out or weighed wrongly moves every
 * border the same way. What each threshold is owed on its own — where it falls and on which side —
 * is the border's ({@link BorderAssessment}); what is owed here is once for the computation and
 * once for each position (White and Cohen, IEEE TSE SE-6(3), 1980).
 *
 * <p><b>The weights are fixed where the rows beside the borders determine them.</b> A row at the
 * value nearest a border satisfies {@code Σ cₚ·xₚ = T} for a {@code T} the model wrote, with the
 * model's own weights {@code cₚ}. A computation that weighs the positions by {@code cₚ·λₚ} instead
 * moves such a row by {@code Σ cₚ·(λₚ − 1)·xₚ}, so the weights are fixed where the vectors
 * {@code (cₚ·xₚ)} the rows give span the space of the positions, and a position's own weight is
 * fixed where its axis is in the span. Which way a wrong weight moves a row decides which rows
 * catch it: one that moves it up is caught by a row where the rule does not hold and one that moves
 * it down by a row where it does, and a strict comparison holds one value further up than a
 * non-strict one. So the two sides are spanned apart, and a weight is fixed where its axis is in
 * both. A side the border has no value on, because the type ends there, is not asked.
 *
 * <p><b>Evidence belongs to the call that reads it.</b> A computation names the calls cut at the
 * same places, and which of them is one computation is not something the borders can prove: two
 * calls written alike may take the value from one place or from two. So a weight is fixed for a
 * computation only where it is fixed for every call of it by the rows on that call's own borders.
 * One value handed to two calls is put to the same rows by both, and each is fixed together; two
 * calls on exclusive branches are put to different rows, and the one no row reaches leaves the
 * weight unfixed.
 *
 * <p><b>And a claim is as strong as the reading behind it.</b> Rows fix a weight whatever else went
 * unread. A weight they leave unfixed is said to be unfixed only where every border was read
 * against every row and every reading of every row was tried; where not, the reading left out is
 * the one place the rest could have been fixed, and the weight is undecided.
 *
 * @param value     the computation
 * @param positions for each position of it a weight can be written for, whether the rows fix it
 * @param forms     the weighings of the positions the computation was cut at, which is what the
 *                  weights are weights in
 * @param cited     the rule the weights are owed under, each once in the order the lines were read
 */
public record TiltOfADerivedValue(DerivedValue value, SequencedMap<NumericTerm, Standing> positions,
                                  List<LinearQuantity> forms, List<RuleCitation> cited) {

    public TiltOfADerivedValue {
        Objects.requireNonNull(value, "a weight is a weight in some computation");
        positions = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(positions));
        forms = List.copyOf(forms);
        cited = List.copyOf(cited);
    }

    /** What the rows came to for one position. */
    public sealed interface Standing {

        /** The rows on the borders fix the weight of this position. */
        record Shown() implements Standing {}

        /** They do not. */
        record NotShown() implements Standing {}

        /**
         * Nothing says: no row was read against the computation, a border of it was not read or a
         * reading of a row was not tried and the rest leave the weight unfixed, or the exact
         * arithmetic gave out on a row. Not a claim that the rows fix nothing, which is a claim
         * about the rows.
         */
        record Undecided() implements Standing {}
    }

    /**
     * The rows that stand at the values nearest a border on one side of where its answer changes.
     *
     * @param readings what each position holds at each reading of a row that stands at the border's
     *             point on this side, and at no other reading
     * @param owed whether the border has a point on this side at all: a rule bounded by its type
     *             has none past the bound, and there is nothing there for a row to show
     */
    public record Side(List<Map<NumericTerm, Place>> readings, boolean owed) {

        public Side {
            readings = List.copyOf(readings);
        }
    }

    /**
     * What the rows on one border say of the weights, as numbers.
     *
     * <p>Both sides of the border are kept apart. A computation that weighs a position more than the
     * model does moves a row across the border one way and one that weighs it less moves it the
     * other, so rows on the side where the rule holds catch the one and rows on the side where it
     * does not catch the other, and neither side says anything of the one it does not catch.
     *
     * @param weights    the model's weight of each position the border's weighing names
     * @param holding    the rows at the value nearest the border where the rule holds
     * @param notHolding the rows at the value nearest the border where it does not
     * @param complete   whether those are every reading of every row there is: the border was read
     *                   against every row, every reading of each was tried, and none was left out
     *                   for nothing having watched it run
     */
    public record RowsOnABorder(Map<NumericTerm, ExactRatio> weights, Side holding,
                                Side notHolding, boolean complete) {

        public RowsOnABorder {
            weights = Map.copyOf(weights);
            Objects.requireNonNull(holding, "the rule holds on one side of the border");
            Objects.requireNonNull(notHolding, "and does not on the other");
        }

        /** A border nothing was read against, which says nothing and is not left out. */
        static RowsOnABorder unread() {
            return new RowsOnABorder(Map.of(), new Side(List.of(), false),
                    new Side(List.of(), false), false);
        }
    }

    /**
     * One border of a computation, and what its rows say.
     *
     * @param border   the border, which says which weighing of the positions it cuts and where
     * @param evidence what the rows on it say, made when asked: a border no row is on has nothing
     *                 to walk
     */
    public record Reading(Border border, Supplier<RowsOnABorder> evidence) {

        public Reading {
            Objects.requireNonNull(border, "a reading is of a border");
            Objects.requireNonNull(evidence, "and says what its rows are");
        }
    }

    /**
     * What the rows fix of each position of the computation {@code of}.
     *
     * @param byCopy the evidence of the borders of each call of it, for every call; a call none of
     *               whose borders was read has no entry
     */
    static TiltOfADerivedValue of(DerivedValue.Replaced of,
                                  Map<ModelOccurrence, List<RowsOnABorder>> byCopy) {
        List<NumericTerm> places = NumericTerms.inOrder(of.positions());
        List<List<RowsOnABorder>> perCall = new ArrayList<>();
        for (ModelOccurrence copy : of.value().copies()) {
            perCall.add(byCopy.getOrDefault(copy, List.of()));
        }
        return new TiltOfADerivedValue(of.value(), standingsOf(places, perCall), of.forms(),
                of.cited());
    }

    /**
     * The standing of each place given what the borders of each call say, which is the whole of
     * the decision and needs no border to be made.
     *
     * @param perCall for each call of the computation, the evidence of its borders
     */
    static SequencedMap<NumericTerm, Standing> standingsOf(List<NumericTerm> places,
                                                           List<List<RowsOnABorder>> perCall) {
        List<List<Standing>> each = new ArrayList<>();
        for (List<RowsOnABorder> borders : perCall) {
            each.add(standingsOfOneCall(places, borders));
        }
        SequencedMap<NumericTerm, Standing> out = new LinkedHashMap<>();
        for (int at = 0; at < places.size(); at++) {
            List<Standing> ofOne = new ArrayList<>();
            for (List<Standing> call : each) {
                ofOne.add(call.get(at));
            }
            out.put(places.get(at), together(ofOne));
        }
        return out;
    }

    /** What the borders of one call fix of each place. */
    private static List<Standing> standingsOfOneCall(List<NumericTerm> places,
                                                     List<RowsOnABorder> borders) {
        if (borders.isEmpty()) {
            return places.stream().<Standing>map(_ -> new Standing.Undecided()).toList();
        }
        ExactSpan holding = new ExactSpan(places.size());
        ExactSpan notHolding = new ExactSpan(places.size());
        boolean holdingOwed = false;
        boolean notHoldingOwed = false;
        boolean complete = true;
        for (RowsOnABorder border : borders) {
            complete &= border.complete();
            holdingOwed |= border.holding().owed();
            notHoldingOwed |= border.notHolding().owed();
            // A row the exact arithmetic gave out on is a row left out: what the rest reach is
            // still reached, and what they leave unreached is no longer known to be unfixed.
            complete &= takeIn(places, border, border.holding(), holding);
            complete &= takeIn(places, border, border.notHolding(), notHolding);
        }
        if (!holdingOwed && !notHoldingOwed) {
            return places.stream().<Standing>map(_ -> new Standing.Undecided()).toList();
        }
        List<Standing> out = new ArrayList<>();
        for (int at = 0; at < places.size(); at++) {
            // Rows fix a weight whatever else went unread; one they leave unfixed is unfixed only
            // where nothing was left unread.
            boolean fixed = (!holdingOwed || holding.reaches(at))
                    && (!notHoldingOwed || notHolding.reaches(at));
            out.add(fixed ? new Standing.Shown()
                    : complete ? new Standing.NotShown() : new Standing.Undecided());
        }
        return out;
    }

    /** Takes the rows of one side of a border into the space of that side, or false where one was
     *  left out because the exact arithmetic gave out. */
    private static boolean takeIn(List<NumericTerm> places, RowsOnABorder border, Side side,
                                  ExactSpan into) {
        boolean all = true;
        for (Map<NumericTerm, Place> values : side.readings()) {
            ExactRatio[] vector = vectorOf(places, border.weights(), values);
            all &= vector != null && into.add(vector);
        }
        return all;
    }

    /** What the calls say of one place together: fixed where every call fixes it, unfixed where
     *  some call is shown not to, and undecided otherwise. */
    private static Standing together(List<Standing> calls) {
        if (calls.stream().anyMatch(each -> each instanceof Standing.NotShown)) {
            return new Standing.NotShown();
        }
        return calls.stream().allMatch(each -> each instanceof Standing.Shown)
                ? new Standing.Shown() : new Standing.Undecided();
    }

    /** What each position contributes at a row, each weighed by the model's own weight of it in
     *  this border's weighing, or null where the exact arithmetic gave out. */
    private static ExactRatio[] vectorOf(List<NumericTerm> places, Map<NumericTerm, ExactRatio> weights,
                                         Map<NumericTerm, Place> values) {
        ExactRatio[] vector = new ExactRatio[places.size()];
        for (int at = 0; at < vector.length; at++) {
            ExactRatio weight = weights.get(places.get(at));
            Place held = values.get(places.get(at));
            if (weight == null || held == null) {
                vector[at] = ExactRatio.ZERO;
                continue;
            }
            ExactRatio contributed = weight.times(Count.number(held).exactly()).orNull();
            if (contributed == null) {
                return null;
            }
            vector[at] = contributed;
        }
        return vector;
    }

    /**
     * The weighing of the positions the weight of {@code position} is said to be a weight in: the
     * widest of the weighings it is in, which is the one it is least a part of.
     */
    public LinearQuantity widestWith(NumericTerm position) {
        LinearQuantity widest = null;
        for (LinearQuantity each : forms) {
            if (each.terms().contains(position)
                    && (widest == null || each.terms().size() > widest.terms().size())) {
                widest = each;
            }
        }
        return Objects.requireNonNull(widest, "a position of a computation is in some weighing");
    }
}
