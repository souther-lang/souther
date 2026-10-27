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
 * <p><b>The weights are fixed where the rows on the borders determine them.</b> A row on a border
 * satisfies {@code Σ cₚ·xₚ = T}, with the model's own weights {@code cₚ} and a threshold {@code T}
 * the model wrote. A computation that weighs the positions by {@code cₚ·λₚ} instead agrees with
 * every such row only where {@code Σ cₚ·(λₚ − 1)·xₚ = 0} for each, so the weights are fixed where
 * the vectors {@code (cₚ·xₚ)} the rows give span the space of the positions, and a position's own
 * weight is fixed where its axis is in the span. That is a property of what the rows determine, and
 * not of how a row is shaped.
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
     * What the rows on one border say of the weights, as numbers.
     *
     * @param weights     the model's weight of each position the border's weighing names
     * @param onTheBorder what each position holds at each reading of a row that stands at the
     *                    border's point, and at no other reading
     * @param complete    whether those are every reading of every row there is: the border was read
     *                    against every row, every reading of each was tried, and none was left out
     *                    for nothing having watched it run
     */
    public record RowsOnABorder(Map<NumericTerm, ExactRatio> weights,
                                List<Map<NumericTerm, Place>> onTheBorder, boolean complete) {

        public RowsOnABorder {
            weights = Map.copyOf(weights);
            onTheBorder = List.copyOf(onTheBorder);
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
        ExactSpan span = new ExactSpan(places.size());
        boolean complete = true;
        for (RowsOnABorder border : borders) {
            complete &= border.complete();
            for (Map<NumericTerm, Place> values : border.onTheBorder()) {
                ExactRatio[] vector = vectorOf(places, border.weights(), values);
                if (vector == null) {
                    return places.stream().<Standing>map(_ -> new Standing.Undecided()).toList();
                }
                span.add(vector);
            }
        }
        if (!span.known()) {
            return places.stream().<Standing>map(_ -> new Standing.Undecided()).toList();
        }
        List<Standing> out = new ArrayList<>();
        for (int at = 0; at < places.size(); at++) {
            // Rows fix a weight whatever else went unread; one they leave unfixed is unfixed only
            // where nothing was left unread.
            out.add(span.reaches(at) ? new Standing.Shown()
                    : complete ? new Standing.NotShown() : new Standing.Undecided());
        }
        return out;
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
