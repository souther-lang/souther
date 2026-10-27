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
import souther.compiler.partition.ObservedInputs;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.function.Function;
import java.util.function.Predicate;

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
 * not of how a row is shaped: a row that moves one position alone and three rows that each move two
 * can fix the same weights, and a position weighed by minus one has no row that moves it alone and
 * can still be fixed.
 *
 * <p><b>The computation and not one border's weighing.</b> A comparison read at one call over the
 * different windows of a table's input weighs the same positions into every window, so the rows of
 * every border it cuts are put together; the same comparison read at another call is another
 * computation and has its own rows.
 *
 * @param value     the computation
 * @param positions for each position of it a weight can be written for, whether the rows fix it
 * @param forms     the weighings of the positions the computation was cut at, which is what the
 *                  weights are weights in
 * @param cited     the rule the weights are owed under
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
         * Nothing says: no row was read against the computation, a border of it was not read and
         * the rest leave the weight unfixed, or the exact arithmetic gave out on a row. Not a claim
         * that the rows fix nothing, which is a claim about the rows.
         */
        record Undecided() implements Standing {}
    }

    /**
     * One border of a computation as the rows are put to it.
     *
     * @param border   the border, which says which weighing of the positions it cuts and where
     * @param standsOn whether one of the rows given is on the border, at the point a row is owed
     *                 there for where the line falls. Answered at once for a border no row is on,
     *                 so asking it of every row costs a walk of the rows only where one is
     * @param valuesOf what each position of the weighing holds at a row, once for every way the row
     *                 reaches the border
     */
    public record Reading(Border border, Predicate<List<ObservedInputs>> standsOn,
                          Function<ObservedInputs, List<Map<NumericTerm, Place>>> valuesOf) {

        public Reading {
            Objects.requireNonNull(border, "a reading is of a border");
            Objects.requireNonNull(standsOn, "a row is on a border or not");
            Objects.requireNonNull(valuesOf, "a row holds a number at each position");
        }
    }

    /**
     * What {@code rows} fix of each position of the computation {@code of}, put to the borders
     * {@code readings} it is cut by.
     *
     * <p>Existential over the borders and over the ways a row reaches one, the way a point met at
     * one position of a behavior is met: a row on any border, at any reading of it, is a row that
     * fixes what it fixes. Undecided throughout where no border was read.
     *
     * @param everyBorderRead whether every border of the computation was read against the rows;
     *                        where not, a weight the rows leave unfixed is undecided and not
     *                        unfixed
     */
    static TiltOfADerivedValue of(DerivedValue.Replaced of, List<Reading> readings,
                                  List<ObservedInputs> rows, boolean everyBorderRead) {
        List<NumericTerm> places = NumericTerms.inOrder(of.positions());
        if (readings.isEmpty()) {
            return undecided(of, places);
        }
        ExactSpan span = new ExactSpan(places.size());
        for (Reading reading : readings) {
            Map<NumericTerm, ExactRatio> weights = formOf(reading).direction().coefs();
            for (ObservedInputs row : rows) {
                if (!reading.standsOn().test(List.of(row))) {
                    continue;
                }
                for (Map<NumericTerm, Place> values : reading.valuesOf().apply(row)) {
                    ExactRatio[] vector = vectorOf(places, weights, values);
                    if (vector == null) {
                        return undecided(of, places);
                    }
                    span.add(vector);
                }
            }
        }
        if (!span.known()) {
            return undecided(of, places);
        }
        SequencedMap<NumericTerm, Standing> out = new LinkedHashMap<>();
        for (int at = 0; at < places.size(); at++) {
            // Rows fix a weight whatever else went unread, and a weight they leave unfixed is said
            // so only where every border was read: a border nothing was read against is the one
            // place the rest could have been fixed.
            out.put(places.get(at), span.reaches(at) ? new Standing.Shown()
                    : everyBorderRead ? new Standing.NotShown() : new Standing.Undecided());
        }
        return new TiltOfADerivedValue(of.value(), out, of.forms(), of.cited());
    }

    private static TiltOfADerivedValue undecided(DerivedValue.Replaced of,
                                                 List<NumericTerm> places) {
        SequencedMap<NumericTerm, Standing> out = new LinkedHashMap<>();
        places.forEach(each -> out.put(each, new Standing.Undecided()));
        return new TiltOfADerivedValue(of.value(), out, of.forms(), of.cited());
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

    private static LinearQuantity formOf(Reading reading) {
        return reading.border().cut().of().derivedFromSeveralPositions().orElseThrow(
                () -> new IllegalArgumentException("a border of a derived value cuts a form of"
                        + " several positions: " + reading.border()));
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
