package souther.compiler.query;

import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
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
 * <p><b>A weight is fixed where a computation weighing it otherwise would fail a row.</b> The faults
 * are the ones a border is held against beside its own line ({@link FaultFamily}): one position
 * weighed one more or one less than the model weighs it, and nothing else. For each such
 * computation, a row at the value nearest a border answers differently from the model where the
 * border's rule, read against the threshold the model wrote and the value the changed computation
 * works out, puts the row on the other side. A weight is fixed where both the computation weighing
 * it one more and the one weighing it one less fail some row, on any border of the call. Which way a
 * wrong weight moves a row is the row's own, and a row on each side of a border can still be moved
 * to the side the model has it on, so the check is made against the rule and not against how the
 * rows are spread.
 *
 * <p>What this establishes is what E1938 establishes and no more: no fault of one step in one
 * weight is left, which is a fault domain stated and not the weights pinned down.
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
         *
         * <p>It says what it went without, in two parts. What a border's own reading went without
         * is that border's fact and travels as the border said it. What is first a fact of the
         * weights is a reason of its own.
         *
         * @param carried what the borders of the computation went without, as they said it
         * @param own     why else the weight is undecided
         */
        record Undecided(WeakeningSet carried,
                         CanonicalSelection<Weakening.AWeightNotDecided.Why> own)
                implements Standing {

            public Undecided {
                Objects.requireNonNull(carried, "an undecided weight says what it went without");
                Objects.requireNonNull(own, "and says why else, or that there is nothing else");
                if (carried.isEmpty() && own.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a weight neither fixed nor shown unfixed went without something");
                }
            }

            /** An undecided weight whose reasons are {@code why}, in the order they are said. */
            static Undecided of(WeakeningSet carried, Set<Weakening.AWeightNotDecided.Why> why) {
                return new Undecided(carried,
                        PublicationOrders.WEIGHT_NOT_DECIDED_REASONS.keep(why));
            }

            /** What this and {@code other} went without between them. */
            Undecided and(Undecided other) {
                Set<Weakening.AWeightNotDecided.Why> both = new LinkedHashSet<>(own.written());
                both.addAll(other.own.written());
                return of(carried.union(other.carried), both);
            }
        }
    }

    /**
     * What a border's rule says of a row when the positions are weighed otherwise, with the
     * threshold the model wrote.
     */
    @FunctionalInterface
    public interface Rule {

        /**
         * Whether the rule holds at a row weighed {@code weights}, or empty where the exact
         * arithmetic could not hold the sum.
         */
        Optional<Boolean> holdsAt(Map<NumericTerm, ExactRatio> weights,
                                  Map<NumericTerm, Place> values);
    }

    /**
     * What the rows on one border say of the weights.
     *
     * @param weights    the model's weight of each position the border's weighing names, in the
     *                   quantity's own units
     * @param rule       the border's rule, which answers for the weights a row is read under
     * @param readings   what each position holds at each reading of a row that stands at a value
     *                   nearest the border, on either side of it, and at no other reading. Which
     *                   side the model has a row on is the rule's answer under the model's own
     *                   weights and is not carried here
     * @param complete   whether those are every reading of every row there is: the border was read
     *                   against every row, every reading of each was tried, and none was left out
     *                   for nothing having watched it run
     * @param wentWithout what the reading of the border went without, in the words the border's
     *                   own reading says it in; empty where it went without nothing or where
     *                   nothing is said of it
     * @param unwatched  whether a row was left out because nothing watched its run
     */
    public record RowsOnABorder(Map<NumericTerm, ExactRatio> weights, Rule rule,
                                List<Map<NumericTerm, Place>> readings, boolean complete,
                                WeakeningSet wentWithout, boolean unwatched) {

        public RowsOnABorder {
            weights = Map.copyOf(weights);
            Objects.requireNonNull(rule, "a border has a rule");
            readings = List.copyOf(readings);
            Objects.requireNonNull(wentWithout, "a border says what it went without, or nothing");
        }

        /** Evidence that went without nothing it could name. */
        public RowsOnABorder(Map<NumericTerm, ExactRatio> weights, Rule rule,
                             List<Map<NumericTerm, Place>> readings, boolean complete) {
            this(weights, rule, readings, complete, WeakeningSet.none(), false);
        }

        /**
         * A border nothing was read against, which says nothing and is not left out.
         *
         * @param wentWithout why nothing was read, as the border's own measurement says it
         */
        static RowsOnABorder unread(WeakeningSet wentWithout) {
            return new RowsOnABorder(Map.of(), (_, _) -> Optional.empty(), List.of(), false,
                    wentWithout, false);
        }

        /** A border nothing was read against, for no reason it has a word for. */
        static RowsOnABorder unread() {
            return unread(WeakeningSet.none());
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
            return places.stream().<Standing>map(_ -> Standing.Undecided.of(WeakeningSet.none(),
                    Set.of(Weakening.AWeightNotDecided.Why.NO_BORDER_OF_IT_WAS_READ))).toList();
        }
        boolean complete = borders.stream().allMatch(RowsOnABorder::complete);
        List<Standing> out = new ArrayList<>();
        for (NumericTerm place : places) {
            Caught more = caught(place, ExactRatio.ONE, borders);
            Caught fewer = caught(place, ExactRatio.ONE.negated(), borders);
            // A fault a row fails is caught whatever else went unread; one no row fails is
            // uncaught only where nothing was left unread.
            if (more.byARow() && fewer.byARow()) {
                out.add(new Standing.Shown());
            } else if (complete && more.tried() && fewer.tried()) {
                out.add(new Standing.NotShown());
            } else {
                out.add(undecided(borders, complete, more.tried() && fewer.tried()));
            }
        }
        return out;
    }

    /**
     * What the weight went without. A border's own reading says what it went without, and that is
     * carried as it was said; a reading short of every word of that kind is the weights' own fact,
     * so a weight is never undecided for no reason.
     */
    private static Standing.Undecided undecided(List<RowsOnABorder> borders, boolean complete,
                                                boolean arithmeticHeld) {
        WeakeningSet carried = WeakeningSet.none();
        Set<Weakening.AWeightNotDecided.Why> own = new LinkedHashSet<>();
        for (RowsOnABorder border : borders) {
            carried = carried.union(border.wentWithout());
            if (border.unwatched()) {
                own.add(Weakening.AWeightNotDecided.Why.A_RUN_WAS_NOT_WATCHED);
            }
        }
        if (!arithmeticHeld) {
            own.add(Weakening.AWeightNotDecided.Why.THE_ARITHMETIC_GAVE_OUT);
        }
        if (!complete && carried.isEmpty() && own.isEmpty()) {
            own.add(Weakening.AWeightNotDecided.Why.A_BORDER_WAS_NOT_READ_IN_FULL);
        }
        return Standing.Undecided.of(carried, own);
    }

    /**
     * Whether a row fails under the computation that weighs {@code place} {@code step} more.
     *
     * @param byARow whether some row on some border is put to the other side of it than the model
     *               has it on
     * @param tried  whether every row was worked out under it, and no sum was past the exact
     *               arithmetic
     */
    private record Caught(boolean byARow, boolean tried) {}

    private static Caught caught(NumericTerm place, ExactRatio step, List<RowsOnABorder> borders) {
        boolean tried = true;
        for (RowsOnABorder border : borders) {
            ExactRatio weight = border.weights().get(place);
            if (weight == null) {
                continue;
            }
            ExactRatio moved = weight.plus(step).orNull();
            if (moved == null) {
                tried = false;
                continue;
            }
            Map<NumericTerm, ExactRatio> weighed = new LinkedHashMap<>(border.weights());
            weighed.put(place, moved);
            // A computation weighing nothing at all is no computation, as it is no line beside one.
            if (weighed.values().stream().allMatch(each -> each.signum() == 0)) {
                continue;
            }
            for (Map<NumericTerm, Place> values : border.readings()) {
                // The side the model has the row on is what its own rule says of it, and the
                // changed computation fails the row where its rule says otherwise.
                Optional<Boolean> kept = border.rule().holdsAt(border.weights(), values);
                Optional<Boolean> changed = border.rule().holdsAt(weighed, values);
                tried &= kept.isPresent() && changed.isPresent();
                if (kept.isPresent() && changed.isPresent() && !kept.equals(changed)) {
                    return new Caught(true, tried);
                }
            }
        }
        return new Caught(false, tried);
    }

    /** What the calls say of one place together: fixed where every call fixes it, unfixed where
     *  some call is shown not to, and undecided otherwise. */
    private static Standing together(List<Standing> calls) {
        if (calls.stream().anyMatch(each -> each instanceof Standing.NotShown)) {
            return new Standing.NotShown();
        }
        Standing.Undecided together = null;
        for (Standing each : calls) {
            if (each instanceof Standing.Undecided undecided) {
                together = together == null ? undecided : together.and(undecided);
            }
        }
        return together == null ? new Standing.Shown() : together;
    }

    /**
     * What a measure over this behavior's lines went without for the weights the rows left
     * undecided, one fact per position. Empty where every position is fixed or shown unfixed.
     */
    public WeakeningSet notDecided(String behavior) {
        WeakeningSet out = WeakeningSet.none();
        for (Map.Entry<NumericTerm, Standing> each : positions.entrySet()) {
            if (each.getValue() instanceof Standing.Undecided undecided) {
                out = out.union(undecided.carried());
                for (Weakening.AWeightNotDecided.Why why : undecided.own().written()) {
                    out = out.union(WeakeningSet.of(new Weakening.AWeightNotDecided(
                            behavior, value, each.getKey(), why)));
                }
            }
        }
        return out;
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
