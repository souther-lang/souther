package souther.compiler.partition;

import souther.compiler.inputs.DecimalPoints;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Predicate;

/**
 * The values to hold the other fields of each element at, the same in every element, so that a
 * container of a given count comes to {@code total} with the one field left solved for: worked
 * out of the total, and not searched for.
 *
 * <p>What each element comes to is a form of its fields, {@code c + Σ wⱼ·qⱼ + w·f}, each field
 * anywhere in its run. Held at one value in every element, the fields held add {@code Q} to each
 * element; {@code n} elements then come to {@code n·(c + Q)} and what the field solved for adds
 * over them, which is anywhere from {@code n} times the least it adds to {@code n} times the
 * most. So the total is written with {@code n} elements wherever {@code Q} can be chosen with
 * {@code total / n − c − Q} within what one element's field adds — a run of {@code Q}, met with
 * what the held fields can add together. The value of {@code Q} is then shared out among the
 * held fields: each starts at the end it adds least at, and each in turn takes as much of what is
 * left as its run lets it. Every total {@code n} elements come to over the fields' runs is
 * written so where the field solved for steps through its run, which is what the reading of the
 * total says it takes ({@code UndividedByARelation#overTheCounts}).
 *
 * <p>The count is the caller's: which counts the container may hold is its rules' to say, and a
 * count this chose would be one they may not leave it.
 *
 * <p>On an order that steps every value is a whole number; on one that does not, a value is one
 * a row can be written at ({@code writable}). Where no value is, nothing is held, and the total
 * is not written this way.
 */
final class FieldsHeldForATotal {

    private FieldsHeldForATotal() {
    }

    /**
     * A field of each element: its weight in what the element comes to, and the least and the
     * greatest value it may stand at, each null where the run has no end on that side.
     */
    record Field(ExactRatio weight, ExactRatio least, ExactRatio greatest) {

        Field {
            Objects.requireNonNull(weight, "a field is weighed");
            if (weight.isZero()) {
                throw new IllegalArgumentException("a field weighed nought is in no form");
            }
        }

        /** The least this field adds to what one element comes to, or null where there is none. */
        ExactRatio leastAdded() {
            return times(weight.signum() > 0 ? least : greatest);
        }

        /** The most this field adds, or null where there is none. */
        ExactRatio mostAdded() {
            return times(weight.signum() > 0 ? greatest : least);
        }

        private ExactRatio times(ExactRatio value) {
            return value == null ? null : weight.times(value).orNull();
        }
    }

    /**
     * The value to hold each of {@code held} at, so that {@code many} elements of
     * {@code constant} plus the held fields and {@code free} come to {@code total} — or null
     * where no such values are shown.
     *
     * @param many     how many elements the container holds, one or more
     * @param whole    whether the fields' values step by whole numbers
     * @param writable whether a value is one a row of the fields can be written at
     */
    static <K> Map<K, ExactRatio> heldFor(Map<K, Field> held, Field free, ExactRatio constant,
                                         ExactRatio total, int many, boolean whole,
                                         Predicate<ExactRatio> writable) {
        if (many < 1) {
            throw new IllegalArgumentException("a container of none holds no field: " + many);
        }
        ExactRatio heldLeast = ExactRatio.ZERO;
        ExactRatio heldMost = ExactRatio.ZERO;
        for (Field each : held.values()) {
            heldLeast = heldLeast == null || each.leastAdded() == null ? null
                    : heldLeast.plus(each.leastAdded()).orNull();
            heldMost = heldMost == null || each.mostAdded() == null ? null
                    : heldMost.plus(each.mostAdded()).orNull();
        }
        ExactRatio each = total.dividedBy(ExactRatio.of(many)).orNull();
        ExactRatio beside = each == null ? null : each.minus(constant).orNull();
        if (beside == null) {
            return null;
        }
        // What the held fields may add for the field solved for to make up the rest.
        ExactRatio from = max(heldLeast, free.mostAdded() == null ? null
                : beside.minus(free.mostAdded()).orNull());
        ExactRatio to = min(heldMost, free.leastAdded() == null ? null
                : beside.minus(free.leastAdded()).orNull());
        if (from != null && to != null && from.compareTo(to) > 0) {
            return null;
        }
        for (ExactRatio added : valuesBetween(from, to, whole, writable)) {
            Map<K, ExactRatio> values = sharedOut(held, added, whole, writable);
            if (values != null) {
                return values;
            }
        }
        return null;
    }

    /**
     * The values from {@code from} to {@code to} a share is tried at: on an order that steps,
     * the whole numbers at the ends, or nought where neither end has one; on one that does not,
     * the ends a row can be written at, or the decimal a row is built at inside the run nearest
     * {@code from} ({@link DecimalPoints#within}), which is where the values of a run are chosen
     * when a relation is read.
     */
    private static List<ExactRatio> valuesBetween(ExactRatio from, ExactRatio to, boolean whole,
                                                  Predicate<ExactRatio> writable) {
        List<ExactRatio> out = new ArrayList<>();
        if (whole) {
            ExactRatio low = from == null ? null : wholeAt(from.ceiling());
            ExactRatio high = to == null ? null : wholeAt(to.floor());
            for (ExactRatio each : low == null && high == null ? List.of(ExactRatio.ZERO)
                    : low == null ? List.of(high) : high == null ? List.of(low)
                    : List.of(low, high)) {
                if (each != null && within(each, from, to) && !out.contains(each)) {
                    out.add(each);
                }
            }
            return out;
        }
        if (from == null && to == null) {
            out.add(ExactRatio.ZERO);
            return out;
        }
        for (ExactRatio each : new ExactRatio[] {from, to}) {
            if (each != null && writable.test(each) && !out.contains(each)) {
                out.add(each);
            }
        }
        if (out.isEmpty() && from != null) {
            ExactRatio inside = DecimalPoints.within(ExactCut.inclusive(from),
                    to == null ? null : ExactCut.inclusive(to), true);
            if (inside != null && writable.test(inside)) {
                out.add(inside);
            }
        }
        return out;
    }

    /**
     * Each of {@code held} at a value of its run, the values adding {@code added} between them
     * — or null where they cannot. Each starts at the end of its run it adds least at, or at the
     * one it adds most at where that is the only end, or at nought where it has none; then each
     * in turn is moved as far toward what is left as its run lets it.
     */
    private static <K> Map<K, ExactRatio> sharedOut(Map<K, Field> held, ExactRatio added,
                                                   boolean whole,
                                                   Predicate<ExactRatio> writable) {
        Map<K, ExactRatio> values = new LinkedHashMap<>();
        ExactRatio left = added;
        for (Map.Entry<K, Field> each : held.entrySet()) {
            Field field = each.getValue();
            ExactRatio start = field.leastAdded() != null
                    ? (field.weight().signum() > 0 ? field.least() : field.greatest())
                    : field.mostAdded() != null
                    ? (field.weight().signum() > 0 ? field.greatest() : field.least())
                    : ExactRatio.ZERO;
            values.put(each.getKey(), start);
            left = left.minus(field.weight().times(start).orNull()).orNull();
            if (left == null) {
                return null;
            }
        }
        for (Map.Entry<K, Field> each : held.entrySet()) {
            if (left.isZero()) {
                break;
            }
            Field field = each.getValue();
            ExactRatio at = values.get(each.getKey());
            ExactRatio moved = left.dividedBy(field.weight()).orNull();
            if (moved == null) {
                return null;
            }
            ExactRatio wanted = at.plus(moved).orNull();
            ExactRatio reached = wanted == null ? null
                    : max(field.least(), min(field.greatest(), wanted));
            if (reached != null && whole) {
                reached = moved.signum() > 0 ? wholeAt(reached.floor()) : wholeAt(reached.ceiling());
            }
            if (reached == null) {
                return null;
            }
            ExactRatio taken = field.weight().times(reached.minus(at).orNull()).orNull();
            left = taken == null ? null : left.minus(taken).orNull();
            if (left == null) {
                return null;
            }
            values.put(each.getKey(), reached);
        }
        if (!left.isZero()) {
            return null;
        }
        for (ExactRatio value : values.values()) {
            if (!whole && !writable.test(value)) {
                return null;
            }
        }
        return values;
    }

    private static boolean within(ExactRatio value, ExactRatio from, ExactRatio to) {
        return (from == null || value.compareTo(from) >= 0) && (to == null || value.compareTo(to) <= 0);
    }

    private static ExactRatio wholeAt(ExactAnswer<BigInteger> whole) {
        return whole instanceof ExactAnswer.Held<BigInteger>(BigInteger at) ? ExactRatio.of(at) : null;
    }

    /** The greater of the two, an absent one standing for no bound: the other. */
    private static ExactRatio max(ExactRatio one, ExactRatio other) {
        return one == null ? other : other == null ? one : one.compareTo(other) >= 0 ? one : other;
    }

    private static ExactRatio min(ExactRatio one, ExactRatio other) {
        return one == null ? other : other == null ? one : one.compareTo(other) <= 0 ? one : other;
    }
}
