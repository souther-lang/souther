package souther.compiler.values;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The values of a set whose length lies between two numbers of code points.
 *
 * <p>What a rule is shown over, where it is shown only so far: the strings a relation shows to be
 * another value's are those of a language no longer than a value can be written round them, and
 * the strings past that are shown neither way. One value and not a set beside a length, so that
 * whatever asks about it — whether it holds a value, whether a value is in it, what it holds met
 * with something else, which value stands for it — asks the length with the set, and none of them
 * can ask the set alone.
 *
 * <p>A length bounds strings and nothing else: a value that is no string is in this where it is in
 * the set.
 *
 * @param values   the set
 * @param shortest the fewest code points a string of this has
 * @param longest  the most, or null where only the set bounds them
 */
public record ValuesWithin(ValueSet values, long shortest, Long longest) {

    public ValuesWithin {
        if (values == null || shortest < 0 || (longest != null && longest < shortest)) {
            throw new IllegalArgumentException("a set, and lengths a string of it may have");
        }
    }

    /** Every value of {@code values}, whatever its length. */
    public static ValuesWithin all(ValueSet values) {
        return new ValuesWithin(values, 0, null);
    }

    /**
     * The values of {@code values} no longer than {@code longest} code points, or every one of
     * them where that is null. The length is kept only where the set is not shown to hold
     * nothing longer, so a set that is the same with it and without it is one value.
     */
    public static ValuesWithin upTo(ValueSet values, Long longest) {
        if (longest == null) {
            return all(values);
        }
        ValuesWithin bounded = new ValuesWithin(values, 0, longest);
        return new ValuesWithin(values, longest + 1, null).shownToHoldNone()
                ? all(values) : bounded;
    }

    /** The values of {@code values} longer than {@code length} code points. */
    public static ValuesWithin longerThan(ValueSet values, long length) {
        return new ValuesWithin(values, length + 1, null);
    }

    /** Whether a length bounds these beside the set. */
    public boolean bounded() {
        return shortest > 0 || longest != null;
    }

    /** The values of {@code narrowed}, which is the set met with something, as long as these. */
    public ValuesWithin over(ValueSet narrowed) {
        return new ValuesWithin(narrowed, shortest, longest);
    }

    /** The values in both, where {@code narrowed} is what the two sets met to. */
    public ValuesWithin meeting(ValuesWithin other, ValueSet narrowed) {
        long fewest = Math.max(shortest, other.shortest);
        Long most = longest == null ? other.longest
                : other.longest == null ? longest : Long.valueOf(Math.min(longest, other.longest));
        return most != null && most < fewest ? new ValuesWithin(ValueSet.NONE, 0, null)
                : new ValuesWithin(narrowed, fewest, most);
    }

    /** Whether {@code value} is one of these. */
    public boolean has(Value value) {
        return values.has(value) && fits(value);
    }

    private boolean fits(Value value) {
        return TextExtents.ofALengthWithin(value, shortest, longest);
    }

    /** Whether one of these is shown to be a value, as {@link TextExtents#shownToHoldAValue}
     *  answers it of a set and its lengths. */
    public boolean shownToHoldAValue() {
        return TextExtents.shownToHoldAValue(values, shortest, longest);
    }

    /** Whether none of these is shown to be one. */
    public boolean shownToHoldNone() {
        return TextExtents.shownToHoldNone(values, shortest, longest);
    }

    /**
     * The set a value standing for these is looked for in: the set, with what it names outright
     * kept to the lengths these allow. A value found in a set that names none outright is the
     * shortest one it holds, so where that is longer than these allow every value of it is; a
     * value found shorter than these allow says nothing of the longer ones, and is no answer.
     */
    public ValueSet toLookIn() {
        if (!bounded() || !(values instanceof ValueSet.Finite finite)) {
            return values;
        }
        Set<Value> kept = new LinkedHashSet<>();
        finite.values().stream().filter(this::fits).forEach(kept::add);
        return ValueSet.oneOf(kept);
    }
}
