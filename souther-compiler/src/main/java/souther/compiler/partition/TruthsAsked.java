package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which of its two values each {@code Bool} position a row is asked to hold.
 *
 * <p>The third thing a way asks of a row, beside where its numbers stand ({@link SearchRegion})
 * and which case each value is ({@link Requirements}). A {@code Bool} stands on no order and divides into no
 * cases, so neither of those says it; what is asked is a value, and a composer meets it by writing
 * that value. Carried beside the other two, so every composer handed a way is handed all three and
 * none of them works this one out for itself.
 *
 * <p><b>One merge decides whether two truths hold together.</b> The same value asked twice is one
 * ask; the two values asked of one position are a way no row takes, which is a fact about the model
 * and said as one ({@link Reachability.NothingReaches}) — never a row a composer could not write.
 *
 * @param at the value each position is asked to hold, in the order the way asked them
 */
public record TruthsAsked(Map<TermPath, Boolean> at) {

    /** Nothing asked. */
    public static final TruthsAsked NONE = new TruthsAsked(Map.of());

    public TruthsAsked {
        at = Collections.unmodifiableMap(new LinkedHashMap<>(at));
    }

    /** What came of putting truths together. */
    public sealed interface Merge {

        /** They hold together, and this is what holds. */
        record Merged(TruthsAsked truths) implements Merge {}

        /** They do not: {@code at} is asked to hold both values. */
        record Conflict(TermPath at) implements Merge {}
    }

    /** Every one of {@code truths} at once, or the position asked for both values. */
    public static Merge of(List<RowDemand.ATruth> truths) {
        Map<TermPath, Boolean> out = new LinkedHashMap<>();
        for (RowDemand.ATruth each : truths) {
            Boolean had = out.putIfAbsent(each.at(), each.held());
            if (had != null && had != each.held()) {
                return new Merge.Conflict(each.at());
            }
        }
        return new Merge.Merged(new TruthsAsked(out));
    }

    /**
     * The same truths, each at the position {@code standing} says the name it is asked at stands
     * at, or the position asked for both values.
     *
     * <p>A {@code Bool} the cases of a sum share is read at the sum and written under whichever case
     * the row is, the way every name the cases share is ({@link ContentsAsked#underTheCases}): asked
     * of the name, a truth is a value a row writes at no position at all.
     *
     * @param standing where each name a way of writing the row wrote stands under its cases. A name
     *                 not in it stands where it is written
     */
    Merge standingAt(Map<TermPath, TermPath> standing) {
        Map<TermPath, Boolean> out = new LinkedHashMap<>();
        for (Map.Entry<TermPath, Boolean> each : at.entrySet()) {
            TermPath there = standing.getOrDefault(each.getKey(), each.getKey());
            Boolean had = out.putIfAbsent(there, each.getValue());
            if (had != null && !had.equals(each.getValue())) {
                return new Merge.Conflict(there);
            }
        }
        return new Merge.Merged(new TruthsAsked(out));
    }

    /**
     * Each value written at its position, or the first position where something else is to be
     * written already — null where none is.
     *
     * <p>Into the one account of what a row writes ({@link LocationWrites}), so a truth and a value
     * asked of the location holding it are told apart by the reader that tells every two asks of
     * one location apart.
     */
    TermPath writtenInto(LocationWrites decided) {
        for (Map.Entry<TermPath, Boolean> each : at.entrySet()) {
            if (decided.write(each.getKey(), List.of(FixtureTemplate.bool(each.getValue())))
                    == LocationWrites.Written.CONFLICTING) {
                return each.getKey();
            }
        }
        return null;
    }
}
