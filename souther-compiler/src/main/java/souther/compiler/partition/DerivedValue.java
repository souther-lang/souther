package souther.compiler.partition;

import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The computation of one value derived from several positions: a total, a difference, any weighing
 * of them that a comparison holds against a threshold.
 *
 * <p><b>A computation is what the same rows fix the weights of.</b> The weights of the positions are
 * weights of the expression that computes the value. The comparison is read at each call of the
 * helper that holds it, and what each call is cut at — which weighings of the positions, at which
 * values — is what the rows on its borders can say of it. Two calls cut at the same places are one
 * computation: a value computed once and handed to two calls, or two calls written alike, are put to
 * the same rows and fixed by them together. Two calls cut at different places are two: one comparison
 * read at two calls with two values, {@code gradeOf(a + b)} and {@code gradeOf(a + 3 * b)}, can weigh
 * its positions wrongly in one and rightly in the other, and a row on a border of one is on no
 * border of the other. The comparison alone merges those, and the call alone splits the first.
 *
 * @param line   the comparison the author wrote
 * @param copies every copy of it a call of the helper made that is cut at the same places, in the
 *               order they were read
 */
public record DerivedValue(AuthoredLine line, List<ModelOccurrence> copies) {

    public DerivedValue {
        Objects.requireNonNull(line, "a computation is of some comparison");
        copies = List.copyOf(copies);
        if (copies.isEmpty()) {
            throw new IllegalArgumentException("a computation is read at some call of its helper");
        }
    }

    /** Whether the border is one this computation is cut by. */
    public boolean isCutBy(Border border) {
        return line.equals(border.origin().authoredLine())
                && border.origin().readAt().inOrder().stream().anyMatch(copies::contains);
    }

    /** One comparison as one call of it reads it. */
    record Reading(AuthoredLine line, ModelOccurrence copy) {}

    /** Where a computation is cut: which weighing of the positions, and where on it. */
    record Place(QuantityKey expression, QuantityCut at) {}

    /**
     * One line cutting a comparison as one call reads it.
     *
     * @param reading the comparison as the call reads it
     * @param place   where on which weighing of its positions the line cuts it
     * @param form    that weighing of the positions
     * @param by      where the line comes from, which is the rule a weight is owed under
     */
    record Cut(Reading reading, Place place, LinearQuantity form, LineOrigin by) {

        /** The positions the weighing names that a weight can be written for. */
        Set<NumericTerm> positions() {
            return OrderedAffineBoundary.weighedByANumber(form);
        }
    }

    /**
     * A computation whose positions are not divided by its thresholds, and so are owed a weight each.
     *
     * @param value     the computation
     * @param positions every position any weighing of it names that a weight can be written for
     * @param forms     the weighings of the positions it was cut at, each once
     * @param cited     the rule a weight of it is owed under, as the lines that cut it cite it, each
     *                  once in the order the lines were read: a set would hand a reader an order
     *                  that changes between runs
     */
    public record Replaced(DerivedValue value, Set<NumericTerm> positions,
                           List<LinearQuantity> forms, List<RuleCitation> cited) {

        public Replaced {
            positions = Set.copyOf(positions);
            forms = List.copyOf(forms);
            cited = List.copyOf(cited);
        }
    }

    /**
     * Every comparison as a call reads it that the line drawn on {@code of} by {@code by} cuts, with
     * where, or none where {@code of} is not a value derived from several positions.
     *
     * <p>One per copy the line was read at: a line read at two calls with one weighing of the
     * positions cuts both.
     */
    static List<Cut> cutsBy(LineOrigin by, BorderQuantity of, QuantityCut at) {
        Optional<LinearQuantity> derived = of.derivedFromSeveralPositions();
        if (derived.isEmpty()) {
            return List.of();
        }
        LinearQuantity form = derived.get();
        Place place = new Place(QuantityKey.of(form.direction()), at);
        List<Cut> out = new ArrayList<>();
        for (ModelOccurrence copy : by.readAt()) {
            out.add(new Cut(new Reading(by.authoredLine(), copy), place, form, by));
        }
        return out;
    }
}
