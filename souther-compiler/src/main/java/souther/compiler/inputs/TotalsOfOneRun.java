package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.AdditiveImage;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.Accumulation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Totals of one run, weighed and added, read as the one total they are.
 *
 * <p>An operation that starts from nought and adds each value it is handed answers, over one run,
 * the sum of what it answers over each part of what the run holds: {@code Σ f + c·Σ g} is
 * {@code Σ (f + c·g)}, over the same elements in the same order. So a rule weighing a total of one
 * thing an element holds against a total of another, over the same list, is a rule about one total,
 * and what one element comes to is the difference: one value however the totals were written.
 *
 * <p>Only in a type whose sums have no end to pass. A sum of whole numbers stops at the end of a
 * long, and two writings of one total stop at different totals, so there they are two numbers and
 * are left as they were written.
 *
 * <p>What makes it one total is what the library says the operation is
 * ({@link DefaultBoundOperationFacts#accumulation}): an addition from nought. Two runs over the same
 * elements are one run only where each element is handed to both in the same order, which is asked
 * only of a computation that turns on that order.
 */
public final class TotalsOfOneRun {

    private TotalsOfOneRun() {}

    /**
     * {@code form} with every group of totals over one run read as one total of what each element
     * comes to, at the weight every part of that number shares — or {@code form} as it is where
     * that is how it is written.
     *
     * <p>A total alone is read the same way, so {@code Σ 3·q} is {@code 3·Σ q} and a total of what
     * stands at a field is that field's total, whichever way it was spelled.
     *
     * <p>A group whose elements' numbers this has no value for added up is left as it was, and so is
     * one whose sum names no field: a total of a constant is a number of how many elements there
     * are, which is not a total of any of them.
     */
    public static LinearForm<NumericTerm> addedUp(LinearForm<NumericTerm> form, InputDomain inputs,
                                                  RuleReadingSource source) {
        Map<Run, List<Part>> runs = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            Part part = each.getKey() instanceof NumericTerm.TakenOver over
                    ? partOf(over, each.getValue(), inputs, source) : null;
            if (part != null) {
                runs.computeIfAbsent(part.run(), _ -> new ArrayList<>()).add(part);
            }
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>(form.coefs());
        boolean merged = false;
        for (Map.Entry<Run, List<Part>> group : runs.entrySet()) {
            List<Part> parts = group.getValue();
            Weighed total = oneTotal(group.getKey(), parts, inputs, source);
            if (total == null || (parts.size() == 1 && total.term().equals(parts.getFirst().term())
                    && total.weight().equals(form.coefs().get(parts.getFirst().term())))) {
                continue;
            }
            parts.forEach(part -> coefs.remove(part.term()));
            ExactRatio had = coefs.get(total.term());
            ExactRatio weight = had == null ? total.weight() : had.plus(total.weight()).orNull();
            if (weight == null) {
                return form;
            }
            coefs.put(total.term(), weight);
            coefs.values().removeIf(ExactRatio::isZero);
            merged = true;
        }
        return merged ? new LinearForm<>(form.constant(), coefs) : form;
    }

    /** A total at the weight it stands in a form at. */
    private record Weighed(NumericTerm.TakenOver term, ExactRatio weight) {}

    /**
     * Where a total is taken: by which operation, over which elements, and in which order where
     * what each element comes to turns on it.
     */
    private record Run(ValueName.Stdlib operation, TermPath elements,
                       RunSource.TraversalOrder order) {

        Run {
            Objects.requireNonNull(operation, "a total is taken by an operation");
            Objects.requireNonNull(elements, "over some elements");
        }
    }

    /**
     * One total of a form: the run it is over, what each element comes to weighed by the total's
     * coefficient, and what that number stands as.
     */
    private record Part(Run run, NumericTerm.TakenOver term, ElementValue weighed, Type each) {}

    /** {@code over} weighed by {@code weight} as a part of a total of its run, or null where it is
     *  no addition from nought over one container's elements. */
    private static Part partOf(NumericTerm.TakenOver over, ExactRatio weight, InputDomain inputs,
                               RuleReadingSource source) {
        Accumulation adds = DefaultBoundOperationFacts.get().accumulation(over.operation());
        if (adds == null || adds.combine() != Accumulation.Combine.ADD
                || adds.identity() != Accumulation.Identity.ZERO) {
            return null;
        }
        TermPath elements;
        ElementValue computed;
        Type each;
        RunSource.TraversalOrder order = null;
        switch (over.source()) {
            case RunSource.ComputedOccurrences run -> {
                elements = run.elements();
                computed = run.computation();
                each = run.each();
                order = run.order();
            }
            case RunSource.ProjectedOccurrences run -> {
                List<TermPath> containers = run.subjectPath().containersHoldingIt();
                elements = containers.size() == 1 ? containers.getFirst().element() : null;
                ElementProjection field = elements == null ? null
                        : ElementProjection.below(elements, run.subjectPath());
                computed = field == null ? null
                        : new ElementValue.Affine(LinearForm.atom(field));
                each = computed == null ? null : inputs.typeAt(run.subjectPath(), source);
            }
            case RunSource.FlattenedOccurrences _, RunSource.ReachableNodes _ -> {
                return null;
            }
        }
        // A choice is made for each element on its own, and a total of one is read through its
        // arms; what is added up here is a form or a sum of products, and a choice is left as it
        // was written.
        ElementValue weighed = computed == null || !holdsEverySum(each, source) ? null
                : ElementValue.times(computed, weight);
        return weighed == null || named(weighed) == null ? null
                : new Part(new Run(over.operation(), elements, order), over, weighed, each);
    }

    /**
     * Whether a total computed in {@code each} is the number the arithmetic says wherever it is
     * computed: where the type has no end its sums pass, so no total stops where another writing
     * of it would not.
     *
     * <p>A whole number stops at the ends of a long, and {@code Σ 2·n} stops where {@code n}'s
     * total passes half of one while {@code 2·Σ n} stops where that total passes all of one. The
     * two are one number only short of those ends, and a reading that took one for the other would
     * take the values between them as rows.
     */
    private static boolean holdsEverySum(Type each, RuleReadingSource source) {
        Carrier carrier = each == null ? null : Carrier.ofValue(each, source.declarations());
        return carrier != null && carrier.extent().low() == null
                && carrier.extent().high() == null;
    }

    /**
     * The one total {@code parts} come to over {@code run}, or null where their numbers stand as
     * different types, this holds no value of what each element comes to added up, or that value
     * names no field.
     *
     * <p>What every weight of each element's number shares is the total's weight and not part of
     * the number: {@code 10·Σc − 6·Σq} is {@code 2·Σ(5·c − 3·q)}. A form over totals steps by what
     * its coefficients share, and the one total has only its own coefficient to step by.
     */
    private static Weighed oneTotal(Run run, List<Part> parts, InputDomain inputs,
                                    RuleReadingSource source) {
        Type each = parts.getFirst().each();
        ElementValue sum = null;
        for (Part part : parts) {
            if (!part.each().equals(each)) {
                return null;
            }
            sum = sum == null ? part.weighed() : ElementValue.sumOf(sum, part.weighed());
            if (sum == null) {
                return null;
            }
        }
        LinearForm<String> named = sum == null ? null : named(sum);
        if (named == null || named.coefs().isEmpty()) {
            return null;
        }
        ExactRatio shared = sharedBy(named);
        ElementValue perElement = shared.equals(ExactRatio.ONE) ? sum
                : ExactRatio.ONE.dividedBy(shared) instanceof ExactAnswer.Held<ExactRatio>(var by)
                        ? ElementValue.times(sum, by) : null;
        if (perElement == null) {
            return null;
        }
        // A field's total where the field is what is added, as it stands: a closure that turns it
        // into another type answers another number, and is computed of the element.
        ElementProjection place = perElement.asAPlace();
        TermPath at = place == null ? null : place.from(run.elements());
        Type standing = at == null ? null : inputs.typeAt(at, source);
        RunSource over = standing != null
                && TypeOps.base(each, source.inners()).equals(TypeOps.base(standing,
                        source.inners()))
                ? RunSource.overTheOccurrencesAt(at)
                : RunSource.computedOverTheElementsAt(run.elements(), perElement, each,
                        run.order());
        NumericTerm.TakenOver total = over == null ? null
                : NumericTerm.TakenOver.of(run.operation(), over, each, source.inners(),
                        source.symbols());
        return total == null ? null : new Weighed(total, shared);
    }

    /**
     * {@code value} with its fields and products named, where it is a form or a sum of products —
     * or null where it is anything else, which is no part this adds up.
     */
    private static LinearForm<String> named(ElementValue value) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        ExactRatio constant;
        switch (value) {
            case ElementValue.Affine affine -> {
                affine.form().coefs().forEach((field, weight) ->
                        coefs.put(field.toString(), weight));
                constant = affine.form().constant();
            }
            case ElementValue.Multilinear products -> {
                products.form().coefs().forEach((product, weight) ->
                        coefs.put(product.toString(), weight));
                constant = products.form().constant();
            }
            case ElementValue.Choose _, ElementValue.ByPosition _, ElementValue.Indexed _,
                 ElementValue.OfItsCase _, ElementValue.SumOfChoices _ -> {
                return null;
            }
        }
        return new LinearForm<>(constant, coefs);
    }

    /**
     * What every weight of {@code form} and its constant are whole multiples of, signed so that
     * the weight first in the order of the names it weighs is positive once divided by it: a total
     * of minus a field is minus that field's total, whichever way it was written.
     */
    private static ExactRatio sharedBy(LinearForm<String> form) {
        List<ExactRatio> weights = new ArrayList<>(form.coefs().values());
        weights.add(form.constant());
        ExactRatio shared = AdditiveImage.divisorOf(weights);
        String first = form.coefs().keySet().stream().sorted().findFirst().orElseThrow();
        return form.coefs().get(first).signum() < 0 ? shared.negated() : shared;
    }
}
