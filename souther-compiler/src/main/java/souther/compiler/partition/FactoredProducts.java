package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A form with the product of two forms in it, brought to the one number it is when a factor of the
 * product stands in the form beside it: {@code g - g * r} is {@code g * (1 - r)}.
 *
 * <p>The numbers {@code g} and {@code g * r} share a place, so a row cannot be asked to hold them
 * at two values apart, and a relation read as over the two would be about values no row has. Over
 * the one product of the number alone and the form {@code 1 - r}, whose numbers are apart, it is
 * about values a row holds: the number at one value and the form at another.
 *
 * <p>This is the relation between numbers and nothing more. What a run works out is worked out as
 * it was written — the product, and then the difference — and which rows it gets past is told by
 * the operations of the comparison, over the numbers they were written over. A form brought to
 * another is the same number wherever the run answers, and answers nowhere it does not.
 */
final class FactoredProducts {

    private FactoredProducts() {
    }

    /**
     * {@code form} with every product in it that stands beside a factor of its own brought to the
     * one product; the same form where there is none.
     */
    static LinearForm<Quantity> of(LinearForm<Quantity> form) {
        if (form.coefs().keySet().stream().noneMatch(FactoredProducts::isAProduct)) {
            return form;
        }
        LinearForm<Quantity> now = asNumbers(form);
        for (boolean changed = true; changed; ) {
            LinearForm<Quantity> next = once(now);
            changed = next != null;
            now = changed ? next : now;
        }
        return now;
    }

    /** Whether {@code atom} is a product of two numbers: the only atoms this brings together. */
    private static boolean isAProduct(Quantity atom) {
        return atom instanceof Quantity.ProductOfTwo
                || atom instanceof DecisionAtom.OfTheInput(NumericTerm.ProductOf _);
    }

    /**
     * {@code form} with a product of two positions in it, where it stands beside another number,
     * held as the number of its own it is: a line is drawn on a product against a written
     * number and on nothing else, and a product beside other numbers relates the numbers of
     * both.
     */
    private static LinearForm<Quantity> asNumbers(LinearForm<Quantity> form) {
        if (form.coefs().size() < 2) {
            return form;
        }
        List<LinearForm<Quantity>> parts = new ArrayList<>();
        parts.add(LinearForm.constant(form.constant()));
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getKey() instanceof Quantity.ProductOfTwo two
                    && NumericTerm.ProductOf.signed(LinearForm.atom(two.one()),
                            LinearForm.atom(two.other()))
                    instanceof NumericTerm.ProductOf.Signed made
                    && each.getValue().times(made.sign())
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio weight)) {
                parts.add(LinearForm.weighing(new DecisionAtom.OfTheInput(made.product()), weight));
            } else {
                parts.add(LinearForm.weighing(each.getKey(), each.getValue()));
            }
        }
        // Two writings of one product are one atom with the weights added, and a sum the exact
        // arithmetic cannot hold is no reason to drop the atom: the form is left as it was.
        return LinearForm.sum(parts) instanceof ExactAnswer.Held<LinearForm<Quantity>>(
                LinearForm<Quantity> together) ? together : form;
    }

    /** One product brought together with the factor beside it, or null where there is none. */
    private static LinearForm<Quantity> once(LinearForm<Quantity> form) {
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof DecisionAtom.OfTheInput(
                    NumericTerm.ProductOf product))) {
                continue;
            }
            for (int at = 0; at < 2; at++) {
                NumericTerm alone = numberAlone(product.factors().get(at));
                if (alone == null) {
                    continue;
                }
                Quantity beside = new DecisionAtom.OfTheInput(alone);
                ExactRatio weighed = form.coefs().get(beside);
                if (weighed == null) {
                    continue;
                }
                LinearForm<Quantity> together = together(form, each.getKey(), each.getValue(),
                        alone, product.factors().get(1 - at), beside, weighed);
                if (together != null) {
                    return together;
                }
            }
        }
        return null;
    }

    /** The one number a form is, weighed one with no constant — or null where it is more. */
    private static NumericTerm numberAlone(LinearForm<NumericTerm> factor) {
        return factor.coefs().size() == 1 && factor.constant().isZero()
                && ExactRatio.ONE.equals(factor.coefs().values().iterator().next())
                ? factor.coefs().keySet().iterator().next() : null;
    }

    /**
     * {@code form}, the product at {@code made} (weighed {@code ofIt}) and the number {@code alone}
     * at {@code beside} (weighed {@code weighed}) put together: {@code alone * (weighed + ofIt *
     * other)}. Null where the numbers of the form it comes to are not apart, or exact arithmetic
     * cannot hold them.
     */
    private static LinearForm<Quantity> together(LinearForm<Quantity> form, Quantity made,
                                                 ExactRatio ofIt, NumericTerm alone,
                                                 LinearForm<NumericTerm> other, Quantity beside,
                                                 ExactRatio weighed) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : other.coefs().entrySet()) {
            ExactRatio scaled = ofIt.times(each.getValue()).orNull();
            if (scaled == null) {
                return null;
            }
            coefs.put(each.getKey(), scaled);
        }
        ExactRatio constant = ofIt.times(other.constant()).flatMap(weighed::plus).orNull();
        NumericTerm.ProductOf.Signed product = constant == null ? null
                : NumericTerm.ProductOf.signed(LinearForm.atom(alone),
                        new LinearForm<>(constant, coefs));
        if (product == null) {
            return null;
        }
        List<LinearForm<Quantity>> parts = new ArrayList<>();
        parts.add(LinearForm.constant(form.constant()));
        form.coefs().forEach((atom, weight) -> {
            if (!atom.equals(made) && !atom.equals(beside)) {
                parts.add(LinearForm.weighing(atom, weight));
            }
        });
        parts.add(LinearForm.weighing(new DecisionAtom.OfTheInput(product.product()),
                product.sign()));
        // A form the weights of which cannot be added is not brought together.
        return LinearForm.sum(parts) instanceof ExactAnswer.Held<LinearForm<Quantity>>(
                LinearForm<Quantity> together) ? together : null;
    }
}
