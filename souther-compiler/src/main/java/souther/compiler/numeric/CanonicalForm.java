package souther.compiler.numeric;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * A weighted sum of positions, written the one way every rule that states it is written.
 *
 * <p>What a rule says and not how it was typed. {@code 300 * straw + 600 * choco <= 4800} and
 * {@code straw + 2 * choco <= 16} are one rule; so are {@code 3a - 3b <= 1} and
 * {@code a - b <= 1/3}, and so are {@code a - b <= 2} and {@code b - a >= -2}. Held as written, they
 * were four rules to anything keyed on the coefficients — which is how a difference stated with
 * coefficients of two fell outside the shape that holds differences, leaving one of its positions
 * with no bound at all while the same rule written with ones bounded it.
 *
 * <p>So the coefficients are divided through by what they all share, which leaves them whole numbers
 * with nothing left in common, and what they were divided by goes to the threshold. Scaling is the
 * only freedom there is: negating turns the comparison around, so it belongs to reading the
 * comparison rather than to writing the form.
 *
 * <p>No constant. A constant belongs to the threshold the form is compared against — left in, the
 * values {@code 2 * a} takes would be the even numbers under one spelling and the odd ones shifted
 * by nine under another, which is the same thing {@link souther.compiler.partition.BorderQuantity}
 * says of a quantity.
 *
 * <p>Compared by its map, so two forms that say one thing are one key. That is what makes asserting
 * a rule twice the same as asserting it once, and it is the property everything downstream leans on
 * when it stops caring what order the rules arrived in.
 */
public record CanonicalForm<A>(Map<A, Rational> coefs) {

    public CanonicalForm {
        if (coefs == null || coefs.isEmpty()) {
            throw new IllegalArgumentException("a form names at least one position");
        }
        coefs = Map.copyOf(coefs);
        for (Map.Entry<A, Rational> each : coefs.entrySet()) {
            if (each.getValue().isZero()) {
                throw new IllegalArgumentException(
                        "a position with a zero coefficient is one the form does not name: "
                                + each.getKey());
            }
        }
    }

    /**
     * The form {@code coefs} states, scaled so that what it is multiplied by is the smallest it can
     * be, with the scaling handed back to apply to whatever the form is compared against.
     *
     * <p>Positions with a zero coefficient are dropped: a rule mentioning a position it does not
     * weigh says nothing about it, and keeping it would make two writings of one rule two rules.
     *
     * @return the form and the factor the threshold has to be divided by to go with it, or
     *         {@code null} where nothing is left — a form that weighs no position is a constant, and
     *         what a constant comparison settles is not a constraint about anybody
     */
    public static <A> Scaled<A> of(Map<A, Rational> coefs) {
        Map<A, Rational> weighed = new LinkedHashMap<>();
        coefs.forEach((atom, coef) -> {
            if (!coef.isZero()) {
                weighed.put(atom, coef);
            }
        });
        if (weighed.isEmpty()) {
            return null;
        }
        Rational shared = AdditiveImage.divisorOf(weighed.values());
        Map<A, Rational> primitive = new LinkedHashMap<>();
        weighed.forEach((atom, coef) -> primitive.put(atom, coef.dividedBy(shared)));
        return new Scaled<>(new CanonicalForm<>(primitive), shared);
    }

    /**
     * A canonical form and what the writing of it was multiplied by.
     *
     * @param by never zero and always positive, so dividing a threshold by it leaves which side of
     *           the threshold a value falls on
     */
    public record Scaled<A>(CanonicalForm<A> form, Rational by) {}

    /**
     * The values this form can add up to, over positions spaced as {@code spacing} says.
     *
     * <p>Asked of {@link AdditiveImage} rather than answered here. The coefficients being whole and
     * sharing nothing does settle it — every whole number where the positions step, every finite
     * decimal where they fill — but that is a conclusion about this arrangement rather than a rule
     * of it, and the day a form arrives here weighed some other way it is the general answer that
     * has to be right.
     */
    public AdditiveImage imageOver(Function<A, Granularity> spacing) {
        return AdditiveImage.of(coefs, spacing);
    }

    /**
     * The same form over positions called something else.
     *
     * <p>A renaming and nothing more. What a form says is a relation between the positions it
     * weighs, and calling them by the names of another vocabulary leaves that relation where it
     * was — so this is how a rule read of one value is asked about as a rule of the thing that
     * holds it, rather than being re-derived there.
     *
     * <p>Still canonical, because canonical is a fact about the coefficients and this touches none
     * of them.
     *
     * <p><b>The naming has to be one-to-one.</b> Two positions called by one name is not a wider
     * reading of this rule, it is a different rule: the coefficients would be added together and
     * {@code a - b <= 0}, which says one is no larger than the other, would come back weighing
     * nothing at all. Refused rather than merged, for the same reason a second spacing under one
     * key is refused — the naming and the form disagree about how many positions there are, and
     * neither of them is this record's to correct.
     */
    public <B> CanonicalForm<B> over(Function<A, B> naming) {
        Map<B, Rational> out = new LinkedHashMap<>();
        coefs.forEach((atom, coef) -> {
            B called = naming.apply(atom);
            if (called == null) {
                throw new IllegalArgumentException(
                        "a position with no name in the vocabulary asked for is one this form"
                                + " cannot be written in: " + atom);
            }
            if (out.put(called, coef) != null) {
                throw new IllegalArgumentException(
                        "two positions of this form are called `" + called + "`, so the form over"
                                + " those names weighs fewer positions than this one does");
            }
        });
        return new CanonicalForm<>(out);
    }

    /** This form with every coefficient turned around, which is what reading a comparison the other
     *  way produces. Still canonical: negating leaves what the coefficients share. */
    public CanonicalForm<A> negated() {
        Map<A, Rational> out = new LinkedHashMap<>();
        coefs.forEach((atom, coef) -> out.put(atom, coef.negated()));
        return new CanonicalForm<>(out);
    }

    /**
     * In an order that does not move between runs.
     *
     * <p>The map this holds is compared by its contents and iterated in whatever order it was built
     * with — which is the right way round for deciding that two writings are one rule, and the wrong
     * way round for writing one out. Sorted by the name of the position for the same reason
     * {@link souther.compiler.partition.QuantityKey#key} sorts: a form written {@code 6b + 3a} and
     * one written {@code 3a + 6b} are one form and should read as one.
     */
    @Override
    public String toString() {
        java.util.Map<String, Rational> named = new java.util.TreeMap<>();
        coefs.forEach((atom, coef) -> named.put(String.valueOf(atom), coef));
        StringBuilder out = new StringBuilder();
        named.forEach((atom, coef) -> {
            if (!out.isEmpty()) {
                out.append(" + ");
            }
            out.append(coef).append("·").append(atom);
        });
        return out.toString();
    }
}
