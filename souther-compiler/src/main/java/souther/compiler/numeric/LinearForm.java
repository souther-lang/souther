package souther.compiler.numeric;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;

/**
 * An affine form {@code const + Σ coef·atom} over whatever a caller names its atoms by.
 *
 * <p><b>What an expression came to, and nothing about what is left at it.</b> A range, a
 * granularity, what a rule entails — those are a domain's answers about the numbers a form is over,
 * and none of them is here. What is here is the form itself and the arithmetic that composes one:
 * two forms added, negated, subtracted, scaled. So a reader that only has to know what an
 * expression is can have one without holding anything that answers about it.
 *
 * <p>Which is why it is its own type and not {@link NumericDomain}'s. It was declared inside that
 * one, and a reader wanting the canonical form of a clause had to name the domain to get it — so a
 * classification asking what a rule states could not be told apart, by anything a check could read,
 * from one asking what the rules leave. The domain is a consumer of this like every other.
 *
 * @param constant what the form comes to where every atom is nought
 * @param coefs    what each atom is multiplied by, with nought coefficients left out so that two
 *                 writings of one form are one value
 */
public record LinearForm<A>(BigDecimal constant, Map<A, BigDecimal> coefs) {

    public static <A> LinearForm<A> constant(BigDecimal c) {
        return new LinearForm<>(c, Map.of());
    }

    public static <A> LinearForm<A> atom(A a) {
        return new LinearForm<>(BigDecimal.ZERO, Map.of(a, BigDecimal.ONE));
    }

    public LinearForm<A> plus(LinearForm<A> o) {
        Map<A, BigDecimal> m = new HashMap<>(coefs);
        o.coefs.forEach((k, v) -> m.merge(k, v, BigDecimal::add));
        m.values().removeIf(v -> v.signum() == 0);
        return new LinearForm<>(constant.add(o.constant), m);
    }

    public LinearForm<A> negate() {
        Map<A, BigDecimal> m = new HashMap<>();
        coefs.forEach((k, v) -> m.put(k, v.negate()));
        return new LinearForm<>(constant.negate(), m);
    }

    public LinearForm<A> minus(LinearForm<A> o) {
        return plus(o.negate());
    }

    /** This form scaled by a constant {@code k} (a scalar multiply). */
    public LinearForm<A> times(BigDecimal k) {
        if (k.signum() == 0) {
            return constant(BigDecimal.ZERO);
        }
        Map<A, BigDecimal> m = new HashMap<>();
        coefs.forEach((key, v) -> m.put(key, v.multiply(k)));
        return new LinearForm<>(constant.multiply(k), m);
    }
}
