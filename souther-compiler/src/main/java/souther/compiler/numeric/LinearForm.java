package souther.compiler.numeric;

import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Function;

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
 * <p><b>In exact ratios and not in written decimals.</b> What an expression comes to is the value
 * the arithmetic puts there, and the arithmetic that composes a form is not closed over the numbers
 * a model writes: a quotient by a constant is affine and a third is no decimal. Held as one, the
 * coefficient would be rounded where it is made and every reader downstream would reason about the
 * rounded number instead. A constant a model wrote is embedded exactly on the way in
 * ({@link ExactRatio#of}), and turning one back into a value on a carrier is done where the carrier
 * is known.
 *
 * @param constant what the form comes to where every atom is nought
 * @param coefs    what each atom is multiplied by, with nought coefficients left out so that two
 *                 writings of one form are one value
 */
public record LinearForm<A>(ExactRatio constant, Map<A, ExactRatio> coefs) {

    public static <A> LinearForm<A> constant(ExactRatio c) {
        return new LinearForm<>(c, Map.of());
    }

    public static <A> LinearForm<A> atom(A a) {
        return new LinearForm<>(ExactRatio.ZERO, Map.of(a, ExactRatio.ONE));
    }

    /**
     * The sum, or {@code null} where the exact arithmetic could not hold it.
     *
     * <p>A model's own decimals can put a constant or a coefficient of one side far enough apart in
     * scale from the other that the exact sum has no representation. Answered {@code null} rather
     * than thrown, which is the word this whole file already uses for an expression that is not a
     * linear form — {@link check.Terms#add} passes it straight through, the same as it does for
     * either side not being one in the first place. Where every term named is a constant, that is
     * this compiler declining to fold one, and the model's own arithmetic aborts wherever it runs.
     */
    public LinearForm<A> plus(LinearForm<A> o) {
        Map<A, ExactRatio> m = new HashMap<>(coefs);
        boolean[] everyTermWasComposed = {true};
        o.coefs.forEach((k, v) -> m.merge(k, v, (a, b) -> {
            ExactAnswer<ExactRatio> sum = a.plus(b);
            if (sum instanceof ExactAnswer.Held<ExactRatio> held) {
                return held.value();
            }
            everyTermWasComposed[0] = false;
            return a;
        }));
        if (!everyTermWasComposed[0]) {
            return null;
        }
        ExactRatio summedConstant = constant.plus(o.constant).orNull();
        if (summedConstant == null) {
            return null;
        }
        m.values().removeIf(ExactRatio::isZero);
        return new LinearForm<>(summedConstant, m);
    }

    public LinearForm<A> negate() {
        Map<A, ExactRatio> m = new HashMap<>();
        coefs.forEach((k, v) -> m.put(k, v.negated()));
        return new LinearForm<>(constant.negated(), m);
    }

    /** The difference, or {@code null} where the exact arithmetic could not hold it — see
     *  {@link #plus}, which a difference is the sum of the negation of. */
    public LinearForm<A> minus(LinearForm<A> o) {
        return plus(o.negate());
    }

    /**
     * The form with its numbers spelled the way a reader is shown them.
     *
     * <p>Written out rather than left to the record, because this reaches a document: a decision
     * table names a condition by the form it compares. An exact ratio says the plain shape of the
     * number and a report wants the decimal wherever one is the number exactly, which is what
     * {@link ExactRatio#spelled} answers — a coefficient of four fifths reads {@code 0.8} in a
     * document that has always said {@code 0.8}.
     *
     * <p>In one order whichever order the form was built in. What this holds is a mapping, so a
     * form written {@code 6b + 3a} and one written {@code 3a + 6b} are one form — and a reader
     * shown them as they happen to be held would be shown two things about one value. Sorted by
     * the name of the position, for the reason {@link CanonicalForm#toString} sorts.
     */
    @Override
    public String toString() {
        Map<String, ExactRatio> named = new TreeMap<>();
        coefs.forEach((atom, coef) -> named.put(String.valueOf(atom), coef));
        StringBuilder out = new StringBuilder("LinearForm[constant=")
                .append(constant.spelled()).append(", coefs={");
        boolean first = true;
        for (Map.Entry<String, ExactRatio> each : named.entrySet()) {
            out.append(first ? "" : ", ").append(each.getKey()).append('=')
                    .append(each.getValue().spelled());
            first = false;
        }
        return out.append("}]").toString();
    }

    /**
     * This form scaled by a constant {@code k} (a scalar multiply), or {@code null} where a number
     * scaled has no representation — the same word {@link #plus} uses, for the same reason.
     */
    public LinearForm<A> times(ExactRatio k) {
        if (k.isZero()) {
            return constant(ExactRatio.ZERO);
        }
        return scaledBy(coef -> coef.times(k), constant.times(k));
    }

    /**
     * This form over a constant {@code k}, each number divided by it and not multiplied by its
     * reciprocal — the reciprocal of a number at the least exponent has none, and its quotient by
     * itself is one. {@code null} where a number divided has no representation.
     *
     * @throws ArithmeticException where {@code k} is zero
     */
    public LinearForm<A> dividedBy(ExactRatio k) {
        return scaledBy(coef -> coef.dividedBy(k), constant.dividedBy(k));
    }

    private LinearForm<A> scaledBy(Function<ExactRatio, ExactAnswer<ExactRatio>> scale,
                                   ExactAnswer<ExactRatio> constantScaled) {
        ExactRatio scaledConstant = constantScaled.orNull();
        if (scaledConstant == null) {
            return null;
        }
        Map<A, ExactRatio> scaled = new HashMap<>();
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            ExactRatio coef = scale.apply(each.getValue()).orNull();
            if (coef == null) {
                return null;
            }
            scaled.put(each.getKey(), coef);
        }
        return new LinearForm<>(scaledConstant, scaled);
    }
}
