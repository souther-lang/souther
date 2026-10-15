package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
     * {@code weight · a}, for a weight the caller has in hand.
     *
     * <p>Built and not multiplied: an atom is one of nothing else, so scaling it is naming the
     * weight, and there is no arithmetic in it for a number to have no representation in.
     */
    public static <A> LinearForm<A> weighing(A a, ExactRatio weight) {
        return weight.isZero() ? constant(ExactRatio.ZERO) : new LinearForm<>(ExactRatio.ZERO, Map.of(a, weight));
    }

    /**
     * {@code a - b}.
     *
     * <p>Built and not subtracted, for the reason {@link #weighing} gives: the weights are one and
     * minus one, and an atom against itself is nothing. No number is added to another, so this is
     * total where {@link #minus} answers.
     */
    public static <A> LinearForm<A> difference(A a, A b) {
        if (a.equals(b)) {
            return constant(ExactRatio.ZERO);
        }
        return new LinearForm<>(ExactRatio.ZERO, Map.of(a, ExactRatio.ONE, b, ExactRatio.ONE.negated()));
    }

    /**
     * {@code a + b}, built like {@link #difference}. An atom with itself is twice it.
     */
    public static <A> LinearForm<A> sumOfAtoms(A a, A b) {
        if (a.equals(b)) {
            return weighing(a, ExactRatio.of(2));
        }
        return new LinearForm<>(ExactRatio.ZERO, Map.of(a, ExactRatio.ONE, b, ExactRatio.ONE));
    }

    /**
     * {@code a - c}, for a constant the caller has in hand.
     *
     * <p>Built like {@link #weighing}: a form with nothing but an atom in it has nought for its
     * constant, and nought minus {@code c} is {@code c} negated, which no number is far enough
     * from.
     */
    public static <A> LinearForm<A> atomMinusConstant(A a, ExactRatio c) {
        return new LinearForm<>(c.negated(), Map.of(a, ExactRatio.ONE));
    }

    /**
     * The sum of {@code forms}, or which way the exact arithmetic could not hold it — the same
     * answer for the same forms in whatever order they are handed.
     *
     * <p>Every weight an atom has in any of them is added at once ({@link ExactRatio#sum}), and the
     * constants likewise. Added as a run of {@link #plus}, two weights of one atom far apart in
     * scale would fail where they met even where a third cancels one of them, so the answer would
     * turn on which form came first. Where the weights of several atoms cannot be held, more room
     * answers the sum only where it answers every one of them.
     */
    public static <A> ExactAnswer<LinearForm<A>> sum(List<LinearForm<A>> forms) {
        List<ExactRatio> constants = new ArrayList<>();
        Map<A, List<ExactRatio>> weights = new HashMap<>();
        for (LinearForm<A> each : forms) {
            constants.add(each.constant);
            each.coefs.forEach((atom, weight) ->
                    weights.computeIfAbsent(atom, _ -> new ArrayList<>()).add(weight));
        }
        Set<UnheldNumber> unheld = EnumSet.noneOf(UnheldNumber.class);
        ExactRatio constant = ExactRatio.ZERO;
        switch (ExactRatio.sum(constants)) {
            case ExactAnswer.Held<ExactRatio> held -> constant = held.value();
            case ExactAnswer.Unheld<ExactRatio> not -> unheld.add(not.why());
        }
        Map<A, ExactRatio> coefs = new HashMap<>();
        for (Map.Entry<A, List<ExactRatio>> each : weights.entrySet()) {
            switch (ExactRatio.sum(each.getValue())) {
                case ExactAnswer.Held<ExactRatio> held -> {
                    if (!held.value().isZero()) {
                        coefs.put(each.getKey(), held.value());
                    }
                }
                case ExactAnswer.Unheld<ExactRatio> not -> unheld.add(not.why());
            }
        }
        if (!unheld.isEmpty()) {
            return ExactAnswer.unheld(UnheldNumber.ofAll(unheld));
        }
        return ExactAnswer.held(new LinearForm<>(constant, coefs));
    }

    /**
     * The sum, or which way the exact arithmetic could not hold it.
     *
     * <p>A model's own decimals can put a constant or a coefficient of one side far enough apart in
     * scale from the other that the exact sum has no representation. That is an answer of this and
     * not an absence: a reader that has no word for it says so with {@link ExactAnswer#orNull}, which
     * reads as this being no form the reader can reason with, and a reader that has one (the
     * reading of a comparison) says which. Where every term named is a constant, that is this
     * compiler declining to fold one, and the model's own arithmetic aborts wherever it runs.
     */
    public ExactAnswer<LinearForm<A>> plus(LinearForm<A> o) {
        Map<A, ExactRatio> m = new HashMap<>(coefs);
        for (Map.Entry<A, ExactRatio> each : o.coefs.entrySet()) {
            ExactRatio mine = m.get(each.getKey());
            if (mine == null) {
                m.put(each.getKey(), each.getValue());
                continue;
            }
            switch (mine.plus(each.getValue())) {
                case ExactAnswer.Held<ExactRatio> held -> m.put(each.getKey(), held.value());
                case ExactAnswer.Unheld<ExactRatio> unheld -> {
                    return ExactAnswer.unheld(unheld.why());
                }
            }
        }
        return constant.plus(o.constant).flatMap(summed -> {
            m.values().removeIf(ExactRatio::isZero);
            return ExactAnswer.held(new LinearForm<>(summed, m));
        });
    }

    public LinearForm<A> negate() {
        Map<A, ExactRatio> m = new HashMap<>();
        coefs.forEach((k, v) -> m.put(k, v.negated()));
        return new LinearForm<>(constant.negated(), m);
    }

    /** The difference, or which way the exact arithmetic could not hold it — see {@link #plus},
     *  which a difference is the sum of the negation of. */
    public ExactAnswer<LinearForm<A>> minus(LinearForm<A> o) {
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
     * This form scaled by a constant {@code k} (a scalar multiply), or which way a number scaled has
     * no representation — the same answer {@link #plus} gives, for the same reason.
     */
    public ExactAnswer<LinearForm<A>> times(ExactRatio k) {
        if (k.isZero()) {
            return ExactAnswer.held(constant(ExactRatio.ZERO));
        }
        return scaledBy(coef -> coef.times(k), constant.times(k));
    }

    /**
     * This form over a constant {@code k}, each number divided by it and not multiplied by its
     * reciprocal — the reciprocal of a number at the least exponent has none, and its quotient by
     * itself is one. Or which way a number divided has no representation.
     *
     * @throws ArithmeticException where {@code k} is zero
     */
    public ExactAnswer<LinearForm<A>> dividedBy(ExactRatio k) {
        return scaledBy(coef -> coef.dividedBy(k), constant.dividedBy(k));
    }

    private ExactAnswer<LinearForm<A>> scaledBy(
            Function<ExactRatio, ExactAnswer<ExactRatio>> scale, ExactAnswer<ExactRatio> constantScaled) {
        Map<A, ExactRatio> scaled = new HashMap<>();
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            switch (scale.apply(each.getValue())) {
                case ExactAnswer.Held<ExactRatio> held -> scaled.put(each.getKey(), held.value());
                case ExactAnswer.Unheld<ExactRatio> unheld -> {
                    return ExactAnswer.unheld(unheld.why());
                }
            }
        }
        return constantScaled.flatMap(held -> ExactAnswer.held(new LinearForm<>(held, scaled)));
    }
}
