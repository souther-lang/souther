package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A row that meets every statement of a way, found by trying numbers: that one exists is proved
 * by the numbers it is made of, which no projection of a region says. A region leaves a form a
 * range where it leaves one at all, and {@code 3 * (d - h) == 1} holds of no decimal however the
 * range is read.
 *
 * <p>Asked of statements that are all differences of numbers, which no assignment is better than
 * another for: the first number is nought and the others are whole numbers and halves near it. A
 * way no such assignment meets is not shown to hold a row, which is not that it holds none.
 */
final class AWitnessOfDifferences {

    /** More numbers than this are not tried: the assignments grow as a power of them. */
    private static final int MOST_NUMBERS = 4;

    /** Minus four to four, by halves. */
    private static final List<ExactRatio> VALUES = values();

    private AWitnessOfDifferences() {
    }

    /** Whether some assignment of numbers meets all of {@code statements}. */
    static boolean exists(List<TakenConstraint.Affine> statements) {
        Set<NumericTerm> terms = new LinkedHashSet<>();
        statements.forEach(each -> terms.addAll(each.form().coefs().keySet()));
        return !terms.isEmpty() && terms.size() <= MOST_NUMBERS
                && meeting(statements, List.copyOf(terms), new LinkedHashMap<>());
    }

    private static boolean meeting(List<TakenConstraint.Affine> statements,
                                   List<NumericTerm> terms, Map<NumericTerm, ExactRatio> at) {
        if (at.size() == terms.size()) {
            return statements.stream().allMatch(each -> holdsAt(each, at));
        }
        NumericTerm next = terms.get(at.size());
        for (ExactRatio value : at.isEmpty() ? List.of(ExactRatio.ZERO) : VALUES) {
            at.put(next, value);
            if (meeting(statements, terms, at)) {
                return true;
            }
            at.remove(next);
        }
        return false;
    }

    private static boolean holdsAt(TakenConstraint.Affine statement,
                                   Map<NumericTerm, ExactRatio> at) {
        ExactRatio sum = statement.form().constant();
        for (Map.Entry<NumericTerm, ExactRatio> each : statement.form().coefs().entrySet()) {
            ExactRatio weighed = each.getValue().times(at.get(each.getKey())).orNull();
            sum = weighed == null ? null : sum.plus(weighed).orNull();
            if (sum == null) {
                return false;
            }
        }
        return statement.rel().holds(sum.signum());
    }

    private static List<ExactRatio> values() {
        ExactRatio half = ExactRatio.ONE.dividedBy(ExactRatio.of(2)).orNull();
        List<ExactRatio> out = new ArrayList<>();
        for (int each = -8; each <= 8; each++) {
            out.add(ExactRatio.of(each).times(half).orNull());
        }
        return List.copyOf(out);
    }
}
