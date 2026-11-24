package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Whether a clause states exactly a conjunction of order comparisons of one sum of the places it
 * reads, and which.
 *
 * <p><b>Exact is the whole clause.</b> The clause holds of a value if and only if every comparison
 * of {@link Exact} holds of it, so nothing besides them ties the places the clause reads to one
 * another. A reading that collected the comparisons it could make of a clause and left the rest
 * would state something every clause containing them implies, which is a bound and not what the
 * clause says: {@code a + b >= 100 && opaque(a, b)} implies {@code a + b >= 100} and holds back
 * more.
 *
 * <p>So a clause stating anything this has no word for is {@link Unread}, which is not that the
 * clause states nothing. The places are named as the rules of the value name them
 * ({@link RuleKey}), and the numbers are whole ones.
 */
public sealed interface ClauseAffineMeaning {

    /**
     * The clause holds exactly where all of {@code conjuncts} do, and they weigh the same places
     * alike: each is one form up to a factor.
     */
    record Exact(List<Comparison> conjuncts) implements ClauseAffineMeaning {

        public Exact {
            if (conjuncts.isEmpty()) {
                throw new IllegalArgumentException("a clause that states something is some comparisons");
            }
            conjuncts = List.copyOf(conjuncts);
            if (!weighSameAlike(conjuncts)) {
                throw new IllegalArgumentException(
                        "the comparisons of an exact clause are of one form: " + conjuncts);
            }
        }
    }

    /**
     * The meaning of a clause that comes to {@code conjuncts} exactly: {@link Exact} where they
     * are of one form, and {@link Unread} where they are not, which a reader of one form cannot
     * take them for.
     */
    static ClauseAffineMeaning ofComparisons(List<Comparison> conjuncts) {
        return conjuncts.isEmpty() || !weighSameAlike(conjuncts) ? UNREAD : new Exact(conjuncts);
    }

    /** Whether every comparison weighs the same places as the first, each by the same number of
     *  times as the others: they are the one form up to a factor. */
    private static boolean weighSameAlike(List<Comparison> conjuncts) {
        Map<RuleKey, ExactRatio> first = conjuncts.getFirst().form().coefs();
        if (first.isEmpty() || first.values().stream().anyMatch(ExactRatio::isZero)) {
            return false;
        }
        for (Comparison each : conjuncts) {
            Map<RuleKey, ExactRatio> other = each.form().coefs();
            if (!first.keySet().equals(other.keySet())) {
                return false;
            }
            ExactRatio factor = null;
            for (Map.Entry<RuleKey, ExactRatio> weighed : first.entrySet()) {
                ExactRatio here = other.get(weighed.getKey()).dividedBy(weighed.getValue()).orNull();
                if (here == null || here.isZero()
                        || (factor != null && factor.compareTo(here) != 0)) {
                    return false;
                }
                factor = here;
            }
        }
        return true;
    }

    /** What the clause states is more than this can say, or something it cannot. */
    record Unread() implements ClauseAffineMeaning {}

    /** The one answer for a clause this has no form for. */
    ClauseAffineMeaning UNREAD = new Unread();

    /**
     * {@code form} standing to nought as {@code rel} says: the sum of the places with its constant.
     *
     * <p>The sides are already taken to one side, so {@code a + b >= 100} and
     * {@code b + a - 100 >= 0} are the one comparison.
     */
    record Comparison(LinearForm<RuleKey> form, Rel rel) {

        public Comparison {
            Objects.requireNonNull(form, "a comparison is of a sum");
            Objects.requireNonNull(rel, "a comparison stands one way to nought");
            // A published fact is a value: the places a caller weighed are copied in the order it
            // gave them and cannot be changed through the form this hands out, so what the exact
            // clause was checked to be at construction is what it is afterwards.
            form = new LinearForm<>(form.constant(),
                    Collections.unmodifiableMap(new LinkedHashMap<>(form.coefs())));
        }
    }
}
