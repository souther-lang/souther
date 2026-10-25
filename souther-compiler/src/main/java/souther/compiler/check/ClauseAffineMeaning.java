package souther.compiler.check;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
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
        }
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
        }
    }
}
