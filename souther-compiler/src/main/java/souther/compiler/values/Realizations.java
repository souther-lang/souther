package souther.compiler.values;

import souther.compiler.regex.PatternPlan;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What several plans of one position come to, taken as one answer.
 *
 * <p>All of them or none of them. A caller here is about to publish what a position's rules leave
 * to readers that do not build anything, and the plans it hands over are what those readers were
 * promised — so an answer holding some of them would leave which rules a reader is told about
 * decided by which plan the allowance reached first. Two rules of one position, either of which is
 * affordable alone, would be published or not by the order they were walked in, and the order is
 * this compiler's rather than the model's.
 *
 * <p>So the position is the unit. Where every plan is built, what comes back is the set each of
 * them admits; where one is not, nothing is, and what comes back is which limit refused — a fact
 * about the position's allowance and not about whichever plan was in hand.
 */
public sealed interface Realizations {

    /** Every plan built, each with the set it admits. */
    record Exact(Map<AdmittedPlan, ValueSet> byPlan) implements Realizations {

        public Exact {
            byPlan = Collections.unmodifiableMap(new LinkedHashMap<>(byPlan));
        }

        /**
         * What {@code plan} admits.
         *
         * <p>Refused rather than answered with nothing where the plan is one this was not asked
         * for: a caller reading an answer it never asked to be built is one whose two lists have
         * come apart, and a null here would be published as a rule about which nothing is known.
         */
        public ValueSet of(AdmittedPlan plan) {
            ValueSet made = byPlan.get(plan);
            if (made == null) {
                throw new IllegalArgumentException("no answer was asked for: " + plan);
            }
            return made;
        }
    }

    /**
     * One of them ran past what the position may build, so none of them is an answer.
     *
     * <p>Which limit refused is here, and it is the group's. The plans are built as one answer out
     * of one allowance and the first refusal stops the rest, so what refused the plan it stopped at
     * is what refused the group — a machine larger than one may be, or the allowance run down. A
     * block given up on before this asked anything is refused at the limit it was given up on at,
     * which this allowance reached then.
     *
     * <p>Which figure of this compiler's that is, is not here: the same budget bounds different
     * questions, and the caller that asked for the group is the one that knows which question it
     * was.
     *
     * @param refused which limit of the allowance refused, of the budget it was made from
     */
    record NotBuilt(PatternPlan.Refused refused) implements Realizations {

        public NotBuilt {
            if (refused == null) {
                throw new IllegalArgumentException("a group that was not built was refused by a"
                        + " limit");
            }
        }
    }
}
