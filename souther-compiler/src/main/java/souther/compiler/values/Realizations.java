package souther.compiler.values;

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
     * <p>Which limit refused is not here. What a caller has is a position that did not answer for
     * its own rules, and the two things that can be said about that — a machine larger than one may
     * be, and an allowance run down — are said of the position by whatever built it. Carried here,
     * the one that ran out on the plan this stopped at would stand for a group of plans, and for a
     * position that was given up on before this asked anything it would be a limit nothing here
     * ever reached.
     */
    record NotBuilt() implements Realizations {}
}
