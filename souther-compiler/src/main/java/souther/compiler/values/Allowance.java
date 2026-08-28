package souther.compiler.values;

import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternPlan;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What each position of one answer is allowed to build, and everything that builds under it.
 *
 * <p>Held per position, because a position is what an answer is about: every rule reaching one pays
 * into the machine it finally admits, whether the rules are two halves of a clause or two clauses of
 * two declarations. One allowance for the whole reading instead would let a complicated rule at one
 * position spend what a plain one at another was going to need, and which of them went unanswered
 * would turn on the order they were written in.
 *
 * <p><b>Two things build, and they are the same allowance.</b> Turning one rule into the set it
 * names is one — a pattern is a machine — and putting a position's sets together is the other. A
 * position that spent its allowance on one pattern has that much less for the meet, which is what
 * "what this position finally admits" costs and is the only number that means anything.
 *
 * <p>They are not the same failure. A rule that could not be turned into a set at all is about that
 * rule and names it; a composition that could not be built is about the answer and names none. So
 * the first is answered here, before anything reaches a plan, and the second is answered where the
 * plan is worked out ({@link Realizer}).
 *
 * @param <A> what a position is called
 */
public final class Allowance<A> {

    private final PatternPlan.Budget budget;
    private final Map<A, Meter> meters = new LinkedHashMap<>();
    private final Map<A, Realizer> realizers = new LinkedHashMap<>();

    private Allowance(PatternPlan.Budget budget) {
        this.budget = budget;
    }

    /** A fresh allowance for every position of one answer. */
    public static <A> Allowance<A> of(PatternPlan.Budget budget) {
        if (budget == null) {
            throw new IllegalArgumentException("an allowance allows something");
        }
        return new Allowance<>(budget);
    }

    /** The same, at what one answer of a declaration is allowed. */
    public static <A> Allowance<A> ofAdmittedValues() {
        return of(PatternPlan.Budget.OF_ADMITTED_VALUES);
    }

    /**
     * What works this position's descriptions out, and what it has left to do it with.
     *
     * <p>One per position and kept, so a plan worked out twice is worked out once — which is what
     * lets a caller ask early without the position paying twice, and what makes when it was asked
     * no part of what it cost.
     */
    public Realizer realizer(A atom) {
        return realizers.computeIfAbsent(atom, _ -> new Realizer(meter(atom)));
    }

    /**
     * The same for a set belonging to no position.
     *
     * <p>A reading holds one of those: what it guarantees at every position it holds no guarantee
     * for. It is not any position's, so it cannot be charged to one — put on the first position
     * that happened to be asked, it would take the allowance of a position whose own rules had not
     * been read yet.
     */
    public Realizer elsewhere() {
        if (nowhere == null) {
            nowhere = new Realizer(budget.meter());
        }
        return nowhere;
    }

    private Realizer nowhere;

    private Meter meter(A atom) {
        return meters.computeIfAbsent(atom, _ -> budget.meter());
    }
}
