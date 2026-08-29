package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What holds where the walk stands: numeric relations, predicates known to hold or to fail, relations
 * known of every element of a container, and the terms an assumption named — which is what makes a
 * computed value one a clause may be read against. Threaded functionally through the walk, as the
 * domain alone once was.
 *
 * <p>Beside it is {@link Unguarded}, the same reading with nothing a condition on the path settled.
 * Both are refined by the same acts and differ only in which acts reach both, so a clause that comes
 * out refuted can be asked which of the two refuted it. That is what a violation is explained by: one
 * the unguarded reading already refutes holds wherever the construction stands, and one only the full
 * reading refutes took something more than the values to settle. Which something is not recorded, so
 * it is not claimed either.
 */
record Known(ConstraintState<FactSubject> constraints, List<Quantified> quantified,
                     Set<FactSubject> spoken, Unguarded unguarded) {

    /** What holds of the values here whatever the path did — what a type guarantees of a value and
     * what a name was given. It carries no quantifiers and no spoken terms: those decide which
     * clauses are read at all, and both readings are asked about the same clauses. */
    record Unguarded(ConstraintState<FactSubject> constraints) {

        Unguarded taking(LinearForm<FactSubject> f, Rel rel, Map<FactSubject, Granularity> kinds) {
            return new Unguarded(constraints.taking(f, rel, kinds));
        }

        Unguarded taking(FactSubject key, boolean positive) {
            return new Unguarded(constraints.taking(key, positive));
        }

        NumericDomain<FactSubject> numbers() {
            return constraints.numbers();
        }

        PredicateFacts<FactSubject> facts() {
            return constraints.facts();
        }
    }

    /** The relations between numbers this state holds. Handed out for what only an interval can
     * answer — a bound is read off one and off nothing else — and for nothing about the state as a
     * whole. Whether a value exists and whether a path is reached are both
     * {@link ConstraintState#isBottom}, and neither is assembled from this. */
    NumericDomain<FactSubject> numbers() {
        return constraints.numbers();
    }

    /** The predicates this state has settled, read the same way and for the same reason. */
    PredicateFacts<FactSubject> facts() {
        return constraints.facts();
    }

    /**
     * Whether the conditions that hold here cannot all hold, so nothing stands where this does.
     *
     * <p>Asked of the whole state ({@link ConstraintState#isBottom}) and not of a domain, because a
     * clause reaches whatever domain has a word for it: guards that settle a predicate both ways
     * leave the predicates contradictory and every number untouched, and a reader that asked the
     * numbers would walk that path and report the construction standing on it. That is a report
     * about a value the program never builds.
     *
     * <p>No flag of its own, for the same reason. A second record of the answer is a second thing to
     * keep in step, and the first domain added without touching it would put the two out of
     * agreement — which is the shape this question already came apart along once.
     */
    boolean reachesNothing() {
        return constraints.isBottom();
    }

    /** How far a fact reaches: a value's type and a name's binding say something wherever that value
     * is named, and a condition says it only on the path it guards. */
    enum Held { OF_THE_VALUE, ON_THE_PATH }

    static Known top() {
        return new Known(ConstraintState.<FactSubject>top(), List.of(), Set.of(),
                new Unguarded(ConstraintState.<FactSubject>top()));
    }

    /** This, with {@code f rel 0} taken as holding as far as {@code held} reaches. */
    Known taking(LinearForm<FactSubject> f, Rel rel, Held held, Map<FactSubject, Granularity> kinds) {
        return new Known(constraints.taking(f, rel, kinds), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(f, rel, kinds) : unguarded);
    }

    /** This, with the predicate {@code key} taken as holding — or as failing, where {@code positive}
     * is false — as far as {@code held} reaches. */
    Known taking(FactSubject key, boolean positive, Held held) {
        return new Known(constraints.taking(key, positive), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(key, positive) : unguarded);
    }

    /**
     * This, where the conditions on the path cannot all hold, so nothing here is reached.
     *
     * <p>Said of the state and not lodged in a domain ({@link ConstraintState#shownToHoldNothing}):
     * what shows it is a reading of the cases an operation is defined in, and no interval and no
     * predicate holds that argument. The reading that ignores the path is left as it was — it is the
     * guards that cannot all hold, not the values that fail, and a construction under them is one
     * the program never builds rather than one it builds wrongly.
     */
    Known reachingNothing() {
        return new Known(constraints.shownToHoldNothing(), quantified, spoken, unguarded);
    }

    /**
     * This, with each of {@code terms} recorded as one an assumption on this path named. It is
     * recorded where the assumption is made rather than searched for afterwards: what a guard
     * spoke about is known exactly then, and reading it back out of a domain would mean matching
     * key text, which is how a term that merely reads like another gets mistaken for it.
     */
    Known speaking(Collection<FactSubject> terms) {
        if (terms.isEmpty()) {
            return this;
        }
        Set<FactSubject> all = new HashSet<>(spoken);
        all.addAll(terms);
        return new Known(constraints, quantified, all, unguarded);
    }

    /** Whether an assumption on this path named {@code term}. */
    boolean speaksOf(FactSubject term) {
        return spoken.contains(term);
    }

    Known and(List<Quantified> more) {
        if (more.isEmpty()) {
            return this;
        }
        List<Quantified> all = new ArrayList<>(quantified);
        all.addAll(more);
        return new Known(constraints, List.copyOf(all), spoken, unguarded);
    }
}
