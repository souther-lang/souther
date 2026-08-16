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
record Known(ConstraintState constraints, List<Quantified> quantified,
                     Set<Term> spoken, Unguarded unguarded) {

    /** What holds of the values here whatever the path did — what a type guarantees of a value and
     * what a name was given. It carries no quantifiers and no spoken terms: those decide which
     * clauses are read at all, and both readings are asked about the same clauses. */
    record Unguarded(ConstraintState constraints) {

        Unguarded taking(LinearForm<Term> f, Rel rel, Map<Term, Granularity> kinds) {
            return new Unguarded(constraints.taking(f, rel, kinds));
        }

        Unguarded taking(Term key, boolean positive) {
            return new Unguarded(constraints.taking(key, positive));
        }

        NumericDomain<Term> numbers() {
            return constraints.numbers();
        }

        PredicateFacts facts() {
            return constraints.facts();
        }
    }

    /** The relations between numbers this state holds. Handed out because a bound is read off an
     * interval and off nothing else; whether anything satisfies the state at all is
     * {@link ConstraintState#isBottom} and is not assembled from this. */
    NumericDomain<Term> numbers() {
        return constraints.numbers();
    }

    /** The predicates this state has settled, read the same way and for the same reason. */
    PredicateFacts facts() {
        return constraints.facts();
    }

    /** How far a fact reaches: a value's type and a name's binding say something wherever that value
     * is named, and a condition says it only on the path it guards. */
    enum Held { OF_THE_VALUE, ON_THE_PATH }

    static Known top() {
        return new Known(ConstraintState.top(), List.of(), Set.of(),
                new Unguarded(ConstraintState.top()));
    }

    /** This, with {@code f rel 0} taken as holding as far as {@code held} reaches. */
    Known taking(LinearForm<Term> f, Rel rel, Held held, Map<Term, Granularity> kinds) {
        return new Known(constraints.taking(f, rel, kinds), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(f, rel, kinds) : unguarded);
    }

    /** This, with the predicate {@code key} taken as holding — or as failing, where {@code positive}
     * is false — as far as {@code held} reaches. */
    Known taking(Term key, boolean positive, Held held) {
        return new Known(constraints.taking(key, positive), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(key, positive) : unguarded);
    }

    /**
     * This, where the conditions on the path cannot all hold, so nothing here is reached.
     *
     * <p>Said as a contradiction in the numbers, which is how the domain already records that it
     * holds nothing. The reading that ignores the path is left as it was: it is the guards that
     * cannot all hold, not the values that fail, and a construction under them is one the program
     * never builds rather than one it builds wrongly.
     */
    Known reachingNothing() {
        return taking(LinearForm.constant(java.math.BigDecimal.ONE), Rel.LE, Held.ON_THE_PATH,
                Map.of());
    }

    /**
     * This, with each of {@code terms} recorded as one an assumption on this path named. It is
     * recorded where the assumption is made rather than searched for afterwards: what a guard
     * spoke about is known exactly then, and reading it back out of a domain would mean matching
     * key text, which is how a term that merely reads like another gets mistaken for it.
     */
    Known speaking(Collection<Term> terms) {
        if (terms.isEmpty()) {
            return this;
        }
        Set<Term> all = new HashSet<>(spoken);
        all.addAll(terms);
        return new Known(constraints, quantified, all, unguarded);
    }

    /** Whether an assumption on this path named {@code term}. */
    boolean speaksOf(Term term) {
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
