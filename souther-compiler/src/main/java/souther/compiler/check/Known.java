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
record Known(NumericDomain<Term> numbers, PredicateFacts facts, List<Quantified> quantified,
                     Set<Term> spoken, Unguarded unguarded) {

    /** What holds of the values here whatever the path did — what a type guarantees of a value and
     * what a name was given. It carries no quantifiers and no spoken terms: those decide which
     * clauses are read at all, and both readings are asked about the same clauses. */
    record Unguarded(NumericDomain<Term> numbers, PredicateFacts facts) {

        Unguarded taking(LinearForm<Term> f, Rel rel, Map<Term, Granularity> kinds) {
            return new Unguarded(numbers.assume(f, rel, kinds), facts);
        }

        Unguarded taking(Term key, boolean positive) {
            return new Unguarded(numbers, facts.assume(key, positive));
        }
    }

    /** How far a fact reaches: a value's type and a name's binding say something wherever that value
     * is named, and a condition says it only on the path it guards. */
    enum Held { OF_THE_VALUE, ON_THE_PATH }

    static Known top() {
        return new Known(NumericDomain.top(), PredicateFacts.none(), List.of(), Set.of(),
                new Unguarded(NumericDomain.top(), PredicateFacts.none()));
    }

    /** This, with {@code f rel 0} taken as holding as far as {@code held} reaches. */
    Known taking(LinearForm<Term> f, Rel rel, Held held, Map<Term, Granularity> kinds) {
        return new Known(numbers.assume(f, rel, kinds), facts, quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(f, rel, kinds) : unguarded);
    }

    /** This, with the predicate {@code key} taken as holding — or as failing, where {@code positive}
     * is false — as far as {@code held} reaches. */
    Known taking(Term key, boolean positive, Held held) {
        return new Known(numbers, facts.assume(key, positive), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(key, positive) : unguarded);
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
        return new Known(numbers, facts, quantified, all, unguarded);
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
        return new Known(numbers, facts, List.copyOf(all), spoken, unguarded);
    }
}
