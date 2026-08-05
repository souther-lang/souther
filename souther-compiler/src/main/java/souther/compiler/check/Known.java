package souther.compiler.check;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/** What the guards have settled on the current path: numeric relations, predicates known to hold
 * or to fail, and relations known of every element of a container. Threaded functionally through
 * the walk, as the domain alone once was. */
record Known(NumericDomain numbers, PredicateFacts facts, List<Quantified> quantified,
                     Set<String> spoken) {

    static Known top() {
        return new Known(NumericDomain.top(), PredicateFacts.none(), List.of(), Set.of());
    }

    Known with(NumericDomain n) {
        return new Known(n, facts, quantified, spoken);
    }

    Known with(PredicateFacts f) {
        return new Known(numbers, f, quantified, spoken);
    }

    /**
     * This, with each of {@code terms} recorded as one an assumption on this path named. It is
     * recorded where the assumption is made rather than searched for afterwards: what a guard
     * spoke about is known exactly then, and reading it back out of a domain would mean matching
     * key text, which is how a term that merely reads like another gets mistaken for it.
     */
    Known speaking(Collection<String> terms) {
        if (terms.isEmpty()) {
            return this;
        }
        Set<String> all = new HashSet<>(spoken);
        all.addAll(terms);
        return new Known(numbers, facts, quantified, all);
    }

    /** Whether an assumption on this path named {@code term}. */
    boolean speaksOf(String term) {
        return spoken.contains(term);
    }

    Known and(List<Quantified> more) {
        if (more.isEmpty()) {
            return this;
        }
        List<Quantified> all = new ArrayList<>(quantified);
        all.addAll(more);
        return new Known(numbers, facts, List.copyOf(all), spoken);
    }
}
