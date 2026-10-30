package souther.compiler.check;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * A relation an operation guarantees of its answer where another relation holds: the remainder of
 * a floor division is not negative where the divisor is above nought.
 *
 * <p>Not an {@link NumericConstraint}. What the operation guarantees is the same statement
 * wherever it is read, but whether its condition holds is the reading's: the divisor is above
 * nought on one path and not on another, and a name given a constant is that constant wherever it
 * was written. So the pair is filed against the atom once ({@link AtomKnowledge}) and the
 * consequence is taken in by a reading that has the premise ({@link DerivedNumericFacts#readingOf}).
 * Taken in whatever the path, it would be a fact about a divisor that could be either side of
 * nought.
 *
 * @param premise     what has to hold of the arguments, as a relation to nought
 * @param consequence what then holds of the answer
 */
record ConditionalConstraint(NumericConstraint premise, NumericConstraint consequence) {

    /** The atoms either relation is written over. */
    Set<FactSubject> atoms() {
        Set<FactSubject> out = new LinkedHashSet<>(premise.atoms());
        out.addAll(consequence.atoms());
        return out;
    }
}
