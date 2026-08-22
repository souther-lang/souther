package souther.compiler.coverage;

import java.util.LinkedHashSet;

/**
 * Who owns the rule a fork decides by.
 *
 * <p>Read off the declaration ({@link DecisionSources}). What a caller does with it is decide what
 * one obligation is: a fork deciding for itself is one obligation however many bodies it is spliced
 * into, and a fork deciding by a rule the caller handed in is one per rule handed in.
 *
 * <p>Two answers and no third. A declaration either names a function parameter its fork applies or
 * it does not, and both are things this reading establishes. Whether an occurrence of a supplied
 * fork could be told which rule it was handed is the other half of the question and is answered
 * where the occurrence is ({@link DecidedBy}).
 */
public sealed interface DecisionSource {

    /** The declaration decides. Its arguments are what its rule reads and not the rule. */
    record Own() implements DecisionSource {}

    /**
     * The caller decides, through the function parameters named {@code parameters}.
     *
     * <p>More than one, because one fork can be decided by more than one: {@code if p(x) && q(x)}
     * is a fork neither predicate settles on its own, and a reader taking the first of them would
     * call two call sites alike that agree about {@code p} and differ about {@code q}.
     *
     * <p>Named rather than numbered because the name is what the rule handed in is expanded under
     * ({@code HelperInliner.suppliedAs}), and that is how an occurrence says which rule it was
     * handed. A slot would have to be turned into the name to ask, which is the same lookup with a
     * step in front of it that can be got wrong.
     */
    record Supplied(java.util.SequencedSet<String> parameters) implements DecisionSource {

        public Supplied {
            parameters = java.util.Collections.unmodifiableSequencedSet(
                    new LinkedHashSet<>(parameters));
            if (parameters.isEmpty()) {
                throw new IllegalArgumentException(
                        "a supplied decision is supplied through something");
            }
        }
    }

    /** The one {@link Own}, which carries nothing to tell instances apart. */
    DecisionSource OWN = new Own();
}
