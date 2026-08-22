package souther.compiler.coverage;

import java.util.Set;

/**
 * Who owns the rule a fork decides by.
 *
 * <p>Read off the declaration ({@link DecisionSources}). What a caller does with it is decide what
 * one obligation is: a fork deciding for itself is one obligation however many bodies it is spliced
 * into, and a fork deciding by a rule the caller handed in is one per rule handed in.
 *
 * <p>Two answers and no third. A declaration's fork either rests on one or more of the rules it was
 * handed or it does not, and both are things this reading establishes. Rests on, and not applies: a
 * fork can test what another helper answered out of a rule without applying the rule itself, and a
 * reading that asked the narrower question called that fork the declaration's own. Whether an
 * occurrence of a supplied fork could be told which rule it was handed is the other half of the
 * question and is answered where the occurrence is ({@link DecidedBy}).
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
     * <p>In the order the declaration names them, so what the rules of one occurrence are read into
     * is a list that means the same thing at every occurrence. Held as a set, the order would be
     * whatever the reading happened to meet them in, and the answer two occurrences are compared by
     * would turn on that.
     *
     * <p>{@code declaration} is whose parameters those are. A name says which of one declaration's
     * parameters it is and nothing more — two declarations name a parameter alike as often as not —
     * so a reader looking for the copy that owns them by their names finds whichever copy spells one
     * that way. Asked that way, a fork written in a helper and handed to another that happens to
     * name a parameter the same was answered with the inner one's rule, and the rules two call sites
     * wrote were counted as one.
     */
    record Supplied(String declaration, java.util.List<String> parameters)
            implements DecisionSource {

        public Supplied {
            parameters = java.util.List.copyOf(parameters);
            if (parameters.size() != Set.copyOf(parameters).size()) {
                throw new IllegalArgumentException(
                        "a parameter is named once: " + parameters);
            }
            if (parameters.isEmpty()) {
                throw new IllegalArgumentException(
                        "a supplied decision is supplied through something");
            }
            if (declaration == null) {
                throw new IllegalArgumentException(
                        "a parameter is one of some declaration's, and says which");
            }
        }
    }

    /** The one {@link Own}, which carries nothing to tell instances apart. */
    DecisionSource OWN = new Own();
}
