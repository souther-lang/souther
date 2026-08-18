package souther.runtime;

import org.jspecify.annotations.Nullable;

/**
 * Which {@code ensures} clause of which behavior did not hold, what it was declared for, and what
 * was answered.
 *
 * <p>A behavior states a relation between what it is given and what it answers, and the compiler
 * does not prove that a body establishes its own. What holds it is the check that runs where the
 * behavior answers, and this is what that check found: a clause the model declared, and a run that
 * did not keep it.
 *
 * <p>{@code selector} and {@code answeredCase} are two facts and not one said twice. A clause names
 * the cases its rules are about, and an arm may name a case that has cases of its own — an
 * {@code ensures} written for {@code Errors} is a rule every {@code NotFound} and every
 * {@code Denied} is held to. So what a rule was declared for and what the answer turned out to be
 * are at different levels: the first is read from the declaration, the second from the answer.
 * Carrying one of them under both names told a reader the answer was an {@code Errors}, which is
 * not a thing any run produces.
 *
 * <p>{@code selector} is the case named by the arm the broken rule is written under, as the type it
 * is declared as and never as the arm's spelling. It says why this rule was applied to this answer.
 * A clause may be written over several cases — {@code Found -> p | Missing -> q} — and one arm may
 * state something of several at once, so the clause's name alone leaves a reader unable to tell
 * which of its rules broke.
 *
 * <p>It is the case and not the rule's whole identity. A rule is told from its sibling by which arm
 * it was written as, which is a position — add an arm above it and every one below moves — so a
 * value that travels out of the compiler and into a boundary's logs would be carrying the one part
 * of that identity an edit can shift.
 *
 * <p>{@code answeredCase} is the case the answer is: the leaf under the selector that the value
 * turned out to be, or the case a written answer stated where no value was built. It is what the
 * word "answering" means, and it is read from the answer rather than from what was declared about
 * it.
 *
 * <p>Both are null together, and for one reason: the clause's rule is guarded by no case, which is
 * what a behavior whose output has no cases declares. Nothing counts cases to decide it — an output
 * with cases admits an arm and one without admits none, and that is settled where the arm is read.
 *
 * <p>{@code clause} is null where the clause was declared without a name. There is nothing to tell
 * it apart from the behavior's other unnamed clauses by, which is what declaring it without a name
 * says — the same answer {@link InvariantFailure} gives for the same reason.
 */
public record EnsuresFailure(String module, String behavior, @Nullable String clause,
                             @Nullable String selector, @Nullable String answeredCase)
        implements ConstraintFailure {

    /** The behavior as Souther identifies it: a behavior is its module and its name, and two modules
     *  may each declare a {@code find}. */
    public String qualifiedBehavior() {
        return module + "." + behavior;
    }

    /**
     * The abort's message: the clause, what it was declared for, and what was answered.
     *
     * <p>Read in that order because that is the order the question is asked in — which contract
     * broke, what it was checking, what came back. What the rule was declared for is left out where
     * it is the case that answered: the two are the same fact there, and saying it twice would put
     * a distinction in front of a reader that this answer does not have.
     */
    @Override
    public String toString() {
        StringBuilder said = new StringBuilder("ensures not held on ").append(qualifiedBehavior());
        String separator = ": ";
        if (clause != null) {
            said.append(separator).append(clause);
            separator = ", ";
        }
        if (selector != null && !selector.equals(answeredCase)) {
            said.append(separator).append("for ").append(selector);
            separator = ", ";
        }
        if (answeredCase != null) {
            said.append(separator).append("answering ").append(answeredCase);
        }
        return said.toString();
    }
}
