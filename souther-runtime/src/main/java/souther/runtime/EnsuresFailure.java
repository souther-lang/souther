package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which {@code ensures} clause of which behavior did not hold, and for which of its answer's cases.
 *
 * <p>A behavior states a relation between what it is given and what it answers, and the compiler
 * does not prove that a body establishes its own. What holds it is the check that runs where the
 * behavior answers, and this is what that check found: a clause the model declared, and a run that
 * did not keep it.
 *
 * <p>{@code answeredCase} is the case the answer turned out to be, where the clause spoke of cases.
 * A clause may be written over several — {@code Found -> p | Missing -> q} — and one arm may state
 * something of several at once, so naming the clause alone leaves a reader unable to tell which of
 * its rules broke, and a reader that wanted to know would walk the declaration again. Null where the
 * answer has no cases and the clause named none, which is the one form with nothing to say here.
 *
 * <p>It is the case and not the rule's whole identity. A rule is told from its sibling by which arm
 * it was written as, which is a position — add an arm above it and every one below moves — so a
 * value that travels out of the compiler and into a boundary's logs would be carrying the one part
 * of that identity an edit can shift. What does not move is which clause it is and which case it is
 * about, which is also what a reader of the abort has any use for.
 *
 * <p>{@code clause} is null where the clause was declared without a name. There is nothing to tell
 * it apart from the behavior's other unnamed clauses by, which is what declaring it without a name
 * says — the same answer {@link InvariantFailure} gives for the same reason.
 */
public record EnsuresFailure(String module, String behavior, @Nullable String clause,
                             @Nullable String answeredCase) implements ConstraintFailure {

    /** The failure of a clause written over one case of the answer. */
    public static EnsuresFailure of(String module, String behavior, String clause,
                                    String answeredCase) {
        return new EnsuresFailure(module, behavior, clause, answeredCase);
    }

    /** The failure of a clause declared without a name, written over one case of the answer. */
    public static EnsuresFailure unnamed(String module, String behavior, String answeredCase) {
        return new EnsuresFailure(module, behavior, null, answeredCase);
    }

    /** The failure of a clause over an answer that has no cases to speak of. */
    public static EnsuresFailure ofWholeAnswer(String module, String behavior, String clause) {
        return new EnsuresFailure(module, behavior, clause, null);
    }

    /** The same, declared without a name. */
    public static EnsuresFailure unnamedOverWholeAnswer(String module, String behavior) {
        return new EnsuresFailure(module, behavior, null, null);
    }

    /** The behavior as Souther identifies it: a behavior is its module and its name, and two modules
     *  may each declare a {@code find}. */
    public String qualifiedBehavior() {
        return module + "." + behavior;
    }

    /**
     * What a boundary reporting this has to switch on, beside the shared code.
     *
     * <p>Each part is its own entry rather than folded into a name, for the reason
     * {@link InvariantFailure#meta()} keeps a module out of a type's name: a resolver keyed on
     * {@code find} alone would answer for two behaviors, and one that wants to act on a particular
     * case should not have to parse a sentence to find it.
     */
    public Map<String, Object> meta() {
        Map<String, Object> meta = new LinkedHashMap<>();
        meta.put("module", module);
        meta.put("behavior", behavior);
        if (clause != null) {
            meta.put("clause", clause);
        }
        if (answeredCase != null) {
            meta.put("case", answeredCase);
        }
        return Map.copyOf(meta);
    }

    /** The abort's message. */
    @Override
    public String toString() {
        StringBuilder said = new StringBuilder("ensures not held on ").append(qualifiedBehavior());
        if (clause != null) {
            said.append(": ").append(clause);
        }
        if (answeredCase != null) {
            said.append(clause == null ? ": " : ", ").append("answering ").append(answeredCase);
        }
        return said.toString();
    }
}
