package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.Map;

/**
 * Which invariant clause a construction failed, and of which type — the failure side of the
 * {@code __construct} a generated class carries (spec 7.6, §invariant-declaration).
 *
 * <p>A construction runs the type's clauses in the order they are declared and stops at the first
 * that does not hold, so this names one clause and not a set. Where that clause was declared with a
 * name, {@code clause} is it, and the three destinations of a violation read it: an attempted
 * construction departs by the arm answering it, a derived decoder reports it in the issue's metadata,
 * and an abort names it in the message. A clause declared without a name leaves {@code clause} null —
 * there is nothing to tell it apart from the type's other unnamed clauses by, which is what declaring
 * it without a name says.
 *
 * <p>This is not a value the domain can see. It rides the {@code Result} between a generated
 * constructor and its caller, and every path out of that turns it into an abort, a departure, or a
 * boundary issue.
 */
public record InvariantFailure(String type, @Nullable String clause) {

    /** The failure of a clause declared with a name. */
    public static InvariantFailure of(String type, String clause) {
        return new InvariantFailure(type, clause);
    }

    /** The failure of a clause declared without one. */
    public static InvariantFailure unnamed(String type) {
        return new InvariantFailure(type, null);
    }

    /**
     * What an issue reports beside the shared {@code invariant_violation} code: the rejecting type
     * always, and the clause where it has a name. A resolver switches on these, which is why the type
     * travels even when the clause cannot.
     */
    public Map<String, Object> meta() {
        return clause == null ? Map.of("type", type) : Map.of("type", type, "clause", clause);
    }

    /** The abort's message, and the issue's default one. */
    @Override
    public String toString() {
        return clause == null
                ? "invariant violated on " + type
                : "invariant violated on " + type + ": " + clause;
    }
}
