package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.Map;
import java.util.Objects;

/**
 * Which invariant clause a construction failed, and of which type — the failure side of the
 * {@code __construct} a generated class carries (spec §invariant-mvp, §invariant-declaration).
 *
 * <p>A construction runs the type's clauses in the order they are declared and stops at the first
 * that does not hold, so this names one clause and not a set. Where that clause was declared with a
 * name, {@code clause} is it, and the three destinations of a violation read it: an attempted
 * construction departs by the arm answering it, a derived decoder reports it in the issue's metadata,
 * and an abort names it in the message. A clause declared without a name leaves {@code clause} null —
 * there is nothing to tell it apart from the type's other unnamed clauses by, which is what declaring
 * it without a name says.
 *
 * <p>{@code declared} is which clause it was whether it has a name or not: the type that wrote it and
 * where it stands among that type's clauses. A type spreading another's clauses holds them under the
 * type that wrote them, so it is not always {@code type}. What reads it is a tool that has the source
 * and is asked which clause stopped a run; the destinations above go by the name.
 *
 * <p>This is not a value the domain can see. It rides the {@code Result} between a generated
 * constructor and its caller, and every path out of that turns it into an abort, a departure, or a
 * boundary issue.
 */
public record InvariantFailure(String module, String type, @Nullable String clause,
                               Declared declared) implements ConstraintFailure {

    public InvariantFailure {
        Objects.requireNonNull(declared, "a failed clause is one of the clauses some type wrote");
    }

    /**
     * Which clause, as the declaration that wrote it and its place among that declaration's
     * clauses, counted from nought in the order they are written.
     */
    public record Declared(String module, String type, int ordinal) {}

    /** The failure of a clause declared with a name. */
    public static InvariantFailure of(String module, String type, String clause,
                                      String declaredModule, String declaredType, int ordinal) {
        return new InvariantFailure(module, type, clause,
                new Declared(declaredModule, declaredType, ordinal));
    }

    /** The failure of a clause declared without one. */
    public static InvariantFailure unnamed(String module, String type, String declaredModule,
                                           String declaredType, int ordinal) {
        return new InvariantFailure(module, type, null,
                new Declared(declaredModule, declaredType, ordinal));
    }

    /** The rejecting type as Souther identifies it: a type is its module and its name, and two modules
     * may each declare a {@code Id}. */
    public String qualifiedType() {
        return module + "." + type;
    }

    /**
     * What an issue reports beside the shared {@code invariant_violation} code: the rejecting type
     * always, and the clause where it has a name. A resolver switches on these, which is why the type
     * travels even when the clause cannot.
     *
     * <p>The module is its own entry rather than folded into the name. What a type is, is its module
     * and its name, so a resolver keyed on `+Id+` alone would answer for two types; keeping them apart
     * lets it key on either without parsing.
     */
    public Map<String, Object> meta() {
        return clause == null
                ? Map.of("module", module, "type", type)
                : Map.of("module", module, "type", type, "clause", clause);
    }

    /** The abort's message, and the issue's default one. */
    @Override
    public String toString() {
        return clause == null
                ? "invariant violated on " + qualifiedType()
                : "invariant violated on " + qualifiedType() + ": " + clause;
    }
}
