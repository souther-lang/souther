package souther.compiler.program;

import souther.compiler.core.Core;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A declaration the module carries a method for, because a call to it was left standing.
 *
 * <p>Most helpers are gone by the time a module is checked: the checker inlines a {@code let} at
 * the place it is used. What is left here is the one that cannot be inlined — a recursion — and a
 * body reaches it by a call like any other. A reader given only the behaviors would find that call
 * naming something it had never been handed.
 *
 * <p>{@link #reachedAs} is the reference the calls in this module reach it by, which is the value
 * one of those calls carries. So a reader holding a call gets from it to this by asking what the
 * call reaches, and never by writing a name out of the two halves of one.
 *
 * <p>What it is a copy of is {@link #declares}, off that reference. Not the module emitting the
 * method: {@code souther.list} declares {@code foldFrom} and a module carries it under the alias
 * the library publishes it as, so a copy filed as though the emitting module had declared it says
 * that module declares an operation of the standard library.
 *
 * <p>What it answers is not a member: it is {@code body().type()}, which the checker decided.
 */
public final class CheckedHelper {

    private final ReachName reachedAs;
    private final List<Parameter> parameters;
    private final Core body;

    CheckedHelper(ReachName reachedAs, List<Parameter> parameters, Core body) {
        this.reachedAs = reachedAs;
        this.parameters = List.copyOf(parameters);
        this.body = body;
    }

    /** One parameter: the binding its body reads, and the type arriving in it. */
    public record Parameter(Core.Binder binder, Type type) {}

    /** The reference a call in this module reaches it by — what a call carries, and what a name
     *  for the method an output emits is built from. */
    public ReachName reachedAs() {
        return reachedAs;
    }

    /**
     * The declaration this is a copy of.
     *
     * <p>Read off the reference rather than held beside it. A declaration kept next to the route
     * that reached it is the same fact twice, and the alias in that route is nowhere in the
     * declaration — so nothing could put the two back together if they came apart.
     */
    public ValueName declares() {
        return reachedAs.denotes();
    }

    /** Its parameters, in the order a call supplies them. */
    public List<Parameter> parameters() {
        return parameters;
    }

    /** Its body, as the checker typed it. */
    public Core body() {
        return body;
    }

    @Override
    public String toString() {
        return reachedAs.rendered();
    }
}
