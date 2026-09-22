package souther.compiler.program;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A value this module declares, as the one place it runs.
 *
 * <p>A value has one executable home, the module that declares it. That module builds it and hands
 * it to what reads it; another module reads it by calling the entry the declaring module publishes,
 * and never builds a copy of its own. So a value is not a helper: a helper is a declaration a module
 * carries a copy of because a call to it was left standing, and it lives as long as that call does.
 * A value is what this module's own build of it answers, whoever reads it.
 *
 * <p>What it takes is not an argument of the value. A value takes none. The method it runs as takes
 * the values its root region demands, which the region building it has built already and hands
 * over, so that nothing is built twice; each of those says which value it holds. A reader that
 * counted them to decide whether this is a value would be reading how it runs rather than what it
 * is, and a value that names another value at its root takes one.
 *
 * <p>What it answers is not a member: it is {@code body().type()}, which the checker decided.
 */
public final class CheckedValue {

    private final ValueName.Helper name;
    private final List<Handover> handovers;
    private final Core body;

    CheckedValue(ValueName.Helper name, List<Handover> handovers, Core body) {
        this.name = name;
        this.handovers = List.copyOf(handovers);
        this.body = body;
    }

    /**
     * What the method this value runs as is handed: the binding its body reads, the type arriving in
     * it, and the value {@code carries} it holds.
     */
    public record Handover(Core.Binder binder, Type type, ValueName.Helper carries) {}

    /** Which value this is. */
    public ValueName.Helper name() {
        return name;
    }

    /** What the method it runs as is handed, in the order a call supplies them. */
    public List<Handover> handovers() {
        return handovers;
    }

    /** Its body, as the checker typed it. */
    public Core body() {
        return body;
    }

    /** What it answers, which is what its body was checked to answer. */
    public Type answers() {
        return body.type();
    }

    @Override
    public String toString() {
        return name.toString();
    }
}
