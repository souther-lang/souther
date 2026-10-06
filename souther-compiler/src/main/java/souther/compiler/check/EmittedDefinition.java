package souther.compiler.check;

import java.util.List;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * A definition the module emits as a method of its own, as the check settled it.
 *
 * <p>Each parameter is the binder its body reads and the type arriving in it. A parameter the source
 * annotates has the type it wrote; one the lowering added, which no source spells, has the type the
 * check settled the value it carries as. No reader asks the lowered syntax for a type, because a
 * compiler-added parameter has none.
 *
 * <p>What the method is — a value's one place to run, a helper, a row's value, the entry of a value —
 * is carried whole rather than left to be read back off the parameters or the name. A value's method
 * takes the values its root region demands, so what it takes does not say whether it is one. What it
 * takes does follow from what it is, and is held to that: a value's method takes only what is
 * handed over to it, and every other method only what its source wrote.
 *
 * @param body the Core the check elaborated for it
 * @param parameters what it takes, in the order a call supplies them
 * @param role what it runs as
 */
public record EmittedDefinition(Core body, List<Parameter> parameters, LoweringRole.Emitted role) {

    /** One parameter: the binding its body reads, and the type arriving in it. */
    public sealed interface Parameter {

        /** The binding the body reads. */
        Core.Binder binder();

        /** The type arriving in it. */
        Type type();
    }

    /** A parameter the definition was written with. */
    public record Declared(Core.Binder binder, Type type) implements Parameter {}

    /**
     * A parameter the lowering gave a value's method: the value {@code carries}, which the region
     * that builds the value has built already and hands over.
     *
     * <p>Not an argument of the value. A value takes none; this is how the method it runs as is
     * handed what it would otherwise build a second time.
     */
    public record Handover(Core.Binder binder, Type type, ValueName.Helper carries)
            implements Parameter {}

    public EmittedDefinition {
        parameters = List.copyOf(parameters);
        // Every role by name, so a method of a new kind says which it takes before it is built.
        boolean handedOver = switch (role) {
            case LoweringRole.ValueHome _ -> true;
            case LoweringRole.Helper _, LoweringRole.RowValue _,
                 LoweringRole.PublishedValueEntry _, LoweringRole.FixtureValueEntry _ -> false;
        };
        for (Parameter parameter : parameters) {
            if ((parameter instanceof Handover) != handedOver) {
                throw new IllegalStateException("a method emitted as " + role + " takes "
                        + parameter + ", and only a value's method is handed what it takes");
            }
        }
    }

    /**
     * Whether what this method compares and forks on is among the places of its module.
     *
     * <p>A value's method is: it is a body a run of every behavior that calls the value passes
     * through. A helper is not, nor is an entry or a row's value. The plan numbers the places of
     * exactly these bodies and the emitter records a run through exactly these, so both read it
     * here; asked apart, one of them can number a place the other never writes. Every role is
     * answered by name, so a method of a new kind is neither counted nor left out until someone
     * says which.
     */
    public boolean placesAreCounted() {
        return switch (role) {
            case LoweringRole.ValueHome _ -> true;
            case LoweringRole.Helper _, LoweringRole.RowValue _,
                 LoweringRole.PublishedValueEntry _, LoweringRole.FixtureValueEntry _ -> false;
        };
    }
}
