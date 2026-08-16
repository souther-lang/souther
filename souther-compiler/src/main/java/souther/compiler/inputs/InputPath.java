package souther.compiler.inputs;

import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;

import java.util.List;

/**
 * Which position of a behavior's input an expression names, or nothing where it names none.
 *
 * <p>One answer, for every reader of a body that has something to say about a position. A
 * {@code guard} comparing a field, a {@code match} on a parameter and an arm declaring a case
 * cannot arrive are three statements about the same positions, and each working out for itself
 * which position it was talking about is three spellings of one path — of which the axes carry one,
 * so the other two would be about positions nothing measures.
 *
 * <p>Nothing about the reading of an input reaches this and nothing here reaches it: what a
 * position can hold is read from the declarations ({@link InputDomain}), and this only says which
 * position an expression is pointing at.
 */
public final class InputPath {

    /**
     * The position {@code e} names.
     *
     * <p>Which fields are steps is {@link Location}'s rule, asked here rather than restated: a
     * newtype's {@code value} is not one, so {@code request.cost} and {@code request.cost.value}
     * are one position, and if the two spellings disagreed the same position would become two axes,
     * one of which no row would ever cover.
     *
     * <p>The root is not that rule's. What a behavior takes is what it declares, and a declared
     * parameter is not a binding — a behavior with no implementation has positions all the same —
     * so this path is rooted at the parameter and {@link Location} at the binding a body gave it.
     *
     * @param parameters the behavior's parameter names, which is what tells a read of an input from
     *                   a read of anything else
     */
    public static TermPath of(Core e, List<String> parameters, Symbols symbols) {
        return switch (e) {
            case Core.Read r -> parameters.contains(r.name()) ? TermPath.of(r.name()) : null;
            case Core.FieldAccess fa -> {
                TermPath base = of(fa.target(), parameters, symbols);
                if (base == null) {
                    yield null;
                }
                yield Location.isStep(fa.target().type(), fa.field(), symbols)
                        ? base.then(fa.field()) : base;
            }
            // A call kept standing names no location, and its presence says this walk was handed a
            // representation it does not read. Said rather than answered with "no path", which would
            // be the same answer a number gives.
            case Core.PreservedCall p -> throw p.unexpectedIn("an input position");
            case null, default -> null;
        };
    }

    private InputPath() {}
}
