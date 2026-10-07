package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Optional;

/**
 * The case a value is, where the value itself settles it — the leaf of a case space an arm is asked
 * whether it takes ({@link Core.ResolvedPattern#takes}).
 *
 * <p>Two ways a value settles it. Some forms write the case down: a construction is the data it
 * builds, a unit value is its data, and an optional's two carriers are {@code Some} and
 * {@code None}, which is the only way an optional's case is ever fixed. And a value of a primitive
 * type is that primitive whatever form it has, since a primitive is a leaf of every union that
 * holds it. Anything else is a value whose case turns on what it is handed, and answers nothing.
 *
 * <p>Said in the atoms the checker resolves an arm's cases to cover, so the answer is held to the
 * arm without either side being read again: an optional's carriers cover {@code Some} and
 * {@code None}, and a primitive covers itself.
 *
 * <p>The switch names every form and has no default. A form added to {@link Core} stops here until
 * somebody says whether writing it settles a case.
 */
final class WrittenCase {

    private WrittenCase() {}

    /** The case {@code e} is, or empty where nothing about {@code e} itself settles it. */
    static Optional<TypeSymbol> of(Core e) {
        return switch (e) {
            case Core.Construct made -> Optional.of(made.typeName());
            case Core.UnitValue unit -> Optional.of(unit.data());
            case Core.OptionSome _ -> Optional.of(TypeSymbol.SOME);
            case Core.OptionNone _ -> Optional.of(TypeSymbol.NONE);
            // Standing as a wider type changes what it is read as, not which case it is.
            case Core.Widen widened -> of(widened.value());
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.Read _, Core.MaterialisedValue _, Core.Neg _, Core.FieldAccess _,
                 Core.FieldProjection _, Core.Binary _, Core.Call _, Core.PreservedCall _,
                 Core.Apply _, Core.If _, Core.IfConstructed _, Core.LetIn _, Core.Block _,
                 Core.ListLit _, Core.Tuple _, Core.TupleGet _, Core.Match _ -> ofItsType(e);
            // Nothing arrives from it, so it is no value of any case.
            case Core.Unreachable _ -> Optional.empty();
        };
    }

    private static Optional<TypeSymbol> ofItsType(Core e) {
        return e.type() instanceof Type.Prim primitive
                ? Optional.of(TypeSymbol.primitive(primitive))
                : Optional.empty();
    }
}
