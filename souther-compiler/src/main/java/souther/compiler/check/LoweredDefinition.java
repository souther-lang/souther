package souther.compiler.check;

import java.util.Map;
import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

/**
 * A definition as it runs, and the value each parameter the lowering gave it carries.
 *
 * <p>A value runs as a method that takes the values its root region demands: the region that builds
 * the value has built those already and hands them over. Which value each of those parameters holds
 * is known where the lowering makes the parameter, and is kept here from there rather than written
 * into the parameter's name for a reader to take apart again. A parameter the source wrote carries
 * nothing and is not in {@code carried}.
 *
 * @param definition the definition as lowered
 * @param carried the value each parameter the lowering added holds, by the binding of the parameter
 */
public record LoweredDefinition(Hir.FnDef definition, Map<BindingId, ValueName.Helper> carried) {

    public LoweredDefinition {
        carried = Map.copyOf(carried);
    }

    /** A definition that runs as the body it was written with, which takes nothing it was not
     *  written to take. */
    public static LoweredDefinition asWritten(Hir.FnDef definition) {
        return new LoweredDefinition(definition, Map.of());
    }
}
