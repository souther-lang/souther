package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

/**
 * What a definition is, as the lowering of its body reads it: what it runs as, rather than where it
 * came from.
 *
 * <p>Where a definition came from is {@link DefinitionRole}, and the two are not one question read
 * twice. Where the role a definition was made as settles what it runs as — a row's value, the entry
 * a module publishes for a value, a declaration another module wrote — this is that answer carried
 * over. Where it does not, this is what decides it: a {@code let} the module wrote is a behavior's
 * implementation where a behavior of its name declares it, a value where it has no parameter list,
 * and a helper otherwise.
 *
 * <p>Nothing here reads a graph. Whether a definition recurses in some representation is a fact
 * about the declarations in reach of that representation, and a value is a value in every one of
 * them: a value that reaches itself is refused as a value, before anything expands a body of its
 * module, and not turned into a recursion.
 *
 * <p>Nor does anything here read a lowered definition. Lowering a value gives the method it runs as
 * the values its root region demands, so the parameters a lowered value takes say nothing about
 * whether it is one.
 */
public sealed interface LoweringRole
        permits LoweringRole.Behavior, LoweringRole.ValueDeclaredElsewhere, LoweringRole.Emitted {

    /**
     * What {@code definition}, held by {@code module}, runs as.
     *
     * @param implementsABehavior whether a behavior of {@code module} declares the definition, which
     *                            is a fact about the module's behaviors and not about the definition
     */
    static LoweringRole of(Hir.FnDef definition, String module, boolean implementsABehavior) {
        return switch (definition.role()) {
            case DefinitionRole.RowValue(RowPosition position) -> new RowValue(position);
            case DefinitionRole.PublishedValueEntry(ValueName.Helper value) ->
                    new PublishedValueEntry(value);
            case DefinitionRole.TakenOn(ReachName.Declaration reachedAs) ->
                    definition.params().isEmpty() ? new ValueDeclaredElsewhere(reachedAs)
                            : new Helper(reachedAs);
            case DefinitionRole.Ordinary _, DefinitionRole.AttachedValue _ -> {
                if (implementsABehavior) {
                    yield new Behavior(new ValueName.Behavior(module, definition.name()));
                }
                ValueName.Helper declared = new ValueName.Helper(module, definition.name());
                yield definition.params().isEmpty() ? new ValueHome(declared)
                        : new Helper(new ReachName.Own(declared));
            }
        };
    }

    /**
     * {@code role}, of the definition {@code module} emits as the method {@code definition}.
     *
     * <p>A narrowing of what the definition was already answered to be, not a second reading of it.
     * What a module emits as a method is never a behavior's implementation, which is emitted as the
     * behavior, and never a value another module declared, which runs in that module and nowhere
     * else. A definition that arrives here as either is this compiler disagreeing with itself about
     * what it emits.
     */
    static Emitted emitted(LoweringRole role, String definition, String module) {
        return switch (role) {
            case Emitted emitted -> emitted;
            case ValueDeclaredElsewhere elsewhere -> throw new IllegalStateException("`"
                    + definition + "` is emitted by `" + module + "` as a method, and it is the"
                    + " value `" + elsewhere.reachedAs() + "`, which runs where it is declared");
            case Behavior behavior -> throw new IllegalStateException("`" + definition
                    + "` is emitted by `" + module + "` as a method, and it implements the behavior `"
                    + behavior.behavior() + "`");
        };
    }

    /** The implementation of {@code behavior}, which the module emits as the behavior. */
    record Behavior(ValueName.Behavior behavior) implements LoweringRole {}

    /**
     * A value another module declares, held here under the reference this module reaches it by.
     *
     * <p>Its body is read here — an analysis builds it from its template — and it runs in the module
     * that declares it, so no module but that one emits a method for it.
     */
    record ValueDeclaredElsewhere(ReachName.Declaration reachedAs) implements LoweringRole {}

    /** What a module emits as a method of its own. */
    sealed interface Emitted extends LoweringRole
            permits ValueHome, Helper, RowValue, PublishedValueEntry {}

    /**
     * The one place {@code value} runs: the module that declares it builds it and hands it to what
     * reads it.
     */
    record ValueHome(ValueName.Helper value) implements Emitted {}

    /**
     * A helper, reached by {@code declaration}: a method is emitted for it where a call to it is left
     * standing, which is where it recurses.
     */
    record Helper(ReachName.Declaration declaration) implements Emitted {}

    /** The value a row writes at {@code position}. */
    record RowValue(RowPosition position) implements Emitted {}

    /** The entry through which another module calls {@code value}. */
    record PublishedValueEntry(ValueName.Helper value) implements Emitted {}
}
