package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;
import java.util.Set;

/**
 * The classes of declared types that a helper's closed body names once a module that imports it
 * emits it.
 *
 * <p>Read off the body typed as its reader types it, because what an order or a field read names is
 * a fact about types and the written tree has none. A body whose parameters take their types from
 * where it is called has no types to be read against here, so it is read as written
 * ({@link ExecutableDependencies}), which lists the forms that name a class without one; the
 * emitter refuses what either reading missed.
 */
public final class CarriedBodyDependencies {

    private CarriedBodyDependencies() {}

    /**
     * @param closed        a definition as it is handed to a reader
     * @param standingCalls what the calls it leaves standing are typed against
     */
    public static Set<TypeSymbol.AtModule> of(Hir.FnDef closed, DerivedSymbols symbols,
                                              PublishedDeclarations published,
                                              DeclarationKinds kinds,
                                              Map<String, Type> standingCalls) {
        Scope env = Scope.NONE;
        for (Hir.FnParam p : closed.params()) {
            if (p.type() == null) {
                return ExecutableDependencies.of(closed.writtenBody());
            }
            env = env.with(p.binder(), TypeOps.resolveParamType(p.type()));
        }
        NewtypeInners inners = NewtypeInners.asWritten(symbols);
        Type declared = closed.declaredReturn() == null
                ? null : TypeOps.successType(closed.declaredReturn());
        try {
            Core typed = Elaborator.elaborate(closed.writtenBody(), env.reaching(standingCalls),
                    new CheckContext(symbols, published, kinds, inners,
                            EffectiveFieldTypes.asWritten(symbols), FieldLayout.asWritten(symbols),
                            null, Map.of(), Map.of(), false, Preserved.NONE),
                    declared);
            return EmittedClassReferences.of(typed, inners, symbols, kinds, published);
        } catch (CompileException e) {
            // Not a body this can type on its own, which is a fact about the body and no finding:
            // whatever is wrong with it is reported where it is written.
            return ExecutableDependencies.of(closed.writtenBody());
        }
    }
}
