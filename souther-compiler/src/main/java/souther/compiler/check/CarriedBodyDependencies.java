package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;
import java.util.Set;

/**
 * The classes of declared types that a helper handed to another module names once that module emits
 * it.
 *
 * <p>Read off the definition typed as its reader types it, because what an order or a cast names is a
 * fact about types and the written tree has none. A helper that is emitted as a method of its own is
 * read as the check settled it, which is the definition the reader emits; one that is expanded where
 * it is called is typed here, as the reader types it.
 */
public final class CarriedBodyDependencies {

    private CarriedBodyDependencies() {}

    /**
     * The classes emitting a definition that is a method of its own names: what it takes, and its
     * body.
     */
    public static Set<TypeSymbol.AtModule> of(EmittedDefinition emitted, DerivedSymbols symbols,
                                              PublishedDeclarations published,
                                              DeclarationKinds kinds) {
        return EmittedClassReferences.of(emitted, NewtypeInners.asWritten(symbols), symbols, kinds,
                published);
    }

    /**
     * The classes emitting {@code closed} inline names, whichever module they are of.
     *
     * <p>A parameter that takes its type from the body is settled as the check settles it, so a
     * helper with one is typed like any other. A helper that checked on its own and cannot be typed
     * as its reader types it is this compiler disagreeing with itself, and is said so.
     *
     * @param closed        a definition as it is handed to a reader
     * @param standingCalls what the calls it leaves standing are typed against
     */
    public static Set<TypeSymbol.AtModule> of(Hir.FnDef closed, DerivedSymbols symbols,
                                              PublishedDeclarations published,
                                              DeclarationKinds kinds,
                                              Map<String, Type> standingCalls) {
        NewtypeInners inners = NewtypeInners.asWritten(symbols);
        Type declared = closed.declaredReturn() == null
                ? null : TypeOps.successType(closed.declaredReturn());
        Core typed;
        try {
            Scope env = HelperTyping.parameterScope(closed, closed.writtenBody(), symbols,
                    published, kinds, standingCalls);
            typed = Elaborator.elaborate(closed.writtenBody(), env.reaching(standingCalls),
                    new CheckContext(symbols, published, kinds, inners,
                            EffectiveFieldTypes.asWritten(symbols), FieldLayout.asWritten(symbols),
                            null, Map.of(), Map.of(), false, Preserved.NONE),
                    declared);
        } catch (CompileException e) {
            throw new IllegalStateException("`" + closed.name() + "` was typed on its own and could"
                    + " not be typed as its reader types it: " + e.getMessage(), e);
        }
        return EmittedClassReferences.of(typed, inners, symbols, kinds, published);
    }
}
