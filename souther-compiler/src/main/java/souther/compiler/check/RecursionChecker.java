package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Types the body of a recursive helper as the analysis reads it: the language's own operations left
 * standing, and its parameters bound to the types they declare.
 *
 * <p>Not the body the backend emits. That one is typed where the module is checked, over a tree in
 * which every operation of the library has been expanded into its algorithm; a reader of what the
 * helper answers reads the operations, as it does in a behavior's body.
 *
 * <p>Each parameter of a recursive helper declares its type, since no call expands the helper to
 * give it one; one that does not is no body this types.
 */
public final class RecursionChecker {

    private RecursionChecker() { }

    /**
     * The body of {@code helper}, typed, with the bindings its parameters arrive on — or null where
     * a parameter declares no type.
     *
     * @param helper             the helper as the analysis expands it
     * @param recursiveHelperFns the recursive helpers its body calls, itself among them, by their
     *                           signatures
     * @param settledValues      what each value of the module was settled as
     */
    public static Typed check(Hir.FnDef helper, Symbols symbols, DeclarationAccess declarations,
                              ReachedValueLocations reachedLocations,
                              Map<ValueName.Behavior, ReqSig> reqSigs,
                              Map<String, StandingSignature> recursiveHelperFns,
                              Preserved.SettledValues settledValues) {
        Scope env = Scope.NONE;
        List<Core.Binder> parameters = new ArrayList<>();
        for (Hir.FnParam p : helper.params()) {
            if (p.type() == null) {
                return null;
            }
            env = env.with(p.binder(), TypeOps.resolveParamType(p.type()));
            parameters.add(CoreBinders.of(p.binder()));
        }
        CheckContext context =
                new CheckContext(symbols, declarations, reachedLocations, null, reqSigs)
                        .forDischarge(settledValues);
        Type declared = helper.declaredReturn() == null
                ? null : TypeOps.successType(helper.declaredReturn());
        Core typed = Elaborator.elaborate(helper.writtenBody(), env.reaching(recursiveHelperFns),
                context, declared);
        return new Typed(typed, parameters);
    }

    /** A helper's body, typed, and the bindings a call hands its arguments to, in order. */
    public record Typed(Core body, List<Core.Binder> parameters) {

        public Typed {
            if (body == null) {
                throw new IllegalArgumentException("a helper typed has a body");
            }
            parameters = List.copyOf(parameters);
        }
    }
}
