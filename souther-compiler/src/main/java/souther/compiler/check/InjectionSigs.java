package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The signatures of the behaviors a module injects (spec 13.2): a {@code behavior} declared with no
 * matching {@code let} here, plus the ones an imported module declared and this one names (spec
 * 14.3). A call to any of them is typed from its declaration, so both the settling of helper
 * parameter types (before the module is lowered) and the type check itself read the same map.
 */
public final class InjectionSigs {

    private InjectionSigs() {}

    /**
     * Builds the map. Whether a behavior is an injection target is decided the same way in both
     * callers — it is a {@code SpecBehavior} this module writes no {@code let} for. A local behavior
     * of the same name as an imported one wins; the imported signature only fills a name this module
     * does not declare.
     */
    public static Map<String, ReqSig> of(Ast.Module module, Symbols symbols,
                                         Map<String, Sig> importedSigs, Set<String> importedInjected) {
        Set<String> own = new HashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec
                    && (isInjectionTarget(module, spec) || !spec.requires().isEmpty())) {
                own.add(spec.name());
            }
        }
        return dependencies(module, symbols, own, importedSigs, importedInjected);
    }

    /** Whether {@code spec} is written with no {@code let} of its own, so something else supplies
     *  the body (spec {@code [#injected-behavior]}). */
    private static boolean isInjectionTarget(Ast.Module module, Ast.SpecBehavior spec) {
        for (Ast.FnDef fn : module.fns()) {
            if (fn.name().equals(spec.name())) {
                return false;
            }
        }
        return true;
    }

    /**
     * The signatures of the behaviors a {@code requires} clause may name — the ones whose
     * requirement set is not empty. {@code dependencies} names this module's own, computed by the
     * caller so a module read from the path, which publishes no {@code let}, is decided the same way
     * as one being compiled.
     */
    public static Map<String, ReqSig> dependencies(Ast.Module module, Symbols symbols,
                                                   Set<String> dependencies,
                                                   Map<String, Sig> importedSigs,
                                                   Set<String> importedInjected) {
        Map<String, ReqSig> sigs = new HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec && dependencies.contains(spec.name())) {
                List<Type> params = new ArrayList<>();
                for (Ast.Param p : spec.params()) {
                    params.add(TypeOps.successType(p.type(), symbols));
                }
                sigs.put(spec.name(), new ReqSig(params, TypeOps.successType(spec.ret(), symbols)));
            }
        }
        for (String name : importedInjected) {
            Sig sig = importedSigs.get(name);
            if (sig != null) {
                sigs.putIfAbsent(name, new ReqSig(sig.ins(), sig.out()));
            }
        }
        return sigs;
    }

    /**
     * The signatures of the behaviors a body may call by name — the ones whose requirement set is
     * empty (spec {@code [#calling-a-behavior]}). Built the same way as {@link #of}, from the same
     * material, because a call is typed against a declaration either way: what differs is how the
     * behavior is reached at run time, not what the call site has to agree with.
     *
     * <p>{@code callable} names this module's own; {@code importedCallable} the ones it borrows. A
     * local behavior of the same name as an imported one wins, as it does for an injection target.
     */
    public static Map<String, ReqSig> callable(Ast.Module module, Symbols symbols,
                                               Set<String> callable,
                                               Map<String, Sig> importedSigs,
                                               Set<String> importedCallable) {
        Map<String, ReqSig> sigs = new HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec && callable.contains(spec.name())) {
                List<Type> params = new ArrayList<>();
                for (Ast.Param p : spec.params()) {
                    params.add(TypeOps.successType(p.type(), symbols));
                }
                sigs.put(spec.name(), new ReqSig(params, TypeOps.successType(spec.ret(), symbols)));
            }
        }
        for (String name : importedCallable) {
            Sig sig = importedSigs.get(name);
            if (sig != null) {
                sigs.putIfAbsent(name, new ReqSig(sig.ins(), sig.out()));
            }
        }
        return sigs;
    }
}
