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
final class InjectionSigs {

    private InjectionSigs() {}

    /**
     * Builds the map. Whether a behavior is an injection target is decided the same way in both
     * callers — it is a {@code SpecBehavior} this module writes no {@code let} for. A local behavior
     * of the same name as an imported one wins; the imported signature only fills a name this module
     * does not declare.
     */
    static Map<String, ReqSig> of(Ast.Module module, Symbols symbols,
                                  Map<String, Sig> importedSigs, Set<String> importedInjected) {
        Set<String> implemented = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            implemented.add(fn.name());
        }
        Map<String, ReqSig> sigs = new HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec && !implemented.contains(spec.name())) {
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
}
