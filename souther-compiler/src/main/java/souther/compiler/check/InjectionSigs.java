package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The signatures of the behaviors a module injects (spec §injected-behavior): a {@code behavior} declared with no
 * matching {@code let} here, plus the ones an imported module declared and this one names (spec
 * 14.3). A call to any of them is typed from its declaration, so both the settling of helper
 * parameter types (before the module is lowered) and the type check itself read the same map.
 */
public final class InjectionSigs {

    private InjectionSigs() {}

    /**
     * Builds the map. Whether a behavior is an injection target is decided the same way in both
     * callers — it is a {@code SpecBehavior} this module writes no {@code let} for.
     *
     * <p>Keyed by the declaration each signature belongs to. A behavior this module declares and one
     * it borrows may share a name, and they are two behaviors: under the spelling, one of them
     * silently answered for the other and which it was fell to the order the two were written in.
     */
    public static Map<ValueName.Behavior, ReqSig> of(String module, List<Hir.BehaviorDef> behaviors,
                                                     List<Hir.FnDef> fns,
                                                     Symbols symbols,
                                                     Map<ValueName.Behavior, Sig> importedSigs,
                                                     Set<ValueName.Behavior> importedInjected) {
        Set<String> own = new HashSet<>();
        for (Hir.BehaviorDef b : behaviors) {
            if (b instanceof Hir.SpecBehavior spec
                    && (isInjectionTarget(fns, spec) || !spec.dependsOn().isEmpty())) {
                own.add(spec.name());
            }
        }
        return dependencies(module, behaviors, symbols, own, importedSigs, importedInjected);
    }

    /** Whether {@code spec} is written with no {@code let} of its own, so something else supplies
     *  the body (spec {@code [#injected-behavior]}). */
    private static boolean isInjectionTarget(List<Hir.FnDef> fns, Hir.SpecBehavior spec) {
        for (Hir.FnDef fn : fns) {
            if (fn.name().equals(spec.name())) {
                return false;
            }
        }
        return true;
    }

    /**
     * The signatures of the behaviors a {@code depends on} clause may name — the ones whose
     * requirement set is not empty. {@code dependencies} names this module's own, computed by the
     * caller so a module read from the path, which publishes no {@code let}, is decided the same way
     * as one being compiled.
     */
    public static Map<ValueName.Behavior, ReqSig> dependencies(
            String module, List<Hir.BehaviorDef> behaviors, Symbols symbols,
            Set<String> dependencies,
            Map<ValueName.Behavior, Sig> importedSigs,
            Set<ValueName.Behavior> importedInjected) {
        return sigsOf(module, behaviors, dependencies, importedSigs, importedInjected);
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
    public static Map<ValueName.Behavior, ReqSig> callable(
            String module, List<Hir.BehaviorDef> behaviors, Symbols symbols,
            Set<String> callable,
            Map<ValueName.Behavior, Sig> importedSigs,
            Set<ValueName.Behavior> importedCallable) {
        return sigsOf(module, behaviors, callable, importedSigs, importedCallable);
    }

    /**
     * The two questions above, which differ only in which behaviors are named — one walk, so that a
     * borrowed declaration and a declared one are read the same way whichever question is asked.
     */
    private static Map<ValueName.Behavior, ReqSig> sigsOf(
            String module, List<Hir.BehaviorDef> behaviors, Set<String> own,
            Map<ValueName.Behavior, Sig> importedSigs, Set<ValueName.Behavior> borrowed) {
        Map<ValueName.Behavior, ReqSig> sigs = new LinkedHashMap<>();
        for (Hir.BehaviorDef b : behaviors) {
            if (b instanceof Hir.SpecBehavior spec && own.contains(spec.name())) {
                List<Type> params = new ArrayList<>();
                for (Hir.Param p : spec.params()) {
                    params.add(TypeOps.successType(p.type()));
                }
                sigs.put(new ValueName.Behavior(module, spec.name()),
                        new ReqSig(params, TypeOps.successType(spec.ret())));
            }
        }
        for (ValueName.Behavior each : borrowed) {
            Sig sig = importedSigs.get(each);
            if (sig != null) {
                sigs.put(each, new ReqSig(sig.inputTypes(), sig.outputType()));
            }
        }
        return sigs;
    }

    /**
     * The same behaviors, with only how many inputs each takes — what turning one of their names
     * into a function value needs (spec {@code [#blocks]}).
     *
     * <p>The expansion that does it is written before anything is typed, so it cannot read a
     * signature. One projection rather than one per caller, so a body expanded for the backend and a
     * helper expanded for its own check answer the same about the same name.
     */
    public static Map<ValueName.Behavior, Integer> arities(Map<ValueName.Behavior, ReqSig> sigs) {
        Map<ValueName.Behavior, Integer> arities = new LinkedHashMap<>();
        sigs.forEach((name, sig) -> arities.put(name, sig.params().size()));
        return arities;
    }
}
