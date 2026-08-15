package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What each behavior of a module requires injected to be constructed, in the order it takes them.
 *
 * <p>A behavior with a body requires what it declares it depends on (spec §depends-on, §requirement-propagation). A
 * composition requires the union of its stages', transitively: a stage with a body is constructed by
 * the composition and handed the fields it needs, so what has to be injected are the injected
 * behaviors the stages reach (§composition-with-requirements). A stage that is itself injected is one of those.
 *
 * <p>The order is first appearance, walking the stages left to right. That order is the injecting
 * constructor's parameter order, so it is the order fakes are passed in at an example as well —
 * which is why this is answered once and read by both. Two computations that agreed today would
 * bind a fake to the wrong dependency the first time one of them changed.
 */
public final class Requirements {

    private Requirements() {}

    /**
     * The injection targets a module builds against: its own behaviors written with no body, and the imported
     * ones it names, whose base lives in the module that declares them (spec §injected-behavior,
     * §composition-with-requirements).
     *
     * <p>This is the rule that decides whether a name is something to inject or something to
     * construct, and both the emitter and the requirement walk below read it here so they cannot
     * disagree about one behavior.
     */
    public static Set<String> injectedNames(Hir.Module module, Set<String> importedInjected) {
        Set<String> fns = new LinkedHashSet<>();
        for (Hir.FnDef fn : module.fns()) {
            fns.add(fn.name());
        }
        Set<String> injected = new LinkedHashSet<>(importedInjected);
        for (Hir.BehaviorDef bd : module.behaviors()) {
            if (bd instanceof Hir.SpecBehavior spec && !fns.contains(spec.name())) {
                injected.add(spec.name());
            }
        }
        return injected;
    }

    /**
     * The requirement list of every behavior in {@code module} that is constructed here, keyed by
     * name. An injected behavior is not constructed — the Java side supplies it — so it is not a key
     * (it appears as a dependency of the definitions that name it).
     *
     * <p>{@code importedInjected} are the injection targets this module borrows; its own are read off
     * the module ({@link #injectedNames}).
     */
    public static Map<String, List<BehaviorRequirement>> of(Hir.Module module,
                                                            Set<String> importedInjected) {
        Set<String> injected = injectedNames(module, importedInjected);
        Map<String, Hir.BehaviorDef> byName = new HashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            byName.put(bd.name(), bd);
        }
        Map<String, Map<String, List<String>>> memo = new LinkedHashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            resolve(bd.name(), byName, injected, memo, new LinkedHashSet<>());
        }
        Map<String, List<BehaviorRequirement>> out = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, List<String>>> e : memo.entrySet()) {
            List<BehaviorRequirement> reqs = new ArrayList<>();
            for (Map.Entry<String, List<String>> r : e.getValue().entrySet()) {
                reqs.add(new BehaviorRequirement(r.getKey(), List.copyOf(r.getValue())));
            }
            out.put(e.getKey(), List.copyOf(reqs));
        }
        return out;
    }

    /** The dependency names of {@code requirements}, in the order they are taken — the injecting
     * constructor's parameter order. */
    public static List<String> names(List<BehaviorRequirement> requirements) {
        List<String> names = new ArrayList<>();
        for (BehaviorRequirement r : requirements) {
            names.add(r.dependency());
        }
        return names;
    }

    /**
     * The requirements of constructing {@code name}: dependency to requesters, in first-appearance
     * order. An injected behavior requires nothing to construct, and is reached as a dependency of
     * whatever names it rather than as a walk of its own.
     */
    private static Map<String, List<String>> resolve(String name, Map<String, Hir.BehaviorDef> byName,
                                                     Set<String> injected,
                                                     Map<String, Map<String, List<String>>> memo,
                                                     LinkedHashSet<String> inProgress) {
        if (injected.contains(name)) {
            return Map.of();
        }
        Map<String, List<String>> cached = memo.get(name);
        if (cached != null) {
            return cached;
        }
        Hir.BehaviorDef bd = byName.get(name);
        if (bd == null) {
            return Map.of();
        }
        if (!inProgress.add(name)) {
            String path = String.join(" >-> ", inProgress) + " >-> " + name;
            throw CompileException.of(Diagnostic.at(bd.pos())
                            .hint(new DeclarationMessage.ABehaviorDoesNotRecurse()).say(new DeclarationMessage.ABehaviorReachesItself(name, path)).build());
        }
        Map<String, List<String>> acc = new LinkedHashMap<>();
        switch (bd) {
            // An injection target is answered above, so a SpecBehavior here has a body: what it
            // requires is what it declared, in that order (spec §depends-on, §requirement-propagation).
            case Hir.SpecBehavior spec -> {
                for (Hir.Var req : spec.dependsOn()) {
                    // Reported where it is written; it names no requirement to propagate.
                    if (req.answered() instanceof Hir.Var.Denoting named) {
                        add(acc, named.bare(), name);
                    }
                }
            }
            case Hir.PipeBehavior pipe -> {
                for (Hir.Var stage : pipe.stages()) {
                    if (!(stage.answered() instanceof Hir.Var.Denoting named)) {
                        continue;   // it names no behavior, so it carries no requirement in
                    }
                    String s = named.bare();
                    if (injected.contains(s)) {
                        // the stage is the dependency: the composition holds it in a field and
                        // applies it there (spec §composition-with-requirements)
                        add(acc, s, name);
                        continue;
                    }
                    for (Map.Entry<String, List<String>> e
                            : resolve(s, byName, injected, memo, inProgress).entrySet()) {
                        for (String requester : e.getValue()) {
                            add(acc, e.getKey(), requester);
                        }
                    }
                }
            }
        }
        inProgress.remove(name);
        memo.put(name, acc);
        return acc;
    }

    /** Records {@code requester} as wanting {@code dependency}, keeping the dependency at the
     * position it first appeared and the requesters in the order they asked. */
    private static void add(Map<String, List<String>> acc, String dependency, String requester) {
        List<String> requesters = acc.computeIfAbsent(dependency, _ -> new ArrayList<>());
        if (!requesters.contains(requester)) {
            requesters.add(requester);
        }
    }
}
