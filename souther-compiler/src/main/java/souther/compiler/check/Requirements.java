package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.Diagnostic;

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
 * <p>A behavior with a body requires what it declares it depends on (spec 12.6, 13.6). A
 * composition requires the union of its stages', transitively: a stage with a body is constructed by
 * the composition and handed the fields it needs, so what has to be injected are the injected
 * behaviors the stages reach (14.3). A stage that is itself injected is one of those.
 *
 * <p>The order is first appearance, walking the stages left to right. That order is the injecting
 * constructor's parameter order, so it is the order fakes are passed in at an example as well —
 * which is why this is answered once and read by both. Two computations that agreed today would
 * bind a fake to the wrong dependency the first time one of them changed.
 */
public final class Requirements {

    private Requirements() {}

    /**
     * The injection targets a module builds against: its own behaviors written with no body, and the
     * imported ones it names, whose base lives in the module that declares them (spec 13.2, 14.3).
     *
     * <p>This is the rule that decides whether a name is something to inject or something to
     * construct, and both the emitter and the requirement walk below read it here so they cannot
     * disagree about one behavior.
     */
    public static Set<String> injectedNames(Ast.Module module, Set<String> importedInjected) {
        Set<String> fns = new LinkedHashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            fns.add(fn.name());
        }
        Set<String> injected = new LinkedHashSet<>(importedInjected);
        for (Ast.BehaviorDef bd : module.behaviors()) {
            if (bd instanceof Ast.SpecBehavior spec && !fns.contains(spec.name())) {
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
    public static Map<String, List<BehaviorRequirement>> of(Ast.Module module,
                                                            Set<String> importedInjected) {
        Set<String> injected = injectedNames(module, importedInjected);
        Map<String, Ast.BehaviorDef> byName = new HashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            byName.put(bd.name(), bd);
        }
        Map<String, Map<String, List<String>>> memo = new LinkedHashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
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
    private static Map<String, List<String>> resolve(String name, Map<String, Ast.BehaviorDef> byName,
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
        Ast.BehaviorDef bd = byName.get(name);
        if (bd == null) {
            return Map.of();
        }
        if (!inProgress.add(name)) {
            String path = String.join(" >-> ", inProgress) + " >-> " + name;
            throw CompileException.of(
                    Diagnostic.of(DiagnosticCode.E1608, "e1608.msg").at(bd.pos())
                            .args(name, path).hint("e1608.hint").build(),
                    "cyclic behavior composition: " + path);
        }
        Map<String, List<String>> acc = new LinkedHashMap<>();
        switch (bd) {
            // An injection target is answered above, so a SpecBehavior here has a body: what it
            // requires is what it declared, in that order (spec 12.6, 13.6).
            case Ast.SpecBehavior spec -> {
                for (Ast.Var req : spec.dependsOn()) {
                    add(acc, req.bare(), name);
                }
            }
            case Ast.PipeBehavior pipe -> {
                for (Ast.Var stage : pipe.stages()) {
                    String s = stage.bare();
                    if (injected.contains(s)) {
                        // the stage is the dependency: the composition holds it in a field and
                        // applies it there (spec 14.3)
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
