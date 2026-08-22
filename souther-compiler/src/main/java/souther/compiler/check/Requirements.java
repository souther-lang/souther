package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.types.ValueName;

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
     * Where {@code behavior}'s body comes from (spec §injected-behavior, §unwritten-behavior).
     *
     * <p>How the behavior is written, and nothing else. It answers no question about what a compile
     * emitted for it or about what a run can apply: those are settled where they happen, and a reader
     * asking one of them from here would be reading a declaration for a fact about a run.
     *
     * <p>Asked of the declaration and not of a name. What is being asked about is the behavior the
     * module wrote, so a caller hands it over rather than a spelling to look one up by — and there is
     * then no answer to give for a name that names no behavior.
     */
    public static BehaviorImplementation implementationOf(Hir.Module module,
                                                          Hir.BehaviorDef behavior) {
        return implementationOf(behavior, definedNames(module));
    }

    /**
     * The injection targets a module builds against: its own behaviors written with no body, and the imported
     * ones it names, whose base lives in the module that declares them (spec §injected-behavior,
     * §composition-with-requirements).
     *
     * <p>This is the rule that decides whether a name is something to inject or something to
     * construct, and both the emitter and the requirement walk below read it here so they cannot
     * disagree about one behavior.
     */
    public static Set<ValueName.Behavior> injectedNames(Hir.Module module,
                                                       Set<ValueName.Behavior> importedInjected) {
        Set<String> fns = definedNames(module);
        Set<ValueName.Behavior> injected = new LinkedHashSet<>(importedInjected);
        for (Hir.BehaviorDef bd : module.behaviors()) {
            if (implementationOf(bd, fns).isInjectionTarget()) {
                injected.add(new ValueName.Behavior(module.name(), bd.name()));
            }
        }
        return injected;
    }

    /** The behaviors of {@code module} Souther is to implement and nobody has, which is the state a
     *  model written example-first passes through (spec §unwritten-behavior). */
    public static Set<ValueName.Behavior> unwrittenNames(Hir.Module module) {
        Set<String> fns = definedNames(module);
        Set<ValueName.Behavior> unwritten = new LinkedHashSet<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            if (implementationOf(bd, fns) == BehaviorImplementation.UNIMPLEMENTED) {
                unwritten.add(new ValueName.Behavior(module.name(), bd.name()));
            }
        }
        return unwritten;
    }

    /** How this representation asks {@link BehaviorImplementation#of}: a {@code >->} composition is
     *  its own implementation, and a behavior stating only its specification has a body here when a
     *  {@code let} of its name does.
     *
     *  <p>Public so that a checker walking the same module with the definition names already in hand
     *  reads this rather than counting the {@code let}s again. */
    public static BehaviorImplementation implementationOf(Hir.BehaviorDef bd, Set<String> fns) {
        if (!(bd instanceof Hir.SpecBehavior spec)) {
            return BehaviorImplementation.IMPLEMENTED;
        }
        return BehaviorImplementation.of(fns.contains(spec.name()), !spec.dependsOn().isEmpty());
    }

    /** The names the module's definitions are written under. */
    private static Set<String> definedNames(Hir.Module module) {
        Set<String> fns = new LinkedHashSet<>();
        for (Hir.FnDef fn : module.fns()) {
            fns.add(fn.name());
        }
        return fns;
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
                                                            Set<ValueName.Behavior> importedInjected) {
        Set<ValueName.Behavior> injected = injectedNames(module, importedInjected);
        Map<ValueName.Behavior, Hir.BehaviorDef> byName = new HashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            byName.put(new ValueName.Behavior(module.name(), bd.name()), bd);
        }
        Map<ValueName.Behavior, Map<ValueName.Behavior, List<String>>> memo = new LinkedHashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            resolve(new ValueName.Behavior(module.name(), bd.name()), byName, injected, memo,
                    new LinkedHashSet<>());
        }
        Map<String, List<BehaviorRequirement>> out = new LinkedHashMap<>();
        for (Map.Entry<ValueName.Behavior, Map<ValueName.Behavior, List<String>>> e
                : memo.entrySet()) {
            List<BehaviorRequirement> reqs = new ArrayList<>();
            for (Map.Entry<ValueName.Behavior, List<String>> r : e.getValue().entrySet()) {
                reqs.add(new BehaviorRequirement(r.getKey(), List.copyOf(r.getValue())));
            }
            out.put(e.getKey().name(), List.copyOf(reqs));
        }
        return out;
    }

    /**
     * The names a {@code fake} writes for these dependencies, in the same order.
     *
     * <p>A row names one identifier (spec {@code [#fake]}), so this is the spelling side of the
     * question and not the identity: what a dependency is called is the declaring module's, and two
     * modules may call one thing the same. Held apart from {@link #names} so a reader asking which
     * declarations a construction wants cannot be handed spellings by mistake.
     */
    public static List<String> asWritten(List<BehaviorRequirement> requirements) {
        List<String> written = new ArrayList<>();
        for (BehaviorRequirement r : requirements) {
            written.add(r.dependency().name());
        }
        return written;
    }

    /** The dependency names of {@code requirements}, in the order they are taken — the injecting
     * constructor's parameter order. */
    public static List<ValueName.Behavior> names(List<BehaviorRequirement> requirements) {
        List<ValueName.Behavior> names = new ArrayList<>();
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
    private static Map<ValueName.Behavior, List<String>> resolve(
            ValueName.Behavior name, Map<ValueName.Behavior, Hir.BehaviorDef> byName,
            Set<ValueName.Behavior> injected,
            Map<ValueName.Behavior, Map<ValueName.Behavior, List<String>>> memo,
            LinkedHashSet<ValueName.Behavior> inProgress) {
        if (injected.contains(name)) {
            return Map.of();
        }
        Map<ValueName.Behavior, List<String>> cached = memo.get(name);
        if (cached != null) {
            return cached;
        }
        Hir.BehaviorDef bd = byName.get(name);
        if (bd == null) {
            return Map.of();
        }
        if (!inProgress.add(name)) {
            StringBuilder written = new StringBuilder();
            for (ValueName.Behavior each : inProgress) {
                written.append(each.name()).append(" >-> ");
            }
            String path = written + name.name();
            throw CompileException.of(Diagnostic.at(bd.pos())
                            .hint(new DeclarationMessage.ABehaviorDoesNotRecurse()).say(new DeclarationMessage.ABehaviorReachesItself(name.name(), path)).build());
        }
        Map<ValueName.Behavior, List<String>> acc = new LinkedHashMap<>();
        switch (bd) {
            // An injection target is answered above, so a SpecBehavior here has a body: what it
            // requires is what it declared, in that order (spec §depends-on, §requirement-propagation).
            case Hir.SpecBehavior spec -> {
                for (Hir.Var req : spec.dependsOn()) {
                    // Reported where it is written; it names no requirement to propagate.
                    ValueName.Behavior required = reaches(req);
                    if (required != null) {
                        add(acc, required, name.name());
                    }
                }
            }
            case Hir.PipeBehavior pipe -> {
                for (Hir.Var stage : pipe.stages()) {
                    ValueName.Behavior s = reaches(stage);
                    if (s == null) {
                        continue;   // it names no behavior, so it carries no requirement in
                    }
                    if (injected.contains(s)) {
                        // the stage is the dependency: the composition holds it in a field and
                        // applies it there (spec §composition-with-requirements)
                        add(acc, s, name.name());
                        continue;
                    }
                    for (Map.Entry<ValueName.Behavior, List<String>> e
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
    private static void add(Map<ValueName.Behavior, List<String>> acc,
                            ValueName.Behavior dependency, String requester) {
        List<String> requesters = acc.computeIfAbsent(dependency, _ -> new ArrayList<>());
        if (!requesters.contains(requester)) {
            requesters.add(requester);
        }
    }

    /**
     * The behavior {@code named} reaches, or null where resolution found none.
     *
     * <p>The declaration rather than the name it is written under, because a stage naming another
     * module's behavior and one naming this module's own may be written the same, and what a
     * construction requires is one of them.
     */
    private static ValueName.Behavior reaches(Hir.Var named) {
        return named.answered() != null
                && named.answered().denotes() instanceof ValueName.Behavior behavior
                ? behavior : null;
    }
}
