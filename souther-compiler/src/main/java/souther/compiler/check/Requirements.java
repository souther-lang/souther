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
import java.util.SequencedSet;
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
     * Whether this behavior is a {@code >->} composition, which is its own implementation.
     *
     * <p>A composition has no positions, no lines and no arms of its own — its stages have them and
     * are measured there — so it is the one thing a measure of a behavior may answer inapplicable
     * about without reading any further. That makes it a claim about what is written, and a claim
     * about what is written is read from the declarations: a measure that took a behavior's absence
     * from an answer for it would be making the claim out of a derivation that did not come back.
     */
    public static boolean isComposition(Hir.BehaviorDef bd) {
        return !(bd instanceof Hir.SpecBehavior);
    }

    /**
     * The requirement list of every behavior in {@code module} that is constructed here, keyed by
     * name. An injected behavior is not constructed — the Java side supplies it — so it is not a key
     * (it appears as a dependency of the definitions that name it).
     *
     * <p>{@code injected} is every injection target this module builds against, its own and the ones
     * it borrows. Handed in and not read off {@code module}: which behaviors Java supplies is decided
     * where the module is classified, and this walk only follows what that says.
     *
     * <p>{@code foreignStages} is what each stage declared in another module requires, as the module
     * that declares it answered: one entry for every behavior {@link #foreignStages} names. The stage
     * is the requester of what it brings in. What asked for a dependency inside it is that module's
     * business, and one read off the path does not carry it at all.
     */
    public static Map<String, List<BehaviorRequirement>> of(
            Hir.Module module, Set<ValueName.Behavior> injected,
            Map<ValueName.Behavior, List<ValueName.Behavior>> foreignStages) {
        Map<ValueName.Behavior, Hir.BehaviorDef> byName = new HashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            byName.put(new ValueName.Behavior(module.name(), bd.name()), bd);
        }
        Map<ValueName.Behavior, Map<ValueName.Behavior, List<String>>> memo = new LinkedHashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            resolve(new ValueName.Behavior(module.name(), bd.name()), byName, foreignStages,
                    injected, memo, new LinkedHashSet<>());
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
     * The stages of {@code module}'s compositions that another module declares and does not leave to
     * Java: the behaviors whose requirement set {@link #of} has to be handed, because it is the
     * declaring module's to work out. An injected one is not here — it is the dependency itself.
     */
    public static Set<ValueName.Behavior> foreignStages(Hir.Module module,
                                                        Set<ValueName.Behavior> importedInjected) {
        Set<ValueName.Behavior> foreign = new LinkedHashSet<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            if (bd instanceof Hir.PipeBehavior pipe
                    && pipe.composition() instanceof Hir.Composition.Stages written) {
                for (Hir.Var stage : written.stages()) {
                    ValueName.Behavior s = reaches(stage);
                    if (s != null && !s.module().equals(module.name())
                            && !importedInjected.contains(s)) {
                        foreign.add(s);
                    }
                }
            }
        }
        return foreign;
    }

    /**
     * How a stand-in written in {@code module} names {@code dependency}.
     *
     * <p>The spelling side of the question, and only that: which behavior is meant is
     * {@link #names}, and this turns one of those into characters someone can type. Bare for a
     * behavior this module declares, and qualified through the declaring module otherwise — a
     * behavior is reachable through its module whether or not an import brought its bare spelling in
     * (ADR-0058), so the qualified form is one that can always be written. An author holding an
     * alias may write that instead; both name the same behavior, which is why what a fake means is
     * settled by resolving it and not by matching what this returns.
     *
     * <p>One rule, because a hint that shows what to type and a skeleton that types it would
     * otherwise be two answers to the same question.
     */
    public static String writtenIn(String module, ValueName.Behavior dependency) {
        return dependency.module().equals(module)
                ? dependency.name() : dependency.module() + "." + dependency.name();
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
            Map<ValueName.Behavior, List<ValueName.Behavior>> foreignStages,
            Set<ValueName.Behavior> injected,
            Map<ValueName.Behavior, Map<ValueName.Behavior, List<String>>> memo,
            SequencedSet<ValueName.Behavior> inProgress) {
        if (injected.contains(name)) {
            return Map.of();
        }
        Map<ValueName.Behavior, List<String>> cached = memo.get(name);
        if (cached != null) {
            return cached;
        }
        Hir.BehaviorDef bd = byName.get(name);
        if (bd == null) {
            // Declared elsewhere, so what it requires is what its module answered. Not having that
            // answer is not the same as it requiring nothing: a stage built without what it needs
            // is a class that does not link.
            List<ValueName.Behavior> declared = foreignStages.get(name);
            if (declared == null) {
                throw new IllegalStateException("`" + name.module() + "." + name.name()
                        + "` is a stage declared elsewhere, and what it requires was not handed in");
            }
            Map<ValueName.Behavior, List<String>> brought = new LinkedHashMap<>();
            for (ValueName.Behavior dependency : declared) {
                add(brought, dependency, name.name());
            }
            return brought;
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
                List<Hir.Var> stages = switch (pipe.composition()) {
                    case Hir.Composition.Stages written -> written.stages();
                    // A module read off the path is answered from what it published, and its
                    // compositions are never walked for it.
                    case Hir.Composition.Elsewhere _ -> throw new IllegalStateException("`"
                            + name.module() + "." + name.name() + "` was read off the path and has"
                            + " no stages to walk");
                };
                for (Hir.Var stage : stages) {
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
                            : resolve(s, byName, foreignStages, injected, memo, inProgress)
                                    .entrySet()) {
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
