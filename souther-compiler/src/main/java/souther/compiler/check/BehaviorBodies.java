package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where each behavior one module declares gets its body ({@link BehaviorImplementation}).
 *
 * <p>Classified once, where the module is read, and carried from there. A module compiled here is
 * classified from its declarations and its {@code let}s ({@link #fromSource}); a module read off
 * the path publishes no {@code let}, so its table is the one it published. A tree of either says
 * which behaviors there are and not which of these three each one is, so a reader holding a tree
 * asks this rather than counting the definitions beside it.
 *
 * <p>The rule for one behavior is private to {@link #fromSource}. What is handed out is a whole
 * module's table, so there is no way to classify a single behavior from a tree or from two flags,
 * and no second place that could come to hold the rule.
 *
 * <p>Asked by the declaration's identity and not by its spelling. A table is one module's, and a
 * behavior of another module written the same is a different behavior, so asking one module's table
 * about it is refused rather than answered with whatever that module declares under the name. A
 * behavior the module does not declare has no state to give, and is refused as well: an absent entry
 * read as an answer would be one of the three states chosen for it.
 *
 * @param module the module the table is of
 * @param states each behavior the module declares, by the name it is declared under
 */
public record BehaviorBodies(String module, Map<String, BehaviorImplementation> states) {

    public BehaviorBodies {
        states = Collections.unmodifiableMap(new LinkedHashMap<>(states));
    }

    /**
     * The table of a module read from source.
     *
     * <p>A {@code >->} composition is its own implementation. A behavior stating only its
     * specification has a body when a {@code let} of its name is written (spec §fn-declaration).
     * Without one it is Souther's to write and not written where it declares {@code depends on},
     * which takes its dependencies as arguments of a {@code let} (spec §depends-on,
     * §unwritten-behavior), and what Java supplies where it does not (spec §injected-behavior).
     */
    public static BehaviorBodies fromSource(Ast.Module module) {
        Set<String> defined = new LinkedHashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            defined.add(fn.name());
        }
        Map<String, BehaviorImplementation> states = new LinkedHashMap<>();
        for (Ast.BehaviorDef behavior : module.behaviors()) {
            states.put(behavior.name(), classified(behavior, defined));
        }
        return new BehaviorBodies(module.name(), states);
    }

    private static BehaviorImplementation classified(Ast.BehaviorDef behavior,
                                                     Set<String> defined) {
        if (!(behavior instanceof Ast.SpecBehavior spec) || defined.contains(spec.name())) {
            return BehaviorImplementation.IMPLEMENTED;
        }
        return spec.dependsOn().isEmpty()
                ? BehaviorImplementation.INJECTION_TARGET
                : BehaviorImplementation.UNIMPLEMENTED;
    }

    /**
     * Where {@code behavior}'s body comes from.
     *
     * @throws IllegalArgumentException where {@code behavior} is not one this module declares
     */
    public BehaviorImplementation of(ValueName.Behavior behavior) {
        if (!module.equals(behavior.module())) {
            throw new IllegalArgumentException("`" + behavior.module() + "." + behavior.name()
                    + "` is not declared by `" + module + "`");
        }
        BehaviorImplementation state = states.get(behavior.name());
        if (state == null) {
            throw new IllegalArgumentException("`" + module + "` declares no behavior `"
                    + behavior.name() + "`");
        }
        return state;
    }
}
