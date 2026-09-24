package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where each behavior one module declares gets its body ({@link BehaviorImplementation}).
 *
 * <p>Classified once, where the module is read, and carried from there. A module compiled here is
 * classified from its declarations and its {@code let}s; a module read off the path publishes no
 * {@code let}, so its table is the one it published. A tree of either says which behaviors there are
 * and not which of these three each one is, so a reader holding a tree asks this rather than
 * counting the definitions beside it.
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
