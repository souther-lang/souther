package souther.compiler.generated;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

/**
 * Which behaviors of a module this compile generated an implementation for.
 *
 * <p>The emitter's own decision, kept. A behavior written with a {@code let} body and a {@code >->}
 * composition are emitted as classes that apply them, and a behavior written with neither is emitted
 * as a base for something outside to supply — so what is here is the first kind, and what is not here
 * is a behavior this compile has nothing to run.
 *
 * <p>Read off what the emission put rather than worked out again from how the module is written.
 * Both answers agree today, and that they agree is a fact about one compile rather than a rule: the
 * second reader is what makes them able to disagree, and a reader deciding from the declarations
 * would go on saying a behavior has an implementation after the emitter stopped producing one for it.
 * Not read off the classes either — a name that is not in a loader is a class that could not be
 * reached, which is a failure, and reading membership for it would turn that failure into "nothing
 * applies this", which is not a failure at all.
 *
 * @param module     the module these behaviors are of
 * @param behaviors  the names it generated an implementation for
 */
public record GeneratedImplementations(String module, Set<String> behaviors) {

    public GeneratedImplementations {
        Objects.requireNonNull(module, "a manifest says which module it is of");
        Objects.requireNonNull(behaviors, "a manifest says what it implemented, or that it is empty");
        // In the order they were emitted. `Set.copyOf` would keep the members and not the order —
        // its iteration order is salted per JVM run — so anything that came to print or compare this
        // would read differently from one run to the next, for no change to the module.
        behaviors = Collections.unmodifiableSet(new LinkedHashSet<>(behaviors));
    }

    /** Whether this compile generated an implementation for {@code behavior}. */
    public boolean has(String behavior) {
        return behaviors.contains(behavior);
    }
}
