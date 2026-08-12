package souther.compiler;

import souther.compiler.query.Compilation;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which subjects {@code souther examples} was asked to report on.
 *
 * <p>Resolving the names is a separate question from measuring what they name, and it is asked
 * first. A name that resolves to nothing is a fact about the command line, and a report is not
 * where a fact about the command line can be written down: a report says how much of a subject the
 * rows cover, and there is no subject to say it of. Filtering the report instead put the two on one
 * scale, and the empty selection came out reading like a measurement that went through and found no
 * gap — which is what {@code --strict} is entitled to accept.
 *
 * <p>The names are resolved together and not one at a time. What the command was given is a pair,
 * and two names that each name something and hold nothing between them select nothing.
 *
 * <p>Asked of what the sources declare rather than of what reached the report. A module that was
 * declared and could not be prepared shows up nowhere in the report, and refusing the name over it
 * would answer an absent measurement with a usage error.
 */
record Selection(String module, String behavior) {

    /** What a selection that names no subject is refused with: a catalog key and what fills it. */
    record Refusal(String key, Object... args) {}

    /**
     * Why this selection names no subject, or null where it names one.
     *
     * <p>Null is also the answer wherever the declarations themselves could not be read. Nothing
     * there says the name missed, and this only ever says that.
     */
    Refusal unresolved(Compilation compilation) {
        if (module == null && behavior == null) {
            return null;
        }
        List<String> declared = compilation.modules();
        if (declared.isEmpty()) {
            return null;
        }
        if (module != null && !declared.contains(module)) {
            return new Refusal("cli.examples.selector.module", module, named(declared));
        }
        if (behavior == null) {
            return null;
        }
        // A module the selection named is the only one searched; with none named, every module is,
        // because that is what the report would have shown the behavior from.
        Set<String> available = new LinkedHashSet<>();
        for (String name : module == null ? declared : List.of(module)) {
            Set<String> behaviors = compilation.declaredBehaviors(name);
            if (behaviors == null) {
                return null;
            }
            if (behaviors.contains(behavior)) {
                return null;
            }
            available.addAll(behaviors);
        }
        if (module != null) {
            return available.isEmpty()
                    ? new Refusal("cli.examples.selector.pair.none", module, behavior)
                    : new Refusal("cli.examples.selector.pair", module, behavior, named(available));
        }
        return available.isEmpty()
                ? new Refusal("cli.examples.selector.behavior.none", behavior)
                : new Refusal("cli.examples.selector.behavior", behavior, named(available));
    }

    /** The names a reader could have written instead, in the order the sources give them. */
    private static String named(java.util.Collection<String> names) {
        return String.join(", ", names);
    }
}
