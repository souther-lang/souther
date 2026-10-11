package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ReachName;

import java.util.Map;

/**
 * What each value the tree an analysis reads builds means, held once.
 *
 * <p>The tree holds where a value is built ({@link Core.MaterialisedValue}) and not what it comes
 * to, so a reader that needs the meaning asks here. A value takes no parameters and names nothing
 * of the region that builds it, so its meaning is the same wherever it is built and is worked out
 * once — which is what keeps a chain of values from being read once per way through it.
 *
 * <p>Asked by whoever has met a build and needs what it stands for, and only that: which of the
 * readings of a build's place is wanted is theirs, and this says nothing of it.
 *
 * @param templates the meaning of each value, by the name the module reaches it by
 */
public record ValueTemplates(Map<ReachName.Declaration, Core> templates) {

    /** No value is built anywhere, which is what a tree that runs holds. */
    public static final ValueTemplates NONE = new ValueTemplates(Map.of());

    public ValueTemplates {
        templates = Map.copyOf(templates);
    }

    /**
     * The meaning of the value {@code e} is a build of, or null where it is a build of none this
     * holds.
     *
     * <p>A build is written two ways, one per representation: a reference in the tree an analysis
     * reads ({@link Core.MaterialisedValue}), and a call of the value's method in the tree that runs
     * ({@link Core.Reached.OfValue}). Both name the value by the declaration the module reaches it
     * by, and both are answered by the one template held under that name — so which tree a reader
     * walks does not decide which definition a value has. Whatever a call of a value's method is
     * handed is how the method gets the values it names, and the template names them for itself, so
     * what was handed decides nothing here.
     *
     * <p>Which definition, and nothing more. A call reaching any other kind of declaration — a
     * helper, a behavior, a value another module publishes, an operation of the library — is no
     * build of a value held here and answers null, as a value's method answers null where no
     * template of it is held. And a template is what the value is defined as, not what is known of
     * it where it is built: whether that definition is a constant is the reader's question, asked
     * of the template in the reader's own environment.
     *
     * <p>The template is the one held, never a copy: every build of a value is answered with the
     * same tree.
     *
     * @throws IllegalStateException where {@code e} is a reference to a value with no template here,
     *                               which is a tree read against the templates of another
     */
    public Core builtBy(Core e) {
        // The type a value stands as says nothing about which value it is.
        return switch (Core.withoutStanding(e)) {
            case Core.MaterialisedValue build -> bodyOf(build);
            case Core.Call call when call.fn() instanceof Core.Reached.OfValue value ->
                    templates.get(value.name());
            case null, default -> null;
        };
    }

    /**
     * The meaning of the value {@code build} stands for.
     *
     * @throws IllegalStateException where none was held, which is a tree read against the templates
     *                               of another
     */
    public Core bodyOf(Core.MaterialisedValue build) {
        Core body = templates.get(build.value());
        if (body == null) {
            throw new IllegalStateException("a build of " + build.value()
                    + " has no template here, so this tree is read against another's");
        }
        return body;
    }
}
