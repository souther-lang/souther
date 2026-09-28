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
