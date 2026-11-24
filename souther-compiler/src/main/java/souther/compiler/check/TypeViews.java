package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

/**
 * What each type is under the declarations a reading was made against, worked out once for each
 * type asked of it, whichever walk asks.
 *
 * <p>A fact about the declarations and not about a walk, a row or the reader that asked. Held by
 * any of those it was worked out again for each one, and a reading is walked for many rows by many
 * readers while the types it meets are a few; the source of the declarations is what all of them
 * are made from. What it holds is decided by the rest of the source, so a source is the same
 * source whichever of these it holds ({@link RuleReadingSource#equals}).
 */
public final class TypeViews {

    private final Map<Type, TypeView> kept = new ConcurrentHashMap<>();

    /**
     * The view of {@code type} kept, or the one {@code viewing} makes of it, kept from now on.
     *
     * <p>Made outside the map, since making it asks the declarations. Two readers asking at once
     * may both make one, and both are handed the one kept first.
     */
    public TypeView of(Type type, Function<Type, TypeView> viewing) {
        TypeView held = kept.get(type);
        if (held == null) {
            held = viewing.apply(type);
            TypeView first = kept.putIfAbsent(type, held);
            held = first != null ? first : held;
        }
        return held;
    }
}
