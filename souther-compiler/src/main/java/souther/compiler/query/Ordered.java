package souther.compiler.query;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Unmodifiable copies that keep the order they were built in.
 *
 * <p>{@code Map.copyOf} and {@code Set.copyOf} do not, and order is load-bearing here. The modules
 * of a compilation are answered in the order their sources were given, and "the first error" means
 * the first one found in that order — so a set of module names in hash order silently changes which
 * file a batch compile sends the author to.
 */
final class Ordered {

    private Ordered() {}

    static <K, V> Map<K, V> map(Map<K, V> m) {
        return Collections.unmodifiableMap(new LinkedHashMap<>(m));
    }

    static <T> Set<T> set(Set<T> s) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(s));
    }
}
