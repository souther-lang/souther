package souther.compiler.meta;

import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What a behavior requires injected, as {@link ModuleMetadata} writes it and {@link ModuleReadback}
 * reads it: one entry per dependency, in the order the constructor takes them.
 *
 * <p>An entry is the declaring module and the name, each written with its length in front of it and
 * read by counting. A module name holds dots and a behavior name may be spelled like one, so an entry
 * split at a separator would be answering which behavior it is from how the two happen to be spelled.
 */
final class PublishedRequirements {

    private PublishedRequirements() {}

    static List<String> written(List<ValueName.Behavior> dependencies) {
        List<String> out = new ArrayList<>(dependencies.size());
        for (ValueName.Behavior dependency : dependencies) {
            out.add(counted(dependency.module()) + counted(dependency.name()));
        }
        return out;
    }

    /** The dependencies {@code entries} name, or null where one of them is not an entry this writes. */
    static List<ValueName.Behavior> read(List<String> entries) {
        List<ValueName.Behavior> out = new ArrayList<>(entries.size());
        for (String entry : entries) {
            int[] at = {0};
            String module = counted(entry, at);
            String name = module == null ? null : counted(entry, at);
            if (name == null || at[0] != entry.length()) {
                return null;
            }
            out.add(new ValueName.Behavior(module, name));
        }
        return List.copyOf(out);
    }

    static String counted(String text) {
        return text.length() + ":" + text;
    }

    /** The counted text starting at {@code at[0]}, moving {@code at[0]} past it; null where there is
     *  none there. */
    static String counted(String entry, int[] at) {
        int from = at[0];
        int colon = from;
        while (colon < entry.length() && Character.isDigit(entry.charAt(colon))
                && entry.charAt(colon) < 128) {
            colon++;
        }
        if (colon == from || colon - from > 9 || colon >= entry.length()
                || entry.charAt(colon) != ':') {
            return null;
        }
        int length = Integer.parseInt(entry.substring(from, colon));
        int start = colon + 1;
        if (length <= 0 || start + length > entry.length()) {
            return null;
        }
        at[0] = start + length;
        return entry.substring(start, start + length);
    }
}
