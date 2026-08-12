package souther.compiler.core;

import java.util.ArrayList;
import java.util.List;

/**
 * How deep a {@link Core} is, for a test that has to say so about a tree the compiler built.
 *
 * <p>In this package because the walk over a {@code Core}'s children is, and counted without
 * recursion because what it is asked about is trees deep enough to be worth asking about.
 */
public final class Depth {

    private Depth() {}

    /** The longest way down {@code e}, counting {@code e} as one. */
    public static int of(Core e) {
        if (e == null) {
            return 0;
        }
        List<Core> nodes = new ArrayList<>();
        List<Integer> above = new ArrayList<>();
        nodes.add(e);
        above.add(0);
        int most = 0;
        while (!nodes.isEmpty()) {
            Core node = nodes.remove(nodes.size() - 1);
            int here = above.remove(above.size() - 1) + 1;
            most = Math.max(most, here);
            Core.forEachChild(node, child -> {
                if (child != null) {
                    nodes.add(child);
                    above.add(here);
                }
            });
        }
        return most;
    }
}
