package souther.compiler.coverage;

import java.util.ArrayList;
import java.util.List;

/**
 * The way down from a behavior's body to one place in it, as the slots it goes through.
 *
 * <p>What a place is, said in something two walks of one body can both arrive at. The object
 * standing at a place tells it from every other place while a walk holds the tree, and tells a
 * second walk nothing: the trees are equal and the objects are not the same, so an address made of
 * objects crosses nothing. This is made of what the source wrote — the right of a {@code &&}, the
 * second case of a {@code match} — so two walks of one body write the same one.
 *
 * <p>Of a body and not of a module. Which body it is of is said beside it ({@link NodeAddress}),
 * because a path is the same list of slots in every body shaped alike and means a different place
 * in each.
 *
 * <p>The empty path is the body itself.
 *
 * @param edges the slots gone through, outermost first
 */
public record CorePath(List<CoreStructure.Edge> edges) {

    /** The body itself, which is where every way down starts. Public because the constructor
     *  beside it is: this is that same value under the name for it. */
    public static final CorePath ROOT = new CorePath(List.of());

    public CorePath {
        if (edges == null) {
            throw new IllegalArgumentException("a way down is a way down through something");
        }
        edges = List.copyOf(edges);
    }

    /** This, then one more step. */
    CorePath then(CoreStructure.Edge edge) {
        List<CoreStructure.Edge> longer = new ArrayList<>(edges);
        longer.add(edge);
        return new CorePath(longer);
    }

    @Override
    public String toString() {
        if (edges.isEmpty()) {
            return "<body>";
        }
        StringBuilder out = new StringBuilder();
        for (CoreStructure.Edge edge : edges) {
            // A slot with nothing to say beyond which one it is says only that. The rest carry an
            // index, and it is the half of the answer.
            String said = edge.toString();
            out.append('/').append(said.endsWith("[]")
                    ? said.substring(0, said.length() - 2) : said);
        }
        return out.toString();
    }
}
