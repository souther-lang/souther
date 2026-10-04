package souther.lsp.analysis;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * An immutable snapshot of a workspace: its Souther sources keyed by document URI, and the compiled
 * modules an import that names none of them is resolved against. The {@link souther.lsp.LspServer}
 * builds it by scanning the workspace roots and overlaying the text of any open buffer; the
 * {@link Analyzer} reads it to resolve names and diagnostics across the whole module set, the way
 * the batch compiler does.
 *
 * <p>The modules on the path are here and not remembered by whoever compiles, because a compile
 * reads both and both have to be one reading of the workspace. A request answered between a change
 * and the next diagnose would otherwise read the sources as they now are against the path as it was.
 */
public final class ModuleGraph {

    private final Map<String, String> sources;
    private final ModulesOnThePath onThePath;
    private final Set<String> open;

    private ModuleGraph(Map<String, String> sources, ModulesOnThePath onThePath,
                        Set<String> open) {
        this.sources = sources;
        this.onThePath = onThePath;
        this.open = open;
    }

    /** A graph over the given {@code uri -> source text} map, with nothing built beside it, every
     *  source of it open in the editor. */
    public static ModuleGraph of(Map<String, String> sources) {
        return of(sources, ModulesOnThePath.NONE);
    }

    /** A graph over the given sources, resolving what they import from elsewhere against
     *  {@code onThePath}, every source of it open in the editor. */
    public static ModuleGraph of(Map<String, String> sources, ModulesOnThePath onThePath) {
        return of(sources, onThePath, sources.keySet());
    }

    /** The same, with only the sources {@code open} names open in the editor and the rest read
     *  from where they are kept. */
    public static ModuleGraph of(Map<String, String> sources, ModulesOnThePath onThePath,
                                 Set<String> open) {
        return new ModuleGraph(new LinkedHashMap<>(sources), onThePath, Set.copyOf(open));
    }

    /** A graph over a map its caller made for it and hands over, so it is not copied again: the
     *  caller keeps no reference to it, and nothing else can change it. */
    static ModuleGraph over(LinkedHashMap<String, String> handedOver, ModulesOnThePath onThePath,
                            Set<String> open) {
        return new ModuleGraph(handedOver, onThePath, Set.copyOf(open));
    }

    /** Whether the editor has the document at {@code uri} open, rather than it being read from
     *  disk. */
    public boolean isOpen(String uri) {
        return open.contains(uri);
    }

    /** Every document URI in the workspace. */
    public Set<String> uris() {
        return sources.keySet();
    }

    /** The source text of {@code uri}, or {@code null} if it is not in the graph. */
    public String text(String uri) {
        return sources.get(uri);
    }

    /** What the projects beside this one have already built, as this snapshot read it. */
    public ModulesOnThePath onThePath() {
        return onThePath;
    }
}
