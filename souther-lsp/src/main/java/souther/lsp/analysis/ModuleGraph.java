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

    private ModuleGraph(Map<String, String> sources, ModulesOnThePath onThePath) {
        this.sources = sources;
        this.onThePath = onThePath;
    }

    /** A graph over the given {@code uri -> source text} map, with nothing built beside it. */
    public static ModuleGraph of(Map<String, String> sources) {
        return of(sources, ModulesOnThePath.NONE);
    }

    /** A graph over the given sources, resolving what they import from elsewhere against
     *  {@code onThePath}. */
    public static ModuleGraph of(Map<String, String> sources, ModulesOnThePath onThePath) {
        return new ModuleGraph(new LinkedHashMap<>(sources), onThePath);
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
