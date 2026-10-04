package souther.lsp.analysis;

import java.util.Collections;
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
 * <p>Nothing that reads a graph can change it, and nothing that built it keeps a way to. A graph
 * copies what it is made from, once, and hands out only views that refuse a change, so a reader that
 * holds a graph between two requests, or compares two of them by identity, is reading the workspace
 * as it was when the graph was made.
 *
 * <p>The modules on the path are here and not remembered by whoever compiles, because a compile
 * reads both and both have to be one reading of the workspace. A request answered between a change
 * and the next diagnose would otherwise read the sources as they now are against the path as it was.
 */
public final class ModuleGraph {

    private final Map<String, String> sources;
    private final ModulesOnThePath onThePath;
    private final Set<String> open;

    private ModuleGraph(Map<String, String> sources, ModulesOnThePath onThePath, Set<String> open) {
        this.sources = Collections.unmodifiableMap(sources);
        this.onThePath = onThePath;
        this.open = Set.copyOf(open);
    }

    /** A graph over the given {@code uri -> source text} map, with nothing built beside it, every
     *  source of it open in the editor. */
    public static ModuleGraph of(Map<String, String> sources) {
        return of(sources, ModulesOnThePath.NONE);
    }

    /** A graph over the given sources, resolving what they import from elsewhere against
     *  {@code onThePath}, every source of it open in the editor. */
    public static ModuleGraph of(Map<String, String> sources, ModulesOnThePath onThePath) {
        return new ModuleGraph(new LinkedHashMap<>(sources), onThePath, sources.keySet());
    }

    /**
     * A graph over what is kept on disk with the text of the editor's open buffers over it.
     *
     * <p>The sources are made here, once, from the two, and the open documents are what the buffers
     * name, so a source cannot be called open without being in the graph, and nobody outside holds
     * the map the sources are kept in.
     */
    static ModuleGraph overlaying(Map<String, String> onDisk, Map<String, String> openBuffers,
                                  ModulesOnThePath onThePath) {
        Map<String, String> sources = new LinkedHashMap<>(onDisk);
        sources.putAll(openBuffers);
        return new ModuleGraph(sources, onThePath, openBuffers.keySet());
    }

    /** Whether the editor has the document at {@code uri} open, rather than it being read from
     *  disk. */
    public boolean isOpen(String uri) {
        return open.contains(uri);
    }

    /** Every document URI in the workspace. A view that refuses a change. */
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
