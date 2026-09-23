package souther.compiler;

import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.SourceContext;
import souther.compiler.diag.SourceContextResolver;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.SourceNames;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The sources one compile is handed, in order, and what a lone one with no {@code module} header is
 * called.
 *
 * <p>That is everything about the sources a compile depends on. Whether a source writes a header is
 * the parser's to read, and which other modules an import may reach is the {@link ModulePath}'s to
 * say — so a caller holding one file and a class path hands over one file and a class path, and
 * nothing here asks whether the file names itself or whether the path is empty. A source that writes
 * a header is called what it says whether or not a fallback name was given; the fallback is only
 * what a header-less source falls back to.
 *
 * <p>The fallback exists for a lone source and never for several. A module compiled beside others
 * can be reached by an import, and a module an import can reach has to say what it is called.
 *
 * <p>The ids the compile gives these sources are the ids {@link #contexts} and {@link #names} answer
 * for, taken from the same list, so a report is quoted from the source it was about and from no
 * other. An id that is none of these is unknown however many sources there are.
 */
public final class CompilationSources {

    /**
     * A source read from a file.
     *
     * @param path the file's path as the caller would show it to a person
     * @param text what the file says
     */
    public record SourceFile(String path, String text) {}

    private final List<String> texts;

    /** What to call each source in a report, in order; null throughout where none has a name. */
    private final List<String> shownAs;

    /** What a lone header-less source is called, or null where every source has to name itself. */
    private final String implicitModuleName;

    private CompilationSources(List<String> texts, List<String> shownAs, String implicitModuleName) {
        this.texts = List.copyOf(texts);
        this.shownAs = shownAs;
        this.implicitModuleName = implicitModuleName;
    }

    /** One source handed over as a string, with no file to name it after. */
    public static CompilationSources text(String text) {
        return new CompilationSources(List.of(text), Collections.nCopies(1, null),
                ImplicitModuleName.OF_A_TEXT);
    }

    /**
     * Sources linked as a module set, each of which has to write its own header — however many there
     * are.
     */
    public static CompilationSources modules(List<String> texts) {
        return new CompilationSources(texts, Collections.nCopies(texts.size(), null), null);
    }

    /**
     * Sources read from files. A lone one with no header is named after its file.
     *
     * <p>The file name is the last segment of the path on either separator, the way {@link
     * SourceNames} reads one, so a path a caller wrote by hand names the same file there and here.
     */
    public static CompilationSources files(List<SourceFile> files) {
        List<String> texts = new ArrayList<>(files.size());
        List<String> paths = new ArrayList<>(files.size());
        for (SourceFile file : files) {
            texts.add(file.text());
            paths.add(file.path());
        }
        String implicit = files.size() == 1
                ? ImplicitModuleName.ofFileName(fileNameOf(files.get(0).path())) : null;
        return new CompilationSources(texts, SourceNames.of(paths), implicit);
    }

    /** The texts, in the order the compile identifies them by. */
    public List<String> texts() {
        return texts;
    }

    /** A compilation of these sources, resolving an import that names none of them against
     *  {@code path}. */
    Compilation compilation(ModulePath path) {
        return implicitModuleName == null
                ? Compilation.ofSources(texts, path)
                : Compilation.ofSource(texts.get(0), implicitModuleName, path);
    }

    /**
     * What to quote for each source a diagnostic points into, under the id the compile gave it.
     *
     * <p>Built from the texts that were compiled rather than read again, so the line quoted is the
     * line the compile read. Laid out only for a source a diagnostic is about, since laying one out
     * parses it.
     */
    public SourceContextResolver contexts() {
        Map<SourceId, Integer> at = new LinkedHashMap<>();
        for (int i = 0; i < texts.size(); i++) {
            at.put(Compilation.idOfSourceIndex(i), i);
        }
        return SourceContextResolver.memoized(id -> {
            Integer i = at.get(id);
            return i == null ? null : new SourceContext(shownAs.get(i), texts.get(i),
                    SourceLayout.of(texts.get(i), id));
        });
    }

    /** What to call each source a report names — the same names {@link #contexts} quotes under. */
    public SourceNameResolver names() {
        Map<SourceId, String> byId = new LinkedHashMap<>();
        for (int i = 0; i < texts.size(); i++) {
            if (shownAs.get(i) != null) {
                byId.put(Compilation.idOfSourceIndex(i), shownAs.get(i));
            }
        }
        SourceNameResolver identity = SourceNameResolver.identity();
        return id -> byId.containsKey(id) ? byId.get(id) : identity.nameOf(id);
    }

    private static String fileNameOf(String path) {
        String[] segments = path.split("[/\\\\]");
        for (int i = segments.length - 1; i >= 0; i--) {
            if (!segments[i].isEmpty()) {
                return segments[i];
            }
        }
        return path;
    }
}
