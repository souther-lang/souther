package souther.lsp.analysis;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Abandonment;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * The Souther sources of a workspace: the {@code .sou} files under the roots the client announced at
 * initialize or has added since, with any open editor buffer overlaid on the on-disk text. A {@link #snapshot} is the
 * immutable {@link ModuleGraph} the {@link Analyzer} resolves diagnostics and names against — the
 * same module set the batch compiler would link.
 */
public final class Workspace {

    private static final String SUFFIX = ".sou";

    private final Set<Path> roots = new LinkedHashSet<>();

    /** What stops a walk of the workspace short. Reading the files under a root is not a question put
     * to a store, so what abandons the compile does not reach it; this is where it is asked, at every
     * path a walk reaches rather than at the ones it was looking for. */
    private Abandonment abandonment = Abandonment.NEVER;

    /** What makes reading this workspace stop short of an answer. */
    public void abandonWhen(Abandonment abandonment) {
        this.abandonment = abandonment;
    }

    /** The last on-disk scan ({@code uri -> text}), or {@code null} when it must be re-read. Cached so
     * an edit to an open buffer does not re-walk and re-read the whole workspace on every keystroke. */
    private Map<String, String> diskScan;

    /**
     * The last walk for class output, or {@code null} when it must be walked again. Cached for the
     * reason the disk scan is.
     *
     * <p>What it holds is which directories there are, not what is in them: a class is read from its
     * directory when it is asked for, and a directory that has gone reads as holding nothing. So it
     * goes stale only when a class output appears, which is what {@link #classOutputGlobs()} asks
     * the client to report.
     */
    private ModulePath modulePath;

    /** Records the workspace roots from their {@code file://} URIs; non-file URIs are ignored. */
    public void setRoots(List<String> rootUris) {
        diskScan = null;   // the set of files to scan changed
        modulePath = null;
        roots.clear();
        for (String uri : rootUris) {
            rootOf(uri).ifPresent(roots::add);
        }
    }

    /**
     * Takes {@code removed} out of the roots and then puts {@code added} in, as the client reports
     * folders leaving and joining the workspace.
     *
     * <p>Whether the roots changed is asked of the set before and after, not of each step: a folder
     * named on both sides leaves the set as it was, and the disk scan still describes it.
     *
     * @return whether the set of roots is now different
     */
    public boolean changeRoots(List<String> added, List<String> removed) {
        Set<Path> before = Set.copyOf(roots);
        for (String uri : removed) {
            rootOf(uri).ifPresent(roots::remove);
        }
        for (String uri : added) {
            rootOf(uri).ifPresent(roots::add);
        }
        boolean changed = !roots.equals(before);
        if (changed) {
            diskScan = null;
            modulePath = null;
        }
        return changed;
    }

    /** The directory a root's {@code file://} URI names, or empty for any other URI. */
    private static Optional<Path> rootOf(String uri) {
        if (uri == null) {
            return Optional.empty();
        }
        try {
            URI parsed = URI.create(uri);
            return "file".equals(parsed.getScheme()) ? Optional.of(Path.of(parsed)) : Optional.empty();
        } catch (IllegalArgumentException _) {
            return Optional.empty();   // a malformed root URI is skipped rather than failing the session
        }
    }

    /**
     * The current module graph: every {@code .sou} file under the roots, read from disk, with the
     * given {@code openBuffers} (keyed by document URI) overlaid — an open buffer's unsaved text wins,
     * and an open document outside the roots is still included.
     */
    public ModuleGraph snapshot(Map<String, String> openBuffers) {
        if (diskScan == null) {
            diskScan = scanDisk();
        }
        Map<String, String> sources = new LinkedHashMap<>(diskScan);
        sources.putAll(openBuffers);
        return ModuleGraph.of(sources);
    }

    /**
     * Drops what the files at {@code uris} changed, as the client reports them
     * ({@code workspace/didChangeWatchedFiles}).
     *
     * <p>The client reports what {@link #sourceGlob()} and {@link #classOutputGlobs()} asked for and
     * nothing else, so a file that is not a source is under a class output: a source changes the
     * scan and anything else the module path.
     */
    public void filesChanged(List<String> uris) {
        for (String uri : uris) {
            if (uri.endsWith(SUFFIX)) {
                diskScan = null;
            } else {
                modulePath = null;
            }
        }
    }

    /** Drops everything read from disk, for a report of changes that could not be read. */
    public void markChanged() {
        diskScan = null;
        modulePath = null;
    }

    /** The files a client is asked to report so the disk scan is dropped when one changes. */
    public static String sourceGlob() {
        return "**/*" + SUFFIX;
    }

    /**
     * The class outputs a client is asked to report, the directory and what is under it, so the
     * module path is dropped when one appears.
     */
    public static List<String> classOutputGlobs() {
        List<String> globs = new ArrayList<>();
        for (Path output : CLASS_OUTPUTS) {
            List<String> names = new ArrayList<>();
            output.forEach(name -> names.add(name.toString()));
            String written = String.join("/", names);
            globs.add("**/" + written);
            globs.add("**/" + written + "/**");
        }
        return List.copyOf(globs);
    }

    /**
     * Where a module the workspace imports but does not contain is looked for: the class output of
     * every project under the roots. A project that has been built once is then importable in the
     * editor, so an import the build resolves is not underlined here as unknown.
     *
     * <p>This finds what has been built beside the source being edited. A dependency that exists only
     * as a jar in the local repository is not found — knowing about that means reading the build,
     * which the language server does not do.
     */
    public ModulePath modulePath() {
        if (modulePath == null) {
            modulePath = walkForClassOutput();
        }
        return modulePath;
    }

    private ModulePath walkForClassOutput() {
        List<Path> outputs = new ArrayList<>();
        for (Path root : roots) {
            if (!Files.isDirectory(root)) {
                continue;
            }
            try (Stream<Path> walk = Files.walk(root, CLASS_OUTPUT_DEPTH)) {
                // Asked of every path the walk reaches, and not of the ones that turn out to be
                // what is wanted. What costs time is the walk, and a root with no class output in
                // it is a root this would read to the end after being told to stop.
                walk.forEach(path -> {
                    abandonment.stopIfAsked();
                    if (Files.isDirectory(path) && isClassOutput(path)) {
                        outputs.add(path);
                    }
                });
            } catch (IOException _) {
                // a root that cannot be walked contributes nothing; the workspace still works
            }
        }
        return outputs.isEmpty() ? ModulePath.EMPTY : ModulePath.ofClassPath(outputs);
    }

    /** Where a project's build writes its classes, under the project: Maven's and Gradle's. */
    private static final List<Path> CLASS_OUTPUTS = List.of(
            Path.of("target", "classes"), Path.of("build", "classes", "java", "main"));

    /** How many directories down from a root a project may be: the root itself, a project in it,
     *  or a project in a directory that groups several. */
    private static final int PROJECT_DEPTH = 2;

    /** How far under a root a class output is looked for: as deep as the deepest layout goes under
     *  the deepest project. */
    private static final int CLASS_OUTPUT_DEPTH = PROJECT_DEPTH
            + CLASS_OUTPUTS.stream().mapToInt(Path::getNameCount).max().orElseThrow();

    private static boolean isClassOutput(Path dir) {
        return CLASS_OUTPUTS.stream().anyMatch(dir::endsWith);
    }

    private Map<String, String> scanDisk() {
        Map<String, String> sources = new LinkedHashMap<>();
        for (Path root : roots) {
            if (!Files.isDirectory(root)) {
                continue;
            }
            try (Stream<Path> walk = Files.walk(root)) {
                // Every path, as above: the walk is what a workspace of a hundred thousand files
                // spends its time on, and how many of them end in `.sou` says nothing about that.
                walk.forEach(path -> {
                    abandonment.stopIfAsked();
                    if (Files.isRegularFile(path) && path.getFileName().toString().endsWith(SUFFIX)) {
                        sources.put(path.toUri().toString(), readOrEmpty(path));
                    }
                });
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        return sources;
    }

    private static String readOrEmpty(Path p) {
        try {
            return Files.readString(p);
        } catch (IOException _) {
            return "";   // a file that cannot be read contributes nothing, but never crashes the scan
        }
    }
}
