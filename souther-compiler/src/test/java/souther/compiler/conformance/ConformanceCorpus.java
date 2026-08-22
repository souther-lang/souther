package souther.compiler.conformance;

import souther.compiler.Compiler;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * A model written to be compiled here, and what this compiler answers about it.
 *
 * <p>Written rather than copied. A model taken from somewhere it was written for its own reasons
 * reaches the constructs that domain happened to need and no others, and it changes for reasons
 * that have nothing to do with this compiler. What is here is written against what the language
 * declares, and {@link AConformanceCorpusReachesEveryConstructTheLanguageDeclaresTest} says which
 * of those it does not reach yet.
 *
 * <p>A corpus is a directory of {@code .sou} files plus a {@code sources.txt} naming them in the
 * order they are handed over, and {@code corpora.txt} names the directories. Both are written out
 * rather than discovered because a jar has no directory to list, and because the order is part of
 * what is compiled: a file of {@code examples for} a module is read after the module it is
 * attached to.
 */
public record ConformanceCorpus(String name, List<String> files, List<String> sources) {

    static final String ROOT = "/souther/compiler/conformance/";

    /** Where these resources are written, for the one caller that writes rather than reads them. */
    static final Path SOURCE_DIR = Path.of("src", "test", "resources", "souther", "compiler",
            "conformance");

    public static List<ConformanceCorpus> all() {
        List<ConformanceCorpus> out = new ArrayList<>();
        for (String name : read(ROOT + "corpora.txt").lines().toList()) {
            if (!name.isBlank()) {
                out.add(load(name.strip()));
            }
        }
        return out;
    }

    public static ConformanceCorpus load(String name) {
        List<String> files = new ArrayList<>();
        List<String> sources = new ArrayList<>();
        for (String file : read(ROOT + name + "/sources.txt").lines().toList()) {
            if (!file.isBlank()) {
                files.add(file.strip());
                sources.add(read(ROOT + name + "/" + file.strip()));
            }
        }
        return new ConformanceCorpus(name, files, sources);
    }

    /**
     * What to call each source in a rendering of this corpus.
     *
     * <p>The file it was written in. A compile names its sources by the position they were handed
     * over at, which is right for saying that two reasons are about one source and says nothing to
     * a reader of a checked-in document — and a document naming a position would also change every
     * time a file was inserted before another.
     */
    public SourceNameResolver names() {
        return id -> {
            for (int i = 0; i < files.size(); i++) {
                if (Compilation.idOfSourceIndex(i).equals(id)) {
                    return files.get(i);
                }
            }
            return id == null ? null : id.value();
        };
    }

    private static String read(String resource) {
        try (InputStream in = ConformanceCorpus.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("no such conformance resource: " + resource);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * This corpus analysed, with everything the report needs measured and every warning collected.
     *
     * <p>The analysing entry point rather than the compiling one. What the rows cover is answered
     * from whatever was observed, and an entry point that raises at the first error would make
     * every failure here a report about the one thing that stopped it.
     */
    public Analysed analyse() {
        List<Located> warnings = new ArrayList<>();
        Compilation compilation = Compiler.analyzedModules(sources, ModulePath.EMPTY, warnings,
                Adequacy.Asked.fullReport());
        return new Analysed(this, compilation, compilation.errors(), warnings);
    }

    @Override
    public String toString() {
        return name;
    }

    /** One analysis of one corpus: what it came to, and everything it said getting there. */
    public record Analysed(ConformanceCorpus corpus, Compilation compilation,
                           List<Located> errors, List<Located> warnings) {

        /** Everything said about this corpus, errors before warnings, as the report writes them. */
        public List<Located> said() {
            List<Located> out = new ArrayList<>(errors);
            out.addAll(warnings);
            return out;
        }
    }
}
