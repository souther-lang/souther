package souther.bench;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Sources a measurement is taken against, carried in this module rather than read off disk, so a
 * number means the same thing on any machine and in CI.
 *
 * <p>A corpus is a directory of {@code .sou} files plus a {@code sources.txt} naming them in the
 * order they are handed over. The order is written out rather than discovered because a jar has no
 * directory to list, and because it is part of what is being measured: an attached example file is
 * read after the module it is attached to.
 *
 * <p>Every corpus must compile without an error. A language change that leaves one behind is caught
 * by {@link #check()} before any timing is reported — a compile that stops early is faster and would
 * read as an improvement.
 *
 * <p>Compiling is all that is asked of these. What the compiler <em>answers</em> about a model of
 * this size is held by the conformance corpus in {@code souther-compiler}, against documents written
 * down beside it. These two were one thing once, and asking both of one corpus pulls it two ways: a
 * corpus a number is compared against must not move, and a corpus an answer is checked against grows
 * whenever a rule is tightened. So what is here is chosen for its size and shape, and it is not
 * where a change of answer is found.
 */
public record Corpus(String name, List<String> sources, int lines) {

    private static final String ROOT = "/souther/bench/corpus/";

    /**
     * The corpora the compile measurements are taken against, largest first. The {@code runtime}
     * corpus is not among them: it is there to be run rather than to be compiled, and it is small
     * enough that timing its compile would say nothing.
     */
    public static List<Corpus> all() {
        return List.of(load("crm"), load("issuetracker"));
    }

    public static Corpus load(String name) {
        List<String> sources = new ArrayList<>();
        int lines = 0;
        for (String file : read(ROOT + name + "/sources.txt").lines().toList()) {
            String text = read(ROOT + name + "/" + file.strip());
            sources.add(text);
            lines += (int) text.lines().count();
        }
        return new Corpus(name, sources, lines);
    }

    private static String read(String resource) {
        try (InputStream in = Corpus.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("no such corpus resource: " + resource);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** One compile of this corpus, everything answered — what the timings time. */
    public Compilation compile() {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        compilation.answerEverything();
        compilation.classes();
        return compilation;
    }

    /**
     * Raises when this corpus no longer compiles, naming what it now says.
     *
     * <p>Takes the compile to check rather than making one, because the first compile in a process
     * is also the cold measurement and there is only one of those: compiling here to check would
     * warm the JIT and the number reported as cold would be a warm one.
     */
    public void check(Compilation compilation) {
        List<String> errors = new ArrayList<>();
        for (Map.Entry<SourceId, List<Diagnostic>> found
                : Located.diagnosticsOf(compilation.diagnostics()).entrySet()) {
            for (Diagnostic diagnostic : found.getValue()) {
                if (diagnostic.severity() == Severity.ERROR) {
                    errors.add(name + " source " + found.getKey() + ": " + diagnostic.code()
                            + " at " + diagnostic.primary());
                }
            }
        }
        if (!errors.isEmpty()) {
            throw new IllegalStateException("the `" + name + "` corpus no longer compiles:\n  "
                    + String.join("\n  ", errors));
        }
        if (compilation.classes().isEmpty()) {
            throw new IllegalStateException("the `" + name + "` corpus generated no classes");
        }
    }

    @Override
    public String toString() {
        return name;
    }
}
