package souther.compiler.fmt;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Every Souther source this repository holds, read once.
 *
 * <p>What the formatter's repository-wide properties are held over. Two of them sweep it, and each
 * had found the files for itself by walking the reactor root and dropping whatever had
 * {@code target} in its path. That walk descended into the module directories, where surefire
 * writes the {@code .surefire-*} record naming which fork took which class — and writes it while
 * the tests are running. {@link Files#walk} reads an entry's attributes after it has listed the
 * parent, so an entry removed between the two ends the walk, and a filter downstream of the walk is
 * downstream of the attributes too. About one full build in seven failed here, on branches touching
 * nothing in this module.
 *
 * <p>{@link RepositoryLayout#southerSources} descends into {@code <module>/src} and nowhere else.
 * The record and {@code target/} are siblings of {@code src}, so they are not entries this can
 * reach rather than entries it drops, and there is no list of what a build writes to keep one name
 * behind. What the sweep costs is set by how much source there is: {@code .git} and the build's
 * output can grow without the formatter's tests noticing.
 *
 * <p>Read once because the sweeps read the same files repeatedly —
 * {@link ARowOfATableIsWrittenAtItsTablesColumnTest} asks for the corpus from three of its checks —
 * and the text of a file is the same answer each time. Only the text is held. What each check makes
 * of it is that check's own: a parse, a formatting, a report kept here would make two checks share a
 * result rather than each ask its own question.
 */
final class FormatterCorpus {

    private FormatterCorpus() {}

    private static final Map<Path, String> SOURCES = read();

    private static Map<Path, String> read() {
        RepositoryLayout repository = RepositoryLayout.ofWorkingDirectory();
        Map<Path, String> out = new LinkedHashMap<>();
        for (Path source : repository.southerSources()) {
            try {
                out.put(repository.root().relativize(source),
                        Files.readString(source, StandardCharsets.UTF_8));
            } catch (IOException unreadable) {
                throw new UncheckedIOException(unreadable);
            }
        }
        return Map.copyOf(out);
    }

    /**
     * Where each of them is, relative to the repository root, sorted.
     *
     * <p>Relative because a check that names one names it the way the repository does, and because
     * it is what a parameterized case is called: an absolute path would print whatever directory
     * the machine happened to check out into.
     */
    static List<Path> paths() {
        return SOURCES.keySet().stream().sorted().toList();
    }

    /** What is written in the one at {@code path}. */
    static String textOf(Path path) {
        String text = SOURCES.get(path);
        if (text == null) {
            throw new IllegalArgumentException(path + " is not a source this repository holds");
        }
        return text;
    }

    /** All of them, for a check that holds a property over the corpus rather than over a file. */
    static List<String> texts() {
        return paths().stream().map(FormatterCorpus::textOf).toList();
    }
}
