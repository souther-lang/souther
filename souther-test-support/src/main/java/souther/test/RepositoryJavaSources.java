package souther.test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * What this repository's main Java sources say, read once for a fork.
 *
 * <p>The checks that hold a rule over the compiler's own sources each ask for the same text of the
 * same files. Which files there are is {@link RepositoryLayout}'s answer; this holds what is in
 * them and nothing derived from it, so what each check searches for and finds stays its own.
 */
public final class RepositoryJavaSources {

    private static final RepositoryJavaSources FOR_THIS_FORK = new RepositoryJavaSources(
            RepositoryLayout.ofWorkingDirectory(), RepositoryJavaSources::readUtf8);

    private final RepositoryLayout repository;
    private final Function<Path, String> reading;
    private Map<Path, String> main;

    RepositoryJavaSources(RepositoryLayout repository, Function<Path, String> reading) {
        this.repository = repository;
        this.reading = reading;
    }

    /** The reading every check of this fork shares. */
    public static RepositoryJavaSources forThisFork() {
        return FOR_THIS_FORK;
    }

    /** The text of every main Java source, keyed by file, in the order {@link
     *  RepositoryLayout#mainJavaSources} names them. */
    public synchronized Map<Path, String> mainTexts() {
        if (main == null) {
            Map<Path, String> read = new LinkedHashMap<>();
            for (Path source : repository.mainJavaSources()) {
                read.put(source, reading.apply(source));
            }
            main = Collections.unmodifiableMap(read);
        }
        return main;
    }

    private static String readUtf8(Path source) {
        try {
            return Files.readString(source, StandardCharsets.UTF_8);
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
    }
}
