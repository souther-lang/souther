package souther.compiler.partition;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * The models written to ask what a behavior's body tells apart, each with the answer written in it.
 *
 * <p>One file a shape. What a fixture is for is said in its own comments, beside the model, and what
 * the body tells apart at each position of {@code judge} is written there too, by hand, in the words
 * {@link #spelled} writes an answer in. The answer is never taken from what this compiler says:
 * written from its output, a fixture would hold the compiler to agreeing with itself.
 */
final class ToldApartCorpus {

    /** Where the fixtures are, which is this module's own test resources. */
    static final Path DIR = Path.of("src", "test", "resources", "souther", "compiler", "partition",
            "toldapart");

    /** The behavior every fixture is about. */
    static final String BEHAVIOR = "judge";

    /** A line saying what the body tells apart at one position. */
    private static final Pattern TOLD_APART = Pattern.compile("^// told apart at (\\S+): (.+)$");

    /** The module a fixture declares, which is what its answers are asked of. */
    private static final Pattern MODULE = Pattern.compile("^module (\\S+)$", Pattern.MULTILINE);

    private ToldApartCorpus() {}

    /**
     * One fixture.
     *
     * @param file     its name, which is what a failure names it by
     * @param source   the model
     * @param module   the module it declares
     * @param expected what the body tells apart at each position, as written, by position name
     */
    record Fixture(String file, String source, String module, Map<String, String> expected) {}

    /** Every fixture, by file name. Refused where there is none, which no sweep could tell from
     *  every one of them holding. */
    static List<Fixture> all() {
        List<Fixture> out = new ArrayList<>();
        try (Stream<Path> files = Files.list(DIR)) {
            for (Path file : files.filter(each -> each.toString().endsWith(".sou")).sorted()
                    .toList()) {
                out.add(read(file));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (out.isEmpty()) {
            throw new IllegalStateException("no fixture under " + DIR.toAbsolutePath());
        }
        return out;
    }

    private static Fixture read(Path file) {
        String source;
        try {
            source = Files.readString(file, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        Map<String, String> expected = new LinkedHashMap<>();
        for (String line : source.lines().toList()) {
            Matcher told = TOLD_APART.matcher(line.strip());
            if (told.matches() && expected.put(told.group(1), told.group(2).strip()) != null) {
                throw new IllegalStateException(file.getFileName() + " says twice what is told"
                        + " apart at " + told.group(1));
            }
        }
        Matcher module = MODULE.matcher(source);
        if (!module.find()) {
            throw new IllegalStateException(file.getFileName() + " declares no module");
        }
        if (expected.isEmpty()) {
            throw new IllegalStateException(file.getFileName() + " says what is told apart at no"
                    + " position, so nothing in it is checked");
        }
        return new Fixture(file.getFileName().toString(), source, module.group(1), expected);
    }

    /**
     * An answer in the words a fixture writes one in.
     *
     * <p>The groups beside the classes, so that a fixture says what the position is divided into as
     * well as how the body divides it: a fixture whose model moved under it is then a failure and
     * not an answer that happens to stay the same.
     */
    static String spelled(BodyDistinction told, int classes) {
        return switch (told) {
            case BodyDistinction.Untouched _ -> "untouched";
            case BodyDistinction.Drawn it -> it.groups().size()
                    + (it.groups().size() == 1 ? " group of " : " groups of ") + classes;
            case BodyDistinction.Unread _ -> "unread";
            case BodyDistinction.NoBody _ -> "no body";
        };
    }
}
