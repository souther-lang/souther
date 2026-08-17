package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Repairing what the rules say writes the canonical form, over every source this repository has.
 *
 * <p>The oracle is the formatter. What the rules answer is composed into a text and that text is the
 * one the formatter writes — so a set of rules that implements a different canonical form fails
 * here, however well each of them reads.
 *
 * <p>Applied until it stops changing the text, and not in one pass. The rules read each other's
 * results: which tokens are written settles what the layout rules' boundaries are, and where the
 * lines break settles what the indentation rule's lines are. Asked of a source whose breaks are
 * still wrong, the indentation rule answers about lines that will not exist.
 *
 * <p>{@link Deviations.Report#whole} is that statement, so this holds the report rather than
 * repeating the repair — a source it is true of is one where every difference from the canonical
 * form was named by a rule.
 */
class RepairingWhatTheRulesSayWritesTheCanonicalFormTest {

    static Stream<Path> sources() throws IOException {
        List<Path> out = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(Path.of(".."))) {
            walk.filter(p -> p.toString().endsWith(".sou"))
                    .filter(p -> !p.toString().contains("target"))   // a build's copy of one
                    .sorted().forEach(out::add);
        }
        return out.stream();
    }

    private static String read(Path p) {
        try {
            return Files.readString(p, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * What the rules have against each source, taken once.
     *
     * <p>{@link Deviations#of} is a function of its text and the two checks here ask about the same
     * files, so a source that departs from the canonical form had its report written twice — once
     * to hold it against the formatter, once to count what it said.
     */
    private static final Map<Path, Deviations.Report> REPORTS = new ConcurrentHashMap<>();

    private static Deviations.Report reportOn(Path path) {
        return REPORTS.computeIfAbsent(path, p -> Deviations.of(read(p)));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("sources")
    void everySourceIsWhollyNamed(Path path) {
        String source = read(path);
        assertEquals(List.of(), CstParser.parse(source).errors(), "this source does not parse");

        Deviations.Report report = reportOn(path);

        assertTrue(report.whole(),
                "repairing what the rules say does not write the canonical form of " + path
                        + "; what they said was " + report.deviations());
    }

    /**
     * And some of them are not in canonical form, so the sweep above is answering a question.
     *
     * <p>A corpus every file of which is already canonical would pass with no rule written at all:
     * the report would be empty and repairing nothing would write the text back.
     */
    @Test
    void andSomeOfThemHaveSomethingAgainstThem() throws IOException {
        List<Path> differ = new ArrayList<>();
        int deviations = 0;
        for (Path path : sources().toList()) {
            String source = read(path);
            if (!Formatter.format(source).equals(source)) {
                differ.add(path);
                deviations += reportOn(path).deviations().size();
            }
        }

        assertTrue(differ.size() >= 5,
                "too few sources depart from the canonical form for this to hold anything: "
                        + differ);
        assertTrue(deviations >= 500, "and too few deviations among them: " + deviations);
    }
}
