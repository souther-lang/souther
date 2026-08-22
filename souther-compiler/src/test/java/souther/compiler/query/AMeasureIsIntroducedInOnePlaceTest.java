package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A measure's answer is chosen in one place, and production code never writes one of its cases.
 *
 * <p>{@link PartitionDerivation#of} and {@link BoundaryDerivation#of} are the rule: what a measure
 * came to follows from what it found and whether its own reading ran out, and those two facts
 * arrive together or not at all. A caller writing {@code new Complete(entries)} decides it from the
 * entries alone, which is the reconstruction the whole type exists to stop — and it is exactly what
 * every reader did while the answer was a list beside a status.
 *
 * <p>The type cannot forbid it. {@code Absent} takes the proof its own measure's reading ran out,
 * and that proof can only be made where the reading is; {@code Complete} claims the same thing and
 * carries entries instead, so a case record public enough to match on is public enough to write. A
 * proof on {@code Complete} as well would close it, at the price of every fixture that wants a
 * measure made in full needing a reading to have made it — which is a price the tests that fabricate
 * a border to hold a criterion to cannot pay.
 *
 * <p>So the rule is checked where it is a rule: in what is written. Over the sources of every module
 * and not the classes of one, and over the text rather than the bytecode — who may write a
 * constructor is a fact about a source file, and a check that reads what was compiled would answer a
 * question about the JVM instead.
 *
 * <p>{@code PartitionEvidence.NONE} is the exception and it is named below. It is a {@code >->}
 * composition, whose measures claim nothing about a reading: {@code NoSubject} says there was
 * nothing to read, which is the one case no proof is owed for.
 */
class AMeasureIsIntroducedInOnePlaceTest {

    /** Where the two are declared, which is where their cases may be written. */
    private static final List<String> DECLARED_IN =
            List.of("PartitionDerivation.java", "BoundaryDerivation.java");

    /** And the one production value that names a case, which claims nothing a proof would cover. */
    private static final List<String> ALLOWED =
            List.of("PartitionEvidence.java: PartitionDerivation.NoSubject",
                    "PartitionEvidence.java: BoundaryDerivation.NoSubject");

    @Test
    void noProductionSourceWritesACaseOfAMeasure() throws IOException {
        List<Path> roots = mainSourceRoots();

        assertTrue(roots.size() > 1,
                () -> "a check over one module's sources is not the rule this is about: " + roots);

        List<String> written = new ArrayList<>();
        for (Path root : roots) {
            try (Stream<Path> sources = Files.walk(root)) {
                for (Path source : sources.filter(p -> p.toString().endsWith(".java")).toList()) {
                    String name = source.getFileName().toString();
                    if (DECLARED_IN.contains(name)) {
                        continue;
                    }
                    // Per occurrence and not per line. `PartitionEvidence.NONE` writes both of
                    // its measures on one line, and a line counted once would hold two cases under
                    // one name — so a case added beside an allowed one would be invisible.
                    for (String line : Files.readAllLines(source)) {
                        for (String each : List.of("PartitionDerivation.", "BoundaryDerivation.")) {
                            int at = line.indexOf("new " + each);
                            while (at >= 0) {
                                written.add(name + ": " + each
                                        + caseNameAt(line, at + 4 + each.length()));
                                at = line.indexOf("new " + each, at + 1);
                            }
                        }
                    }
                }
            }
        }
        assertEquals(ALLOWED, written,
                "production sources writing a case of a measure rather than asking `of`");
    }

    /** The name written after the case's owner, which is what tells one case from another. */
    private static String caseNameAt(String line, int from) {
        int to = from;
        while (to < line.length() && Character.isJavaIdentifierPart(line.charAt(to))) {
            to++;
        }
        return line.substring(from, to);
    }

    /**
     * Every module's production sources, found from this one rather than listed.
     *
     * <p>A list of modules is a copy of the reactor that stops covering the module added after it.
     * The check above asserts it found more than one, so a walk that reaches nothing is this test
     * failing rather than passing over an empty set.
     */
    private static List<Path> mainSourceRoots() throws IOException {
        Path reactor = Path.of("").toAbsolutePath().getParent();
        try (Stream<Path> modules = Files.list(reactor)) {
            return modules.map(module -> module.resolve("src/main/java"))
                    .filter(Files::isDirectory).sorted().toList();
        }
    }
}
