package souther.exact;

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
 * Exact arithmetic names nothing of the JVM backend, of the compiler, or of the language's own types.
 *
 * <p>What the compiler and the run time share is a mathematics, and it is shared by being independent
 * of both. A dependency from here to {@code souther.runtime} would make the compiler's reasoning depend
 * on the backend it was written not to depend on, by the one route the package name of that dependency
 * does not show; one to the compiler would make the run time carry it. So what is imported is the JDK,
 * the nullness annotations, and this package.
 */
class TheExactPackageDependsOnTheJdkAloneTest {

    @Test
    void everyImportIsTheJdkTheNullnessAnnotationsOrThisPackage() throws IOException {
        List<String> foreign = new ArrayList<>();
        for (Path source : sources()) {
            for (String line : Files.readAllLines(source)) {
                String trimmed = line.strip();
                if (!trimmed.startsWith("import ")) {
                    continue;
                }
                String name = trimmed.replaceFirst("^import (static )?", "");
                if (!(name.startsWith("java.") || name.startsWith("org.jspecify.")
                        || name.startsWith("souther.exact."))) {
                    foreign.add(source.getFileName() + ": " + trimmed);
                }
            }
        }

        assertEquals(List.of(), foreign, "exact arithmetic is shared by depending on nothing either side is");
    }

    @Test
    void noSourceNamesAnotherPackageOfTheSystemWithoutImportingIt() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            for (String other : List.of("souther.runtime", "souther.compiler")) {
                if (text.replaceAll("(?s)/\\*.*?\\*/|//[^\n]*", "").contains(other)) {
                    naming.add(source.getFileName() + " names " + other);
                }
            }
        }

        assertEquals(List.of(), naming);
    }

    private static List<Path> sources() throws IOException {
        Path main = Path.of("src/main/java/souther/exact");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> found = walk.filter(each -> each.toString().endsWith(".java")).sorted().toList();
            assertTrue(found.size() >= 5, () -> "that is not the exact package: " + found.size());
            return found;
        }
    }
}
