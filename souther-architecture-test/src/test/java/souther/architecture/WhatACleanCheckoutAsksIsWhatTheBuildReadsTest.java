package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a publication refuses an ignored file is where the build reads one.
 *
 * <p>A file git ignores is not recorded by the commit a jar's manifest names, so one the build copies
 * into an artifact makes the manifest wrong, and one anywhere else does nothing. Each module refuses
 * an ignored file in its own {@code src}; what the build copies from outside every module's
 * {@code src} is listed in the root pom as {@code souther.build.reads}, and refused there. The list
 * is held here to what the poms copy from, both ways: a copy from somewhere unlisted would carry an
 * ignored file into a jar unasked, and a listed place nothing copies from would refuse a publication
 * over a file nothing reads.
 */
class WhatACleanCheckoutAsksIsWhatTheBuildReadsTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void whatIsReadFromOutsideEveryModulesSourcesIsWhatIsListed() {
        Set<String> copied = new TreeSet<>();
        for (Path module : REPOSITORY.modules()) {
            for (Path read : REPOSITORY.pathsCopiedFrom(module)) {
                if (!underAModulesSources(read)) {
                    copied.add(REPOSITORY.root().relativize(read).toString());
                }
            }
        }
        Set<String> listed = new TreeSet<>(
                Arrays.asList(REPOSITORY.rootProperty("souther.build.reads").split("\\s+")));
        assertEquals(copied, listed);
    }

    private static boolean underAModulesSources(Path read) {
        for (Path module : REPOSITORY.modules()) {
            if (read.startsWith(module.resolve("src"))) {
                return true;
            }
        }
        return false;
    }
}
