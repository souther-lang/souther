package souther.cli.init;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The module a project declares is derived from what its build calls it, and is a name the language
 * reads.
 *
 * <p>Derived rather than asked for, because it is the fourth name in a project that had four names
 * to keep in step. What it has to survive is that a coordinate may carry what a name may not:
 * {@code org.souther-lang} is a group of this project's own.
 */
class AModuleNameFollowsFromTheCoordinateTest {

    @Test
    void aHyphenACoordinateMayCarryBecomesAnUnderscore() {
        assertEquals("com.example.hello",
                new Coordinate("com.example", "hello").moduleName());
        assertEquals("com.acme.billing_service",
                new Coordinate("com.acme", "billing-service").moduleName());
        assertEquals("org.souther_lang.souther_cli",
                new Coordinate("org.souther-lang", "souther_cli").moduleName());
    }

    /**
     * A file is named after the module it declares, which is not always the artifact.
     *
     * <p>The two part company exactly where the artifact carries a hyphen. Naming the file after the
     * artifact would leave one name spelt two ways inside one project — the header, the Java package
     * and the test directory all say the module's spelling.
     */
    @Test
    void theSourceIsNamedAfterTheModuleAndNotTheArtifact() {
        Coordinate coordinate = new Coordinate("com.acme", "billing-service");
        Project project = new Project(coordinate, coordinate.moduleName(), Model.FULL,
                BuildSystem.MAVEN, "9.9.9");

        assertEquals("src/main/souther/billing_service.sou", Templates.modelPathOf(project));
        assertEquals("com/acme/billing_service", project.packagePath());
    }

    /**
     * A coordinate no name follows from is refused rather than mangled.
     *
     * <p>The words are the lexer's, not a list written beside it: a word the language takes later
     * would otherwise go on being derived into a header that no longer parses.
     */
    @Test
    void aCoordinateThatDerivesNoNameSaysSo() {
        assertNull(new Coordinate("com.data", "hello").moduleName(),
                "a segment the language has taken as a keyword");
        assertNull(new Coordinate("com.example", "2fast").moduleName(),
                "a segment beginning with a digit");
        assertNull(new Coordinate("com.example", "_leading").moduleName(),
                "an underscore carries a name on and begins none");
        assertNull(new Coordinate("com.example", "-").moduleName(),
                "a segment that is nothing but a separator");
    }

    @Test
    void aCoordinateIsBothHalvesOrItIsNotOne() {
        assertEquals("com.example:hello", Coordinate.written("com.example:hello").toString());
        assertNull(Coordinate.written("hello"));
        assertNull(Coordinate.written(":hello"));
        assertNull(Coordinate.written("com.example:"));
        assertNull(Coordinate.written("com.example:hello:1.0"));
    }

    @Test
    void aWrittenModuleNameIsHeldAgainstTheSameRule() {
        assertTrue(Coordinate.isAModuleName("com.example.hello"));
        assertTrue(Coordinate.isAModuleName("hello"));
        assertFalse(Coordinate.isAModuleName("com..hello"));
        assertFalse(Coordinate.isAModuleName("com.hello."));
        assertFalse(Coordinate.isAModuleName("billing-service"));
        assertFalse(Coordinate.isAModuleName(""));
    }
}
