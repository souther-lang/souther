package souther.compiler.examples;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import javax.tools.ToolProvider;

import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A value a supplied implementation answered is read through its own class's accessors, and a link
 * failure there is what that class's dependencies came to. It is not a class this compile generated,
 * and ending the run as an internal compiler error for it would blame the wrong code.
 */
class AValueOfAnotherBuildWhoseClassWillNotLinkIsNotThisCompilesDefectTest {

    /** Resolving this one's accessor needs {@code Missing}, which the loader will not have. */
    private static final String NEEDS_A_CLASS_THAT_IS_GONE = """
            package other;
            public final class Needs {
                public Missing value() { return null; }
            }
            """;

    private static final String MISSING = """
            package other;
            public final class Missing {}
            """;

    /** Reads fine to resolve and fails when called, as a dependency of the accessor's body would. */
    private static final String FAILS_WHEN_CALLED = """
            package other;
            public final class Fails {
                public Object value() { throw new NoSuchMethodError("a driver the answer needs"); }
            }
            """;

    /** Named the way an optional's present case is, which is what the walk unwraps by name. */
    private static final String SOME = """
            package other;
            public final class Option$Some {
                public Object value() { throw new NoSuchMethodError("a driver the answer needs"); }
            }
            """;

    @TempDir
    Path built;

    @Test
    void anAccessorWhoseSignatureNamesAClassThatIsGoneIsAFieldThatCannotBeRead() throws Exception {
        Object live = loaded("Needs", NEEDS_A_CLASS_THAT_IS_GONE, true);

        assertNull(ObservedValues.readOrNull(live, "value"));
    }

    @Test
    void anAccessorThatFailsWhenCalledIsAFieldThatCannotBeRead() throws Exception {
        Object live = loaded("Fails", FAILS_WHEN_CALLED, false);

        assertNull(ObservedValues.readOrNull(live, "value"));
    }

    @Test
    void anOptionalOfAnotherBuildWhoseValueCannotBeReadIsAFixtureThatCannotBeReadBack()
            throws Exception {
        Object live = loaded("Option$Some", SOME, false);

        FixtureException refused = assertThrows(FixtureException.class, () -> NeutralForm.heldBy(live));
        assertEquals("an optional's value cannot be read back: `Option$Some` has no `value` to read",
                refused.getMessage());
    }

    /** {@code name} compiled with {@code Missing}, loaded by a loader that is then without it where
     *  {@code withoutMissing}. */
    private Object loaded(String name, String source, boolean withoutMissing) throws Exception {
        Path directory = Files.createDirectories(built.resolve("src/other"));
        Path file = directory.resolve(name + ".java");
        Path missing = directory.resolve("Missing.java");
        Files.writeString(file, source);
        Files.writeString(missing, MISSING);
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-d", built.resolve("classes").toString(), file.toString(), missing.toString());
        assertEquals(0, rc, "the other build compiles");
        if (withoutMissing) {
            Files.delete(built.resolve("classes/other/Missing.class"));
        }
        URLClassLoader loader = new URLClassLoader(new URL[] {built.resolve("classes").toUri().toURL()},
                ClassLoader.getPlatformClassLoader());
        return loader.loadClass("other." + name).getDeclaredConstructor().newInstance();
    }
}
