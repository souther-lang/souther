package souther.compiler.examples;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.CheckedDeclarations;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.generated.GeneratedLinkage;
import souther.compiler.generated.GeneratedLinkage.GeneratedClassDefect;
import souther.compiler.observe.FieldTypes;

import javax.tools.ToolProvider;

import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A member of a live value that cannot be read means one of two things, and the value's class says
 * which. Of a class a supplied implementation brought, it is what that class's own dependencies came
 * to. Of a class this compile generated, it is this compiler's output failing.
 *
 * <p>That the value exists settles nothing: the JVM resolves what an accessor's body names when the
 * body runs, so an instance of a class whose accessor needs a class that is gone is made without
 * complaint.
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

    /** Resolves fine and fails when called, as a dependency of the accessor's body would. */
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

    /** Whose accessor is there and resolves, but does not answer. */
    private static final String HAS_NO_VALUE = """
            package other;
            public final class Option$Some {
                public Object notValue() { return null; }
            }
            """;

    @TempDir
    Path built;

    @Test
    void anAccessorWhoseSignatureNamesAClassThatIsGoneIsAFieldThatCannotBeRead() throws Exception {
        Object live = loaded("Needs", NEEDS_A_CLASS_THAT_IS_GONE, true);

        assertNull(ObservedValues.readOrNull(live, "value", ValueOwnership.none()));
    }

    @Test
    void anAccessorThatFailsWhenCalledIsAFieldThatCannotBeRead() throws Exception {
        Object live = loaded("Fails", FAILS_WHEN_CALLED, false);

        assertNull(ObservedValues.readOrNull(live, "value", ValueOwnership.none()));
    }

    /** The counterpart: the same failures of a class this compile generated are its own. */
    @Test
    void theSameFailuresOfAClassThisCompileGeneratedAreItsOutputFailing() throws Exception {
        Object resolving = loaded("Needs", NEEDS_A_CLASS_THAT_IS_GONE, true);
        assertThrows(GeneratedClassDefect.class, () -> ObservedValues.readOrNull(resolving, "value",
                new ValueOwnership(resolving.getClass().getClassLoader())));

        Object calling = loaded("Fails", FAILS_WHEN_CALLED, false);
        assertThrows(GeneratedClassDefect.class, () -> ObservedValues.readOrNull(calling, "value",
                new ValueOwnership(calling.getClass().getClassLoader())));
    }

    /** A defect something below found is not a member that cannot be read, whichever class the
     * value is of and however it was wrapped on the way up. */
    @Test
    void aDefectAlreadyFoundIsNotReadAsAMemberThatCannotBeRead() {
        GeneratedClassDefect found = assertThrows(GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new VerifyError("Bad type on operand stack")));

        GeneratedClassDefect again = assertThrows(GeneratedClassDefect.class,
                () -> ValueOwnership.none().readFailed(new Object(),
                        new InvocationTargetException(found)));
        assertSame(found, again);
    }

    @Test
    void anOptionalOfAnotherBuildWhoseValueCannotBeReadIsAFixtureThatCannotBeReadBack()
            throws Exception {
        Object live = loaded("Option$Some", SOME, false);

        FixtureException refused = assertThrows(FixtureException.class,
                () -> neutral(ValueOwnership.none()).heldBy(live));
        assertEquals("an optional's value cannot be read back: `value` of `Option$Some` could not"
                + " be read: java.lang.NoSuchMethodError: a driver the answer needs",
                refused.getMessage());
    }

    @Test
    void anAccessorThatIsNotThereIsSaidToBeNotThere() throws Exception {
        Object live = loaded("Option$Some", HAS_NO_VALUE, false);

        FixtureException refused = assertThrows(FixtureException.class,
                () -> neutral(ValueOwnership.none()).heldBy(live));
        assertEquals("an optional's value cannot be read back: `Option$Some` has no `value` to read",
                refused.getMessage());
    }

    @Test
    void anOptionalOfAClassThisCompileGeneratedThatCannotBeReadIsItsOutputFailing()
            throws Exception {
        Object live = loaded("Option$Some", SOME, false);

        assertThrows(GeneratedClassDefect.class, () -> neutral(
                new ValueOwnership(live.getClass().getClassLoader())).heldBy(live));
    }

    private static NeutralForm neutral(ValueOwnership ownership) {
        Symbols symbols = Symbols.none(DefaultStdlib.get());
        return new NeutralForm(symbols, ScopedDeclarations.sumsOf(symbols),
                ScopedDeclarations.kindsOf(symbols),
                FieldTypes.over(new CheckedDeclarations(_ -> null, _ -> null)), ownership);
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
