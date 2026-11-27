package souther.cli.backend;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.compiler.command.Environment;
import souther.compiler.meta.ModuleMetadata;
import souther.test.WrittenOn;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A backend runs in the JVM of the Souther that chose it: the command is the one its jar provides,
 * and the compiler it reaches is this Souther's.
 *
 * <p>What a class of the compiler answers is asked of a jar that holds a second definition of that
 * class, since a jar that holds none would reach this Souther's whichever way the two were ordered.
 */
class ABackendIsRunByTheOneCommandItsJarProvidesBesideThisSouthersCompilerTest {

    private static final String HERE = ModuleMetadata.compilerVersion();

    @TempDir
    Path dir;

    private final ByteArrayOutputStream out = new ByteArrayOutputStream();

    private Environment environment() {
        PrintStream nowhere = new PrintStream(OutputStream.nullOutputStream());
        return new Environment(Map.of(),
                Map.of("user.home", dir.toString(), "fake.property", "handed-to-the-run"), dir,
                new ByteArrayInputStream(new byte[0]),
                new PrintStream(out, true, StandardCharsets.UTF_8), nowhere, false, WrittenOn.DAY);
    }

    private int run(Path jar) throws Exception {
        return BackendCommand.run(new Backends.Backend("fake", HERE, jar), List.of("--exit", "3"),
                environment());
    }

    private String said() {
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void theCompilerABackendReachesIsThisSouthersWhateverItsJarHolds() throws Exception {
        Path jar = FakeBackend.writeCarryingAClassOfTheCompiler(dir.resolve("fake.jar"), "fake",
                HERE);

        assertEquals(3, run(jar));

        assertTrue(said().contains("compiler=" + HERE + "\n"), said());
    }

    /** The control: the second definition is in the jar, and says what it says where it is read. */
    @Test
    void theJarHoldsADefinitionOfItsOwnThatWouldHaveAnsweredOtherwise() throws Exception {
        Path jar = FakeBackend.writeCarryingAClassOfTheCompiler(dir.resolve("fake.jar"), "fake",
                HERE);

        try (URLClassLoader alone = new URLClassLoader(new URL[] {jar.toUri().toURL()},
                ClassLoader.getPlatformClassLoader())) {
            Object version = alone.loadClass(ModuleMetadata.class.getName())
                    .getMethod("compilerVersion").invoke(null);

            assertEquals(FakeBackend.THE_JARS_OWN_COMPILER, version);
        }
    }

    @Test
    void theLoaderALookupFallsBackOnIsGivenBackWhenTheCommandHasAnswered() throws Exception {
        ClassLoader before = Thread.currentThread().getContextClassLoader();

        run(FakeBackend.write(dir.resolve("fake.jar"), "fake", HERE, "ran"));

        assertSame(before, Thread.currentThread().getContextClassLoader());
    }

    @Test
    void aJarThatNamesNoCommandIsRefusedSayingItProvidesNone() throws Exception {
        Path jar = FakeBackend.writeProviding(dir.resolve("fake.jar"), "fake", HERE, null);

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command", refused.key());
        assertEquals(List.of(jar, 0), List.of(refused.arguments()));
    }

    /**
     * A provider the jar names and does not hold is this class path's, and a command of this
     * Souther's is not what the backend provides.
     */
    @Test
    void aCommandTheJarNamesAndDoesNotHoldIsNotItsOwn() throws Exception {
        Path jar = FakeBackend.writeProviding(dir.resolve("fake.jar"), "fake", HERE,
                ACommandOfThisClassPath.class.getName() + "\n");

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command", refused.key());
        assertEquals("", said());
    }

    @Test
    void aJarProvidingTwoCommandsIsRefusedBeforeEitherRuns() throws Exception {
        Path jar = FakeBackend.writeProvidingTwoCommands(dir.resolve("fake.jar"), "fake", HERE);

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command", refused.key());
        assertEquals(List.of(jar, 2), List.of(refused.arguments()));
        assertEquals("", said());
    }

    @Test
    void aClassTheJarNamesThatIsNoCommandIsRefusedSayingWhy() throws Exception {
        Path jar = FakeBackend.writeProvidingWhatIsNoCommand(dir.resolve("fake.jar"), "fake",
                HERE);

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command.unusable", refused.key());
        assertTrue(String.valueOf(refused.arguments()[1]).contains("not a subtype"),
                String.valueOf(refused.arguments()[1]));
    }

    /**
     * A class that does not link is not what a lookup of providers reports as its own failure: the
     * JVM throws it as it is. It is a refusal of the jar all the same, naming what was missing.
     */
    @Test
    void aCommandThatExtendsAClassHeldNowhereIsRefusedNamingIt() throws Exception {
        Path jar = FakeBackend.writeProvidingACommandThatExtendsWhatIsNowhere(
                dir.resolve("fake.jar"), "fake", HERE);

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command.unusable", refused.key());
        String why = String.valueOf(refused.arguments()[1]);
        assertTrue(why.contains(NoClassDefFoundError.class.getSimpleName())
                && why.contains(FakeBackend.NOWHERE.replace('.', '/')), why);
    }

    /**
     * A jar whose manifest names a class path would have its loader read the jars named there as
     * the backend's own, so it is refused, though the command it holds is one that runs.
     */
    @Test
    void aJarThatNamesAClassPathBesideItselfIsRefusedAndNothingRuns() throws Exception {
        Path jar = FakeBackend.writeNamingAClassPath(dir.resolve("fake.jar"), "fake", HERE,
                "another.jar");

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.classpath", refused.key());
        assertEquals("", said());
    }

    /**
     * The fake's constructor refuses to make it under a context loader other than its own, so its
     * running at all says the loader was the thread's before the command was constructed.
     */
    @Test
    void theCommandIsConstructedUnderItsOwnContextLoader() throws Exception {
        int status = run(FakeBackend.write(dir.resolve("fake.jar"), "fake", HERE, "ran"));

        assertEquals(3, status);
        assertTrue(said().contains("marker=ran\n"), said());
    }

    /** What the command throws is thrown on as it is, and the thread's loader is the one before. */
    @Test
    void whatTheCommandThrowsIsThrownOnAndTheContextLoaderIsGivenBack() throws Exception {
        ClassLoader before = Thread.currentThread().getContextClassLoader();
        Path jar = FakeBackend.write(dir.resolve("fake.jar"), "fake", HERE, "ran");

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> BackendCommand.run(new Backends.Backend("fake", HERE, jar),
                        List.of("--throw"), environment()));

        assertEquals(FakeCommand.ASKED_TO_FAIL, thrown.getMessage());
        assertSame(before, Thread.currentThread().getContextClassLoader());
    }

    @Test
    void theCommandReadsThePropertiesItsRunWasGiven() throws Exception {
        run(FakeBackend.write(dir.resolve("fake.jar"), "fake", HERE, "ran"));

        assertTrue(said().contains("property=handed-to-the-run\n"), said());
    }

    @Test
    void aCommandThatCannotBeLoadedIsRefusedSayingWhy() throws Exception {
        Path jar = FakeBackend.writeProviding(dir.resolve("fake.jar"), "fake", HERE,
                "NoSuchCommand\n");

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> run(jar));

        assertEquals("cli.backend.command.unusable", refused.key());
        assertTrue(String.valueOf(refused.arguments()[1]).contains("NoSuchCommand"),
                String.valueOf(refused.arguments()[1]));
    }
}
