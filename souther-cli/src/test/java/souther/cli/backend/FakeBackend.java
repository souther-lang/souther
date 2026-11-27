package souther.cli.backend;

import souther.compiler.command.TargetCommand;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassTransform;
import java.lang.classfile.CodeTransform;
import java.lang.constant.ClassDesc;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;

/**
 * A jar built inside a test, carrying the descriptor of a backend and a command it provides.
 *
 * <p>What the command does when run is to say what it was given — its arguments, the directory it
 * is run in, one environment variable and its input — on the output it was given, to say which
 * compiler it reached, to say something on the error output, and to answer with the status written
 * after {@code --exit}. A test reads that back through the CLI and so holds the CLI to handing
 * each of them over.
 *
 * <p>The command is {@link FakeCommand}, which this build compiled, held in the jar under a name
 * no class of this class path has: a class the jar holds under its own name here would be defined
 * by this class path, and a backend's command is one its jar defines.
 *
 * <p>The marker is a file in the jar and not a constant in the class, so every jar holds the same
 * class. What tells two jars apart is what the class reads out of the one it was loaded from,
 * which is what a jar written with another marker would have said.
 */
public final class FakeBackend {

    private FakeBackend() {}

    /** Where in the jar the marker is written. */
    static final String MARKER = "fake-backend-marker";

    /** Where a jar names the commands it provides. */
    private static final String PROVIDED = "META-INF/services/" + TargetCommand.class.getName();

    /** The name a jar holds its command under. */
    private static final String THE_COMMAND = "Fake";

    /** The name a jar that provides two holds its second command under. */
    private static final String ANOTHER_COMMAND = "FakeToo";

    /** The name a jar holds a class under that is no command, where it names one as its command. */
    private static final String NO_COMMAND = "NoCommand";

    /** The name a jar holds a command under whose superclass is nowhere. */
    private static final String DEPENDENT = "Dependent";

    /** The class such a command extends, which no jar and no class path holds. */
    public static final String NOWHERE = "nowhere.ABaseNoJarHolds";

    /** The class of the compiler a jar may carry a second definition of. */
    private static final String A_CLASS_OF_THE_COMPILER = "souther.compiler.meta.ModuleMetadata";

    /** What the second definition says the compiler's version is. */
    public static final String THE_JARS_OWN_COMPILER = "the-jar's-own";

    /** Writes a backend jar at {@code jar}, whose output says {@code marker}. */
    public static Path write(Path jar, String name, String southerVersion, String marker)
            throws IOException {
        return pack(jar, marker, descriptor(name, southerVersion), THE_COMMAND + "\n", Map.of(),
                null);
    }

    /** Writes a jar at {@code jar} whose descriptor is exactly {@code descriptor}, or none. */
    public static Path writeWithDescriptor(Path jar, String descriptor) throws IOException {
        return pack(jar, "described", descriptor, THE_COMMAND + "\n", Map.of(), null);
    }

    /**
     * Writes a backend jar at {@code jar} that names the commands it provides as {@code provided}
     * says, one class to a line, or names none where that is null.
     */
    public static Path writeProviding(Path jar, String name, String southerVersion,
                                      String provided) throws IOException {
        return pack(jar, "providing", descriptor(name, southerVersion), provided, Map.of(), null);
    }

    /**
     * Writes a backend jar at {@code jar} that also holds a class under a name of the compiler's,
     * which answers {@link #THE_JARS_OWN_COMPILER} where the compiler's answers its version.
     */
    public static Path writeCarryingAClassOfTheCompiler(Path jar, String name,
                                                        String southerVersion) throws IOException {
        return pack(jar, "carrying", descriptor(name, southerVersion), THE_COMMAND + "\n",
                Map.of(A_CLASS_OF_THE_COMPILER,
                        renamed(ASecondDefinition.class, A_CLASS_OF_THE_COMPILER)), null);
    }

    /** Writes a backend jar at {@code jar} that holds two commands and names both. */
    public static Path writeProvidingTwoCommands(Path jar, String name, String southerVersion)
            throws IOException {
        return pack(jar, "two", descriptor(name, southerVersion),
                THE_COMMAND + "\n" + ANOTHER_COMMAND + "\n",
                Map.of(ANOTHER_COMMAND, renamed(FakeCommand.class, ANOTHER_COMMAND)), null);
    }

    /** Writes a backend jar at {@code jar} that names, as its command, a class that is none. */
    public static Path writeProvidingWhatIsNoCommand(Path jar, String name, String southerVersion)
            throws IOException {
        return pack(jar, "none", descriptor(name, southerVersion), NO_COMMAND + "\n",
                Map.of(NO_COMMAND, renamed(ASecondDefinition.class, NO_COMMAND)), null);
    }

    /**
     * Writes a backend jar at {@code jar} whose command extends {@link #NOWHERE}, a class neither
     * the jar nor this class path holds: what a backend built against a library this Souther does
     * not run with comes to.
     */
    public static Path writeProvidingACommandThatExtendsWhatIsNowhere(
            Path jar, String name, String southerVersion) throws IOException {
        byte[] dependent = ClassFile.of().build(ClassDesc.of(DEPENDENT), built -> built
                .withFlags(ClassFile.ACC_PUBLIC)
                .withSuperclass(ClassDesc.of(NOWHERE))
                .withInterfaceSymbols(TargetCommand.class.describeConstable().orElseThrow()));
        return pack(jar, "dependent", descriptor(name, southerVersion), DEPENDENT + "\n",
                Map.of(DEPENDENT, dependent), null);
    }

    /**
     * Writes a backend jar at {@code jar} whose manifest names {@code classPath} as a class path
     * beside it, and which is a backend that runs in everything else.
     */
    public static Path writeNamingAClassPath(Path jar, String name, String southerVersion,
                                             String classPath) throws IOException {
        return pack(jar, "class-path", descriptor(name, southerVersion), THE_COMMAND + "\n",
                Map.of(), classPath);
    }

    private static String descriptor(String name, String southerVersion) {
        return "name=" + name + "\nsouther.version=" + southerVersion + "\n";
    }

    /**
     * The class file of {@code written} as a class named {@code named}. Its name is changed where
     * the class says what it is and nowhere else, so a class written to be held under another name
     * names itself nowhere in its code. Each method body is written again rather than copied, so
     * the frames a verifier reads say what {@code this} is under the new name.
     */
    private static byte[] renamed(Class<?> written, String named) throws IOException {
        byte[] bytes;
        try (InputStream in = written.getResourceAsStream(written.getSimpleName() + ".class")) {
            bytes = in.readAllBytes();
        }
        ClassFile classFile = ClassFile.of(ClassFile.StackMapsOption.GENERATE_STACK_MAPS);
        return classFile.transformClass(classFile.parse(bytes), ClassDesc.of(named),
                ClassTransform.transformingMethodBodies(CodeTransform.ACCEPT_ALL));
    }

    /**
     * Writes the jar: the command under its name, the marker, and beside them each class of
     * {@code beside}, by its name. A jar says a class path only where {@code classPath} is one.
     */
    private static Path pack(Path jar, String marker, String descriptor, String provided,
                             Map<String, byte[]> beside, String classPath) throws IOException {
        Files.createDirectories(jar.getParent());
        Manifest manifest = new Manifest();
        manifest.getMainAttributes().put(Attributes.Name.MANIFEST_VERSION, "1.0");
        if (classPath != null) {
            manifest.getMainAttributes().put(Attributes.Name.CLASS_PATH, classPath);
        }
        try (OutputStream file = Files.newOutputStream(jar);
             JarOutputStream out = new JarOutputStream(file, manifest)) {
            entry(out, THE_COMMAND + ".class", renamed(FakeCommand.class, THE_COMMAND));
            entry(out, MARKER, marker.getBytes(StandardCharsets.UTF_8));
            if (descriptor != null) {
                entry(out, Backends.DESCRIPTOR, descriptor.getBytes(StandardCharsets.ISO_8859_1));
            }
            if (provided != null) {
                entry(out, PROVIDED, provided.getBytes(StandardCharsets.UTF_8));
            }
            for (Map.Entry<String, byte[]> held : beside.entrySet()) {
                entry(out, held.getKey().replace('.', '/') + ".class", held.getValue());
            }
        }
        return jar;
    }

    private static void entry(JarOutputStream out, String name, byte[] bytes) throws IOException {
        out.putNextEntry(new JarEntry(name));
        out.write(bytes);
        out.closeEntry();
    }
}
