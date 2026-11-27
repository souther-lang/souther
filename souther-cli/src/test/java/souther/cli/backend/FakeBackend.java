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
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

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

    /** The class of the compiler a jar may carry a second definition of. */
    private static final String A_CLASS_OF_THE_COMPILER = "souther.compiler.meta.ModuleMetadata";

    /** What the second definition says the compiler's version is. */
    public static final String THE_JARS_OWN_COMPILER = "the-jar's-own";

    /** Writes a backend jar at {@code jar}, whose output says {@code marker}. */
    public static Path write(Path jar, String name, String southerVersion, String marker)
            throws IOException {
        return pack(jar, marker, descriptor(name, southerVersion), THE_COMMAND + "\n", false);
    }

    /** Writes a jar at {@code jar} whose descriptor is exactly {@code descriptor}, or none. */
    public static Path writeWithDescriptor(Path jar, String descriptor) throws IOException {
        return pack(jar, "described", descriptor, THE_COMMAND + "\n", false);
    }

    /**
     * Writes a backend jar at {@code jar} that names the commands it provides as {@code provided}
     * says, one class to a line, or names none where that is null.
     */
    public static Path writeProviding(Path jar, String name, String southerVersion,
                                      String provided) throws IOException {
        return pack(jar, "providing", descriptor(name, southerVersion), provided, false);
    }

    /**
     * Writes a backend jar at {@code jar} that also holds a class under a name of the compiler's,
     * which answers {@link #THE_JARS_OWN_COMPILER} where the compiler's answers its version.
     */
    public static Path writeCarryingAClassOfTheCompiler(Path jar, String name,
                                                        String southerVersion) throws IOException {
        return pack(jar, "carrying", descriptor(name, southerVersion), THE_COMMAND + "\n", true);
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

    private static Path pack(Path jar, String marker, String descriptor, String provided,
                             boolean carryingAClassOfTheCompiler) throws IOException {
        Files.createDirectories(jar.getParent());
        try (OutputStream file = Files.newOutputStream(jar);
             JarOutputStream out = new JarOutputStream(file)) {
            entry(out, THE_COMMAND + ".class", renamed(FakeCommand.class, THE_COMMAND));
            entry(out, MARKER, marker.getBytes(StandardCharsets.UTF_8));
            if (descriptor != null) {
                entry(out, Backends.DESCRIPTOR, descriptor.getBytes(StandardCharsets.ISO_8859_1));
            }
            if (provided != null) {
                entry(out, PROVIDED, provided.getBytes(StandardCharsets.UTF_8));
            }
            if (carryingAClassOfTheCompiler) {
                entry(out, A_CLASS_OF_THE_COMPILER.replace('.', '/') + ".class",
                        renamed(ASecondDefinition.class, A_CLASS_OF_THE_COMPILER));
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
