package souther.lsp;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

/**
 * What an editor or any other client has to know about this artifact to start it and talk to it:
 * the language it serves, the Java it needs and the arguments that Java has to be given, and where
 * each contract it answers to is written.
 *
 * <p>A file in the jar, not something this code assembles. Some of it is needed before a JVM can be
 * started — a client on too old a Java cannot run anything here to ask — and a jar is an archive any
 * client can read without one. {@code souther tooling} prints the same file for a client that would
 * rather ask a command; it is a reader of this, not a second statement of it.
 *
 * <p>The build fills it in from the properties it is itself compiled and launched with, so what it
 * says about the Java and the stack is what the build did.
 */
public final class ToolingMetadata {

    /** Where the metadata is in either jar, as a path inside the archive. */
    public static final String RESOURCE = "META-INF/souther/tooling.json";

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private ToolingMetadata() {
    }

    /**
     * The arguments a JVM has to be given to run this Souther, as the metadata states them.
     *
     * <p>Read from the file and not kept beside it: a process that starts another JVM for the same
     * front end is a client of this metadata like an editor is, and a stack size written in its own
     * source would be a second statement of it.
     */
    public static List<String> requiredJvmArgs() {
        List<String> arguments = new ArrayList<>();
        for (JsonNode argument : JSON.readTree(text()).get("runtime").get("java")
                .get("requiredJvmArgs")) {
            arguments.add(argument.asString());
        }
        return List.copyOf(arguments);
    }

    /** The metadata as written in the jar this class was loaded from. */
    public static String text() {
        try (InputStream in = ToolingMetadata.class.getClassLoader().getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException(RESOURCE + " is not beside the class that reads it");
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
