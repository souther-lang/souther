package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The command line reads the process it runs in through {@code souther.cli.Environment} and
 * nothing else: its variables, its properties, its streams, the directory a path is read from, and
 * the proxy a request is sent through.
 *
 * <p>A run is a function of its arguments and the environment it is handed, which is what lets a
 * test run the command line in its own JVM with the environment it names. A class of the command
 * line that asks the process for one of these instead reads the JVM running the test, and answers
 * the same in every environment a test names. A path is one of them because a relative path made
 * into a file without a directory is read from the JVM's directory; the proxy is one because the
 * JVM's selector reads the JVM's properties.
 *
 * <p>Read off the compiled classes of the {@code souther-cli} module, so a reference is a row here
 * however it is spelled: a method reference or a static import names the same member.
 */
class TheCommandLineReadsItsProcessThroughItsEnvironmentAloneTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** What asks the process, by the class that answers. */
    private static final Map<String, Set<String>> ASKING_THE_PROCESS = Map.of(
            "java/lang/System", Set.of("getenv", "getProperty", "getProperties", "in", "out", "err",
                    "console"),
            "java/nio/file/Path", Set.of("of"),
            "java/nio/file/Paths", Set.of("get"),
            "java/io/File", Set.of("<init>"),
            "java/net/ProxySelector", Set.of("getDefault"));

    /**
     * Who asks, and what. {@code Environment} is where the process is read, once, into what a run
     * is handed. {@code ProxyProperties} asks the JVM's selector for the system's own proxies,
     * which are not a property and which the JVM alone reads.
     */
    private static final List<String> ASKS = List.of(
            "souther/cli/Environment -> java/lang/System#console",
            "souther/cli/Environment -> java/lang/System#err",
            "souther/cli/Environment -> java/lang/System#getProperties",
            "souther/cli/Environment -> java/lang/System#getenv",
            "souther/cli/Environment -> java/lang/System#in",
            "souther/cli/Environment -> java/lang/System#out",
            "souther/cli/Environment -> java/nio/file/Path#of",
            "souther/cli/backend/ProxyProperties -> java/net/ProxySelector#getDefault");

    @Test
    void everyPlaceTheCommandLineAsksItsProcessIsWrittenDownHere() {
        assertEquals(ASKS, asking(),
                "read it from the Environment the run is handed: a path through Environment.path,"
                        + " a variable or a property through the Environment, a stream through its"
                        + " in, out and err");
    }

    /** The control: the walk sees the command line's own classes, so the answer above is about
     *  them. */
    @Test
    void theWalkSeesTheCommandLine() {
        assertTrue(asking().stream().anyMatch(row -> row.startsWith("souther/cli/Environment ")),
                "the Environment reads the process, so a walk not finding that is finding nothing");
    }

    private static List<String> asking() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-cli"))) {
            for (PoolEntry entry : each.constantPool()) {
                if (entry instanceof MemberRefEntry member) {
                    String owner = member.owner().asInternalName();
                    String name = member.name().stringValue();
                    if (ASKING_THE_PROCESS.getOrDefault(owner, Set.of()).contains(name)) {
                        out.add(each.thisClass().asInternalName() + " -> " + owner + "#" + name);
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }
}
