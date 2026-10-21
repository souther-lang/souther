package souther.cli;

import java.io.Console;
import java.io.InputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

/**
 * What a run of the command line is given besides its arguments: the variables and properties it
 * reads, the directory it is run in, and the streams it reads and writes.
 *
 * <p>Read from the process once, by {@link Main#main}, and handed to everything below it. Nothing
 * under {@code main} asks the process for a variable, a property or a stream of its own accord, so
 * a run is a function of its arguments and this value: a test runs the command line in its own JVM
 * with the variables it names and streams it reads back, and two such runs share nothing a run
 * reads.
 *
 * <p>{@code processStreams} says whether {@code in}, {@code out} and {@code err} are this process's
 * own standard streams. Two things are decided by it and by nothing else: a process the run starts
 * inherits the streams where they are the process's, and is given pipes copied to and from them
 * where they are not; and only the process's own output can be a terminal.
 *
 * @param variables the environment variables, by name
 * @param properties the system properties, by name
 * @param workingDirectory where a project's version file is looked for from, and where a process
 *        the run starts is started
 */
public record Environment(Map<String, String> variables, Map<String, String> properties,
                          Path workingDirectory, InputStream in, PrintStream out, PrintStream err,
                          boolean processStreams) {

    public Environment {
        variables = Map.copyOf(variables);
        properties = Map.copyOf(properties);
    }

    /**
     * What this process was started with: its environment, its system properties as they stand,
     * the directory it runs in, and its standard streams as they stand.
     */
    public static Environment ofThisProcess() {
        Properties system = System.getProperties();
        Map<String, String> properties = new HashMap<>();
        for (String name : system.stringPropertyNames()) {
            properties.put(name, system.getProperty(name));
        }
        return new Environment(System.getenv(), properties, Path.of(""), System.in, System.out,
                System.err, true);
    }

    /** The variable {@code name}, or null where it is not set. */
    public String variable(String name) {
        return variables.get(name);
    }

    /** The property {@code name}, or null where it is not set. */
    public String property(String name) {
        return properties.get(name);
    }

    /**
     * Whether what this run writes to {@code out} lands on a terminal.
     *
     * <p>Two things have to hold, and the console knows only the second. A runtime built without a
     * console provider answers none at all, so the null stands; and where there is one it exists
     * whether or not the output is a terminal, so it is asked which — colour written into a pipe is
     * escape codes in a file. A run whose streams are not the process's writes to none.
     */
    public boolean terminal() {
        return processStreams && System.console() instanceof Console c && c.isTerminal();
    }
}
