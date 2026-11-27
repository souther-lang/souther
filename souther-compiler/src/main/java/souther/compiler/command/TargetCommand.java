package souther.compiler.command;

import java.util.List;

/**
 * What {@code souther compile --target <target>} runs for a target that is not built in.
 *
 * <p>A backend is a jar that provides one of these, named the way a {@code ServiceLoader} finds
 * a provider. The command line loads the jar beside its own classes and calls it in the JVM
 * it is running in, so the compiler a backend reads a program with is the one the command line
 * holds, and the jar carries only what is the backend's own. What a backend uses is in that one
 * jar or is the command line's: a jar is not read for a class path of its own.
 *
 * <p>A provider is a public class with a public constructor that takes nothing. From before the
 * class is linked until {@link #run} has answered, the thread's context class loader is the one
 * that reads the jar, so a lookup made without naming a loader finds what the jar holds, in a
 * static initializer and a constructor as in the run. A provider that cannot be linked or
 * constructed is refused as a jar that is no backend; what {@code run} throws is thrown on to the
 * command line as a failure of its own would be.
 *
 * <p>The run is the command line's, continued: the arguments are what the line holds after the
 * target's name, and the environment is the one the command line was handed. A command reads its
 * variables, its properties, its streams and the directory a path is read from out of that value
 * and asks the process for none of them, and what it answers is what the process exits with. It
 * does not end the process itself.
 */
public interface TargetCommand {

    /** Runs the command with {@code arguments} in {@code environment}, answering its exit status. */
    int run(List<String> arguments, Environment environment);
}
