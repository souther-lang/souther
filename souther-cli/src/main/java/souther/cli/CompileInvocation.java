package souther.cli;

import java.util.Arrays;
import java.util.List;

/**
 * Which grammar the arguments of {@code compile} are read in.
 *
 * <p>{@code --target} is not an option of {@code compile}. Written first, it chooses the grammar:
 * {@code jvm} is the one this compiler has always read, by {@link CliOption}, and any other target
 * is an installed backend's, whose arguments are its own and are not read here at all. Written
 * anywhere else it is an option {@code compile} does not have. So where the CLI's arguments end and a
 * backend's begin is a place on the line and not something to be searched for.
 */
sealed interface CompileInvocation {

    /** The JVM's {@code compile}, with the arguments it reads. */
    record Jvm(List<String> arguments) implements CompileInvocation {}

    /** An installed target's {@code compile}, with the arguments it is handed as written. */
    record Target(String name, List<String> arguments) implements CompileInvocation {}

    /** {@code --target} was written with no target after it. */
    record Unnamed() implements CompileInvocation {}

    /** The grammar these arguments are in. */
    static CompileInvocation read(String[] arguments) {
        if (arguments.length == 0 || !arguments[0].equals("--target")) {
            return new Jvm(List.of(arguments));
        }
        if (arguments.length < 2 || arguments[1].startsWith("-")) {
            return new Unnamed();
        }
        List<String> rest = List.of(Arrays.copyOfRange(arguments, 2, arguments.length));
        return arguments[1].equals("jvm") ? new Jvm(rest) : new Target(arguments[1], rest);
    }
}
