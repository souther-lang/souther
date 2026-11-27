package souther.cli.backend;

import souther.compiler.command.Environment;
import souther.compiler.command.TargetCommand;

import java.util.List;

/**
 * A command the loader of these tests defines, for a jar to name as if it were its own. It is
 * never run: a jar naming it provides nothing.
 */
public final class ACommandOfThisClassPath implements TargetCommand {

    @Override
    public int run(List<String> arguments, Environment environment) {
        throw new AssertionError("a command the jar does not hold was run as the jar's");
    }
}
