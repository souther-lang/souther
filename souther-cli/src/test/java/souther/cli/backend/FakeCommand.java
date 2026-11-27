package souther.cli.backend;

import souther.compiler.command.Environment;
import souther.compiler.command.TargetCommand;
import souther.compiler.meta.ModuleMetadata;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.List;

/**
 * The command a {@link FakeBackend} jar provides, as this build compiles it. A jar holds it under
 * another name, since a class of this name is this class path's and so not the jar's own.
 *
 * <p>It is made only where the thread's context loader is the one that defined it, and says so
 * where it is not: every test that runs one holds the command line to having set that loader
 * before the command is constructed.
 */
public class FakeCommand implements TargetCommand {

    /** What a command constructed under another loader than its own refuses to be made with. */
    public static final String MADE_ELSEWHERE = "constructed under a context loader not its own";

    /** What a command asked to fail throws, with {@code --throw}. */
    public static final String ASKED_TO_FAIL = "the fake backend was asked to fail";

    public FakeCommand() {
        if (Thread.currentThread().getContextClassLoader() != getClass().getClassLoader()) {
            throw new IllegalStateException(MADE_ELSEWHERE);
        }
    }

    @Override
    public int run(List<String> args, Environment environment) {
        if (args.contains("--throw")) {
            throw new IllegalStateException(ASKED_TO_FAIL);
        }
        PrintStream out = environment.out();
        // Asked of the class this is run as and not of this one by name: a jar holds it renamed.
        try (InputStream marker = getClass().getResourceAsStream("/" + FakeBackend.MARKER)) {
            out.println("marker=" + new String(marker.readAllBytes(), StandardCharsets.UTF_8));
            out.println("args=" + String.join("|", args));
            out.println("cwd=" + environment.workingDirectory().toRealPath());
            out.println("env=" + environment.variable("FAKE_ENV"));
            out.println("property=" + environment.property("fake.property"));
            out.println("compiler=" + ModuleMetadata.compilerVersion());
            out.println("stdin=" + new String(environment.in().readAllBytes(),
                    StandardCharsets.UTF_8));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        environment.err().println("said-on-stderr");
        int status = 0;
        for (int i = 0; i < args.size() - 1; i++) {
            if (args.get(i).equals("--exit")) {
                status = Integer.parseInt(args.get(i + 1));
            }
        }
        return status;
    }
}
