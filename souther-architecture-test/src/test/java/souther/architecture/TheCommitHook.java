package souther.architecture;

import com.puppycrawl.tools.checkstyle.Checker;
import com.puppycrawl.tools.checkstyle.ConfigurationLoader;
import com.puppycrawl.tools.checkstyle.PropertiesExpander;
import com.puppycrawl.tools.checkstyle.api.AuditEvent;
import com.puppycrawl.tools.checkstyle.api.AuditListener;
import com.puppycrawl.tools.checkstyle.api.CheckstyleException;
import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The pre-commit hook and the Error Prone it stands for, each asked about the same files.
 *
 * <p>The hook is Checkstyle running {@code config/checkstyle.xml}, the file the hook reads, and
 * nothing is configured here. Error Prone is the compiler plugin at the version the lint build runs,
 * in a {@code javac} of its own with one check turned on, so what it says is what it says and not a
 * reading of its documentation or its source.
 */
final class TheCommitHook {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** What the hook refuses, and where. */
    record Finding(Path file, int line, String rule, String message) {
    }

    private TheCommitHook() {
    }

    /** What the hook refuses in {@code files}, by every rule it runs. */
    static List<Finding> refusals(List<Path> files) throws CheckstyleException {
        List<Finding> found = new ArrayList<>();
        List<Throwable> failures = new ArrayList<>();
        Checker checker = new Checker();
        try {
            checker.setModuleClassLoader(Checker.class.getClassLoader());
            checker.configure(ConfigurationLoader.loadConfiguration(
                    REPOSITORY.root().resolve("config/checkstyle.xml").toString(),
                    new PropertiesExpander(new Properties())));
            checker.addListener(new AuditListener() {
                @Override
                public void auditStarted(AuditEvent event) {
                }

                @Override
                public void auditFinished(AuditEvent event) {
                }

                @Override
                public void fileStarted(AuditEvent event) {
                }

                @Override
                public void fileFinished(AuditEvent event) {
                }

                @Override
                public void addError(AuditEvent event) {
                    found.add(new Finding(Path.of(event.getFileName()), event.getLine(),
                            event.getSourceName().substring(event.getSourceName().lastIndexOf('.') + 1),
                            event.getMessage()));
                }

                @Override
                public void addException(AuditEvent event, Throwable throwable) {
                    failures.add(throwable);
                }
            });
            checker.process(files.stream().map(file -> file.toAbsolutePath().toFile()).toList());
        } finally {
            checker.destroy();
        }
        assertTrue(failures.isEmpty(), "Checkstyle failed: " + failures);
        return found;
    }

    /** How many times the hook's rule named {@code rule} refuses something in each of {@code files}. */
    static Map<Path, Integer> refusalsBy(String rule, List<Path> files) throws CheckstyleException {
        Map<Path, Integer> counted = new LinkedHashMap<>();
        for (Finding each : refusals(files)) {
            if (each.rule().startsWith(rule)) {
                counted.merge(each.file(), 1, Integer::sum);
            }
        }
        return counted;
    }

    /**
     * How many times Error Prone's {@code check} refuses something in each of {@code files}.
     *
     * <p>Run in a {@code javac} of the JDK this test runs on, because Error Prone needs the compiler's
     * packages opened to it and a test's own JVM does not open them. The sources have to compile.
     */
    static Map<Path, Integer> errorProneRefusals(String check, Path scratch, List<Path> files)
            throws IOException, InterruptedException {
        Path javac = Path.of(System.getProperty("java.home"), "bin", "javac");
        assertTrue(Files.isExecutable(javac), "a JDK's javac is what Error Prone runs inside: " + javac);
        List<String> command = new ArrayList<>(List.of(javac.toString(), "-proc:none",
                "-d", Files.createTempDirectory(scratch, "classes").toString()));
        for (String exported : List.of("api", "file", "main", "model", "parser", "processing",
                "tree", "util", "code", "comp")) {
            command.add("-J--add-exports=jdk.compiler/com.sun.tools.javac." + exported + "=ALL-UNNAMED");
        }
        command.add("-J--add-opens=jdk.compiler/com.sun.tools.javac.code=ALL-UNNAMED");
        command.add("-J--add-opens=jdk.compiler/com.sun.tools.javac.comp=ALL-UNNAMED");
        command.addAll(List.of("-XDcompilePolicy=simple", "--should-stop=ifError=FLOW",
                "-Xmaxwarns", "10000", "-Xmaxerrs", "10000",
                "-processorpath", System.getProperty("java.class.path"),
                "-Xplugin:ErrorProne -XepDisableAllChecks -Xep:" + check + ":WARN"));
        files.forEach(file -> command.add(file.toString()));

        Process process = new ProcessBuilder(command).redirectErrorStream(true).start();
        String output = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        assertEquals(0, process.waitFor(), "javac with Error Prone failed:\n" + output);

        // What javac calls a warning depends on the locale it runs in; the check's own tag does not.
        Pattern refusal = Pattern.compile("^(.*\\.java):\\d+: [^\\n]*?\\[" + Pattern.quote(check) + "]",
                Pattern.MULTILINE);
        Map<Path, Integer> counted = new LinkedHashMap<>();
        Matcher found = refusal.matcher(output);
        while (found.find()) {
            counted.merge(Path.of(found.group(1)), 1, Integer::sum);
        }
        return counted;
    }
}
