package souther.architecture;

import com.puppycrawl.tools.checkstyle.Checker;
import com.puppycrawl.tools.checkstyle.ConfigurationLoader;
import com.puppycrawl.tools.checkstyle.PropertiesExpander;
import com.puppycrawl.tools.checkstyle.api.AuditEvent;
import com.puppycrawl.tools.checkstyle.api.AuditListener;
import com.puppycrawl.tools.checkstyle.api.CheckstyleException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.test.RepositoryLayout;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the pre-commit hook says about {@code ArrayList}, {@code LinkedList}, {@code HashSet},
 * {@code LinkedHashSet}, {@code TreeSet}, {@code HashMap}, {@code LinkedHashMap} and
 * {@code TreeMap}, held against what Error Prone's NonApiType says of them.
 *
 * <p>CI refuses one of them in the type of a parameter or of a method's result, at any visibility,
 * and looks through type arguments, so {@code Map<String, ArrayList<X>>} is refused as
 * {@code ArrayList<X>} is. It does not look at a field or a local variable, and a
 * {@code @SuppressWarnings("NonApiType")} on the parameter, the method or a class around it stands.
 * The hook is the same question asked of a parser, so each of those edges is a case here: a rule
 * that stopped at the first line of a signature, or at the outermost type, would let a commit
 * through that CI refuses, and one that went on into the body would stop a commit CI accepts.
 *
 * <p>Run by Checkstyle itself over {@code config/checkstyle.xml}, the file the hook reads.
 */
class TheCommitHookRefusesTheCollectionClassesErrorProneRefusesInASignatureTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** What a member of the class is, and how many times the hook refuses it. */
    private record Case(String name, String members, int refused) {
    }

    private static final List<Case> CASES = List.of(
            new Case("a result named for its class",
                    "ArrayList<String> f() { return null; }", 1),
            new Case("a parameter named for its class",
                    "void f(LinkedHashMap<String, String> m) { }", 1),
            new Case("a result that holds one in a type argument",
                    "Map<String, ArrayList<String>> f() { return null; }", 1),
            new Case("a parameter that holds one two type arguments down",
                    "void f(Map<String, List<TreeSet<String>>> m) { }", 1),
            new Case("a parameter that is not on the first line of the signature",
                    "void f(int n,\n               HashMap<String, String> m) { }", 1),
            new Case("a qualified name",
                    "java.util.HashSet<String> f() { return null; }", 1),
            new Case("a constructor parameter",
                    "Fixture(TreeMap<String, String> m) { }", 1),
            new Case("a method of an interface",
                    "interface Reads { LinkedList<String> all(); }", 1),
            new Case("two in one signature",
                    "HashSet<String> f(HashMap<String, String> m) { return null; }", 2),
            new Case("a field",
                    "private final ArrayList<String> held = new ArrayList<>();", 0),
            new Case("a local variable and what is built into it",
                    "List<String> f() { ArrayList<String> local = new ArrayList<>(); return local; }", 0),
            new Case("a construction returned as the interface",
                    "List<String> f() { return new ArrayList<>(); }", 0),
            new Case("the interfaces they implement",
                    "Map<String, List<String>> f(Map<String, String> m, List<String> l) { return null; }", 0),
            new Case("a method that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") ArrayList<String> f() { return null; }", 0),
            new Case("a parameter that suppresses it",
                    "void f(@SuppressWarnings(\"NonApiType\") HashMap<String, String> m) { }", 0),
            new Case("a method that suppresses it among others",
                    "@SuppressWarnings({\"unused\", \"NonApiType\"}) ArrayList<String> f() { return null; }", 0),
            new Case("a method that suppresses something else",
                    "@SuppressWarnings(\"unused\") ArrayList<String> f() { return null; }", 1),
            new Case("the method beside one that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") ArrayList<String> f() { return null; }\n"
                            + "    ArrayList<String> g() { return null; }", 1));

    @Test
    void eachEdgeOfWhatErrorProneRefusesIsWhatTheHookRefuses(@TempDir Path dir) throws Exception {
        Map<String, Case> filed = new LinkedHashMap<>();
        for (int i = 0; i < CASES.size(); i++) {
            Case each = CASES.get(i);
            Path file = dir.resolve("Fixture" + i + ".java");
            Files.writeString(file, """
                    package fixture;

                    import java.util.*;

                    final class Fixture%d {
                        %s
                    }
                    """.formatted(i, each.members().replace("Fixture(", "Fixture" + i + "(")));
            filed.put(file.toString(), each);
        }

        Map<String, Integer> refused = refusedBy(List.copyOf(filed.keySet()));

        List<String> disagreements = new ArrayList<>();
        for (Map.Entry<String, Case> each : filed.entrySet()) {
            int found = refused.getOrDefault(each.getKey(), 0);
            if (found != each.getValue().refused()) {
                disagreements.add(each.getValue().name() + ": expected "
                        + each.getValue().refused() + ", the hook refused " + found);
            }
        }
        assertEquals(List.of(), disagreements);
    }

    @Test
    void theClassSuppressionStandsForEveryMemberOfTheClass(@TempDir Path dir) throws Exception {
        Path file = Files.writeString(dir.resolve("Suppressed.java"), """
                package fixture;

                import java.util.*;

                @SuppressWarnings("NonApiType")
                final class Suppressed {
                    ArrayList<String> f() { return null; }

                    void g(HashMap<String, String> m) { }
                }
                """);

        assertEquals(0, refusedBy(List.of(file.toString())).getOrDefault(file.toString(), 0),
                "a suppression on the class stands for what is written in it");
    }

    @Test
    void theRuleIsOneTheHookRunsAndNotOnlyOneThatIsWritten() throws IOException {
        String config = Files.readString(REPOSITORY.root().resolve("config/checkstyle.xml"));

        assertTrue(config.contains("<module name=\"MatchXpath\">"),
                "the cases above are run against the file the hook reads, and this is the rule in it");
    }

    /** How many times each file was refused by the NonApiType rule. */
    private static Map<String, Integer> refusedBy(List<String> files) throws CheckstyleException {
        List<AuditEvent> events = new ArrayList<>();
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
                    events.add(event);
                }

                @Override
                public void addException(AuditEvent event, Throwable throwable) {
                    failures.add(throwable);
                }
            });
            checker.process(files.stream().map(File::new).toList());
        } finally {
            checker.destroy();
        }
        assertTrue(failures.isEmpty(), "Checkstyle failed on a fixture: " + failures);
        Map<String, Integer> refused = new LinkedHashMap<>();
        for (AuditEvent event : events) {
            if (event.getSourceName().contains("MatchXpath")) {
                refused.merge(event.getFileName(), 1, Integer::sum);
            }
        }
        return refused;
    }
}
