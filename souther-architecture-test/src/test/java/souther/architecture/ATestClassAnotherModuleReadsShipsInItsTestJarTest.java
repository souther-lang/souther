package souther.architecture;

import org.junit.jupiter.api.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import souther.test.RepositoryLayout;

import javax.xml.parsers.DocumentBuilderFactory;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A test class one module's tests import from another module's tests is one the other module's
 * test-jar ships.
 *
 * <p>Within the reactor a test run hands a module the test classes of the module it depends on as
 * they were compiled, every one of them. A build that packages hands it the test-jar, which ships
 * only the classes its {@code includes} name. A test importing a class the jar leaves out compiles
 * on the one and not on the other, so a local run is green where a build that packages is red.
 * This asks it of the sources, where both builds agree.
 */
class ATestClassAnotherModuleReadsShipsInItsTestJarTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final Pattern IMPORT =
            Pattern.compile("(?m)^import\\s+(?:static\\s+)?([\\w.]+?)\\.([A-Z]\\w*)[\\w.]*;");

    @Test
    void everyTestClassReadAcrossModulesShipsInItsTestJar() throws Exception {
        TreeSet<String> missing = new TreeSet<>();
        int asked = 0;
        for (Path module : REPOSITORY.modules()) {
            Path tests = REPOSITORY.javaTreeOf(module, "test");
            if (tests == null) {
                continue;
            }
            for (String depended : testJarsDependedOn(module.resolve("pom.xml"))) {
                Path other = REPOSITORY.moduleNamed(depended);
                Path otherTests = REPOSITORY.javaTreeOf(other, "test");
                Path otherMain = REPOSITORY.javaTreeOf(other, "main");
                if (otherTests == null) {
                    continue;
                }
                List<Pattern> shipped = includesOfTheTestJar(other.resolve("pom.xml"));
                for (Path source : sourcesUnder(tests)) {
                    Matcher imported = IMPORT.matcher(Files.readString(source));
                    while (imported.find()) {
                        String file = imported.group(1).replace('.', '/') + "/"
                                + imported.group(2);
                        if (!Files.isRegularFile(otherTests.resolve(file + ".java"))
                                || (otherMain != null
                                        && Files.isRegularFile(otherMain.resolve(file + ".java")))) {
                            continue;
                        }
                        asked++;
                        String compiled = file + ".class";
                        if (shipped.stream().noneMatch(one -> one.matcher(compiled).matches())) {
                            missing.add(REPOSITORY.root().relativize(source) + " reads "
                                    + file.replace('/', '.') + ", which the test-jar of "
                                    + depended + " does not ship");
                        }
                    }
                }
            }
        }
        assertFalse(asked == 0, "no test class read across modules was found, so this asked nothing");
        assertEquals(new TreeSet<String>(), missing,
                "a test class read by another module's tests is left out of its module's test-jar:"
                        + " name it in the includes of that module's maven-jar-plugin test-jar");
    }

    /** The modules whose test-jar the pom at {@code pom} depends on, by artifact. */
    private static List<String> testJarsDependedOn(Path pom) throws Exception {
        List<String> out = new ArrayList<>();
        NodeList dependencies = read(pom).getElementsByTagName("dependency");
        for (int i = 0; i < dependencies.getLength(); i++) {
            Element dependency = (Element) dependencies.item(i);
            if ("test-jar".equals(childText(dependency, "type"))) {
                out.add(childText(dependency, "artifactId"));
            }
        }
        return out;
    }

    /**
     * What the test-jar the pom at {@code pom} builds ships: each of its {@code includes} as a
     * pattern over a class file's path, or every class where it names none.
     */
    private static List<Pattern> includesOfTheTestJar(Path pom) throws Exception {
        NodeList executions = read(pom).getElementsByTagName("execution");
        Map<String, Element> byGoal = new LinkedHashMap<>();
        for (int i = 0; i < executions.getLength(); i++) {
            Element execution = (Element) executions.item(i);
            NodeList goals = execution.getElementsByTagName("goal");
            for (int g = 0; g < goals.getLength(); g++) {
                byGoal.put(goals.item(g).getTextContent().strip(), execution);
            }
        }
        Element testJar = byGoal.get("test-jar");
        List<Pattern> out = new ArrayList<>();
        if (testJar != null) {
            NodeList includes = testJar.getElementsByTagName("include");
            for (int i = 0; i < includes.getLength(); i++) {
                out.add(Pattern.compile(Pattern.quote(includes.item(i).getTextContent().strip())
                        .replace("*", "\\E[^/]*\\Q")));
            }
        }
        return out.isEmpty() ? List.of(Pattern.compile(".*")) : out;
    }

    private static List<Path> sourcesUnder(Path tree) throws IOException {
        return REPOSITORY.filesUnderSourceTrees(".java").stream()
                .filter(each -> each.startsWith(tree)).toList();
    }

    private static Document read(Path pom) throws Exception {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        factory.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
        return factory.newDocumentBuilder().parse(pom.toFile());
    }

    private static String childText(Element parent, String name) {
        NodeList children = parent.getChildNodes();
        for (int i = 0; i < children.getLength(); i++) {
            if (children.item(i) instanceof Element child && child.getTagName().equals(name)) {
                return child.getTextContent().strip();
            }
        }
        return null;
    }
}
