package souther.architecture;

import com.puppycrawl.tools.checkstyle.JavaParser;
import com.puppycrawl.tools.checkstyle.api.CheckstyleException;
import com.puppycrawl.tools.checkstyle.api.DetailAST;
import com.puppycrawl.tools.checkstyle.api.TokenTypes;
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A test class one module's tests read from another module's tests is one the other module's
 * test-jar ships, and so is every test class of that module a class it ships names.
 *
 * <p>Within the reactor a test run hands a module the test classes of the module it depends on as
 * they were compiled, every one of them. A build that packages hands it the test-jar, which ships
 * only the classes its {@code includes} name. A test importing a class the jar leaves out compiles
 * on the one and not on the other, and a class the jar ships that names one it leaves out fails
 * when it is run: either way a local run is green where a build that packages is red. A class names
 * another of its own package by its simple name and imports nothing for it, so what it names is
 * read off its code and not off its imports. This asks it of the sources, where both builds agree.
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
                // What the other module's tests are read for, and then every test class of that
                // module those name, until nothing new is named.
                Map<Path, Path> namedBy = new LinkedHashMap<>();
                for (Path source : sourcesUnder(tests)) {
                    for (Path read : importedFrom(source, otherTests, otherMain)) {
                        namedBy.putIfAbsent(read, source);
                    }
                }
                List<Path> toRead = new ArrayList<>(namedBy.keySet());
                for (int at = 0; at < toRead.size(); at++) {
                    Path reached = toRead.get(at);
                    asked++;
                    String file = otherTests.relativize(reached).toString()
                            .replace(reached.getFileSystem().getSeparator(), "/");
                    String compiled = file.substring(0, file.length() - ".java".length())
                            + ".class";
                    if (shipped.stream().noneMatch(one -> one.matcher(compiled).matches())) {
                        missing.add(REPOSITORY.root().relativize(namedBy.get(reached)) + " reads "
                                + compiled.substring(0, compiled.length() - ".class".length())
                                        .replace('/', '.')
                                + ", which the test-jar of " + depended + " does not ship");
                    }
                    Set<Path> named = new LinkedHashSet<>(importedFrom(reached, otherTests, otherMain));
                    named.addAll(ofItsPackageNamedIn(reached, otherMain, otherTests));
                    for (Path each : named) {
                        if (namedBy.putIfAbsent(each, reached) == null) {
                            toRead.add(each);
                        }
                    }
                }
            }
        }
        assertFalse(asked == 0, "no test class read across modules was found, so this asked nothing");
        assertEquals(new TreeSet<String>(), missing,
                "a test class read by another module's tests, or named by one its test-jar ships, is"
                        + " left out of its module's test-jar: name it in the includes of that"
                        + " module's maven-jar-plugin test-jar");
    }

    /** The test classes under {@code tests} that the source at {@code source} imports, leaving
     *  out a name {@code main} declares as well, which is the main class. */
    private static List<Path> importedFrom(Path source, Path tests, Path main) throws IOException {
        List<Path> out = new ArrayList<>();
        Matcher imported = IMPORT.matcher(Files.readString(source));
        while (imported.find()) {
            String file = imported.group(1).replace('.', '/') + "/" + imported.group(2) + ".java";
            if (Files.isRegularFile(tests.resolve(file))
                    && (main == null || !Files.isRegularFile(main.resolve(file)))) {
                out.add(tests.resolve(file));
            }
        }
        return out;
    }

    /**
     * The test classes of its own package the source at {@code source} names by their simple
     * name, in its code and not in a comment, leaving out one {@code main} declares in the same
     * package, which is the main class.
     */
    private static Set<Path> ofItsPackageNamedIn(Path source, Path main, Path tests)
            throws CheckstyleException, IOException {
        Path packageDir = source.getParent();
        Path mainPackage = main == null ? null : main.resolve(tests.relativize(packageDir));
        Set<Path> out = new LinkedHashSet<>();
        List<DetailAST> toWalk = new ArrayList<>();
        toWalk.add(JavaParser.parseFile(source.toFile(), JavaParser.Options.WITHOUT_COMMENTS));
        while (!toWalk.isEmpty()) {
            DetailAST node = toWalk.removeLast();
            for (DetailAST child = node.getFirstChild(); child != null;
                 child = child.getNextSibling()) {
                toWalk.add(child);
            }
            if (node.getType() == TokenTypes.IDENT) {
                Path named = packageDir.resolve(node.getText() + ".java");
                if (!named.equals(source) && Files.isRegularFile(named)
                        && (mainPackage == null
                                || !Files.isRegularFile(mainPackage.resolve(named.getFileName())))) {
                    out.add(named);
                }
            }
        }
        return out;
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
