package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.XMLConstants;
import java.io.StringReader;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A build file this command did not write comes back as its author left it, with a declaration in
 * it.
 *
 * <p>What is asked of the result is that it still parses and says what it now has to say — not that
 * it matches a text written here. A pom rendered out of a parsed tree would also parse, and would
 * come back with the author's comments gone and their layout replaced.
 */
class ABuildIsAddedToRatherThanRewrittenTest {

    private static final String POM = """
            <?xml version="1.0" encoding="UTF-8"?>
            <project xmlns="http://maven.apache.org/POM/4.0.0">
              <modelVersion>4.0.0</modelVersion>
              <groupId>com.acme</groupId>
              <artifactId>billing</artifactId>
              <version>1.2.3</version>

              <!-- pinned deliberately: see the incident on the 3rd -->
              <dependencies>
                <dependency>
                  <groupId>org.junit.jupiter</groupId>
                  <artifactId>junit-jupiter</artifactId>
                  <version>6.1.2</version>
                  <scope>test</scope>
                </dependency>
              </dependencies>
            </project>
            """;

    @Test
    void theDeclarationsGoIntoTheElementsThePomAlreadyHas() throws Exception {
        String edited = MavenBuild.withSoutherDeclared(POM, "9.9.9");

        assertTrue(edited.contains("<!-- pinned deliberately: see the incident on the 3rd -->"),
                "the author's comment did not survive the edit");
        assertEquals(2, elements(edited, "dependency"),
                "the runtime did not land in the dependencies that were there");
        assertTrue(edited.contains("<artifactId>souther-runtime</artifactId>"), edited);
        assertEquals(1, elements(edited, "plugin"));
        assertEquals("com.acme:billing", MavenBuild.coordinateOf(edited).toString());
        assertTrue(edited.contains("<southerVersion>9.9.9</southerVersion>"));
    }

    /** A pom with a {@code <build>} of its own is added to rather than given a second one. */
    @Test
    void aPomThatHasABuildKeepsTheOneItHas() throws Exception {
        String pom = POM.replace("</project>", """
                  <build>
                    <plugins>
                      <plugin>
                        <artifactId>maven-surefire-plugin</artifactId>
                        <version>3.5.6</version>
                      </plugin>
                    </plugins>
                  </build>
                </project>
                """);

        String edited = MavenBuild.withSoutherDeclared(pom, "9.9.9");

        assertEquals(1, elements(edited, "build"));
        assertEquals(1, elements(edited, "plugins"));
        assertEquals(2, elements(edited, "plugin"));
    }

    /** A pom with neither element gets both, and still parses. */
    @Test
    void aPomWithNoDependenciesAndNoBuildGetsBoth() throws Exception {
        String bare = """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>billing</artifactId>
                </project>
                """;

        String edited = MavenBuild.withSoutherDeclared(bare, "9.9.9");

        assertEquals(1, elements(edited, "dependencies"));
        assertEquals(1, elements(edited, "plugins"));
    }

    /** Running it again writes nothing: the same text comes back, so nothing is written at all. */
    @Test
    void aPomThatAlreadyDeclaresSoutherComesBackUnchanged() {
        String once = MavenBuild.withSoutherDeclared(POM, "9.9.9");

        assertSame(once, MavenBuild.withSoutherDeclared(once, "9.9.9"));
    }

    /**
     * A {@code plugins} inside a comment is not the element the declaration belongs in.
     *
     * <p>The reason the path is walked rather than the closing tag searched for. A pom whose comment
     * shows the wiring it replaced is an ordinary pom.
     */
    @Test
    void aCommentThatMentionsPluginsIsNotAPluginsElement() throws Exception {
        String pom = POM.replace("<!-- pinned deliberately: see the incident on the 3rd -->",
                "<!-- we used to have <build><plugins>...</plugins></build> here -->");

        String edited = MavenBuild.withSoutherDeclared(pom, "9.9.9");

        assertEquals(1, elements(edited, "build"), "a declaration went into a comment");
    }

    @Test
    void theGradlePluginGoesIntoThePluginsBlockThatIsThere() {
        String script = """
                plugins {
                    java
                    id("com.diffplug.spotless") version "6.25.0"
                }

                group = "com.acme"
                """;

        String edited = GradleBuild.withThePluginApplied(script, true);

        assertTrue(edited.contains("id(\"org.souther-lang.souther\") version"));
        assertEquals(1, edited.split("plugins \\{", -1).length - 1,
                "a second plugins block, which Gradle refuses:\n" + edited);
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(edited));
        assertEquals("com.acme", GradleBuild.groupOf(edited));
    }

    /**
     * A {@code plugins} block that is only there because it was commented out is not one.
     *
     * <p>The block is found in the script with its comments blanked, and written into the script
     * itself — blanking keeps every other character where it was, so an offset means the same thing
     * in both. Found in the raw text, the line went inside the comment and the run said the build
     * had been edited.
     */
    @Test
    void aCommentedOutPluginsBlockIsNotWrittenInto() {
        String script = """
                /*
                plugins {
                    java
                }
                */
                plugins {
                    java
                }
                """;

        String edited = GradleBuild.withThePluginApplied(script, true);

        assertTrue(edited.indexOf("org.souther-lang.souther") > edited.indexOf("*/"),
                "the line landed inside the comment:\n" + edited);
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(edited),
                "the script does not apply the plugin after being edited:\n" + edited);
    }

    /** A script with no {@code plugins} block gets one, at the top, where the only one may be. */
    @Test
    void aScriptWithNoPluginsBlockGetsOne() {
        String edited = GradleBuild.withThePluginApplied("group = \"com.acme\"\n", true);

        assertTrue(edited.startsWith("plugins {"), edited);
        assertTrue(edited.endsWith("group = \"com.acme\"\n"), edited);
    }

    /** A brace inside a string is not the end of the block it sits in. */
    @Test
    void aBraceInsideAStringDoesNotCloseTheBlock() {
        String script = """
                plugins {
                    java
                    id("com.example.thing") version "1.0" // }
                }
                """;

        String edited = GradleBuild.withThePluginApplied(script, true);

        assertTrue(edited.indexOf("org.souther-lang.souther") > edited.indexOf("com.example.thing"),
                "the line landed before the block it was meant to go inside:\n" + edited);
    }

    /** A Groovy build is written in Groovy, which is what its file name says. */
    @Test
    void aGroovyBuildGetsTheGroovySpelling() {
        assertFalse(GradleBuild.isKotlin("build.gradle"));

        String edited = GradleBuild.withThePluginApplied("plugins {\n    id 'java'\n}\n", false);

        assertTrue(edited.contains("id 'org.souther-lang.souther' version"), edited);
    }

    /**
     * Naming the plugin is not declaring it where declaring it runs it.
     *
     * <p>Each of these poms was read as a project already set up, and each of them compiles no
     * Souther: an entry under {@code pluginManagement} says what version the plugin would have if
     * it were used, one under {@code dependencyManagement} puts nothing on a class path, an
     * artifact of another group is somebody else's artifact, and a comment is prose.
     */
    @Test
    void namingTheArtifactSomewhereElseIsNotDeclaringIt() {
        String managed = """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>billing</artifactId>
                  <dependencyManagement><dependencies><dependency>
                    <groupId>org.souther-lang</groupId>
                    <artifactId>souther-runtime</artifactId>
                    <version>1</version>
                  </dependency></dependencies></dependencyManagement>
                  <build><pluginManagement><plugins><plugin>
                    <groupId>org.souther-lang</groupId>
                    <artifactId>souther-maven-plugin</artifactId>
                    <version>1</version>
                  </plugin></plugins></pluginManagement></build>
                </project>
                """;
        String elsewhere = POM.replace("<groupId>org.junit.jupiter</groupId>", "<groupId>com.elsewhere</groupId>")
                .replace("<artifactId>junit-jupiter</artifactId>",
                        "<artifactId>souther-runtime</artifactId>");
        String mentioned = POM.replace("<!-- pinned deliberately: see the incident on the 3rd -->",
                "<!-- we may add <artifactId>souther-maven-plugin</artifactId> later -->");

        for (String pom : List.of(managed, elsewhere, mentioned)) {
            assertFalse(MavenBuild.declaresThePlugin(pom), pom);
            assertFalse(MavenBuild.declaresTheRuntime(pom), pom);
        }
    }

    /** The control: a pom that declares both where they run is left alone. */
    @Test
    void aPomThatDeclaresThemWhereTheyRunIsLeftAlone() {
        String declared = MavenBuild.withSoutherDeclared(POM, "9.9.9");

        assertTrue(MavenBuild.declaresThePlugin(declared));
        assertTrue(MavenBuild.declaresTheRuntime(declared));
    }

    /**
     * A Gradle script says three things about the plugin, not two.
     *
     * <p>{@code apply false} asks for it without applying it, and a comment naming it says nothing
     * at all. Read as applied, both left a project reported as set up and compiling no Souther;
     * read as absent, the first would have a second request written into a block that already has
     * one, which Gradle refuses outright.
     */
    @Test
    void aGradleScriptSaysWhetherThePluginIsAppliedOrOnlyNamed() {
        assertEquals(GradleBuild.Applied.NOT_YET,
                GradleBuild.appliedIn("plugins {\n    java\n}\n"));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.1.0"
                }
                """));
        assertEquals(GradleBuild.Applied.SOMEWHERE_ELSE, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.1.0" apply false
                }
                """));
        assertEquals(GradleBuild.Applied.NOT_YET, GradleBuild.appliedIn("""
                // id("org.souther-lang.souther") is what we would write
                plugins {
                    java
                }
                """));
        assertEquals(GradleBuild.Applied.SOMEWHERE_ELSE, GradleBuild.appliedIn("""
                plugins {
                    java
                }

                subprojects {
                    apply(plugin = "org.souther-lang.souther")
                }
                """));
    }

    /**
     * A document whose tags do not match is one this says it cannot follow.
     *
     * <p>The walk down a path is what decides where a declaration goes, and an end tag closing
     * something other than what is open leaves it one element up from where it thinks it is. What
     * that produced was both declarations written outside the {@code <project>}, the
     * {@code <dependencies>} that was there ignored, and a pom that then parsed as nothing —
     * reported as an ordinary edit.
     */
    @Test
    void aPomWhoseTagsDoNotMatchIsNotAddedTo() {
        String stray = """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>billing</artifactId>
                  </oops>
                  <dependencies>
                  </dependencies>
                </project>
                """;

        assertFalse(MavenBuild.canBeAddedTo(stray),
                "a document this cannot walk down was taken for one it can");
        assertTrue(MavenBuild.canBeAddedTo(POM), "and the control: an ordinary pom is one it can");
    }

    /**
     * A block written on one line is added to inside its braces.
     *
     * <p>Inserted before the line rather than before the brace, the plugin was applied at the
     * script's top level — where {@code id(...)} is not a function — and the build did not
     * evaluate at all.
     */
    @Test
    void aOneLinePluginsBlockIsAddedToInsideItsBraces() {
        String edited = GradleBuild.withThePluginApplied("plugins { java }\n\ngroup = \"a\"\n", true);

        int applied = edited.indexOf("id(\"org.souther-lang.souther\")");
        assertTrue(applied > edited.indexOf("plugins {"),
                "the line landed before the block it was meant to go inside:\n" + edited);
        assertTrue(applied < edited.indexOf("}"),
                "the line landed after the block closed:\n" + edited);
        assertEquals(1, edited.split("plugins \\{", -1).length - 1, edited);
    }

    /** How many elements of this name the document has, read as a document rather than as text. */
    private static int elements(String xml, String name) throws Exception {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, "");
        factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_SCHEMA, "");
        Document document = factory.newDocumentBuilder()
                .parse(new InputSource(new StringReader(xml)));
        NodeList found = document.getElementsByTagName(name);
        return found.getLength();
    }
}
