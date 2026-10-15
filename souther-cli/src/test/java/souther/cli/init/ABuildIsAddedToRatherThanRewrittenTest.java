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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
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
        // The plugin reads the Souther off the runtime the pom now names, and takes no version of
        // its own.
        assertFalse(edited.contains("southerVersion"), edited);
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

        String edited = GradleBuild.withThePluginApplied(script, true, "9.9.9");

        assertTrue(edited.contains("id(\"org.souther-lang.souther\") version"));
        assertEquals(1, edited.split("plugins \\{", -1).length - 1,
                "a second plugins block, which Gradle refuses:\n" + edited);
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(edited, true));
        assertEquals("com.acme", GradleBuild.groupOf(edited, true));
        assertTrue(edited.endsWith("souther {\n    southerVersion = \"9.9.9\"\n}\n"),
                "the plugin is not told which Souther to compile with:\n" + edited);
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

        String edited = GradleBuild.withThePluginApplied(script, true, "9.9.9");

        assertTrue(edited.indexOf("org.souther-lang.souther") > edited.indexOf("*/"),
                "the line landed inside the comment:\n" + edited);
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(edited, true),
                "the script does not apply the plugin after being edited:\n" + edited);
    }

    /** A script with no {@code plugins} block gets one, at the top, where the only one may be. */
    @Test
    void aScriptWithNoPluginsBlockGetsOne() {
        String edited = GradleBuild.withThePluginApplied("group = \"com.acme\"\n", true, "9.9.9");

        assertTrue(edited.startsWith("plugins {"), edited);
        assertTrue(edited.contains("}\n\ngroup = \"com.acme\"\n\nsouther {"), edited);
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

        String edited = GradleBuild.withThePluginApplied(script, true, "9.9.9");

        assertTrue(edited.indexOf("org.souther-lang.souther") > edited.indexOf("com.example.thing"),
                "the line landed before the block it was meant to go inside:\n" + edited);
    }

    /** A Groovy build is written in Groovy, which is what its file name says. */
    @Test
    void aGroovyBuildGetsTheGroovySpelling() {
        assertFalse(GradleBuild.isKotlin("build.gradle"));

        String edited = GradleBuild.withThePluginApplied("plugins {\n    id 'java'\n}\n", false,
                "9.9.9");

        assertTrue(edited.contains("id 'org.souther-lang.souther' version"), edited);
        assertTrue(edited.contains("southerVersion = '9.9.9'"), edited);
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
                GradleBuild.appliedIn("plugins {\n    java\n}\n", true));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }

                souther {
                    southerVersion = "0.4.0"
                }
                """, true));
        // Applied, and nothing in the script says which Souther it compiles with: the plugin has
        // no default, so a model added here would not build.
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }
                """, true));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }

                // souther { southerVersion = "0.4.0" }
                """, true));
        assertEquals(GradleBuild.Applied.SOMEWHERE_ELSE, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.1.0" apply false
                }
                """, true));
        assertEquals(GradleBuild.Applied.NOT_YET, GradleBuild.appliedIn("""
                // id("org.souther-lang.souther") is what we would write
                plugins {
                    java
                }
                """, true));
        assertEquals(GradleBuild.Applied.SOMEWHERE_ELSE, GradleBuild.appliedIn("""
                plugins {
                    java
                }

                subprojects {
                    apply(plugin = "org.souther-lang.souther")
                }
                """, true));
    }

    /**
     * A version counts as set only in the forms this reads, and only where they configure this
     * project.
     *
     * <p>A yes is what lets a model be written, so a name that only reads the same must be a no: a
     * yes it could not stand behind leaves a project that stops at {@code compileSouther}.
     */
    @Test
    void aVersionIsSetOnlyWhereTheExtensionIsTold() {
        String applied = """
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }

                """;
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(applied
                + "souther.southerVersion.set(\"0.4.0\")\n", true));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(applied
                + "souther { southerVersion = \"0.4.0\" }\n", true));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(applied
                + "souther {\n    southerVersion.set(\"0.4.0\")\n}\n", true));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(
                "plugins {\n    id 'org.souther-lang.souther' version '0.2.0'\n}\n\n"
                        + "souther {\n    southerVersion = '0.4.0'\n}\n", false));

        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(applied
                + "val southerVersion = \"0.4.0\"\n", true));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(applied
                + "println(\"southerVersion\")\n", true));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(applied
                + "subprojects {\n    souther {\n        southerVersion = \"0.4.0\"\n    }\n}\n",
                true));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(applied
                + "souther {\n    sourceDirectory = layout.projectDirectory.dir(\"model\")\n}\n",
                true));
    }

    /**
     * A block written inside a string of any kind is text, and sets nothing.
     *
     * <p>Each of these opens with a quote a reader of single-quoted strings would take as closing
     * at the next one, leaving the block outside it. A template is code, and what it holds closes
     * where it closes rather than at the first quote in it.
     */
    @Test
    void aBlockInsideAStringOfAnyKindSetsNothing() {
        String kotlin = """
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }

                """;
        String groovy = """
                plugins {
                    id 'org.souther-lang.souther' version '0.2.0'
                }

                """;
        String block = "souther {\n    southerVersion = \"0.4.0\"\n}\n";
        String q3 = "\"\"\"";

        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(kotlin
                + "val documentation = " + q3 + "\n\"\n" + block + q3 + "\n", true));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(groovy
                + "def documentation = '''\n'\n" + block + "'''\n", false));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(groovy
                + "def documentation = " + q3 + "\n\"\n" + block + q3 + "\n", false));
        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn(groovy
                + "def documentation = $/\n" + block + "/$\n", false));
        // And a template whose code holds a string with a brace closes at its own brace.
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(kotlin
                + "val note = \"${\"}\"}\"\n\n" + block, true));
    }

    /**
     * A block comment ends where its language ends it: a Kotlin one after every comment opened in
     * it, a Groovy one at the first close.
     */
    @Test
    void aBlockCommentEndsWhereItsLanguageEndsIt() {
        String block = "souther {\n    southerVersion = \"0.4.0\"\n}\n";

        assertEquals(GradleBuild.Applied.UNTOLD, GradleBuild.appliedIn("""
                plugins {
                    id("org.souther-lang.souther") version "0.2.0"
                }

                /*
                    /* what was written before */
                """ + block + "*/\n", true));
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn("""
                plugins {
                    id 'org.souther-lang.souther' version '0.2.0'
                }

                /* an old note /* that Groovy closes here */
                """ + block, false));
    }

    /**
     * A {@code plugins} block counts only at the top level, both where one is read and where one
     * is written into.
     */
    @Test
    void onlyATopLevelPluginsBlockIsTheScriptsOwn() {
        String nested = """
                subprojects {
                    plugins {
                        id("org.souther-lang.souther") version "0.2.0"
                    }
                }
                """;

        assertEquals(GradleBuild.Applied.SOMEWHERE_ELSE, GradleBuild.appliedIn(nested, true));
        String edited = GradleBuild.withThePluginApplied("subprojects {\n    plugins {\n    }\n}\n",
                true, "9.9.9");
        assertTrue(edited.startsWith("plugins {\n    id(\"org.souther-lang.souther\")"), edited);
    }

    /**
     * What a script calls its group and its root project is read where the build reads it: not in
     * a comment, not in a string, not in a block that configures another project.
     */
    @Test
    void aCoordinateIsReadOnlyWhereTheBuildSetsIt() {
        assertEquals("com.acme", GradleBuild.groupOf("""
                // group = "com.wrong"
                val note = "group = 'com.wrong'"
                subprojects {
                    group = "com.wrong"
                }
                group = "com.acme"
                """, true));
        assertNull(GradleBuild.groupOf("/* group = \"com.wrong\" */\n", true));
        assertEquals("billing", GradleBuild.rootProjectNameOf("""
                /* rootProject.name = "wrong" */
                rootProject.name = "billing"
                """, true));
        assertNull(GradleBuild.groupOf("def half = 4 / 2\ngroup = 'com.acme'\n", false));
    }

    /** A script this edited is one it then reads as set up, in either language. */
    @Test
    void aScriptThisEditedIsReadAsSetUp() {
        for (boolean kotlin : List.of(true, false)) {
            String edited = GradleBuild.withThePluginApplied(
                    kotlin ? "plugins {\n    java\n}\n" : "plugins {\n    id 'java'\n}\n", kotlin,
                    "9.9.9");
            assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(edited, kotlin),
                    edited);
        }
    }

    /**
     * Where the walk meets what it cannot place, the script is not read at all.
     *
     * <p>In Groovy a {@code /} that is not a comment's opens a string or divides according to what
     * came before it, which a parser says and this does not; a string, a comment or a brace that
     * never closes may have been meant to close anywhere. Either way a block found after it may be
     * inside it — a version that is only text, or a {@code plugins} block that is only text and
     * would be written into. So every answer that leads to a write or to a model is withheld, and
     * the cost is a refusal of a script that was fine, never a project reported ready that does not
     * build.
     */
    @Test
    void whatTheWalkCannotPlaceIsNotReadAtAll() {
        String block = "souther {\n    southerVersion = \"0.4.0\"\n}\n";
        String groovy = "plugins {\n    id 'org.souther-lang.souther' version '0.2.0'\n}\n\n";

        assertEquals(GradleBuild.Applied.UNREAD, GradleBuild.appliedIn(groovy
                + "def pattern = /\n" + block + "/\n", false));
        assertEquals(GradleBuild.Applied.UNREAD, GradleBuild.appliedIn(groovy
                + "def half = 4 / 2\n\n" + block, false));
        assertEquals(GradleBuild.Applied.UNREAD, GradleBuild.appliedIn(groovy
                + block + "def note = 'never closed\n", false));
        assertEquals(GradleBuild.Applied.UNREAD, GradleBuild.appliedIn(
                "plugins {\n    id(\"org.souther-lang.souther\") version \"0.2.0\"\n}\n\n"
                        + block + "tasks.test {\n", true));
        // A plugins block that is only text is not one to write into.
        assertEquals(GradleBuild.Applied.UNREAD, GradleBuild.appliedIn("""
                def documentation = /
                plugins {
                    java
                }
                /

                group = 'com.acme'
                """, false));
        assertThrows(IllegalStateException.class, () -> GradleBuild.withThePluginApplied(
                "def documentation = /\nplugins {\n    java\n}\n/\n", false, "9.9.9"));
        // A dollar-slashy string is placed, so the block after one is the script's own.
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(groovy
                + "def note = $/a $/ in it/$\n\n" + block, false));
        // Kotlin has no such string, so a division there is read as one.
        assertEquals(GradleBuild.Applied.ALREADY, GradleBuild.appliedIn(
                "plugins {\n    id(\"org.souther-lang.souther\") version \"0.2.0\"\n}\n\n"
                        + "val half = 4 / 2\n\n" + block, true));
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
        String edited = GradleBuild.withThePluginApplied("plugins { java }\n\ngroup = \"a\"\n", true,
                "9.9.9");

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
