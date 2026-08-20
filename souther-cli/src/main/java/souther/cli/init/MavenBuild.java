package souther.cli.init;

import java.util.List;

/**
 * A pom somebody else wrote: what it calls the project, and what it takes to make it compile a
 * model.
 *
 * <p>Two declarations, not one. The plugin runs the compile, and the runtime the generated code
 * calls is declared as an ordinary dependency — the plugin checks it rather than adding it, because
 * what a plugin adds is not in the pom this project publishes and nothing depending on it would get
 * the runtime. What that runtime brings with it, Raoh among it, comes with it.
 */
final class MavenBuild {

    private MavenBuild() {}

    private static final List<String> PROJECT = List.of("project");
    private static final List<String> BUILD = List.of("project", "build");
    private static final List<String> PLUGINS = List.of("project", "build", "plugins");
    private static final List<String> DEPENDENCIES = List.of("project", "dependencies");
    private static final List<String> DEPENDENCY =
            List.of("project", "dependencies", "dependency");
    private static final List<String> PLUGIN =
            List.of("project", "build", "plugins", "plugin");

    /**
     * What this pom calls the project, or null where it does not say.
     *
     * <p>A child pom leaves the group to its parent, so the parent's is the answer where the project
     * writes none — that is what the build resolves it to. A pom that writes neither is a pom this
     * command cannot read a coordinate out of, and it says so rather than inventing one.
     */
    static Coordinate coordinateOf(String pom) {
        String group = Xml.textOf(pom, List.of("project", "groupId"));
        if (group == null) {
            group = Xml.textOf(pom, List.of("project", "parent", "groupId"));
        }
        String artifact = Xml.textOf(pom, List.of("project", "artifactId"));
        if (group == null || artifact == null || group.isEmpty() || artifact.isEmpty()
                || group.contains("${") || artifact.contains("${")) {
            return null;
        }
        return new Coordinate(group, artifact);
    }

    /**
     * Whether this pom is one this command can put a declaration into.
     *
     * <p>Asked before anything is written. What a pom this cannot walk down gets is a block
     * inserted where no element ends, which is a file its author has to restore from the copy
     * beside it — and they would be restoring it from a command that reported success.
     */
    static boolean canBeAddedTo(String pom) {
        return Xml.has(pom, PROJECT);
    }

    /**
     * Whether this pom declares the plugin where declaring it runs it.
     *
     * <p>Asked of {@code build/plugins}, and of nothing else. A name is not a declaration: an entry
     * under {@code pluginManagement} says what version this plugin would have if it were used, a
     * plugin of another group that happens to share the artifact name is another plugin, and a
     * comment mentioning it is prose. Answered by a search of the text, each of those read as a
     * project that was already set up — and what its author got was `kept`, and a build that
     * compiles no Souther.
     *
     * <p>A profile's build is not read. A plugin declared only in one runs when that profile is
     * active, and this would add a second declaration to the base build rather than leave a project
     * with none.
     */
    static boolean declaresThePlugin(String pom) {
        return declares(Xml.everyIn(pom, PLUGIN), BuildPlugins.GROUP, BuildPlugins.MAVEN_ARTIFACT);
    }

    /**
     * Whether this pom declares the runtime the generated code calls, where declaring it puts it on
     * the class path — {@code dependencies}, and not {@code dependencyManagement}.
     */
    static boolean declaresTheRuntime(String pom) {
        return declares(Xml.everyIn(pom, DEPENDENCY), BuildPlugins.GROUP,
                BuildPlugins.RUNTIME_ARTIFACT);
    }

    /**
     * Whether one of these declarations is of that artifact.
     *
     * <p>Both halves of the coordinate. A pom naming {@code souther-runtime} under another group is
     * naming somebody else's artifact, and the runtime the generated code calls would still not be
     * there.
     */
    private static boolean declares(List<String> declarations, String group, String artifact) {
        for (String declared : declarations) {
            if (group.equals(Xml.textOf(declared, List.of("groupId")))
                    && artifact.equals(Xml.textOf(declared, List.of("artifactId")))) {
                return true;
            }
        }
        return false;
    }


    /**
     * The pom with whichever of the two declarations it is missing written into it.
     *
     * <p>Into the elements it already has where it has them, and creating the ones it does not.
     * Nothing else in the file is touched: what comes back is the author's own text with a block
     * inserted, so their comments and their layout survive being added to.
     */
    static String withSoutherDeclared(String pom, String southerVersion) {
        String written = pom;
        if (!declaresTheRuntime(written)) {
            written = withDependency(written, BuildPlugins.GROUP, BuildPlugins.RUNTIME_ARTIFACT,
                    southerVersion);
        }
        if (!declaresThePlugin(written)) {
            written = withPlugin(written, southerVersion);
        }
        return written;
    }

    private static String withDependency(String pom, String group, String artifact,
                                         String version) {
        String dependency = """
                <dependency>
                    <groupId>%s</groupId>
                    <artifactId>%s</artifactId>
                    <version>%s</version>
                </dependency>""".formatted(group, artifact, version);
        if (Xml.has(pom, DEPENDENCIES)) {
            return Xml.insertInto(pom, DEPENDENCIES, dependency);
        }
        return Xml.insertInto(pom, PROJECT, wrap("dependencies", dependency));
    }

    private static String withPlugin(String pom, String southerVersion) {
        String plugin = """
                <plugin>
                    <groupId>%s</groupId>
                    <artifactId>%s</artifactId>
                    <version>%s</version>
                    <configuration>
                        <southerVersion>%s</southerVersion>
                    </configuration>
                    <executions>
                        <execution>
                            <goals><goal>compile</goal></goals>
                        </execution>
                    </executions>
                </plugin>"""
                .formatted(BuildPlugins.GROUP, BuildPlugins.MAVEN_ARTIFACT,
                        BuildPlugins.MAVEN_VERSION, southerVersion);
        if (Xml.has(pom, PLUGINS)) {
            return Xml.insertInto(pom, PLUGINS, plugin);
        }
        if (Xml.has(pom, BUILD)) {
            return Xml.insertInto(pom, BUILD, wrap("plugins", plugin));
        }
        return Xml.insertInto(pom, PROJECT, wrap("build", wrap("plugins", plugin)));
    }

    /**
     * {@code block} inside an element of its own, indented under it.
     *
     * <p>In the form every block here is written in — one level is four spaces — which is what the
     * insertion restates in the document's own unit.
     */
    private static String wrap(String element, String block) {
        return "<" + element + ">\n" + Xml.indent(block, "    ", "    ") + "</" + element + ">";
    }
}
