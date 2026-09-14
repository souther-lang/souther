package souther.cli.init;

import java.util.List;

/**
 * What a project starts with, written out.
 *
 * <p>Every file here is either read by the build or worth reading. A {@code LICENSE} nobody chose, a
 * {@code README} saying "Enter some useful information", a workflow that pins the tool that wrote it
 * — each of those is an edit or a deletion the moment it exists, and the workflow is worse than
 * that: it cannot follow a change to the tool, because it lives in somebody else's repository now.
 *
 * <p>The model is a model and not a placeholder. A generated {@code 1 + 1 == 2} says nothing about
 * the language it is written in; what a first project is for is seeing a rule stated once, where the
 * value is built, and seeing the rows that pin it down answer on the first build.
 */
final class Templates {

    private Templates() {}

    /** A file this command writes: where it goes, relative to the project, and what is in it. */
    record File(String path, String content) {}

    /** The behavior the {@code full} model declares, and the one its rows are written for. */
    private static final String BEHAVIOR = "returnBook";

    /**
     * The source this project starts with: one file, holding the model and the rows that pin it down.
     *
     * <p>The build's own files are not among them. What a build file says depends on whether one is
     * being written or one that exists is being added to, and the source does not.
     */
    static List<File> sourcesOf(Project project) {
        return List.of(new File(modelPathOf(project), model(project)));
    }

    /** Where the module itself goes, which is the file the module header is in. */
    static String modelPathOf(Project project) {
        return "src/main/souther/" + project.sourceStem() + ".sou";
    }

    /** The model, at the level asked for. */
    private static String model(Project project) {
        return switch (project.model()) {
            case NONE -> """
                    module %s
                    """.formatted(project.moduleName());
            case MINIMAL -> """
                    module %s exposing ( Title )

                    // A value with a rule on it. The rule is checked wherever the value is built, so
                    // nothing downstream has to ask again whether a title is empty — there is no
                    // Title that is.
                    data Title = String
                        invariant String.length(value) >= 1
                    """.formatted(project.moduleName());
            case FULL -> """
                    // A library desk takes a book back. What is left to decide is whether what the
                    // desk was handed is a loan at all.
                    //
                    // Every rule the desk works by is written once, where the value is built: a title
                    // is not empty, a loan runs between one and twenty-eight days, and a book cannot
                    // come back before it went out. Nothing downstream checks any of them again.
                    module %s exposing
                        ( Title, LoanDays, Returned
                        , NoTitle, NotALoanPeriod, ReturnedBeforeItWentOut
                        , returnBook
                        )

                    data Title = String
                        invariant String.length(value) >= 1

                    data LoanDays = Int
                        invariant value >= 1 && value <= 28

                    data Returned =
                        { title: Title
                        , lentFor: LoanDays
                        }

                    // The three ways the desk's own input is not a loan. They are cases of the answer
                    // and not exceptions, so a caller reads them in a `match` — or, from Java, in a
                    // `switch` the compiler checks for exhaustiveness.
                    data NoTitle
                    data NotALoanPeriod
                    data ReturnedBeforeItWentOut

                    // What the desk types is what comes in: bare String, Date and Int. The behavior
                    // builds the model's own values out of them, and every way that can fail is one
                    // of the cases it answers with.
                    behavior %s : (title: String, borrowedOn: Date, days: Int, returnedOn: Date)
                        -> Returned | NoTitle | NotALoanPeriod | ReturnedBeforeItWentOut
                        constructs Returned, Title, LoanDays

                    let %s (title, borrowedOn, days, returnedOn) = {
                        guard Title(title) as name else NoTitle
                        guard LoanDays(days) as lent else NotALoanPeriod
                        guard borrowedOn <= returnedOn else ReturnedBeforeItWentOut

                        Returned { title = name, lentFor = lent }
                    }

                    %s""".formatted(project.moduleName(), BEHAVIOR, BEHAVIOR, examples());
        };
    }

    /**
     * The rows, below the behavior they are written for.
     *
     * <p>In the same file as the model. A reader of a first project reads the rule and the cases that
     * pin it down together, and both are compiled, so a row that stops holding is a compile error
     * rather than a failure a suite has to be run to find. {@code examples for} puts them in a file
     * of their own, and that is a move the reader makes once the rows outgrow the file the model is
     * read in.
     */
    private static String examples() {
        return """
                // What the rules come to, one case at a time. These are checked by the compiler, so
                // the build is what finds a row that no longer holds.
                //
                // `souther examples src/main/souther/*.sou` says how much of the model they cover.
                example %s
                    | "a loan the desk can take back" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-10"))
                            -> Returned { title = Title("Souther in Action"), lentFor = LoanDays(14) }
                    | "a book back the day it went out" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-01"))
                            -> Returned { title = Title("Souther in Action"), lentFor = LoanDays(14) }
                    | "the shortest loan there is" :
                        ("Souther in Action", Date("2026-04-01"), 1, Date("2026-04-10"))
                            -> Returned { title = Title("Souther in Action"), lentFor = LoanDays(1) }
                    | "and the longest" :
                        ("Souther in Action", Date("2026-04-01"), 28, Date("2026-04-10"))
                            -> Returned { title = Title("Souther in Action"), lentFor = LoanDays(28) }
                    | "a day under the shortest is not a loan period" :
                        ("Souther in Action", Date("2026-04-01"), 0, Date("2026-04-10"))
                            -> NotALoanPeriod
                    | "nor a day over the longest" :
                        ("Souther in Action", Date("2026-04-01"), 29, Date("2026-04-10"))
                            -> NotALoanPeriod
                    | "an empty title is not a title" :
                        ("", Date("2026-04-01"), 14, Date("2026-04-10"))
                            -> NoTitle
                    | "one character is a title" :
                        ("S", Date("2026-04-01"), 14, Date("2026-04-10"))
                            -> Returned { title = Title("S"), lentFor = LoanDays(14) }
                    | "a book cannot come back the day before it went out" :
                        ("Souther in Action", Date("2026-04-02"), 14, Date("2026-04-01"))
                            -> ReturnedBeforeItWentOut
                    | "nor a week before" :
                        ("Souther in Action", Date("2026-04-10"), 14, Date("2026-04-03"))
                            -> ReturnedBeforeItWentOut
                """.formatted(BEHAVIOR);
    }

    /**
     * The pom a new Maven project is run by.
     *
     * <p>{@code souther-runtime} is declared here and not added by the plugin: what a plugin adds is
     * not in the pom this project publishes, so nothing depending on it would get the runtime its
     * generated code calls. The plugin checks the declaration instead, and both it and the compile
     * read the one version this file states.
     */
    static String pom(Project project) {
        // No test ships with the project — the rows beside the model are checked by the compile. What
        // this declares is where a test the reader writes will run: the level that starts with a
        // behavior to drive is the level that gets the harness for driving it ready.
        String tests = project.model() == Model.FULL ? """
                        <!-- For the tests this project's own reader writes. The `example` rows in
                             src/main/souther are checked by the compile and need nothing here. -->
                        <dependency>
                            <groupId>org.junit.jupiter</groupId>
                            <artifactId>junit-jupiter</artifactId>
                            <version>${junit.version}</version>
                            <scope>test</scope>
                        </dependency>
                """ : "";
        String junitVersion = project.model() == Model.FULL
                ? "        <junit.version>" + Versions.junit() + "</junit.version>\n" : "";
        String surefire = project.model() == Model.FULL ? """
                            <plugin>
                                <groupId>org.apache.maven.plugins</groupId>
                                <artifactId>maven-surefire-plugin</artifactId>
                                <version>%s</version>
                            </plugin>
                """.formatted(Versions.surefire()) : "";
        return """
                <?xml version="1.0" encoding="UTF-8"?>
                <project xmlns="http://maven.apache.org/POM/4.0.0"
                         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                         xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
                    <modelVersion>4.0.0</modelVersion>

                    <groupId>%s</groupId>
                    <artifactId>%s</artifactId>
                    <version>0.1.0-SNAPSHOT</version>

                    <properties>
                        <maven.compiler.release>%s</maven.compiler.release>
                        <project.build.sourceEncoding>UTF-8</project.build.sourceEncoding>
                        <souther.version>%s</souther.version>
                        <souther.plugin.version>%s</souther.plugin.version>
                %s    </properties>

                    <dependencies>
                        <!-- Generated code calls the runtime, so the pom this project publishes says
                             so. The Souther plugin checks that this is the version the model is
                             compiled with rather than adding it. -->
                        <dependency>
                            <groupId>%s</groupId>
                            <artifactId>%s</artifactId>
                            <version>${souther.version}</version>
                        </dependency>
                %s    </dependencies>

                    <build>
                        <plugins>
                            <!-- Compiles src/main/souther into target/classes, so the jar and the
                                 test compilation read the generated classes without being told to. -->
                            <plugin>
                                <groupId>%s</groupId>
                                <artifactId>%s</artifactId>
                                <version>${souther.plugin.version}</version>
                                <configuration>
                                    <southerVersion>${souther.version}</southerVersion>
                                </configuration>
                                <executions>
                                    <execution>
                                        <goals><goal>compile</goal></goals>
                                    </execution>
                                </executions>
                            </plugin>
                %s        </plugins>
                    </build>
                </project>
                """.formatted(project.coordinate().groupId(), project.coordinate().artifactId(),
                JAVA_RELEASE, project.southerVersion(), BuildPlugins.MAVEN_VERSION, junitVersion,
                BuildPlugins.GROUP, BuildPlugins.RUNTIME_ARTIFACT, tests,
                BuildPlugins.GROUP, BuildPlugins.MAVEN_ARTIFACT, surefire);
    }

    /**
     * The build script a new Gradle project is run by.
     *
     * <p>No Souther version and no runtime dependency. On Gradle a dependency the plugin adds is in
     * the metadata this project publishes, so the plugin adds the runtime at the version it compiles
     * the model with, and a project naming no version is compiled by the Souther its plugin release
     * was verified against.
     */
    static String buildScript(Project project) {
        // Where the project starts with a behavior to drive, so a test the reader writes has
        // somewhere to run. A project that starts with a module header gets no dependencies block and
        // no test task: an empty one says a project has something to declare and left it out.
        String tests = project.model() == Model.FULL ? """

                dependencies {
                    testImplementation(platform("org.junit:junit-bom:%s"))
                    testImplementation("org.junit.jupiter:junit-jupiter")
                    // Gradle runs the tests through the platform launcher, and the aggregate above
                    // does not bring it.
                    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
                }
                """.formatted(Versions.junit()) : "";
        String platform = project.model() == Model.FULL ? """

                tasks.test {
                    useJUnitPlatform()
                }
                """ : "";
        return """
                plugins {
                    java
                    id("%s") version "%s"
                }

                group = "%s"
                version = "0.1.0-SNAPSHOT"

                repositories {
                    mavenCentral()
                }
                %s
                // Souther generates class files for this release, so the build reads them with a
                // toolchain that is at least this.
                java {
                    toolchain {
                        languageVersion = JavaLanguageVersion.of(%s)
                    }
                }
                %s""".formatted(BuildPlugins.GRADLE_ID, BuildPlugins.GRADLE_VERSION,
                project.coordinate().groupId(), tests, JAVA_RELEASE, platform);
    }

    /** What Gradle calls the project, which it takes from the settings file and not from the group. */
    static String settingsScript(Project project) {
        return """
                rootProject.name = "%s"
                """.formatted(project.coordinate().artifactId());
    }

    /** What the build writes and nobody edits. */
    static String gitignore(Project project) {
        return project.build() == BuildSystem.MAVEN ? """
                target/
                """ : """
                build/
                .gradle/
                """;
    }

    /**
     * The Java release a generated project reads its own classes with.
     *
     * <p>The compiler emits class files for it, so a project reading them with less is a project
     * whose build cannot load what its own model compiled to.
     */
    private static final String JAVA_RELEASE = "25";

    /** The release a generated project declares, for the test that holds it against what is emitted. */
    static String javaRelease() {
        return JAVA_RELEASE;
    }

}
