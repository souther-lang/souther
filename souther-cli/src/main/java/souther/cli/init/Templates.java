package souther.cli.init;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.util.ArrayList;
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
 * value is built, and seeing the rows and the Java test both answer on the first build.
 */
final class Templates {

    private Templates() {}

    /** A file this command writes: where it goes, relative to the project, and what is in it. */
    record File(String path, String content) {}

    /** The Java test the {@code full} model comes with, and the behavior it drives. */
    private static final String BEHAVIOR = "returnBook";

    private static final String TEST_CLASS = "ReturnBookTest";

    /**
     * The sources this project starts with: the model, its rows, and the test that drives it from
     * Java.
     *
     * <p>The build's own files are not among them. What a build file says depends on whether one is
     * being written or one that exists is being added to, and the sources do not.
     */
    static List<File> sourcesOf(Project project) {
        List<File> files = new ArrayList<>();
        files.add(new File(modelPathOf(project), model(project)));
        if (project.model() == Model.FULL) {
            files.add(new File("src/main/souther/" + project.sourceStem() + ".examples.sou",
                    examples(project)));
            files.add(new File("src/test/java/" + project.packagePath() + "/" + TEST_CLASS + ".java",
                    javaTest(project)));
        }
        return files;
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
                    // A library desk takes a book back. What is left to decide is whether it is late,
                    // and by how much.
                    //
                    // Every rule the desk works by is written once, where the value is built: a title
                    // is not empty, a loan runs between one and twenty-eight days, and a book cannot
                    // come back before it went out. Nothing downstream checks any of them again.
                    module %s exposing
                        ( Title, LoanDays, DaysLate, Returned
                        , NoTitle, NotALoanPeriod, ReturnedBeforeItWentOut
                        , returnBook
                        )

                    data Title = String
                        invariant String.length(value) >= 1

                    data LoanDays = Int
                        invariant value >= 1 && value <= 28

                    data DaysLate = Int
                        invariant value >= 0

                    data Returned =
                        { title: Title
                        , daysLate: DaysLate
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
                        constructs Returned, Title, LoanDays, DaysLate,
                                   NoTitle, NotALoanPeriod, ReturnedBeforeItWentOut

                    let daysOut (borrowedOn: Date, returnedOn: Date): Int =
                        Date.daysBetween(borrowedOn, returnedOn)

                    let lateBy (out: Int, lent: LoanDays): Int =
                        if out > lent.value then out - lent.value else 0

                    let %s (title, borrowedOn, days, returnedOn) = {
                        guard Title(title) as name else NoTitle
                        guard LoanDays(days) as lent else NotALoanPeriod
                        guard borrowedOn <= returnedOn else ReturnedBeforeItWentOut

                        Returned
                            { title = name
                            , daysLate = DaysLate(lateBy(daysOut(borrowedOn, returnedOn), lent))
                            }
                    }
                    """.formatted(project.moduleName(), BEHAVIOR, BEHAVIOR);
        };
    }

    /**
     * The rows, in a file of their own.
     *
     * <p>Beside the model rather than in it, which is what {@code examples for} is for: the model
     * reads as the rules, and what pins them down is read as a set of cases. Both are compiled, and
     * a row that stops holding is a compile error rather than a failure a suite has to be run to
     * find.
     */
    private static String examples(Project project) {
        return """
                // What the rules come to, one case at a time. These are checked by the compiler, so
                // `mvn test` is not what finds a row that no longer holds — the build is.
                //
                // `souther examples src/main/souther/*.sou` says how much of the model they cover.
                examples for %s

                example %s
                    | "a book back inside its loan is not late" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-10"))
                            -> Returned { title = Title("Souther in Action"), daysLate = DaysLate(0) }
                    | "the day after it was due is one day late" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-16"))
                            -> Returned { title = Title("Souther in Action"), daysLate = DaysLate(1) }
                    | "the day it was due is not late" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-15"))
                            -> Returned { title = Title("Souther in Action"), daysLate = DaysLate(0) }
                    | "a book back the day it went out is not late" :
                        ("Souther in Action", Date("2026-04-01"), 14, Date("2026-04-01"))
                            -> Returned { title = Title("Souther in Action"), daysLate = DaysLate(0) }
                    | "an empty title is not a title" :
                        ("", Date("2026-04-01"), 14, Date("2026-04-10"))
                            -> NoTitle
                    | "twenty-nine days is not a loan period" :
                        ("Souther in Action", Date("2026-04-01"), 29, Date("2026-04-10"))
                            -> NotALoanPeriod
                    | "a book cannot come back before it went out" :
                        ("Souther in Action", Date("2026-04-10"), 14, Date("2026-04-01"))
                            -> ReturnedBeforeItWentOut
                """.formatted(project.moduleName(), BEHAVIOR);
    }

    /**
     * The same model, driven from Java the way an application drives it.
     *
     * <p>What this covers is what the rows do not: that the generated types are there under the
     * names the module gave them, and that a caller in another language reads the answer as a value
     * rather than catching something.
     */
    private static String javaTest(Project project) {
        return """
                package %s;

                import org.junit.jupiter.api.Test;

                import java.time.LocalDate;

                import static org.junit.jupiter.api.Assertions.assertEquals;
                import static org.junit.jupiter.api.Assertions.assertInstanceOf;

                /**
                 * The model, driven from Java.
                 *
                 * <p>The `example` rows in src/main/souther already pin the rules down at compile
                 * time. What is left for a test here is the boundary: that the module's types arrive
                 * in Java under their own names, and that what cannot be a loan comes back as a value
                 * to read rather than as an exception to catch.
                 */
                class %s {

                    @Test
                    void aBookHandedBackLateSaysHowLate() {
                        %s answer = %s.of().apply(
                                "Souther in Action", LocalDate.of(2026, 4, 1), 14L,
                                LocalDate.of(2026, 4, 16));

                        Returned returned = assertInstanceOf(Returned.class, answer);
                        assertEquals(1L, returned.daysLate().value());
                    }

                    @Test
                    void anEmptyTitleIsAnAnswerAndNotAnException() {
                        assertInstanceOf(NoTitle.class, %s.of().apply(
                                "", LocalDate.of(2026, 4, 1), 14L, LocalDate.of(2026, 4, 10)));
                    }
                }
                """.formatted(project.moduleName(), TEST_CLASS, resultType(project),
                behaviorType(project), behaviorType(project), behaviorType(project));
    }

    /**
     * The interface a behavior is declared as, as the Java beside it names it.
     *
     * <p>Asked of the one place that decides what a generated class is called. What the rule is —
     * a capital here, a suffix there — is the ABI's to state, and a template restating it would be
     * a second statement of it that a reader would only find wrong by compiling.
     */
    private static String behaviorType(Project project) {
        return simpleNameOf(new GeneratedClass.BehaviorInterface(project.moduleName(), BEHAVIOR));
    }

    /** The sealed interface a behavior answering with several cases hands them back in. */
    private static String resultType(Project project) {
        return simpleNameOf(new GeneratedClass.BehaviorResult(project.moduleName(), BEHAVIOR));
    }

    /** What Java in the same package calls the class, which is its name without the package. */
    private static String simpleNameOf(GeneratedClass generated) {
        String binary = SoutherJvmAbi.nameOf(generated).binaryName();
        return binary.substring(binary.lastIndexOf('.') + 1);
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
        String tests = project.model() == Model.FULL ? """
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
        // Only where there is a test to run. A project that starts with none gets no dependencies
        // block and no test task: an empty one says a project has something to declare and left it
        // out, which is not what a model with no test beside it is.
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
