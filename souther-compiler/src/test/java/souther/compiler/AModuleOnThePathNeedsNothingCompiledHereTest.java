package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.diag.PhysicalRegion;
import souther.compiler.diag.Primary;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A module on the path reaches only modules on the path (spec
 * {@code [#a-module-on-the-path-reaches-only-the-path]}). Its classes run from the path, where the
 * classes this compilation makes are not seen, so one that reaches a module a source here declares
 * is refused before anything is generated or run.
 *
 * <p>Each refused case builds the path module against a dependency and then puts only the path
 * module on the path, with the dependency compiled again from source. Each way a module can reach
 * another is a case: an import its declarations use, a qualified name with no import, a behavior
 * only its body calls. The accepted case is the same program with the dependency on the path too.
 */
class AModuleOnThePathNeedsNothingCompiledHereTest {

    private static final String COMMON = """
            module app.common exposing ( Tag, norm )
            data Tag = String
                invariant lower = String.matches("[a-z]+", value)
            behavior norm : (s: String) -> String
            let norm (s) = s
            """;

    private static final String MAKES_A_TAG = """
            module lib.x exposing ( make )
            import app.common ( Tag )
            behavior make : (s: String) -> Tag constructs Tag
            let make (s) = Tag(s)
            """;

    private static final String USES_THE_MAKER = """
            module app.user
            import app.common ( Tag )
            import lib.x ( make )
            behavior go : (s: String) -> Tag
            let go (s) = make(s)
            example go
                | "made" : ("ab") -> Tag("ab")
            """;

    /** {@code sources} compiled together, and only the classes of the modules named in
     *  {@code kept} put on the path. */
    private static ModulePath builtWith(List<String> sources, String... kept) {
        Map<String, ClassFileImage> built = Compiler.compileModules(sources);
        return name -> {
            for (String module : kept) {
                if (name.startsWith(module + ".") && built.containsKey(name)) {
                    return built.get(name).bytes();
                }
            }
            return null;
        };
    }

    private static List<Diagnostic> refused(ModulePath path, String... sources) {
        return assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(sources), path)).diagnostics();
    }

    /** The issue's program: the example is never run, because the arrangement is refused first —
     *  and refused as what it is, not as the example not holding. */
    @Test
    void theIssuesProgramIsRefusedBeforeItsExampleRuns() {
        List<Diagnostic> said = refused(builtWith(List.of(COMMON, MAKES_A_TAG), "lib.x"),
                COMMON, USES_THE_MAKER);

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), messages(said));
    }

    /** Whether there is an example to run is not what decides it. */
    @Test
    void theArrangementIsRefusedWithNoExampleAtAll() {
        List<Diagnostic> said = refused(builtWith(List.of(COMMON, MAKES_A_TAG), "lib.x"),
                COMMON, """
                        module app.user
                        import app.common ( Tag )
                        import lib.x ( make )
                        behavior go : (s: String) -> Tag
                        let go (s) = make(s)
                        """);

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), messages(said));
    }

    /** The import is dropped from what the module publishes, since no published declaration
     *  needs it, and its classes still call the behavior. */
    @Test
    void aBehaviorOnlyItsBodyCallsIsReachedAllTheSame() {
        String measures = """
                module lib.x exposing ( measure )
                import app.common ( norm )
                behavior measure : (s: String) -> Int
                let measure (s) = String.length(norm(s))
                """;
        List<Diagnostic> said = refused(builtWith(List.of(COMMON, measures), "lib.x"),
                COMMON, """
                        module app.user
                        import lib.x ( measure )
                        behavior go : (s: String) -> Int
                        let go (s) = measure(s)
                        """);

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), messages(said));
    }

    /** A qualified name reaches its module with no import line. */
    @Test
    void aQualifiedNameReachesItsModuleWithNoImport() {
        String qualified = """
                module lib.x exposing ( make )
                behavior make : (s: String) -> app.common.Tag constructs app.common.Tag
                let make (s) = app.common.Tag(s)
                """;
        List<Diagnostic> said = refused(builtWith(List.of(COMMON, qualified), "lib.x"),
                COMMON, """
                        module app.user
                        import lib.x ( make )
                        behavior go : (s: String) -> app.common.Tag
                        let go (s) = make(s)
                        """);

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), messages(said));
    }

    /** Said about the module that reaches the one compiled here, and not about the one in front
     *  of it: rebuilding that one changes nothing. */
    @Test
    void itIsSaidAboutTheModuleThatReachesItNotTheOneBeforeIt() {
        String shouts = """
                module lib.x exposing ( make, shout )
                import app.common ( Tag )
                behavior make : (s: String) -> Tag constructs Tag
                let make (s) = Tag(s)
                behavior shout : (s: String) -> String
                let shout (s) = s
                """;
        String wraps = """
                module lib.a exposing ( wrap )
                import lib.x ( shout )
                behavior wrap : (s: String) -> String
                let wrap (s) = shout(s)
                """;
        List<Diagnostic> said = refused(
                builtWith(List.of(COMMON, shouts, wraps), "lib.x", "lib.a"),
                COMMON, """
                        module app.user
                        import lib.a ( wrap )
                        behavior go : (s: String) -> String
                        let go (s) = wrap(s)
                        """);

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), messages(said));
    }

    /** The same program with the dependency taken from the path as well: the path module and what
     *  it reaches run in one place, and the example holds. That the example is run at all is the
     *  second half: one that does not hold is refused for that. */
    @Test
    void theSameProgramWithItsDependencyOnThePathRuns() {
        ModulePath path = builtWith(List.of(COMMON, MAKES_A_TAG), "lib.x", "app.common");
        Compiler.compileModules(List.of(USES_THE_MAKER), path);

        List<Diagnostic> said = refused(path,
                USES_THE_MAKER.replace("-> Tag(\"ab\")", "-> Tag(\"zz\")"));
        assertEquals(List.of("E1905"), said.stream().map(Diagnostic::code).toList());
    }

    /** A name the path carries too is two modules, and which of them a module on the path reaches
     *  is what that report says is not decided: it is said once, as that. */
    @Test
    void aModuleCompiledHereAndOnThePathIsSaidOnlyAsThat() {
        Compilation compilation = Compilation.ofSources(List.of(COMMON, """
                        module app.user
                        import lib.x ( make )
                        behavior go : (s: String) -> app.common.Tag
                        let go (s) = make(s)
                        """), builtWith(List.of(COMMON, MAKES_A_TAG), "lib.x", "app.common"));

        assertEquals(List.of(new ModuleMessage.TheModuleIsCompiledHereAndOnThePath("app.common")),
                everythingSaid(compilation));
    }

    /** The module compiled here no longer declares what the path module's declarations name. What
     *  those names mean against it is not what the module's classes run with, so the refusal is
     *  said once, and not again as each name it would miss. */
    @Test
    void whatTheModuleHereDoesNotDeclareIsNotSaidBesideIt() {
        String shouts = """
                module lib.x exposing ( make, shout )
                import app.common ( Tag )
                behavior make : (s: String) -> Tag constructs Tag
                let make (s) = Tag(s)
                behavior shout : (s: String) -> String
                let shout (s) = s
                """;
        Compilation compilation = Compilation.ofSources(List.of("""
                        module app.common exposing ( Other )
                        data Other = String
                        """, """
                        module app.user
                        import lib.x ( shout )
                        behavior go : (s: String) -> String
                        let go (s) = shout(s)
                        """), builtWith(List.of(COMMON, shouts), "lib.x"));

        assertEquals(List.of(new ModuleMessage.AModuleOnThePathNeedsOneCompiledHere("lib.x",
                "app.common")), everythingSaid(compilation));
    }

    /** Every report any question of the compilation makes, every question asked: not only what a
     *  build reads before it stops. */
    private static List<Object> everythingSaid(Compilation compilation) {
        compilation.answerEverything();
        List<Object> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            out.add(found.report().diagnostic().said());
        }
        return out;
    }

    /** Said at the import line, in the file this compile holds, that reaches the path module. */
    @Test
    void itIsSaidAtTheImportThatReachesThePathModule() {
        String user = """
                module app.user
                import app.common ( Tag )


                import lib.x ( make )
                behavior go : (s: String) -> Tag
                let go (s) = make(s)
                """;
        Compilation compilation = Compilation.ofSources(List.of(COMMON, user),
                builtWith(List.of(COMMON, MAKES_A_TAG), "lib.x"));

        Located said = compilation.diagnostics().get(new SourceId("1")).stream()
                .filter(d -> d.diagnostic().code().equals("E1511")).findFirst().orElseThrow();
        PhysicalRegion caret = WhereItSits.in(user,
                ((Primary.InSource) said.diagnostic().primary()).place().region());
        assertEquals(5, caret.start().line(), "the import line naming lib.x");
    }

    private static List<Object> messages(List<Diagnostic> said) {
        List<Object> out = new ArrayList<>();
        for (Diagnostic each : said) {
            out.add(each.said());
        }
        return out;
    }
}
