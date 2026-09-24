package souther.compiler;

import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.CheckSurface;
import souther.compiler.check.Prepared;
import souther.compiler.diag.Severity;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Shapes;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where each behavior of a module gets its body is decided where the module is compiled, and a
 * module read off the path is answered with what it published (spec §injected-behavior,
 * §unwritten-behavior).
 *
 * <p>What is published carries no {@code let}. A reader that worked the state out again from the
 * tree it read back would find no body for any behavior and put every one without {@code depends on}
 * among the injection targets — an implemented behavior along with them, which is then held to what
 * an injected behavior's public base needs. So every reader of the module is asked here, over the
 * module as it comes back from its classes.
 */
class AModuleOffThePathIsCheckedAsItWasClassifiedWhereItWasCompiledTest {

    /** One behavior in each state, and a composition, which is its own implementation. */
    private static final String LIB = """
            module lib.s exposing ( Id, Out, supplied, owed, written, chained : Out )
            data Id = { n: Int }
            data Out = { n: Int }
            behavior supplied : (id: Id) -> Out
            behavior owed : (id: Id) -> Out
                depends on supplied
            behavior written : (id: Id) -> Out
                constructs Out
            let written (id) = Out { n = id.n * 2 }
            behavior chained = written >-> again
            behavior again : (o: Out) -> Out
            let again (o) = o
            """;

    /** Reaches the module, so the compilation reads it off the path. */
    private static final String APP = """
            module app.s
            import lib.s ( Out, chained )
            behavior keep : (o: Out) -> Out
            let keep (o) = o
            behavior more = chained >-> keep
            """;

    @Test
    void everyReaderOfAModuleOffThePathIsToldWhatItPublished() {
        Map<String, BehaviorImplementation> compiled = new LinkedHashMap<>();
        compiled.put("supplied", BehaviorImplementation.INJECTION_TARGET);
        compiled.put("owed", BehaviorImplementation.UNIMPLEMENTED);
        compiled.put("written", BehaviorImplementation.IMPLEMENTED);
        compiled.put("chained", BehaviorImplementation.IMPLEMENTED);
        compiled.put("again", BehaviorImplementation.IMPLEMENTED);
        Db here = Compilation.ofSource(LIB, "Main").db();
        assertEquals(compiled, here.ask(new Bodies.Implementation("lib.s")).value().states(),
                "the module classified where it is compiled");

        Db offThePath = againstThePath(LIB, APP).db();

        assertEquals(compiled,
                offThePath.ask(new Bodies.Implementation("lib.s")).value().states());
        CheckSurface surface = offThePath.ask(new Shapes.CheckSurface("lib.s")).value();
        Prepared prepared = offThePath.ask(new Shapes.Prepared("lib.s")).value();
        Map<String, BehaviorImplementation> onTheSurface = new LinkedHashMap<>();
        Map<String, BehaviorImplementation> asPrepared = new LinkedHashMap<>();
        compiled.forEach((behavior, _) -> {
            ValueName.Behavior declared = new ValueName.Behavior("lib.s", behavior);
            onTheSurface.put(behavior, surface.implementationOf(declared));
            asPrepared.put(behavior, prepared.implementationOf(declared));
        });
        assertEquals(compiled, onTheSurface);
        assertEquals(compiled, asPrepared);
        assertEquals(Set.of("supplied"), offThePath.ask(new Bodies.Injected("lib.s")).value());
        assertEquals(Set.of("owed"), offThePath.ask(new Bodies.Unwritten("lib.s")).value());
    }

    /** A behavior is asked about by the module that declares it, and another module's behavior of
     *  the same name is not answered from this one's table. */
    @Test
    void anotherModulesBehaviorOfTheSameNameIsNotAnsweredFromThisOne() {
        Prepared prepared = againstThePath(LIB, APP).db()
                .ask(new Shapes.Prepared("lib.s")).value();

        assertThrows(IllegalArgumentException.class,
                () -> prepared.implementationOf(new ValueName.Behavior("app.s", "written")));
        assertThrows(IllegalArgumentException.class,
                () -> prepared.implementationOf(new ValueName.Behavior("lib.s", "more")));
    }

    /**
     * The module the issue was reported with: an implemented behavior that constructs a type the
     * module keeps to itself. Held to what an injected behavior's public base needs, it is refused
     * for constructing something a Java implementation could not name.
     */
    @Test
    void anImplementedBehaviorOffThePathIsNotHeldToWhatAnInjectedOneIs() {
        String lib = """
                module lib.k exposing ( Out, go )
                data Hidden = { n: Int }
                data Out = { n: Int }
                behavior go : (n: Int) -> Out constructs Out, Hidden
                let go (n) = {
                    let h = Hidden { n = n }
                    Out { n = h.n } }
                """;
        String app = """
                module app.r
                import lib.k ( Out, go )
                behavior go2 : (o: Out) -> Out
                let go2 (o) = o
                behavior again = go >-> go2
                """;
        Compilation compilation = againstThePath(lib, app);

        List<String> errors = new ArrayList<>();
        compilation.diagnostics().forEach((_, said) -> said.forEach(each -> {
            if (each.diagnostic().severity() == Severity.ERROR) {
                errors.add(String.valueOf(each.diagnostic().code()));
            }
        }));
        assertEquals(List.of(), errors);
        assertTrue(compilation.db().ask(new Bodies.ModuleCheck("lib.k")).value().sound(),
                "the module off the path was checked and found nothing wrong");
    }

    /** {@code app} compiled against {@code lib}'s classes, with every question answered, as an
     *  editor session does. */
    private static Compilation againstThePath(String lib, String app) {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(lib));
        Compilation compilation = Compilation.ofSources(List.of(app), ModulePath.of(classes));
        compilation.answerEverything();
        return compilation;
    }
}
