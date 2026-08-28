package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior of another module is named through that module, the same way a type is — as a
 * {@code >->} stage and as a {@code depends on}. What the qualifier says is which module the behavior
 * comes from, which is what an import says, so it needs no import line.
 *
 * <p>A behavior is the module that declares it and its name, so two modules declaring one name
 * declare two behaviors and a qualified reference says which is meant. What cannot be told apart is
 * a bare spelling two import lines both claim: that is a question about what this module writes,
 * and it is refused where the lines are read.
 */
class CompileQualifiedBehaviorRefTest {

    /** An implemented behavior: composable as a stage. */
    private static final String UP = """
            module up exposing ( In, Mid, twice )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior twice : (i: In) -> Mid constructs Mid
            let twice (i) = Mid { n = i.n * 2 }
            """;

    /** The same names again, from another module. */
    private static final String OTHER = """
            module other exposing ( In, Mid, twice )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior twice : (i: In) -> Mid constructs Mid
            let twice (i) = Mid { n = i.n * 3 }
            """;

    /** An injection target: no `let`, so a consumer injects it. */
    private static final String LOOKUP = """
            module up2 exposing ( In, Mid, lookup )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior lookup : (i: In) -> Mid constructs Mid
            """;

    @Test
    void aStageMayNameItsBehaviorThroughItsModule() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(UP, """
                module d exposing ( Out, flow : Out )
                data Out = { n: Int }
                behavior plus : (m: up.Mid) -> Out constructs Out
                let plus (m) = Out { n = m.n + 1 }
                behavior flow = up.twice >-> plus
                """));

        assertTrue(classes.containsKey(Emitted.impl("d", "flow")), classes.keySet().toString());
    }

    @Test
    void anAliasCarriesAStageToo() {
        Compiler.compileModules(List.of(UP, """
                module d exposing ( Out, flow : Out )
                import up as U
                data Out = { n: Int }
                behavior plus : (m: U.Mid) -> Out constructs Out
                let plus (m) = Out { n = m.n + 1 }
                behavior flow = U.twice >-> plus
                """));
    }

    /** The injected field keeps the bare name, so the Java surface is what it was. */
    @Test
    void aRequiresMayNameItsBehaviorThroughItsModule() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(LOOKUP, """
                module d exposing ( Out, run )
                data Out = { n: Int }
                behavior run : (i: up2.In) -> Out constructs Out depends on up2.lookup
                let run (i, lookup) = {
                    let m = lookup(i)
                    Out { n = m.n }
                }
                """));

        assertTrue(classes.containsKey(Emitted.impl("d", "run")), classes.keySet().toString());
    }

    @Test
    void aBehaviorTheModuleDoesNotExposeIsRefused() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module hidden exposing ( In, Mid )
                        data In = { n: Int }
                        data Mid = { n: Int }
                        behavior twice : (i: In) -> Mid constructs Mid
                        let twice (i) = Mid { n = i.n * 2 }
                        """, """
                        module d exposing ( Out, flow : Out )
                        data Out = { n: Int }
                        behavior plus : (m: hidden.Mid) -> Out constructs Out
                        let plus (m) = Out { n = m.n + 1 }
                        behavior flow = hidden.twice >-> plus
                        """)));

        assertTrue(e.getMessage().contains("not exposed"), e.getMessage());
    }

    /** The collision this is really about: it used to be accepted, one import silently winning, and
     * the failure surfaced later as a type mismatch between two types both printed as `Mid`. */
    @Test
    void twoModulesNamingTheSameBehaviorIsReported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, OTHER, """
                        module d exposing ( Out, flow : Out )
                        import up ( Mid, twice )
                        import other ( twice )
                        data Out = { n: Int }
                        behavior plus : (m: Mid) -> Out constructs Out
                        let plus (m) = Out { n = m.n + 1 }
                        behavior flow = twice >-> plus
                        """)));

        assertTrue(e.getMessage().contains("twice"), e.getMessage());
        assertTrue(e.getMessage().contains("up") && e.getMessage().contains("other"), e.getMessage());
    }

    /**
     * Qualifying does separate them. Each stage is typed against the behavior it names, so a module
     * may reach both — the reference says which, and nothing here rests on the spelling.
     */
    @Test
    void twoSameNamedBehaviorsReachedQualifiedAreToldApart() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, OTHER, """
                module d exposing ( Out, fromUp : Out, fromOther : Out )
                data Out = { n: Int }
                behavior plus : (m: up.Mid) -> Out constructs Out
                let plus (m) = Out { n = m.n + 1 }
                behavior plusOther : (m: other.Mid) -> Out constructs Out
                let plusOther (m) = Out { n = m.n + 1 }
                behavior fromUp = up.twice >-> plus
                behavior fromOther = other.twice >-> plusOther
                """)));
    }

    @Test
    void aQualifierThatNamesNoModuleIsReported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module d exposing ( Out, flow : Out )
                        data In = { n: Int }
                        data Out = { n: Int }
                        behavior plus : (i: In) -> Out constructs Out
                        let plus (i) = Out { n = i.n + 1 }
                        behavior flow = absent.twice >-> plus
                        """)));

        assertTrue(e.getMessage().contains("absent"), e.getMessage());
        assertTrue(e.getMessage().contains("no module"), e.getMessage());
    }

    /** {@code X.decoder} names a codec, not a behavior of a module called X — even where a module is
     * named like the type, so reading the stage as an import would take the answer away. */
    @Test
    void aCodecStageKeepsItsOwnAnswerEvenWhereAModuleIsNamedLikeTheType() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module In exposing ( Thing )
                        data Thing = { n: Int }
                        """, """
                        module d exposing ( Out, flow : Out )
                        data In = { n: Int }
                        data Out = { n: Int }
                        behavior plus : (i: In) -> Out constructs Out
                        let plus (i) = Out { n = i.n + 1 }
                        behavior flow = In.decoder >-> plus
                        """)));

        assertTrue(e.getMessage().contains("boundary"), e.getMessage());
    }

    /** A dependency counts however it is written, for a behavior as for a type. Neither module names
     * the other's *types*, so the cycle is closed by the stages alone. */
    @Test
    void aCycleThroughAQualifiedBehaviorIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module cyc.x exposing ( A, B, f, g : B )
                        data A = { n: Int }
                        data B = { n: Int }
                        behavior f : (a: A) -> B constructs B
                        let f (a) = B { n = a.n }
                        behavior g = cyc.y.h >-> f
                        """, """
                        module cyc.y exposing ( A, h, k : A )
                        data A = { n: Int }
                        behavior h : (a: A) -> A constructs A
                        let h (a) = A { n = a.n }
                        behavior k = cyc.x.f >-> h
                        """)));

        assertTrue(e.getMessage().contains("E1501"), e.getMessage());
    }
}
