package souther.compiler;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A type whose invariant calls a recursive helper can be included by a type of another module, and
 * the rule it brings in is the one its own module wrote.
 *
 * <p>The call is left standing by the settling, so the including module runs it: it reaches the
 * helper by the route it has to it, and takes the helper on as a method of its own. Each case builds
 * a value whose fault is past the first link of the chain, so what decides it is the recursion and
 * not the part of the rule the settling could expand.
 */
class AnIncludedRuleThatCallsARecursiveHelperTest {

    private static final String LIB = """
            module lib.v exposing ( Base, Chain )
            data Chain = { k: Int, next: Chain? }
            let valid (c: Chain): Bool = match c.next with
                | Some rest -> c.k >= 0 && valid(rest)
                | None -> c.k >= 0
            data Base = { chain: Chain }
                invariant ok = valid(chain)
            """;

    private static final String APP = """
            module app.v exposing ( Wrapped, wrap )
            import lib.v ( Base, Chain )
            data Wrapped = { ...Base, w: Int }
            behavior wrap : (c: Chain) -> Wrapped
            let wrap (c) = Wrapped { chain = c, w = 1 }
            """;

    @Test
    void theRuleRunsWhereTheModulesAreCompiledTogether() throws Exception {
        heldToTheIncludedRule(Compiler.compileModules(List.of(LIB, APP), ModulePath.EMPTY));
    }

    @Test
    void theRuleRunsWhereTheIncludingModuleIsCompiledAgainstAJar() throws Exception {
        Map<String, ClassFileImage> lib = Compiler.compile(LIB);
        Map<String, ClassFileImage> classes = new HashMap<>(lib);
        classes.putAll(Compiler.compileModules(List.of(APP), ModulePath.of(lib)));
        heldToTheIncludedRule(classes);
    }

    /** A helper of the including module under the same name, recursive and saying yes to
     *  everything, is not the one the included rule reaches. */
    @Test
    void aHelperOfTheIncludingModuleSpelledTheSameIsNotTheOneTheRuleReaches() throws Exception {
        heldToTheIncludedRule(Compiler.compileModules(List.of(LIB, """
                module app.v exposing ( Wrapped )
                import lib.v ( Base, Chain )
                let valid (c: Chain): Bool = match c.next with
                    | Some rest -> valid(rest)
                    | None -> true
                data Wrapped = { ...Base, w: Int }
                data Own = { mine: Chain }
                    invariant ok = valid(mine)
                """), ModulePath.EMPTY));
    }

    /** Two modules each keep a recursive `valid` to themselves, and one type includes a type of
     *  each: each rule reaches its own module's. */
    @Test
    void twoIncludedRulesReachTheHelpersOfTheirOwnModules() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(LIB, """
                module lib.w exposing ( Top )
                import lib.v ( Chain )
                let valid (c: Chain): Bool = match c.next with
                    | Some rest -> c.k <= 10 && valid(rest)
                    | None -> c.k <= 10
                data Top = { top: Chain }
                    invariant capped = valid(top)
                """, """
                module app.v exposing ( Both )
                import lib.v ( Base )
                import lib.w ( Top )
                data Both = { ...Base, ...Top, w: Int }
                """), ModulePath.EMPTY), getClass().getClassLoader());

        assertInstanceOf(Ok.class, Codecs.decode(loader, "app.v.Both",
                Map.of("chain", chainEndingIn(5), "top", chainEndingIn(5), "w", 1L)));
        assertInstanceOf(Err.class, Codecs.decode(loader, "app.v.Both",
                Map.of("chain", chainEndingIn(-1), "top", chainEndingIn(5), "w", 1L)));
        assertInstanceOf(Err.class, Codecs.decode(loader, "app.v.Both",
                Map.of("chain", chainEndingIn(5), "top", chainEndingIn(11), "w", 1L)));
    }

    /** A type taken in through a type of another module brings the rule of the first, and the
     *  module at the end runs it. */
    @Test
    void aRuleTakenInThroughAnotherModulesTypeRuns() throws Exception {
        String middle = """
                module lib.m exposing ( Mid )
                import lib.v ( Base )
                data Mid = { ...Base, m: Int }
                """;
        String top = """
                module app.v exposing ( Top )
                import lib.m ( Mid )
                data Top = { ...Mid, t: Int }
                """;
        Map<String, ClassFileImage> lib = Compiler.compile(LIB);
        Map<String, ClassFileImage> onThePath = new HashMap<>(lib);
        onThePath.putAll(Compiler.compileModules(List.of(middle), ModulePath.of(lib)));
        Map<String, ClassFileImage> classes = new HashMap<>(onThePath);
        classes.putAll(Compiler.compileModules(List.of(top), ModulePath.of(onThePath)));

        for (Map<String, ClassFileImage> each : List.of(classes,
                Compiler.compileModules(List.of(LIB, middle, top), ModulePath.EMPTY))) {
            BytesClassLoader loader = new BytesClassLoader(each, getClass().getClassLoader());
            assertInstanceOf(Ok.class, Codecs.decode(loader, "app.v.Top",
                    Map.of("chain", chainEndingIn(5), "m", 1L, "t", 1L)));
            assertInstanceOf(Err.class, Codecs.decode(loader, "app.v.Top",
                    Map.of("chain", chainEndingIn(-1), "m", 1L, "t", 1L)));
        }
    }

    /** Two helpers that call each other are taken on together. */
    @Test
    void helpersThatCallEachOtherAreTakenOnTogether() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module lib.v exposing ( Base, Chain )
                data Chain = { k: Int, next: Chain? }
                let good (c: Chain): Bool = match c.next with
                    | Some rest -> c.k >= 0 && also(rest)
                    | None -> c.k >= 0
                let also (c: Chain): Bool = match c.next with
                    | Some rest -> c.k >= 0 && good(rest)
                    | None -> c.k >= 0
                data Base = { chain: Chain }
                    invariant ok = good(chain)
                """, """
                module app.v exposing ( Wrapped )
                import lib.v ( Base )
                data Wrapped = { ...Base, w: Int }
                """), ModulePath.EMPTY), getClass().getClassLoader());

        assertInstanceOf(Ok.class, Codecs.decode(loader, "app.v.Wrapped",
                Map.of("chain", Map.of("k", 1L, "next", chainEndingIn(5)), "w", 1L)));
        assertInstanceOf(Err.class, Codecs.decode(loader, "app.v.Wrapped",
                Map.of("chain", Map.of("k", 1L, "next", chainEndingIn(-1)), "w", 1L)));
    }

    /** `app.v.Wrapped` accepts a chain whose links are all at least zero and refuses one that is
     *  not, past its first link. */
    private void heldToTheIncludedRule(Map<String, ClassFileImage> classes) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        assertInstanceOf(Ok.class, Codecs.decode(loader, "app.v.Wrapped",
                Map.of("chain", chainEndingIn(5), "w", 1L)));
        assertInstanceOf(Err.class, Codecs.decode(loader, "app.v.Wrapped",
                Map.of("chain", chainEndingIn(-1), "w", 1L)));
    }

    /** A chain of two links, the first of which is fine and the second of which is {@code k}. */
    private static Map<String, Object> chainEndingIn(long k) {
        return Map.of("k", 1L, "next", Map.of("k", k));
    }
}
