package souther.compiler;

import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module on the path was built against the declarations its classes read, and is held to each of
 * them as this compilation has it — declaration by declaration, and to nothing else.
 *
 * <p>Each case below builds {@code lib.b} against one version of {@code lib.c}, reads it beside
 * another, and compiles a module that uses only the part of {@code lib.b} that reads nothing of
 * {@code lib.c}: what a module was built against is a fact about all of it.
 */
class AModuleOnThePathIsHeldToEachDeclarationItsClassesReadTest {

    /** Uses the one behavior of `lib.b` that reads nothing of `lib.c`. */
    private static final String USES_ONLY_INC = """
            module app.u
            import lib.b ( inc )
            behavior twice : (n: Int) -> Int
            let twice (n) = inc(inc(n))
            """;

    private static final String C = """
            module lib.c exposing ( twice, thrice )
            behavior twice : (n: Int) -> Int
            let twice (n) = n + n
            behavior thrice : (n: Int) -> Int
            let thrice (n) = n * 3
            """;

    /** Calls `lib.c.twice` by name from a body, which is not published. */
    private static final String B_CALLS_TWICE = """
            module lib.b exposing ( inc, use )
            import lib.c ( twice )
            behavior inc : (n: Int) -> Int
            let inc (n) = n + 1
            behavior use : (n: Int) -> Int
            let use (n) = twice(n)
            """;

    /** `lib.b` built against {@code before}, read off the path beside {@code after}. */
    private static Map<String, ClassFileImage> builtAgainst(String before, String b, String after) {
        Map<String, ClassFileImage> path = new HashMap<>(Compiler.compileModules(List.of(b),
                ModulePath.of(Compiler.compile(before))));
        path.putAll(Compiler.compile(after));
        return path;
    }

    /** Every report a compile of {@code app} against {@code path} says, as what each says. */
    private static List<Object> said(String app, Map<String, ClassFileImage> path) {
        Compilation compilation = Compilation.ofSources(List.of(app), ModulePath.of(path));
        compilation.answerEverything();
        List<Object> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            out.add(found.report().diagnostic().said());
        }
        return out;
    }

    /** What moved about {@code name}, as the report about {@code module} says it. */
    private static ModuleMessage.ItWasBuiltAgainstAnotherLinkage moved(List<Object> said,
                                                                     String module, String name) {
        for (Object each : said) {
            if (each instanceof ModuleMessage.ItWasBuiltAgainstAnotherLinkage m
                    && m.module().equals(module) && m.name().equals(name)) {
                return m;
            }
        }
        throw new AssertionError("nothing says " + module + " was built against another " + name
                + ": " + said);
    }

    /** An edit to a declaration nothing of `lib.b` reads, and to the body of one it does: `lib.b`
     *  links against the same things, and is taken. */
    @Test
    void anEditToWhatItsClassesDoNotLinkAgainstIsTaken() {
        Map<String, ClassFileImage> path = builtAgainst(C, B_CALLS_TWICE, """
                module lib.c exposing ( twice, thrice )
                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2
                behavior thrice : (n: Int, m: Int) -> Int
                let thrice (n, m) = n * m
                """);

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(USES_ONLY_INC),
                ModulePath.of(path)));
    }

    /** A behavior `lib.b` calls that takes another type now: its classes hand it what it took. */
    @Test
    void aBehaviorThatTakesAnotherTypeNowIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst(C, B_CALLS_TWICE, """
                module lib.c exposing ( twice, thrice )
                behavior twice : (s: String) -> Int
                let twice (s) = String.length(s)
                behavior thrice : (n: Int) -> Int
                let thrice (n) = n * 3
                """);

        assertEquals("takes", moved(said(USES_ONLY_INC, path), "lib.b", "twice").fact());
    }

    /** A behavior `lib.b` calls that answers another type now: its classes take the answer as what
     *  it was. */
    @Test
    void aBehaviorThatAnswersAnotherTypeNowIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst(C, B_CALLS_TWICE, """
                module lib.c exposing ( twice, thrice )
                behavior twice : (n: Int) -> String
                let twice (n) = "two"
                behavior thrice : (n: Int) -> Int
                let thrice (n) = n * 3
                """);

        assertEquals("answers", moved(said(USES_ONLY_INC, path), "lib.b", "twice").fact());
    }

    /** A behavior `lib.b` calls that its module keeps to itself now: its classes are not public. */
    @Test
    void aBehaviorNoLongerExposedIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst(C, B_CALLS_TWICE, """
                module lib.c exposing ( thrice )
                behavior twice : (n: Int) -> Int
                let twice (n) = n + n
                behavior thrice : (n: Int) -> Int
                let thrice (n) = n * 3
                """);

        assertEquals("exposed", moved(said(USES_ONLY_INC, path), "lib.b", "twice").fact());
    }

    /**
     * A dependency `lib.b` holds, taking one input, that takes two now. A class holding a behavior
     * of one input keeps it as the runtime's unary {@code Behavior} and applies it through that
     * interface, so how it is held rests on how many inputs the behavior takes whatever the class
     * names.
     */
    @Test
    void aDependencyHeldAsTheUnaryBehaviorThatTakesTwoInputsNowIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.c exposing ( rate )
                behavior rate : (n: Int) -> Int
                """, """
                module lib.b exposing ( inc, charged )
                import lib.c ( rate )
                behavior inc : (n: Int) -> Int
                let inc (n) = n + 1
                behavior charged : (n: Int) -> Int depends on rate
                let charged (n, rate) = rate(n)
                """, """
                module lib.c exposing ( rate )
                behavior rate : (n: Int, m: Int) -> Int
                """);

        assertEquals("takes", moved(said(USES_ONLY_INC, path), "lib.b", "rate").fact());
    }

    /** A type whose field `lib.b` reads, holding another type there now: the accessor it calls is
     *  another method. */
    @Test
    void aTypeWhoseFieldHoldsAnotherTypeNowIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.c exposing ( Money )
                data Money = { amount: Int }
                """, """
                module lib.b exposing ( inc, read )
                import lib.c ( Money )
                behavior inc : (n: Int) -> Int
                let inc (n) = n + 1
                behavior read : (m: Money) -> Int
                let read (m) = m.amount
                """, """
                module lib.c exposing ( Money )
                data Money = { amount: Decimal }
                """);

        assertEquals("field amount", moved(said(USES_ONLY_INC, path), "lib.b", "Money").fact());
    }

    /**
     * Two fields of one type trading places in a type `lib.b` builds. Every descriptor stays as it
     * was, so its classes would link and hand each field the other's value; the layout moving is
     * what says so.
     */
    @Test
    void fieldsOfOneTypeTradingPlacesIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.c exposing ( Pair )
                data Pair = { left: Int, right: Int }
                """, """
                module lib.b exposing ( inc, make )
                import lib.c ( Pair )
                behavior inc : (n: Int) -> Int
                let inc (n) = n + 1
                behavior make : (n: Int) -> Pair constructs Pair
                let make (n) = Pair { left = n, right = 0 }
                """, """
                module lib.c exposing ( Pair )
                data Pair = { right: Int, left: Int }
                """);

        ModuleMessage.ItWasBuiltAgainstAnotherLinkage said =
                moved(said(USES_ONLY_INC, path), "lib.b", "Pair");
        assertEquals("laid out as", said.fact());
        assertEquals("(left, right)", said.built());
        assertEquals("(right, left)", said.now());
    }

    /** `lib.b` builds and reads a type of `lib.c`, which only its fields say anything about. */
    private static final String B_BUILDS_MONEY = """
            module lib.b exposing ( inc, make )
            import lib.c ( Money )
            behavior inc : (n: Int) -> Int
            let inc (n) = n + 1
            behavior make : (n: Int) -> Int constructs Money
            let make (n) = (Money { amount = n }).amount
            """;

    /**
     * A type `lib.b` builds gains a rule, or loses one. A class of another module builds it through
     * its {@code __construct} either way — its constructor is its own module's — so what `lib.b`
     * links by has not moved, and `lib.b` is taken both ways: what a rule states runs inside the
     * type's own class and is not linkage.
     */
    @Test
    void aTypeGainingOrLosingARuleIsTaken() {
        String bare = """
                module lib.c exposing ( Money )
                data Money = { amount: Int }
                """;
        String ruled = """
                module lib.c exposing ( Money )
                data Money = { amount: Int }
                    invariant amount >= 0
                """;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(USES_ONLY_INC),
                ModulePath.of(builtAgainst(bare, B_BUILDS_MONEY, ruled))));
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(USES_ONLY_INC),
                ModulePath.of(builtAgainst(ruled, B_BUILDS_MONEY, bare))));
        // And `lib.b` was built against it: a field it builds and reads holding another type moves
        // what it links by, so being taken above is not `lib.b` reading nothing of the type.
        assertEquals("field amount", moved(said(USES_ONLY_INC, builtAgainst(bare, B_BUILDS_MONEY, """
                module lib.c exposing ( Money )
                data Money = { amount: Decimal }
                """)), "lib.b", "Money").fact());
    }

    /** A published value `lib.b` reads that answers another type now: its classes take the entry's
     *  answer as what it was. */
    @Test
    void aValueThatAnswersAnotherTypeNowIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.c exposing ( limit )
                let limit = List.length([1, 2, 3])
                """, """
                module lib.b exposing ( inc, capped )
                import lib.c ( limit )
                behavior inc : (n: Int) -> Int
                let inc (n) = n + 1
                behavior capped : (n: Int) -> Int
                let capped (n) = n + limit
                """, """
                module lib.c exposing ( limit )
                let limit = List.reverse([1, 2, 3])
                """);

        assertEquals("answers", moved(said(USES_ONLY_INC, path), "lib.b", "limit").fact());
    }

    /** The declaration that moved is one of a module compiled here. What it offers is what its
     *  classes are about to offer, and `lib.b` is held to that. */
    @Test
    void aModuleCompiledHereIsWhatAModuleOnThePathIsHeldTo() {
        Map<String, ClassFileImage> path = Compiler.compileModules(List.of(B_CALLS_TWICE),
                ModulePath.of(Compiler.compile(C)));
        Compilation compilation = Compilation.ofSources(List.of("""
                module lib.c exposing ( twice, thrice )
                behavior twice : (n: Int) -> String
                let twice (n) = "two"
                behavior thrice : (n: Int) -> Int
                let thrice (n) = n * 3
                """, USES_ONLY_INC), ModulePath.of(path));
        compilation.answerEverything();
        List<Object> said = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            said.add(found.report().diagnostic().said());
        }

        assertEquals("answers", moved(said, "lib.b", "twice").fact());
    }

    private static final String D_TAKING_ONE = """
            module lib.d exposing ( rate )
            behavior rate : (n: Int) -> Int
            """;

    /**
     * `lib.b` reads `lib.c.twice`, which rests on nothing of `lib.d`; `lib.c`'s own `charged` holds
     * `lib.d.rate`. `lib.d` moves under both. What moved is said about `lib.c`, whose classes read
     * `rate`, and nothing is said about `lib.b`, whose classes did not: a module is held to what it
     * read and not to what the modules it read were built against.
     */
    @Test
    void aDeclarationThatMovedIsSaidOnlyAboutTheModulesWhoseClassesReadIt() {
        Map<String, ClassFileImage> older = Compiler.compileModules(List.of(D_TAKING_ONE, """
                module lib.c exposing ( twice, charged )
                import lib.d ( rate )
                behavior twice : (n: Int) -> Int
                let twice (n) = n + n
                behavior charged : (n: Int) -> Int depends on rate
                let charged (n, rate) = rate(n)
                """));
        Map<String, ClassFileImage> path = new HashMap<>(older);
        path.putAll(Compiler.compileModules(List.of(B_CALLS_TWICE), ModulePath.of(older)));
        path.putAll(Compiler.compile("""
                module lib.d exposing ( rate )
                behavior rate : (n: Int, m: Int) -> Int
                """));

        List<Object> said = said(USES_ONLY_INC, path);

        assertEquals("takes", moved(said, "lib.c", "rate").fact());
        assertTrue(said.stream().noneMatch(each ->
                        each instanceof ModuleMessage.ItWasBuiltAgainstAnotherLinkage m
                                && m.module().equals("lib.b")),
                "lib.b read nothing of lib.d: " + said);
    }
}
