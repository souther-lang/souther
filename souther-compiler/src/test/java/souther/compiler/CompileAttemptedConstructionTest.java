package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An attempted construction — {@code require X(v) as n else C}, and the {@code if X(v) as n then A
 * else B} it desugars to. The construction's invariant decides the branch: it holds, the value is
 * built and bound to {@code n}; it does not, the else value is taken and no value is built. A plain
 * {@code X(v)} still aborts (spec 7.3), so this is the one form that answers a rule the writer
 * cannot restate — an invariant naming a helper {@code let} is not reachable from an importing
 * module at all.
 */
class CompileAttemptedConstructionTest {

    private static final String MODULE = """
            module demo

            data Code = String
                invariant String.matches("[A-Z]{2}", value)

            data Accepted = { code: Code }
            data Rejected

            behavior take : (raw: String) -> Accepted | Rejected
                constructs Accepted, Code, Rejected

            let take (raw) = {
                require Code(raw) as c else Rejected

                Accepted { code = c }
            }
            """;

    private Object take(BytesClassLoader loader, String raw) throws Exception {
        Object impl = loader.loadClass("demo.Take" + "$Impl").getConstructor().newInstance();
        return Codecs.apply(impl, raw);
    }

    @Test
    void theInvariantHoldingBindsTheBuiltValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        Object r = take(loader, "AB");
        assertEquals("demo.Accepted", r.getClass().getName(), "\"AB\" matches [A-Z]{2}");
    }

    @Test
    void theInvariantFailingTakesTheElseValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        Object r = take(loader, "zzz");
        assertEquals("demo.Rejected", r.getClass().getName(),
                "\"zzz\" fails [A-Z]{2}, so the attempt departs rather than aborting");
    }

    /**
     * The {@code if} form is the base one: a helper {@code let} has no departure case to name, so
     * {@code require} does not reach here. Dropping a value the invariant rejects is what
     * {@code domainOf} does with the domain part of an address.
     */
    @Test
    void aHelperKeepsOnlyTheValuesTheInvariantAccepts() throws Exception {
        String src = """
                module demo exposing (collect, Code, Codes)

                data Code = String
                    invariant String.matches("[A-Z]{2}", value)

                data Codes = { kept: List<Code> }

                let accept (raw: String): List<Code> =
                    if Code(raw) as c then [ c ] else []

                behavior collect : (raw: String) -> Codes
                    constructs Codes, Code

                let collect (raw) = Codes { kept = accept(raw) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object impl = loader.loadClass("demo.Collect" + "$Impl").getConstructor().newInstance();

        assertEquals(Map.of("kept", List.of("AB")),
                Codecs.encode(loader, "demo.Codes", Codecs.apply(impl, "AB")),
                "the invariant accepts it, so the helper keeps it");
        assertEquals(Map.of("kept", List.of()),
                Codecs.encode(loader, "demo.Codes", Codecs.apply(impl, "zzz")),
                "the invariant rejects it, so the helper drops it rather than aborting");
    }

    /**
     * The case a restated guard cannot reach. {@code m1}'s invariant names a helper {@code let}, and
     * a helper is not a specification statement, so it cannot be exposed; promoting it to a behavior
     * would put it out of the invariant's reach instead (an invariant calls a {@code let}, never a
     * behavior). An importing module therefore has no name for the rule and no way to guard the
     * construction — it attempts the type, which its module does expose.
     */
    @Test
    void anImportingModuleAttemptsARuleItHasNoNameFor() throws Exception {
        String m1 = """
                module m1 exposing (Code)

                let looksLikeACode (s: String): Bool = String.matches("[A-Z]{2}", s)

                data Code = String
                    invariant looksLikeACode(value)
                """;
        String m2 = """
                module m2 exposing (take, Kept)

                import m1 ( Code )

                data Kept = { codes: List<Code> }

                behavior take : (raw: String) -> Kept
                    constructs Kept, Code

                let take (raw) = Kept { codes = if Code(raw) as c then [ c ] else [] }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(m1, m2)),
                getClass().getClassLoader());
        Object impl = loader.loadClass("m2.Take" + "$Impl").getConstructor().newInstance();

        assertEquals(Map.of("codes", List.of("AB")),
                Codecs.encode(loader, "m2.Kept", Codecs.apply(impl, "AB")));
        assertEquals(Map.of("codes", List.of()),
                Codecs.encode(loader, "m2.Kept", Codecs.apply(impl, "zzz")),
                "the imported invariant decides the branch, with nothing restated here");
    }

    /** What decides the branch is the invariant. A type with none has no failing side, so the else
     * value is unreachable and the attempt is not one — the same reason a unit data may not carry an
     * invariant rather than carry one with no effect. */
    @Test
    void attemptingATypeWithNoInvariantIsAnError() {
        String src = """
                module demo exposing (take, Code, Kept)

                data Code = String
                data Kept = { code: Code }
                data Skipped

                behavior take : (raw: String) -> Kept | Skipped
                    constructs Kept, Code, Skipped

                let take (raw) = {
                    require Code(raw) as c else Skipped

                    Kept { code = c }
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2013", e.code());
    }

    /**
     * The possible-violation warning says a construction may abort here. An attempted one cannot —
     * a failing invariant takes the else branch — so the warning has nothing to report, and the
     * attempt is what silences it for an invariant the checked fragment cannot express at all.
     */
    @Test
    void anAttemptedConstructionIsNotAPossibleViolation() {
        String src = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                data TooSmall

                behavior diff : (p: Pair) -> Money | TooSmall
                    constructs Money, TooSmall

                let diff (p) = {
                    require Money(p.a.value - p.b.value) as d else TooSmall

                    d
                }
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(src);
        assertEquals(0, c.warnings().stream()
                        .filter(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code())).count(),
                "the attempt cannot abort, so there is no possible violation to warn about");
    }

    /**
     * A violation the compiler *decides* is still an error inside an attempt: with the outcome
     * settled at compile time there was never a branch, and the plain construction reports the same
     * thing. The attempt is for a value the compiler cannot decide, not a way past one it can.
     */
    @Test
    void aDecidedViolationIsStillReportedInsideAnAttempt() {
        String src = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data TooSmall

                behavior calc : (x: Int) -> Money | TooSmall
                    constructs Money, TooSmall

                let calc (x) = {
                    require Money(-1m) as m else TooSmall

                    m
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2010", e.code(), e.getMessage());
    }

    /** An attempt builds the value on its success branch, so it needs the permission any other
     * construction needs. */
    @Test
    void anAttemptNeedsTheConstructionPermission() {
        String src = """
                module demo
                data Code = String
                    invariant String.matches("[A-Z]{2}", value)
                data Kept = { code: Code }
                data Skipped

                behavior take : (raw: String) -> Kept | Skipped
                    constructs Kept, Skipped

                let take (raw) = {
                    require Code(raw) as c else Skipped

                    Kept { code = c }
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1002", e.code(), e.getMessage());
    }
    /**
     * {@code example} runs the generated bytecode, so an attempt needs nothing of its own there. Both
     * branches are pinned at compile time: the row that holds and the row that does not.
     */
    @Test
    void anExamplePinsBothBranchesOfAnAttempt() {
        String src = """
                module demo

                data Code = String
                    invariant String.matches("[A-Z]{2}", value)

                data Accepted = { code: Code }
                data Rejected

                behavior take : (raw: String) -> Accepted | Rejected
                    constructs Accepted, Code, Rejected

                let take (raw) = {
                    require Code(raw) as c else Rejected

                    Accepted { code = c }
                }

                example take
                    | "the invariant holds, so the value is built" : ("AB") -> Accepted { code = "AB" }
                    | "the invariant fails, so it departs" : ("zzz") -> Rejected
                """;
        Compiler.compile(src);   // an example that disagreed would fail the build (E1901)
    }

    /** {@code as} names the value a construction builds. Anything else has no value to name and no
     * invariant to decide the branch. */
    @Test
    void asOnSomethingThatIsNotAConstructionIsAnError() {
        String src = """
                module demo
                data Kept = { n: Int }
                data Skipped

                behavior take : (n: Int) -> Kept | Skipped
                    constructs Kept, Skipped

                let take (n) = {
                    require n > 0 as c else Skipped

                    Kept { n = c }
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2012", e.code(), e.getMessage());
    }
}
