package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * One expression, one answer, however it is written. The invariant-discharge check reads a value
 * through what it denotes rather than through the shape it was typed in, so the function form of an
 * operator is that operator, and naming a subexpression with a {@code let} does not change what is
 * known about it.
 */
class CompileInvariantOneDenotationTest {

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void theFunctionFormOfAnOperatorIsRefutedWhereTheOperatorIs() {
        // 0 - 1 is negative — the same definite violation the operator spelling is an error for
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                behavior calc : (m: Money) -> Money
                    constructs Money
                let calc (m) = Money(Decimal.subtract(0m, 1m))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(),
                "Decimal.subtract is `-`, so the violation is decided: " + e.getMessage());
    }

    @Test
    void theFunctionFormOfAnOperatorDischargesWhereTheOperatorDoes() {
        // b >= a, so b - a is non-negative and the re-wrap needs no guard
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                    invariant a <= b
                behavior diff : (p: Pair) -> Money
                    constructs Money
                let diff (p) = Money(Decimal.subtract(p.b.value, p.a.value))
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the reified relation discharges the function form as it does the operator");
    }

    @Test
    void theFunctionFormOfAnAdditionIsThatAddition() {
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior total : (p: Pair) -> Money
                    constructs Money
                let total (p) = Money(Decimal.add(p.a.value, p.b.value))
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a sum of non-negatives is non-negative, written either way");
    }

    @Test
    void aVariableProductIsNotRead() {
        // `x * y` is not affine, and neither is its function form — nothing is proven either way
        String m = """
                module demo
                data Count = Int
                    invariant value >= 0
                data Pair = { a: Count, b: Count }
                behavior area : (p: Pair) -> Count
                    constructs Count
                let area (p) = Count(Int.multiply(p.a.value, p.b.value))
                """;
        assertEquals(warnings(Compiler.compileWithWarnings(m.replace(
                        "Int.multiply(p.a.value, p.b.value)", "p.a.value * p.b.value"))),
                warnings(Compiler.compileWithWarnings(m)),
                "a variable product answers the same in both spellings");
    }

    @Test
    void aScalarProductIsThatProduct() {
        String m = """
                module demo
                data Count = Int
                    invariant value >= 0
                behavior twice : (c: Count) -> Count
                    constructs Count
                let twice (c) = Count(Int.multiply(2, c.value))
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "twice a non-negative is non-negative");
    }

    private static final String EACHES = """
            module demo
            data Eaches = Int
                invariant value >= 0
            data PackSize = Int
                invariant value >= 1
            behavior leftover : (eaches: Eaches, pack: PackSize) -> Eaches
                constructs Eaches
            let leftover (eaches, pack) = %s
            """;

    @Test
    void namingACallDoesNotChangeWhatIsKnownOfIt() {
        // the call is the same call either way, so the construction from it answers the same
        assertEquals(warnings(Compiler.compileWithWarnings(
                        EACHES.formatted("Eaches(Int.modBy(pack.value, eaches.value))"))),
                warnings(Compiler.compileWithWarnings(EACHES.formatted("""
                        {
                                let n = Int.modBy(pack.value, eaches.value)
                                Eaches(n)
                            }"""))),
                "inline and named answer alike");
    }

    @Test
    void aCallNothingHasSpokenAboutIsSilent() {
        assertEquals(0, warnings(Compiler.compileWithWarnings(
                        EACHES.formatted("Eaches(Int.modBy(pack.value, eaches.value))"))),
                "nothing is known of the call, so its construction is left to the run-time check");
    }

    private static final String GUARDED = """
            module demo
            data %s = Int
                invariant value >= %d
            data PackSize = Int
                invariant value >= 1
            data Odd = { why: Int }
            behavior f : (n: Int, pack: PackSize) -> %s | Odd
                constructs %s, Odd
            let f (n, pack) = {
                %s
            }
            """;

    private static String guarded(String type, int bound, String body) {
        return GUARDED.formatted(type, bound, type, type, body);
    }

    @Test
    void aGuardOnACallDischargesWhatItEstablishes() {
        String named = guarded("Eaches", 0, """
                let n = Int.modBy(pack.value, n)
                    guard n >= 0 else Odd { why = n }
                    Eaches(n)""");
        String inline = guarded("Eaches", 0, """
                guard Int.modBy(pack.value, n) >= 0 else Odd { why = 0 }
                    Eaches(Int.modBy(pack.value, n))""");
        assertEquals(0, warnings(Compiler.compileWithWarnings(named)), "the guard establishes it");
        assertEquals(0, warnings(Compiler.compileWithWarnings(inline)),
                "and establishes it written inline too");
    }

    @Test
    void aGuardOnACallLeavesWhatItDoesNotEstablishReported() {
        // `>= 0` is stated and `>= 1` is owed — expressible, and unproven, in both spellings
        String named = guarded("AtLeastOne", 1, """
                let n = Int.modBy(pack.value, n)
                    guard n >= 0 else Odd { why = n }
                    AtLeastOne(n)""");
        String inline = guarded("AtLeastOne", 1, """
                guard Int.modBy(pack.value, n) >= 0 else Odd { why = 0 }
                    AtLeastOne(Int.modBy(pack.value, n))""");
        assertEquals(1, warnings(Compiler.compileWithWarnings(named)), "stated, and still unproven");
        assertEquals(1, warnings(Compiler.compileWithWarnings(inline)), "the same written inline");
    }

    @Test
    void aClauseFoldsTheWayItIsRead() {
        // read under a denial, folding to true is the violation and not the discharge
        String m = """
                module demo
                data Pair = { lo: Int, hi: Int }
                    invariant Bool.not(lo > hi)
                behavior mk : (x: Int) -> Pair
                    constructs Pair
                let mk (x) = Pair { lo = 5, hi = 3 }
                """;
        assertEquals("E2010", assertThrows(CompileException.class, () -> Compiler.compile(m))
                .diagnostic().code(), "5 > 3, and the clause denies it");
    }

    @Test
    void aWrittenDecimalComparesByAmount() {
        // 1.0m and 1.00m are one number, so `/=` of the two is false where it is constructed
        String m = """
                module demo
                data Pair = { a: Decimal, b: Decimal }
                    invariant a /= b
                behavior mk : (x: Int) -> Pair
                    constructs Pair
                let mk (x) = Pair { a = 1.0m, b = 1.00m }
                """;
        assertEquals("E2010", assertThrows(CompileException.class, () -> Compiler.compile(m))
                .diagnostic().code(), "scale is not part of what a decimal is");
    }

    @Test
    void aWrittenValueIsNotSomethingToGuard() {
        // nothing can be stated of `"xyz"` that the text does not say, so nothing is reported of it
        String m = """
                module demo
                data Code = String
                    invariant String.startsWith("x", value)
                behavior mk : (x: Int) -> Code
                    constructs Code
                let mk (x) = Code("xyz")
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a written value carries no guard the author could add");
    }

    private static final String CLAMP = """
            module demo
            data Count = Int
                invariant value >= 0
            behavior mk : (x: Int) -> Count
                constructs Count
            let mk (x) = %s
            """;

    @Test
    void aConstructionOverAConditionalIsReadOnEachBranch() {
        // x is at least one where the condition holds, and the other branch is zero, so both satisfy
        assertEquals(0, warnings(Compiler.compileWithWarnings(
                        CLAMP.formatted("Count(if x > 0 then x else 0)"))),
                "each branch discharges under its own condition");
    }

    @Test
    void namingAConditionalDoesNotChangeWhatIsKnownOfIt() {
        assertEquals(warnings(Compiler.compileWithWarnings(
                        CLAMP.formatted("Count(if x > 0 then x else 0)"))),
                warnings(Compiler.compileWithWarnings(CLAMP.formatted("""
                        {
                                let c = if x > 0 then x else 0
                                Count(c)
                            }"""))),
                "the name answers as the conditional does");
    }

    @Test
    void aConstructionEveryBranchViolatesIsRefuted() {
        assertEquals("E2010", assertThrows(CompileException.class,
                        () -> Compiler.compile(CLAMP.formatted("Count(if x > 0 then 0 - 1 else 0 - 2)")))
                .diagnostic().code(), "neither branch can satisfy it");
    }

    @Test
    void anAliasKeepsWhatTheGuardSaidOfWhatItNames() {
        // `c` is `x`, so the condition bounding x bounds it; copying it must not drop that
        assertEquals(0, warnings(Compiler.compileWithWarnings(CLAMP.formatted("""
                        if x > 0 then {
                                let c = x
                                Count(c)
                            } else Count(0)"""))),
                "a name for a location is that location");
    }

    @Test
    void aConstructionOneBranchSatisfiesIsNotRefuted() {
        // the comprehension is one element or none, so the construction may violate and does not
        // definitely violate — an error here would fail a build over a value that can be fine
        String m = """
                module demo
                data Reasons = { why: List<Int> }
                    invariant List.length(why) >= 1
                behavior mk : (age: Int) -> Reasons
                    constructs Reasons
                let mk (age) = Reasons { why = [ 75 | age >= 75 ] }
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(m);
        assertEquals(1, warnings(c), "possible, and not decided");
        assertFalse(c.classes().isEmpty(), "a possible violation does not fail the build");
    }

    @Test
    void aWrittenTableIsNotSomethingToGuard() {
        // every row is there to read, and no guard an author could add says more about it
        String m = """
                module demo
                data Row = { grade: Int }
                data Table = List<Row>
                    invariant List.allUniqueBy(.grade, value)
                let row (n: Int) = Row { grade = n }
                behavior mk : (x: Int) -> Table
                    constructs Table, Row
                let mk (x) = Table([ row(1), row(2), row(3) ])
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a table written into the source carries no guard");
    }

    @Test
    void aClauseThatFoldsToFalseIsSaid() {
        // the pattern and the value are both written, so whether it holds is computed, not owed
        String m = """
                module demo
                data Zip = { code: String }
                    invariant String.matches("[0-9][0-9]", code)
                behavior bad : (x: Int) -> Zip
                    constructs Zip
                let bad (x) = Zip { code = "abc" }
                """;
        assertEquals("E2010", assertThrows(CompileException.class, () -> Compiler.compile(m))
                .diagnostic().code(), "computed, and it does not hold");
    }

    @Test
    void anAliasOfAComputedTermIsThatTerm() {
        // `m` is `n` is `c.value + 1`, and copying a name must not drop what is known of it
        String m = """
                module demo
                data Count = Int
                    invariant value >= 0
                data Positive = Int
                    invariant value >= 1
                behavior next : (c: Count) -> Positive
                    constructs Positive
                let next (c) = {
                    let n = c.value + 1
                    %s
                }
                """;
        assertEquals(warnings(Compiler.compileWithWarnings(m.formatted("Positive(n)"))),
                warnings(Compiler.compileWithWarnings(m.formatted("let m = n\n        Positive(m)"))),
                "a name for a term is that term");
    }

    @Test
    void aBranchNothingReachesSaysNothing() {
        // under `x > 5` the inner test cannot hold, so what it would have built is not a value
        String m = """
                module demo
                data Positive = Int
                    invariant value >= 1
                behavior mk : (x: Int) -> Positive
                    constructs Positive
                let mk (x) = if x > 5 then Positive(if x < 3 then 0 else 7) else Positive(9)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a branch the conditions exclude is not one the value could have taken");
    }

    @Test
    void aNamedConditionalOneBranchSatisfiesIsNotRefuted() {
        // the two readings of the body are one construction, so they are answered together
        String m = """
                module demo
                data Count = Int
                    invariant value >= 0
                behavior mk : (x: Int) -> Count
                    constructs Count
                let mk (x) = %s
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(m.formatted("""
                {
                        let n = if x > 0 then 0 - 1 else 5
                        Count(n)
                    }"""));
        assertEquals(1, warnings(c), "possible, and not decided");
        assertEquals(warnings(Compiler.compileWithWarnings(
                        m.formatted("Count(if x > 0 then 0 - 1 else 5)"))),
                warnings(c), "the name answers as the conditional does");
    }
}
