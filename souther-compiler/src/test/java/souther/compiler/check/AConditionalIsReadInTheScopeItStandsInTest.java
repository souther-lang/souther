package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A conditional a construction is given is read in the scope it stands in.
 *
 * <p>The discharge walk reads a conditional in a value position by reading the whole value twice,
 * once with each branch standing there and each under what the condition settles. The conditional is
 * found inside the value and the value is read from the outside, so the two are at different places
 * in the body: everything a binding between them introduced is in scope for the conditional and not
 * yet in scope where the reading is decided on. A condition read at the outer place names bindings
 * nothing has entered, {@link Denotations} answers those with nothing, and the condition settles
 * nothing — so both readings run with the same knowledge and the conditional stops deciding anything.
 *
 * <p>What that costs is a warning on a construction the author cannot answer. The value is still
 * nameable through the binding once the reading walks into it, so the clause is owed and unproven,
 * and the remedies the warning names — a guard, a reified relation — are not what the body needs.
 *
 * <p>The bindings are the ones a call's expansion writes, so the shapes below are helpers; what is
 * held here is not about helpers but about the scope a conditional is read in, and the last two hold
 * the other direction — a binding is not in scope for its own initializer, and a condition that
 * settles nothing about what is built is still reported.
 */
class AConditionalIsReadInTheScopeItStandsInTest {

    private static final String YEN = """
            module demo
            data Yen = Int
                invariant nonNegative = value >= 0
            """;

    private static long warnings(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void aConditionalUnderABindingReadsThatBinding() {
        // `atLeastZero(n)` is `let $n = n in if $n < 0 then 0 else $n`, so the condition names a
        // binding the walk enters only on its way into the body.
        assertEquals(0, warnings(YEN + """
                let atLeastZero (n: Int) = if n < 0 then 0 else n
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = Yen(atLeastZero(n))
                """),
                "both branches are non-negative under the condition, as they are written inline");
    }

    @Test
    void aConditionalUnderABindingReadsItWhereverTheConstructionStands() {
        assertEquals(0, warnings(YEN + """
                let atLeastZero (n: Int) = if n < 0 then 0 else n
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = {
                    let k = atLeastZero(n)
                    Yen(k)
                }
                """),
                "naming the value does not change what the conditional settles");
    }

    @Test
    void aConditionalUnderSeveralBindingsReadsThemAll() {
        assertEquals(0, warnings(YEN + """
                let atLeast (n: Int, floor: Int) = if n < floor then floor else n
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = Yen(atLeast(n, 0))
                """),
                "the condition names both bindings the expansion wrote");
    }

    @Test
    void aConditionalUnderNestedExpansionsReadsEachScope() {
        assertEquals(0, warnings(YEN + """
                let atLeastZero (n: Int) = if n < 0 then 0 else n
                let clamped (n: Int) = atLeastZero(n)
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = Yen(clamped(n))
                """),
                "one expansion inside another is two bindings on the way in, entered outermost first");
    }

    @Test
    void aBindingIsNotInScopeForItsOwnInitializer() {
        assertEquals(0, warnings(YEN + """
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = {
                    let k = if n < 0 then 0 else n
                    Yen(k)
                }
                """),
                "the conditional is what `k` is given, and is read before `k` stands for anything");
    }

    @Test
    void aConditionThatSettlesNothingAboutTheValueIsStillReported() {
        assertEquals(1, warnings(YEN + """
                let same (n: Int) = n
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = Yen(same(n))
                """),
                "nothing said `n` is non-negative, and reading the binding does not say it");
        assertEquals(1, warnings(YEN + """
                behavior f : (n: Int, m: Int) -> Yen constructs Yen
                let f (n, m) = Yen(if m < 0 then 0 else n)
                """),
                "the condition is about `m` and the value built is `n`");
    }
}
