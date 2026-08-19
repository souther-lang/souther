package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every binding the invariant-discharge walk descends under is entered as a location and seeded with
 * what its type guarantees, and the two happen together. A binding entered but not seeded is a place
 * the check names and knows nothing about, so a clause reading it is owed with nothing to establish
 * it — a warning no guard clears. A binding seeded but not entered names nothing to seed.
 *
 * <p>Which is why each site is held by a refutation and not by silence. A construction that must
 * violate tells the two halves apart: it is an error where the binding is entered and seeded, a
 * warning where it is entered and not seeded, and nothing at all where it is not entered — so a
 * missing half of either kind fails the assertion rather than passing quietly. A test asserting that
 * a valid program is silent cannot do this: dropping the binding entirely is also silent.
 *
 * <p>The three sites are the three places a value arrives that nothing else names: a behavior's
 * parameter, what a {@code match} arm binds, and what a combinator hands its closure.
 */
class CompileBindingIsEnteredTest {

    /** A non-negative newtype, and a product holding one. `0 - q - 1` is at most -1 for any q the
     * invariant admits, so a construction over it violates wherever the invariant is assumed. */
    private static final String TYPES = """
            data Q = Int
                invariant value >= 0
            data Held = { q: Q }
            """;

    private static String errorFrom(String module) {
        try {
            Compiler.compile(module);
            return "no diagnostic";
        } catch (CompileException e) {
            return e.diagnostic().code();
        }
    }

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void aBehaviorParameterIsEnteredAndSeeded() {
        String m = """
                module demo
                """ + TYPES + """
                behavior use : (held: Held) -> Q
                let use (held) = Q(0 - held.q.value - 1)
                """;
        assertEquals("E2010", errorFrom(m),
                "a parameter carries its type's invariant, so this construction is refuted");
    }

    @Test
    void aMatchArmBindingIsEnteredAndSeeded() {
        // `match` is the only way to open a sum, so a binding it introduces reaching the walk
        // unentered gives up inside every state machine the language is written around.
        String m = """
                module demo
                """ + TYPES + """
                data M = A | B
                data A = { q: Q }
                data B = { q: Q }
                behavior use : (m: M) -> Q
                let use (m) = match m with
                    | A as a -> Q(0 - a.q.value - 1)
                    | B as b -> b.q
                """;
        assertEquals("E2010", errorFrom(m),
                "what an arm binds carries its case type's invariant");
    }

    @Test
    void aClosureAccumulatorIsEnteredAndSeeded() {
        // The element is not the only value a combinator hands its closure. A fold's accumulator
        // holds the seed or a previous step's result, each built through its type's constructor.
        String m = """
                module demo
                """ + TYPES + """
                behavior total : (xs: List<Held>) -> Q
                let total (xs) = List.fold((acc, i) -> Q(0 - acc.value - 1), Q(0), xs)
                """;
        assertEquals("E2010", errorFrom(m),
                "a fold's accumulator carries the type it was seeded with");
    }

    @Test
    void aClosureElementIsEnteredAndSeeded() {
        String m = """
                module demo
                """ + TYPES + """
                behavior firsts : (xs: List<Held>) -> List<Q>
                let firsts (xs) = List.map(i -> Q(0 - i.q.value - 1), xs)
                """;
        assertEquals("E2010", errorFrom(m),
                "an element carries its container's element type's invariant");
    }

    @Test
    void anAttemptsSuccessBindingIsEnteredAndSeeded() {
        // `x * x` is not a form the numeric domain builds, so the attempt denotes nothing this can
        // name — which is what an attempt is written for. Reaching `then` is still the construction
        // having held, so the binding carries the invariant whatever the attempt could be said of.
        String m = """
                module demo
                """ + TYPES + """
                data Nope
                behavior use : (x: Int) -> Q | Nope constructs Q
                let use (x) = if Q(x * x) as q then Q(0 - q.value - 1) else Nope
                """;
        assertEquals("E2010", errorFrom(m),
                "the success binding carries the invariant the attempt established");
    }

    @Test
    void anArmBindingDischargesTheSameArithmeticAParameterDoes() {
        // The same addition over the same two types, reached two ways. Both are non-negative, so
        // both discharge; the arm reaching one through a binding is not what decides it.
        String m = """
                module demo
                """ + TYPES + """
                data M = A | B
                data A = { q: Q }
                data B = { q: Q }
                behavior direct : (a: Q, b: Q) -> Q
                let direct (a, b) = a + b
                behavior viaMatch : (x: Held, m: M) -> Q
                let viaMatch (x, m) = match m with
                    | A as a -> x.q + a.q
                    | B as b -> x.q + b.q
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "an arm's binding is seeded, so the addition discharges as it does for a parameter");
    }

    @Test
    void aFoldOverANewtypeDischargesWithoutGivingTheNewtypeUp() {
        // Staying in the newtype must not cost a warning that unwrapping and re-wrapping avoids.
        String m = """
                module demo
                """ + TYPES + """
                behavior total : (xs: List<Held>) -> Q
                let total (xs) = List.fold((acc, i) -> acc + i.q, Q(0), xs)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the accumulator and the element are both non-negative, so the sum discharges");
    }

    @Test
    void aBindingNothingEnteredNamesNothingRatherThanOwingAClause() {
        // The failure mode when a site is missed: the clause goes to the run-time check rather than
        // becoming a warning about a place the author never introduced. An unconstrained field is
        // named, so what is silent here is what is unknowable and not the whole check.
        String m = """
                module demo
                """ + TYPES + """
                data Loose = { n: Int }
                behavior use : (loose: Loose) -> Q
                let use (loose) = Q(loose.n)
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(m);
        assertTrue(c.warnings().stream()
                        .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code())),
                "an entered parameter over an unconstrained field is named and warned about");
    }
}
