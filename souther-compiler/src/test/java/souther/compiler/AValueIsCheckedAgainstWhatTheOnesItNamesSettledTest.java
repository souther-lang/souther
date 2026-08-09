package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value is substituted where it is named, and its own check does not need the copy.
 *
 * <p>What that check needs of a value it names is what that value's own check settled: the type it
 * stands under, and the constant it is one of where a fold reaches it. Both are worked out once and
 * read, rather than derived again out of a copy of the body — a chain of values would otherwise
 * cost the chain again per link.
 *
 * <p>What the backend emits is the other question and is unchanged: a value is substituted at each
 * of its references, and every test here that runs the emitted code says so.
 */
class AValueIsCheckedAgainstWhatTheOnesItNamesSettledTest {

    private BytesClassLoader loader(String source) {
        return new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
    }

    /** A chain of values still computes what it says. The check reads each one's settled answer;
     *  the emitted body reads the substitution, and the two have to agree. */
    @Test
    void aChainOfValuesIsStillSubstitutedIntoWhatTheBackendEmits() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let one = 1
                let two = one + 1
                let four = two + two

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + four }
                """);
        Object behavior = loader.loadClass("demo.Bump$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", 10L)));
        assertEquals(14L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("n"));
    }

    /** The order the module wrote them in is not the order they have to be settled in: a value may
     *  be written above the one it names. */
    @Test
    void aValueMayBeWrittenAboveTheOneItNames() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let four = two + two
                let two = one + 1
                let one = 1

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + four }
                """);
        Object behavior = loader.loadClass("demo.Bump$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", 10L)));
        assertEquals(14L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("n"));
    }

    /** A mis-typed value is reported at the value, and reported once. Its own check is what reads
     *  the body; the values that name it read the answer. */
    @Test
    void aValueThatDoesNotTypeIsReportedAtItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let text = "no"
                let sum = text + 1
                let more = sum + 1

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + more }
                """));
        assertTrue(e.getMessage().contains("sum") || e.getMessage().contains("String"),
                e.getMessage());
    }

    /** A value the fold does not reach stands under its type, and what it is still types. A
     *  construction is one: nothing folds it to a literal. */
    @Test
    void aValueNoFoldReachesIsStillTypedThroughAChain() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }
                data Hours = Int

                let base = Hours(3)
                let same = base
                let again = same

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + again.value }
                """);
        Object behavior = loader.loadClass("demo.Bump$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", 10L)));
        assertEquals(13L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("n"));
    }

    /** Naming a value in a position that demands a compile-time string still reaches the string.
     *  The value is written out as the constant it folded to, so the fold reads a literal — and it
     *  reaches through a chain of values, each of which folded before the next was checked. */
    @Test
    void aChainOfValuesStillComposesACompileTimePattern() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { s: String }
                data Out = Bool

                let digits = "[0-9]"
                let three = digits ++ digits ++ digits
                let code = three ++ "-" ++ digits

                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(String.matches(code, i.s))
                """));
    }

    /**
     * The same demand inside a value's own body, which is the check that reads a value by its
     * settled answer rather than by a copy. The pattern names another value, and the fold has to
     * reach the string through it — which is what writing a constant out at the reference is for.
     */
    @Test
    void aValueMayItselfDemandACompileTimePatternOfAnotherValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { s: String }
                data Out = Bool

                let digits = "[0-9]"
                let code = digits ++ digits
                let matched = String.matches(code, "42")

                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(matched)
                """));
    }

    /** And a malformed one there is still refused as a regex, rather than as an expression nothing
     *  could evaluate at compile time. */
    @Test
    void aMalformedPatternInsideAValueIsStillARegexError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { s: String }
                data Out = Bool

                let digits = "[0-9]"
                let broken = String.matches(digits ++ "[", "42")

                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(broken)
                """));
        assertTrue(e.getMessage().contains("not a valid regular expression"), e.getMessage());
    }
}
