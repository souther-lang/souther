package souther.compiler;

import souther.compiler.check.HelperInliner;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code partial} declaration does not carry Souther's termination guarantee, and a helper written
 * without the word carries it for everything it reaches (spec §fn-rules). What the size-change check
 * proves on its own is narrower — that one recursion's descent is structural — so a certified helper
 * used to be free to call a {@code partial} one off its cycle and not terminate.
 *
 * <p>The word says nothing about whether the helper diverges. A recursion that does terminate and that
 * the analysis cannot prove is written this way too, and is treated the same: the compiler is not
 * answering for it, so neither is anything that reaches it.
 *
 * <p>Read through {@code diagnoseModules} rather than {@code compile} wherever the count matters — a
 * throw shows one error, and the point of asking per declaration is that a module needing the word in
 * several places says so in one build.
 */
class AnUnmarkedHelperMayNotReachAPartialOneTest {

    private static final String REACHES = "check.totality.reachespartial";
    private static final String INVARIANT = "check.invariant.partial";

    private static List<Diagnostic> diagnosed(String source) {
        return Located.diagnosticsOf(Compiler.diagnoseModules(Map.of("demo", source)))
                .getOrDefault("demo", List.of());
    }

    /** The paths reported under {@code key}, in the order the build found them. The rendered path is
     * the last argument of both diagnostics that carry one. */
    private static List<String> pathsOf(String source, String key) {
        return diagnosed(source).stream()
                .filter(d -> key.equals(d.messageKey()))
                .map(d -> String.valueOf(d.args()[d.args().length - 1]))
                .toList();
    }

    // --- what the word means ------------------------------------------------

    /** The issue as reported: `depth` descends structurally and is certified, and calls a `partial`
     * helper off its cycle, so it does not terminate on any tree with a child. */
    @Test
    void aCertifiedRecursionMayNotCallAPartialHelperOffItsCycle() {
        String src = """
                module demo
                partial let spin (n: Int): Int = spin(n)
                data Tree = { child: Tree?, n: Int }
                data Out = Int
                behavior run : (t: Tree) -> Out constructs Out
                let depth (t: Tree): Int =
                    match t.child with
                        | Some c -> depth(c) + spin(t.n)
                        | None -> 0
                let run (t) = Out(depth(t))
                """;

        assertEquals(List.of("depth -> spin"), pathsOf(src, REACHES));
        assertEquals("E2001", assertThrows(CompileException.class, () -> Compiler.compile(src)).code());
    }

    /** The reached helper need not recurse at all. `partial` on a non-recursive helper disclaims the
     * guarantee just the same, and the caller answers for it. */
    @Test
    void reachingANonRecursivePartialHelperIsTheSameViolation() {
        assertEquals(List.of("bumped -> twice"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let twice (n: Int): Int = n * 2
                let bumped (n: Int): Int = twice(n) + 1
                let run (n) = Out(bumped(n))
                """, REACHES));
    }

    /** A recursion that does terminate but that size-change cannot prove is written `partial` too, and
     * the rule does not distinguish it — what is disclaimed is the guarantee, not the termination. */
    @Test
    void aTerminatingRecursionThatGaveUpTheProofIsTreatedTheSame() {
        assertEquals(List.of("anyOver -> firstOver"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let firstOver (n: Int, xs: List<Int>): Option<Int> = {
                    let head = List.get(0, xs)
                    match head with
                        | Some v -> if v > n then head else firstOver(n, List.drop(1, xs))
                        | None -> head
                }
                let anyOver (n: Int, xs: List<Int>): Int =
                    match firstOver(n, xs) with | Some v -> v | None -> 0
                let run (n) = Out(anyOver(n, [1, 2, 3]))
                """, REACHES));
    }

    /** A `partial` helper may reach anything: it promises nothing, so there is nothing to break. */
    @Test
    void aPartialHelperMayReachAPartialOneAndATotalOne() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let double (n: Int): Int = n * 2
                partial let both (n: Int): Int = spin(n) + double(n)
                let run (n) = Out(both(n))
                """));
    }

    /** Reading a `partial` value is reaching it: a `let` with no parameter list is substituted where it
     * is named, so its body runs there. Naming it is not handing a function over — there is no function
     * — which is why this is an edge in the walk and not the value-position rule below. */
    @Test
    void readingAPartialValueIsReachingIt() {
        assertEquals(List.of("offset -> seed"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                partial let seed = spin(1)
                let offset (n: Int): Int = n + seed
                let run (n) = Out(offset(n))
                """, REACHES));
    }

    // --- the path a report names --------------------------------------------

    /** Two hops, so the report has to name what is in between rather than only the two ends. */
    @Test
    void aTransitiveReachIsNamedWhole() {
        assertTrue(pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let inner (n: Int): Int = spin(n)
                let middle (n: Int): Int = inner(n)
                let outer (n: Int): Int = middle(n)
                let run (n) = Out(outer(n))
                """, REACHES).contains("outer -> middle -> inner -> spin"));
    }

    /** The walk visits a node once, so a cycle on the way to the `partial` helper is walked once and
     * does not appear twice in the path. */
    @Test
    void aCycleOnTheWayIsWalkedOnce() {
        assertTrue(pathsOf("""
                module demo
                data T = { c: T?, n: Int }
                data Out = Int
                behavior run : (t: T) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let walk (t: T): Int =
                    match t.c with | Some c -> walk(c) + spin(t.n) | None -> 0
                let entry (t: T): Int = walk(t)
                let run (t) = Out(entry(t))
                """, REACHES).contains("entry -> walk -> spin"));
    }

    /** Two ways down to the same `partial` helper: the shorter one is what `top` is told about. */
    @Test
    void theShortestPathIsTheOneReported() {
        assertTrue(pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let far (n: Int): Int = spin(n)
                let mid (n: Int): Int = far(n)
                let near (n: Int): Int = spin(n)
                let top (n: Int): Int = mid(n) + near(n)
                let run (n) = Out(top(n))
                """, REACHES).contains("top -> near -> spin"));
    }

    /** One report per helper. `top` reaching two `partial` helpers is one thing to fix, and which of
     * the two it names is settled by name order rather than by which the body writes first. */
    @Test
    void aHelperReachingTwoPartialHelpersIsReportedOnce() {
        assertEquals(List.of("top -> spinA"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spinA (n: Int): Int = spinA(n)
                partial let spinB (n: Int): Int = spinB(n)
                let top (n: Int): Int = spinB(n) + spinA(n)
                let run (n) = Out(top(n))
                """, REACHES));
    }

    /** Every unmarked helper that reaches one is reported in the same build: the word goes on each of
     * them, so one report per build would leave the rest to be found one at a time. */
    @Test
    void everyUnmarkedHelperReachingOneIsReportedInTheSameBuild() {
        assertEquals(List.of("one -> spin", "two -> spin"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let one (n: Int): Int = spin(n)
                let two (n: Int): Int = spin(n)
                let run (n) = Out(one(n) + two(n))
                """, REACHES));
    }

    /** A mutually-recursive group holding a `partial` member: the unmarked members each reach it, so
     * each is told, rather than the group being reported once and fixed one member per build. */
    @Test
    void everyUnmarkedMemberOfAMixedGroupIsTold() {
        assertEquals(List.of("isEven -> isOdd", "third -> isEven -> isOdd"), pathsOf("""
                module demo
                data N = Int
                data Out = Int
                behavior run : (n: N) -> Out constructs Out
                let isEven (n: Int): Int = if n == 0 then 1 else isOdd(n - 1)
                partial let isOdd (n: Int): Int = if n == 0 then 0 else isEven(n - 1)
                let third (n: Int): Int = isEven(n)
                let run (n) = Out(third(n.value))
                """, REACHES));
    }

    // --- the behavior boundary ----------------------------------------------

    /** A behavior's implementing `let` is not a helper and publishes no termination guarantee, so it
     * may call a `partial` helper. */
    @Test
    void aBehaviorImplementationMayCallAPartialHelper() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let run (n) = Out(spin(n))
                """));
    }

    /** And a wrapper that says the word. The boundary is where the guarantee stops being published,
     * not where the walk gives up. */
    @Test
    void aBehaviorImplementationMayCallAWrapperThatSaysTheWord() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                partial let wrapped (n: Int): Int = spin(n) + 1
                let run (n) = Out(wrapped(n))
                """));
    }

    /** The boundary does not excuse a helper above the `partial` one: a wrapper without the word is
     * rejected however close to the behavior it sits. */
    @Test
    void aBehaviorBoundaryDoesNotExcuseTheWrapperBelowIt() {
        assertEquals(List.of("wrapped -> spin"), pathsOf("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let wrapped (n: Int): Int = spin(n) + 1
                let run (n) = Out(wrapped(n))
                """, REACHES));
    }

    // --- a `partial` helper as a value --------------------------------------

    /** A function type says nothing about termination, so a `partial` helper handed over leaves the
     * call graph. It may be applied; it may not be named. */
    @Test
    void aPartialHelperMayNotBeNamedWhereAValueGoes() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Item = { n: Int }
                data Out = Int
                behavior run : (i: Item) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let apply1 (f: (Int) -> Int, n: Int): Int = f(n)
                let run (i) = Out(apply1(spin, i.n))
                """));

        assertEquals("E2001", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("`spin`"), e.getMessage());
    }

    /** Not even from inside a `partial` helper. What the rule protects is the function type, which
     * carries no more information there than anywhere else. */
    @Test
    void notEvenFromInsideAPartialHelper() {
        assertEquals("E2001", assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Item = { n: Int }
                data Out = Int
                behavior run : (i: Item) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                let apply1 (f: (Int) -> Int, n: Int): Int = f(n)
                partial let viaValue (n: Int): Int = apply1(spin, n)
                let run (i) = Out(viaValue(i.n))
                """)).code());
    }

    /** A saturated call is the thing the rule allows. */
    @Test
    void aSaturatedCallIsFine() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let spin (n: Int): Int = spin(n)
                partial let called (n: Int): Int = spin(n)
                let run (n) = Out(called(n))
                """));
    }

    /** A call short of the arity is an arity error and not this one — Souther has no partial
     * application for the value rule to have to speak about. */
    @Test
    void tooFewArgumentsIsStillAnArityError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Out = Int
                behavior run : (n: Int) -> Out constructs Out
                partial let pair (a: Int, b: Int): Int = pair(a, b)
                partial let one (n: Int): Int = pair(n)
                let run (n) = Out(one(n))
                """));

        assertTrue(!"E2001".equals(e.code()),
                "expected an arity error, got " + e.code() + ": " + e.getMessage());
    }

    /**
     * The value-position check reads fn bodies, which is where a function value can be written. The
     * other two surfaces reject it too, each for its own reason, and the three together are what makes
     * reading fn bodies enough.
     *
     * <p>An invariant is inlined before it is checked, and a name written where a value goes is
     * expanded there into a block that applies it — so the clause holds a call and the reachability
     * rule answers, whether or not the helper it was handed to is expanded with it.
     */
    @Test
    void anInvariantHandingOverAPartialHelperIsRejectedByWhatTheClauseReaches() {
        assertEquals(List.of("invariant -> spin"), pathsOf("""
                module demo
                data Item = { n: Int }
                partial let spin (n: Int): Int = spin(n)
                let anyPositive (f: (Int) -> Int, items: List<Item>): Bool =
                    List.all(i -> f(i.n) >= 0, items)
                data X = { items: List<Item> } invariant anyPositive(spin, items)
                """, INVARIANT));
    }

    /** And through a higher-order helper that recurses, which the inlining does not expand — the
     * argument is expanded where it is written, so the call is in the clause either way. */
    @Test
    void andThroughARecursiveHigherOrderHelper() {
        assertEquals(List.of("invariant -> spin"), pathsOf("""
                module demo
                partial let spin (n: Int): Int = spin(n)
                data Tree = { child: Tree?, n: Int }
                let walk (f: (Int) -> Int, t: Tree): Int =
                    match t.child with | Some c -> walk(f, c) | None -> f(t.n)
                data X = { root: Tree } invariant walk(spin, root) >= 0
                """, INVARIANT));
    }

    /** An example row cannot name one, because a behavior cannot take a function at all: a function has
     * no external representation, so it does not cross the boundary. That is what leaves fn bodies as
     * the only surface a function value is written on. */
    @Test
    void anExampleRowHasNoFunctionToHandOver() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Out = Int
                partial let spin (n: Int): Int = spin(n)
                let apply1 (f: (Int) -> Int, n: Int): Int = f(n)
                behavior run : (f: (Int) -> Int) -> Out constructs Out
                let run (f) = Out(apply1(f, 1))
                example run
                    | "hands over a partial helper" : (spin) -> Out(1)
                """));

        assertTrue(e.getMessage().contains("has no external representation"), e.getMessage());
    }

    /** A total helper handed over is untouched: the rule is about the word, not about names in value
     * position. */
    @Test
    void aTotalHelperMayStillBeHandedOver() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Item = { n: Int }
                data Out = Int
                behavior run : (i: Item) -> Out constructs Out
                let double (n: Int): Int = n * 2
                let apply1 (f: (Int) -> Int, n: Int): Int = f(n)
                let run (i) = Out(apply1(double, i.n))
                """));
    }

    // --- across a module boundary -------------------------------------------

    /** The word travels with the declaration, so an importing module reads it off the helper it names
     * and answers without walking what is behind it. */
    @Test
    void anImportedPartialHelperIsRejectedByTheWordOnItsDeclaration() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileModules(List.of("""
                module maths exposing ( spin )

                partial let spin (n: Int) : Int = spin(n)
                """, """
                module order exposing ( Out, bill )

                import maths ( spin )

                data Out = { v: Int }

                let wrapped (n: Int): Int = spin(n)

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = wrapped(n) }
                """)));

        assertEquals("E2001", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("wrapped -> maths.spin"), e.getMessage());
    }

    /** An imported helper written without the word carries the guarantee for its whole closure — the
     * exporting module enforced the same rule — so the reader stops at the declaration. */
    @Test
    void anUnmarkedImportedHelperIsTakenAtItsWord() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module maths exposing ( doubled )

                let doubled (n: Int) : Int = n * 2
                """, """
                module order exposing ( Out, bill )

                import maths ( doubled )

                data Out = { v: Int }

                let wrapped (n: Int): Int = doubled(n)

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = wrapped(n) }
                """)));
    }

    /**
     * An invariant calling an imported `partial` helper with nothing of this module's in between. The
     * marker is asked of the declaration, so it does not matter whether a helper here happens to name
     * it too — the clause names what it names.
     */
    @Test
    void anInvariantMayNotCallAnImportedPartialHelperDirectly() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileModules(List.of("""
                module maths exposing ( spin )

                partial let spin (n: Int) : Int = spin(n)
                """, """
                module order

                import maths ( spin )

                data X = { n: Int }
                    invariant spin(n) >= 0
                """)));

        assertTrue(e.getMessage().contains("invariant -> maths.spin"), e.getMessage());
    }

    /** An imported value read bare. The key a name is looked up by comes from what it denotes, not from
     * how it was spelled, so the edge is there whether or not the import was written out qualified. */
    @Test
    void readingABareImportedPartialValueIsReachingIt() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileModules(List.of("""
                module maths exposing ( seed )

                partial let spin (n: Int) : Int = spin(n)
                partial let seed = spin(1)
                """, """
                module order

                import maths ( seed )

                data Out = Int
                behavior run : (n: Int) -> Out constructs Out

                let offset (n: Int): Int = n + seed
                let run (n) = Out(offset(n))
                """)));

        assertEquals("E2001", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("offset -> maths.seed"), e.getMessage());
    }

    /** That lookup rule, on its own. A helper of another module is filed under its qualified name and
     * one of this module's under its bare name, and which of the two a name is depends on what it
     * denotes. Keying by the spelling would answer differently before and after the pass that writes an
     * imported name out qualified, and a table answers a key it has not got with silence. */
    @Test
    void aHelperIsKeyedByWhatItDenotesRatherThanByHowItIsWritten() {
        ValueName.Helper foreign = new ValueName.Helper("maths", "spin");
        ValueName.Helper own = new ValueName.Helper("order", "spin");

        assertEquals("maths.spin", HelperInliner.keyIn("order", foreign));
        assertEquals("spin", HelperInliner.keyIn("order", own));
    }

    /** An imported `partial` helper may not be handed over either. */
    @Test
    void anImportedPartialHelperMayNotBeNamedWhereAValueGoes() {
        assertEquals("E2001",
                assertThrows(CompileException.class, () -> Compiler.compileModules(List.of("""
                        module maths exposing ( spin )

                        partial let spin (n: Int) : Int = spin(n)
                        """, """
                        module order exposing ( Out, bill )

                        import maths ( spin )

                        data Out = { v: Int }

                        let apply1 (f: (Int) -> Int, n: Int): Int = f(n)

                        behavior bill : (n: Int) -> Out constructs Out
                        let bill (n) = Out { v = apply1(spin, n) }
                        """))).code());
    }

    // --- an invariant -------------------------------------------------------

    /**
     * An invariant runs on every construction and must terminate. A total recursive helper is left
     * standing by the inlining, so what the clause names is not all it runs, and the clause is decided
     * by what it reaches. Two declarations are wrong here and both are said: `depth` claims a guarantee
     * it does not carry, and the clause reaches something that carries none.
     */
    @Test
    void anInvariantMayNotReachAPartialHelperBehindARecursiveOne() {
        String src = """
                module demo
                partial let spin (n: Int): Int = spin(n)
                data Tree = { child: Tree?, n: Int }
                let depth (t: Tree): Int =
                    match t.child with
                        | Some c -> depth(c) + 1
                        | None -> spin(t.n)
                data X = { root: Tree } invariant depth(root) >= 0
                """;

        assertEquals(List.of("invariant -> depth -> spin"), pathsOf(src, INVARIANT));
        assertEquals(List.of("depth -> spin"), pathsOf(src, REACHES));
    }

    /** An invariant reaching one directly says the same thing, with the shorter path. */
    @Test
    void anInvariantMayNotCallAPartialHelperDirectly() {
        assertEquals(List.of("invariant -> spin"), pathsOf("""
                module demo
                partial let spin (n: Int): Int = spin(n)
                data X = { n: Int } invariant spin(n) >= 0
                """, INVARIANT));
    }

    /** A total recursive helper is admissible in an invariant — the compiler has proven it
     * terminates. */
    @Test
    void anInvariantMayReachATotalRecursiveHelper() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Tree = { child: Tree?, n: Int }
                let depth (t: Tree): Int =
                    match t.child with
                        | Some c -> depth(c) + 1
                        | None -> 1
                data X = { root: Tree } invariant depth(root) >= 0
                """));
    }
}
