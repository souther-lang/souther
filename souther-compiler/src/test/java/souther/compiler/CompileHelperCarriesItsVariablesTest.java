package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of a helper's parameters hold one thing and which hold two, where the body named the
 * containers and not what they hold.
 *
 * <p>The relationship is the body's to make. A library signature is read once and shared by every
 * call site, so {@code List.length} and {@code Set.size} both hand back the {@code 'a} the library
 * wrote; two parameters that took their answer from those two calls are not thereby one. What links
 * two parameters is a position that reads them together — an operator that takes one type on both
 * sides, an argument beside another argument of one signature.
 */
class CompileHelperCarriesItsVariablesTest {

    /** Whether {@code name} settled its element to Int: it takes a List of Ints and not of Strings. */
    private static boolean walksInts(String name, String helper) {
        return compiles(helper + "\nlet takesInts (k: Int) = " + name + "([ 1, 2 ]) + k")
                && !compiles(helper + "\nlet takesText (k: Int) = " + name + "([ \"a\" ]) + k");
    }

    /** Whether a module holding {@code defs} and a behavior that uses none of them compiles. */
    private static boolean compiles(String defs) {
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X
                %s
                let f (x) = x
                """.formatted(defs);
        try {
            return Compiler.compile(src).containsKey("demo.F");
        } catch (CompileException _) {
            return false;
        }
    }

    // --- the body does not link them ---

    @Test
    void twoParametersTheBodyDoesNotLinkHoldDifferentThings() {
        // Each is handed to a signature that names the container and not the element, and `+` runs
        // between two Ints rather than between the elements. Nothing here says the two lists hold
        // one thing, and they are both read at once to prove it.
        assertTrue(compiles("""
                let sizes (xs, ys) = List.length(xs) + List.length(ys)
                let use (n: Int) = sizes([ 1, 2 ], [ "a" ]) + n"""),
                "one List of Ints and one of Strings fit `sizes` at the same call");
    }

    @Test
    void twoLibrarySignaturesSpellingOneVariableDoNotLinkTwoParameters() {
        // `List.length` and `Set.size` both wrote `'a`. The spelling is the library's, not this
        // body's, so it links nothing.
        assertTrue(compiles("""
                let mixed (xs, s) = List.length(xs) + Set.size(s)
                let use (n: Int, s: Set<String>) = mixed([ 1, 2 ], s) + n"""),
                "the List holds Ints and the Set holds Strings");
    }

    // --- the body links them ---

    @Test
    void anOperatorThatTakesOneTypeLinksTwoParameters() {
        // `==` reads both sides as one type, so what the two lists hold is one thing.
        assertTrue(compiles("""
                let sameHead (xs, ys) = List.get(0, xs) == List.get(0, ys)
                let use (b: Bool) = sameHead([ 1 ], [ 2 ]) && b"""),
                "two Lists of Ints fit");
        assertFalse(compiles("""
                let sameHead (xs, ys) = List.get(0, xs) == List.get(0, ys)
                let use (b: Bool) = sameHead([ 1 ], [ "a" ]) && b"""),
                "a List of Ints and a List of Strings do not");
    }

    @Test
    void oneSignatureWritingOneVariableTwiceLinksTwoParameters() {
        // `Set.union` declares both of its sets as `Set<'a>` — one variable, written twice.
        assertTrue(compiles("""
                let both (a, b) = Set.union(a, b)
                let use (p: Set<Int>, q: Set<Int>) = Set.size(both(p, q))"""),
                "two Sets of Ints fit");
        assertFalse(compiles("""
                let both (a, b) = Set.union(a, b)
                let use (p: Set<Int>, q: Set<String>) = Set.size(both(p, q))"""),
                "a Set of Ints and a Set of Strings do not");
    }

    @Test
    void oneParameterReadTwiceHoldsOneThing() {
        // Both arguments of `List.zip` are the same parameter, so whatever minting happens at that
        // call has to give the two positions one variable rather than two.
        assertTrue(compiles("""
                let paired (xs) = List.zip(xs, xs)
                let use (n: Int) = List.length(paired([ 1, 2 ])) + n"""),
                "`xs` holds one thing, read at two positions of one call");
    }

    @Test
    void aMapIsLinkedOnlyWhereTheBodyReadsIt() {
        // `Map.keys` answers the keys, and `==` reads two key lists as one type. What the two maps
        // hold as values is not read, so it is not linked.
        assertTrue(compiles("""
                let sameKeys (m1, m2) = Map.keys(m1) == Map.keys(m2)
                let use (a: Map<String, Int>, b: Map<String, Bool>) = sameKeys(a, b)"""),
                "one key type, two value types");
        assertFalse(compiles("""
                let sameKeys (m1, m2) = Map.keys(m1) == Map.keys(m2)
                let use (a: Map<String, Int>, b: Map<Int, Int>) = sameKeys(a, b)"""),
                "two key types do not fit");
    }

    /**
     * A relation a signature makes across its own parameters survives the expansion of the call.
     * {@code List.member} writes one variable for its element and for its list, so {@code y} is the
     * element of {@code xs} — and it says so whether the callee is expanded or stands, which is what
     * makes the answer the language's and not the library's implementation choice.
     */
    @Test
    void aRelationASignatureMakesSurvivesTheExpansionOfTheCall() {
        assertTrue(compiles("""
                let has (xs, y) = List.member(y, xs)
                let use (b: Bool) = has([ 1 ], 2) && b"""),
                "`y` is the element of `xs`, and two Ints fit");
        assertFalse(compiles("""
                let has (xs, y) = List.member(y, xs)
                let use (b: Bool) = has([ 1 ], "a") && b"""),
                "a List of Ints and a String do not");
    }

    /** And it does not depend on which of the two the helper declares first. */
    @Test
    void whichParameterIsWrittenFirstDecidesNothing() {
        assertTrue(compiles("""
                let has (y, xs) = List.member(y, xs)
                let use (b: Bool) = has(2, [ 1 ]) && b"""),
                "the same relation, read the other way round");
        assertFalse(compiles("""
                let has (y, xs) = List.member(y, xs)
                let use (b: Bool) = has("a", [ 1 ]) && b"""),
                "and refused the same way");
    }

    /**
     * A bare variable says what this parameter holds only where another <em>parameter</em> is known
     * to hold it. A binding the body made out of the parameter carries the same variable, and taking
     * that for evidence would settle a parameter by what was built from it.
     */
    @Test
    void whatWasBuiltFromTheParameterIsNotEvidenceAboutIt() {
        assertFalse(compiles("""
                let f (v) = {
                    let xs = [ v ]
                    List.member(v, xs)
                }
                let use (b: Bool) = f(1) && b"""),
                "`xs` is made from `v`, so it says nothing about `v` that `v` did not say first");
    }

    @Test
    void twoApplicationsOfOneHelperDecideSeparately() {
        // Nothing here ties the two calls together, so one deciding Int does not make the other one.
        assertTrue(compiles("""
                let use (b: Bool) = List.member(1, [ 1 ]) && List.member("a", [ "a" ]) && b"""),
                "two applications of `List.member`, at two element types");
    }

    @Test
    void twoApplicationsTiedByOneParameterHoldOneThing() {
        // The caller's own `y` is what ties them, and it is one value.
        assertTrue(compiles("""
                let bothContain (xs, ys, y) = List.member(y, xs) && List.member(y, ys)
                let use (b: Bool) = bothContain([ 1 ], [ 2 ], 3) && b"""),
                "three parameters, one element type");
        assertFalse(compiles("""
                let bothContain (xs, ys, y) = List.member(y, xs) && List.member(y, ys)
                let use (b: Bool) = bothContain([ 1 ], [ "a" ], 3) && b"""),
                "and the two lists hold the same thing");
    }

    @Test
    void aSignatureVariableStandingInThreePositionsHoldsOneThing() {
        // `Map.insert (key: 'k, value: 'a, m: Map<'k, 'a>)` writes `'k` twice and `'a` twice, so
        // three of this helper's parameters are tied by one call.
        assertTrue(compiles("""
                let put (k, v, m) = Map.insert(k, v, m)
                let use (n: Int) = Map.size(put("a", 1, Map.empty)) + n"""),
                "the key, the value and what the map holds are one call's");
        assertFalse(compiles("""
                let put (k, v, m) = Map.insert(k, v, m)
                let use (m: Map<String, Bool>, n: Int) = Map.size(put("a", 1, m)) + n"""),
                "a map of Bools does not take an Int value");
    }

    @Test
    void anExpansionInsideAnExpansionDecidesOnItsOwn() {
        // `outer` expands into the body, and the `List.member` inside it expands again. The two are
        // two applications, and the inner one's element is the outer one's — through the body, not
        // through a name two signatures happen to share.
        assertTrue(compiles("""
                let outer (xs, y) = List.member(y, xs)
                let go (zs, z) = outer(zs, z)
                let use (b: Bool) = go([ 1 ], 2) && b"""),
                "the relation reaches through two expansions");
        assertFalse(compiles("""
                let outer (xs, y) = List.member(y, xs)
                let go (zs, z) = outer(zs, z)
                let use (b: Bool) = go([ 1 ], "a") && b"""),
                "and refuses through them");
    }

    /**
     * A signature variable standing twice is one identity whether the callee is an intrinsic or is
     * written in Souther. {@code Set.union} is an intrinsic and {@code List.member} is self-hosted;
     * which side of that line a function is on is not something an author can read, so it decides
     * nothing here.
     */
    @Test
    void aRepeatedSignatureVariableIsOneIdentityWhicheverWayTheCalleeIsWritten() {
        assertTrue(compiles("""
                let viaIntrinsic (a, b) = Set.union(a, b)
                let viaSouther (xs, y) = List.member(y, xs)
                let use (p: Set<Int>, q: Set<Int>) = Set.size(viaIntrinsic(p, q))
                    + (if viaSouther([ 1 ], 2) then 1 else 0)"""),
                "both hold their repeated variable to one type");
        assertFalse(compiles("""
                let viaIntrinsic (a, b) = Set.union(a, b)
                let use (p: Set<Int>, q: Set<String>) = Set.size(viaIntrinsic(p, q))"""),
                "the intrinsic refuses two element types");
        assertFalse(compiles("""
                let viaSouther (xs, y) = List.member(y, xs)
                let use (b: Bool) = viaSouther([ 1 ], "a") && b"""),
                "and so does the self-hosted one");
    }

    /**
     * What a signature says between its arguments and its result reaches the caller too.
     * {@code Map.upsert} declares {@code Map<'k, 'a>} for its map and for what it answers, so what
     * the result holds is what the argument held.
     *
     * <p>Two ways at once here, and either would do: the body builds its result out of the arguments,
     * and the declaration says the same thing. A helper whose body says nothing about what it answers
     * has only the declaration, which is what {@code CompileTypeVariableTest} holds.
     */
    @Test
    void whatASignatureSaysBetweenItsArgumentsAndItsResultReachesTheCaller() throws Exception {
        Map<?, ?> out = run("""
                module demo
                data In = { counts: Map<String, Int> }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let bump (k, m) = Map.upsert(k, 0, (v) -> v + 1, m)
                let go (i) = Out { n = List.sum(Map.values(bump("a", i.counts))) }
                """, Map.of("counts", Map.of("a", 1L, "b", 5L)));
        assertEquals(7L, out.get("n"), "the result holds Ints because the argument did");
        assertFalse(compiles("""
                let bump (k, m) = Map.upsert(k, 0, (v) -> v + 1, m)
                let use (t: Map<String, Bool>, n: Int) = Map.size(bump("a", t)) + n"""),
                "a map of Bools does not take the Int the call decided");
    }

    // --- what a position states reaches the arms, and what an arm states wins ---

    @Test
    void anArmThatStatesTheWholeTypeWinsOverAPositionThatStatesTheContainer() {
        assertTrue(walksInts("n", "let n (xs) = List.length(if true then xs else [ 1, 2, 3 ])"),
                "the other arm names the element, so `xs` walks Ints and not anything");
    }

    @Test
    void aPositionStatingTheContainerReachesAnArmWhereNoArmStatesMore() {
        assertTrue(compiles("""
                let n (bb: Bool, xs) = List.length(if bb then xs else [])
                let use (k: Int) = n(true, [ 1 ]) + n(false, [ "a" ]) + k"""),
                "nothing names the element, so it stays open and each call decides it");
    }

    @Test
    void twoArmsHoldingTwoParametersHoldOneThing() {
        // The `if` reads them together, so they are one element type — and the position's freshly
        // minted variable must not win over the one the other arm already carries.
        assertTrue(compiles("""
                let n (bb: Bool, xs, ys) = List.length(if bb then xs else ys)
                let use (k: Int) = n(true, [ 1 ], [ 2 ]) + k"""),
                "two lists of Ints fit");
        assertFalse(compiles("""
                let n (bb: Bool, xs, ys) = List.length(if bb then xs else ys)
                let use (k: Int) = n(true, [ 1 ], [ "a" ]) + k"""),
                "a list of Ints and a list of Strings do not");
    }

    // --- one helper, monomorphized per expansion ---

    /** Runs {@code demo.go} over {@code in}, so what the expansions decided is what actually ran. */
    private static Map<?, ?> run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileHelperCarriesItsVariablesTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    @Test
    void oneHelperIsUsedAtTwoElementTypesInOneModule() throws Exception {
        // The visible change: `count` walks a List of Ints and a List of Strings in one body, each
        // expansion resolving the element to what that call passed.
        Map<?, ?> out = run("""
                module demo
                data In = { ns: List<Int> }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let count (xs) = List.length(xs)
                let go (i) = Out { n = count(i.ns) + count([ "a", "b", "c" ]) }
                """, Map.of("ns", List.of(1L, 2L)));
        assertEquals(5L, out.get("n"));
    }

    @Test
    void anEmptyCollectionIsCountedTwiceWithoutTheTwoExpansionsMeeting() throws Exception {
        // Neither call says what the list holds and the result does not carry it either, so nothing
        // downstream can tie the two expansions together — which is what a shared variable would do.
        Map<?, ?> out = run("""
                module demo
                data In = { ns: List<Int> }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let count (xs) = List.length(xs)
                let go (i) = Out { n = count([]) + count([]) + List.length(i.ns) }
                """, Map.of("ns", List.of(1L)));
        assertEquals(1L, out.get("n"));
    }

    @Test
    void aCallThatDoesNotFitIsReportedWhereTheHelperReadsIt() {
        // `count` takes a List, so an Int is refused. The report comes from inside the expansion,
        // as it does for `let double (x) = x * 2` applied to a String — the helper is the body, and
        // the body is what refuses it.
        assertFalse(compiles("""
                let count (xs) = List.length(xs)
                let use (n: Int) = count(n) + n"""),
                "an Int is not a List of anything");
    }

    @Test
    void aVariableCarryingHelperIsHandedToACombinatorByName() throws Exception {
        // Named rather than called, it is still expanded where the combinator applies it, so the
        // element is resolved there. What it is not is a value of a polymorphic type: what travels
        // is the declaration, and each use instantiates it afresh.
        Map<?, ?> out = run("""
                module demo
                data In = { ns: List<Int> }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let count (xs) = List.length(xs)
                let go (i) = Out { n = List.sum(List.map(count, [ i.ns, [ 7 ] ])) }
                """, Map.of("ns", List.of(1L, 2L)));
        assertEquals(3L, out.get("n"));
    }

    @Test
    void aVariableCarryingHelperIsSettledOnceAtEachPlaceItIsNeeded() {
        // An invariant is expanded well before the module is lowered, so the settling runs twice over
        // the same helper. It has to answer the same both times: a second run that minted another set
        // of variables would leave the invariant and the body reading two different declarations.
        String src = """
                module demo
                data Rows = List<Int>
                    invariant count(value) >= 1
                data Out = { n: Int }
                behavior go : (r: Rows) -> Out constructs Out
                let count (xs) = List.length(xs)
                let go (r) = Out { n = count(r.value) }
                """;
        Map<String, byte[]> first = Compiler.compile(src);
        Map<String, byte[]> second = Compiler.compile(src);
        assertEquals(first.keySet(), second.keySet());
        for (String name : first.keySet()) {
            assertArrayEquals(first.get(name), second.get(name), name + " differs between two reads");
        }
    }

    @Test
    void aRecursiveHelperStillWritesItsTypes() {
        // It is lowered to a method rather than expanded, so it has no expansion to monomorphize.
        assertFalse(compiles("let size (xs) = if List.isEmpty(xs) then 0 else 1 + size(List.drop(1, xs))"),
                "a recursive helper writes its parameter and return types");
    }
}
