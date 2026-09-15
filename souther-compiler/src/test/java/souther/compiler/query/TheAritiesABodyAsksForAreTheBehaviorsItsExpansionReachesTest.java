package souther.compiler.query;

import souther.compiler.ast.DefinitionName;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many inputs a behavior takes is asked for every behavior a body's expansion reaches, and for
 * no other.
 *
 * <p>A name written where a value goes becomes the function it names, and what turns it into one is
 * its arity. The names that reach that point are not the ones the author wrote in this body: a
 * helper is expanded where it is called and a value is substituted where it is named, so a behavior
 * written in either arrives in this tree and is asked about here.
 *
 * <p>Both halves are one claim and are checked together. Asked of the module's index, every body
 * gets every behavior and the first half holds for a reason that says nothing; asked of the body's
 * own text, the second holds and a behavior handed over through a value is left standing as a name.
 */
class TheAritiesABodyAsksForAreTheBehaviorsItsExpansionReachesTest {

    /**
     * A behavior handed over through a value, and one nothing here reaches.
     *
     * <p>{@code held} is a value, so it is substituted where it is named rather than called, and
     * {@code twice} arrives in {@code viaValue}'s tree by being written in a definition somewhere
     * else. {@code thrice} is declared beside them and named by nothing.
     */
    private static final String MODULE = """
            module shop.values exposing ( twice, thrice, viaValue )

            behavior twice : (n: Int) -> Int
            let twice (n) = n * 2

            behavior thrice : (n: Int) -> Int
            let thrice (n) = n * 3

            let held = twice
            let through (f: (Int) -> Int, n: Int) = f(n)

            behavior viaValue : (n: Int) -> Int
            let viaValue (n) = through(held, n)
            """;

    private static Map<ValueName.Behavior, Integer> asksFor(String fn, InliningPolicy policy) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("values.sou", MODULE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        return c.db().ask(new Bodies.BehaviorAritiesForBody("shop.values", fn, policy)).value();
    }

    private static final ValueName.Behavior TWICE =
            new ValueName.Behavior("shop.values", "twice");
    private static final ValueName.Behavior THRICE =
            new ValueName.Behavior("shop.values", "thrice");

    /**
     * A helper reaching a behavior through a value, which is what the language refuses.
     *
     * <p>Written into a helper rather than named in it: {@code carried} is a value and is
     * substituted where it is written, so what stands in {@code spin} after expansion is the
     * behavior. E1818 is asked of the tree the expansion made and not of the one the author wrote,
     * so this is refused as a helper calling a behavior.
     */
    private static final String A_HELPER_REACHING_A_BEHAVIOR = """
            module shop.values exposing ( twice, thrice, caller )

            behavior twice : (n: Int) -> Int
            let twice (n) = n * 2

            behavior thrice : (n: Int) -> Int
            let thrice (n) = n * 3

            let carried = thrice
            let through (f: (Int) -> Int, n: Int) = f(n)

            partial let spin (n: Int): Int =
                if n <= 0 then through(carried, 0) else spin(n - 1)

            behavior caller : (n: Int) -> Int
            let caller (n) = spin(n)
            """;

    /**
     * A recursion calling a recursion, and a helper reached only through the first.
     *
     * <p>{@code caller}'s expansion holds one call that is still a call when it is done: the one to
     * {@code spin}. {@code spin} is lowered to a method of its own, and what stands in that method
     * is the call to {@code deeper} and whatever {@code deep} was written into it.
     */
    private static final String THROUGH_A_RECURSION = """
            module shop.values exposing ( caller )

            let deep (n: Int) = n + 1

            partial let deeper (n: Int): Int = if n <= 0 then deep(0) else deeper(n - 1)

            partial let spin (n: Int): Int = if n <= 0 then deeper(0) else spin(n - 1)

            behavior caller : (n: Int) -> Int
            let caller (n) = spin(n)
            """;

    /** The definitions one of the two relations answers with, under the names they are held at. */
    private static Set<String> relation(Key<Set<ReachName.Declaration>> asked) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("values.sou", THROUGH_A_RECURSION);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        Set<String> out = new TreeSet<>();
        c.db().ask(asked).value().forEach(each -> out.add(DefinitionName.of(each).text()));
        return out;
    }

    /**
     * What is written into a body stops where a recursion is left standing.
     *
     * <p>Where the two relations part, and the reason there are two. A recursion is lowered to a
     * method of its own, so what its body reaches is written into that method — followed through
     * here, every name those definitions hold would be a name this body is answered about, and an
     * edit to one of them would be an edit to this body.
     */
    @Test
    void whatIsWrittenIntoABodyStopsAtARecursion() {
        assertEquals(Set.of(), relation(new Bodies.WrittenIntoBody("shop.values", "caller",
                        InliningPolicy.FULL)),
                "a definition reached only through a recursion was read as written into the body"
                        + " that calls the recursion");
    }

    /**
     * And the recursions standing in it are the ones its own tree calls.
     *
     * <p>The other relation, and the control that says the one above is a boundary rather than a
     * walk that found nothing. It stops at a recursion too, and answers with it: what
     * {@code caller} is checked against is the signature of the call its tree holds. Not the closure
     * through it — what {@code deeper} constructs is already inside what {@code spin} constructs,
     * because that index answers transitively, so an entry for it here would be an entry for a
     * recursion this tree never names.
     */
    @Test
    void andTheRecursionsStandingInABodyAreTheOnesItsOwnTreeCalls() {
        assertEquals(Set.of("spin"), relation(new Bodies.StandingRecursionsOfBody("shop.values",
                        "caller", InliningPolicy.FULL)),
                "a body was handed a recursion its own tree does not call, so an edit to that one"
                        + " is an edit to this body");
    }

    /**
     * And the recursion it does call is handed the one it calls in turn, and itself.
     *
     * <p>Its own call among them because that is what is standing there: a recursion's method holds
     * the call it recurses by, and typing that call wants this recursion's own signature.
     */
    @Test
    void andTheRecursionItCallsIsHandedTheOneItCallsInTurn() {
        assertEquals(Set.of("deeper", "spin"),
                relation(new Bodies.StandingRecursionsOfBody("shop.values", "spin",
                        InliningPolicy.FULL)),
                "the method a recursion is lowered to was not handed the recursions standing in"
                        + " it");
    }

    /** What the compiler says about {@code source}, by code. */
    private static List<String> saidAbout(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("values.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c.db().allReports().stream()
                .map(each -> each.report().diagnostic().code()).toList();
    }

    /**
     * A helper may not reach a behavior at all, however the name gets there.
     *
     * <p>Held as a check rather than said in a comment, because what rests on it is a boundary that
     * is otherwise invisible. What is written into a body stops where a recursion is: the recursion
     * is left standing and lowered to a method of its own, so a behavior named in it is named there
     * and not here. A walk that went on through it would hand this body the names of everything its
     * recursions reach — and that this is a difference nobody can write a program to see is exactly
     * what this holds. The day a helper may name a behavior, the walk that goes through a recursion
     * starts answering about names that are not in this tree, and the failure arrives here.
     */
    @Test
    void aHelperMayNotReachABehaviorHoweverItIsCarriedIn() {
        assertEquals(List.of("E1818"), saidAbout(A_HELPER_REACHING_A_BEHAVIOR),
                "a helper reached a behavior through a value, so what a recursion's body names is"
                        + " no longer something no program can put there");
    }

    /**
     * A behavior a value carries into this body is one this body asks about.
     *
     * <p>Nothing in {@code viaValue} writes {@code twice}. What writes it is the value it hands to a
     * helper, and the expansion puts that value's body where the name stood — so by the time an
     * arity is wanted, the name is in this tree.
     */
    @Test
    void aBehaviorAValueCarriesInIsAskedAbout() {
        assertEquals(Map.of(TWICE, 1), asksFor("viaValue", InliningPolicy.FULL),
                "a behavior handed over through a value was not asked about, so the name it is"
                        + " written as is left standing where it has to become the behavior");
    }

    /** And so under the representation the discharge analysis reads, which expands other helpers
     *  into the same body. */
    @Test
    void andUnderTheRepresentationTheRulesAreReadIn() {
        assertEquals(Map.of(TWICE, 1), asksFor("viaValue", InliningPolicy.DISCHARGE));
    }

    /**
     * And a behavior nothing this body reaches names is not asked about.
     *
     * <p>Which is what says the answer is this body's and not its module's. Asked of the module's
     * index, {@code thrice} would be here — and so would every behavior declared beside it after
     * this was written, which is the whole of what the cut is for.
     */
    @Test
    void aBehaviorNothingThisBodyReachesIsNotAskedAbout() {
        assertEquals(Map.of(), asksFor("twice", InliningPolicy.FULL),
                "a body that names no behavior was given one");
        assertTrue(!asksFor("viaValue", InliningPolicy.FULL).containsKey(THRICE),
                "a behavior nothing this body reaches was asked about, so this is the module's"
                        + " answer under another name");
    }
}
