package souther.compiler.query;

import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

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
