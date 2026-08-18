package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which declarations a body is checked against, read as an answer of its own.
 *
 * <p>{@link Bodies.BehaviorsReached} and {@link Bodies.ContractsForBody} exist so that this is something
 * to look at rather than something to work out from the shape of a {@code compute}, and this is what
 * looks at it. {@code IncrementalCompilationTest} holds the other end — that depending on less is
 * what an edit costs — and neither says what the other says: a frontier can be narrow and wrong, and
 * an edit can be absorbed because the answer was never reached at all.
 */
class WhatABodyIsCheckedAgainstIsWhatItReachesTest {

    private static Compilation compiled(String source) {
        Compilation c = Compilation.ofDocuments(Map.of("orders.sou", source), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles: " + c.db().allReports());
        return c;
    }

    private static Set<ValueName.Behavior> reachedBy(Compilation c, String behavior) {
        return c.db().ask(new Bodies.BehaviorsReached("shop.orders", behavior)).value();
    }

    private static Set<ValueName.Behavior> statedTo(Compilation c, String behavior) {
        return c.db().ask(new Bodies.ContractsForBody("shop.orders", behavior)).value().keySet();
    }

    private static ValueName.Behavior of(String name) {
        return new ValueName.Behavior("shop.orders", name);
    }

    private static final String PREAMBLE = """
            module shop.orders exposing ( Amount )

            data Amount = Int
                invariant value >= 0

            """;

    /** Two behaviors that state a relation and one that states none, with a third calling one of
     *  the three. */
    private static final String CALLING = PREAMBLE + """
            behavior called : (n: Amount) -> Amount
                constructs Amount
                ensures value.value >= n.value
            let called (n) = Amount(n.value * 2)

            behavior uncalled : (n: Amount) -> Amount
                constructs Amount
                ensures value.value > n.value - 1
            let uncalled (n) = Amount(n.value * 3)

            behavior silent : (n: Amount) -> Amount
                constructs Amount
            let silent (n) = Amount(n.value * 4)

            behavior caller : (n: Amount) -> Amount
            let caller (n) = called(n)
            """;

    @Test
    void aBodyReachesTheBehaviorsItNamesAndNoOthers() {
        Compilation c = compiled(CALLING);

        assertEquals(Set.of(of("called")), reachedBy(c, "caller"),
                "`caller` calls `called`; the module declaring three more is not `caller`'s business");
        assertEquals(Set.of(), reachedBy(c, "called"),
                "and `called` calls nothing");
    }

    /**
     * A behavior that states nothing is reached and contributes no contract. Absence is the answer
     * to "is there anything to assume", so the frontier and the table it is read into are not the
     * same size and neither stands in for the other.
     */
    @Test
    void aBehaviorThatStatesNothingIsReachedAndStatesNothing() {
        Compilation c = compiled(CALLING.replace("let caller (n) = called(n)",
                "let caller (n) = silent(called(n))"));

        assertEquals(Set.of(of("silent"), of("called")), reachedBy(c, "caller"),
                "both are called");
        assertEquals(Set.of(of("called")), statedTo(c, "caller"),
                "and only one of them said anything about its answer");
    }

    /**
     * A behavior named where a value goes is reached whether or not anything applies it. Known and
     * conservative: what a name becomes is the function it names, and which later step applies it is
     * not something a walk of the body can see, so the frontier is what a contract lookup may ask
     * about rather than what it will.
     */
    @Test
    void aBehaviorNamedAsAValueIsReachedWhetherOrNotItIsApplied() {
        Compilation c = compiled(CALLING.replace("let caller (n) = called(n)",
                "let caller (n) = {\n    let f = called\n    f(n)\n}"));

        assertEquals(Set.of(of("called")), reachedBy(c, "caller"),
                "`called` is named here, and naming it is what brings its contract along");
    }

    /**
     * A behavior can be reached from inside a helper after all — not by being called there, which
     * E1818 refuses, but by being handed to one as a value. The name is the caller's own parameter
     * wherever it is written, so this is reached whether the helper is spliced or not; it is here
     * because a frontier that only looked at applications would miss it.
     */
    @Test
    void anInjectedBehaviorHandedToAHelperIsReachedByTheBodyTheHelperIsExpandedInto() {
        Compilation c = compiled(PREAMBLE + """
                behavior findIt : (n: Amount) -> Amount
                    ensures value.value >= n.value

                let applied (f: (Amount) -> Amount, n) = f(n)

                behavior use : (n: Amount) -> Amount
                    depends on findIt
                let use (n, findIt) = applied(findIt, n)
                """);

        assertEquals(Set.of(of("findIt")), reachedBy(c, "use"),
                "`findIt` is applied inside what `applied` becomes here");
    }

    /**
     * An injected behavior is reached through the parameter {@code depends on} gave the body, so the
     * name at the call denotes that parameter. What it stands for is on the declaration, and a
     * frontier read off the body alone has no way to know.
     */
    @Test
    void aBehaviorReachedByBeingInjectedIsReached() {
        Compilation c = compiled(PREAMBLE + """
                behavior findIt : (n: Amount) -> Amount
                    ensures value.value >= n.value

                behavior use : (n: Amount) -> Amount
                    depends on findIt
                let use (n, findIt) = findIt(n)
                """);

        assertEquals(Set.of(of("findIt")), reachedBy(c, "use"),
                "`findIt` arrives injected and is called all the same");
        assertEquals(Set.of(of("findIt")), statedTo(c, "use"),
                "and what it states is what `use` was checked against");
    }
}
