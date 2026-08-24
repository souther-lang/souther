package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row through one {@code List.filter} establishes nothing about the {@code List.filter} beside it.
 *
 * <p>The two are one fork of one declaration inlined twice, and what each decides is the closure it
 * was handed: they part different values and are separately owed. Counted under the construct that
 * wrote the fork alone — which stands in {@code souther.list} — both calls came out under one key,
 * and a row that reached either marked both.
 *
 * <p>Which is right for the case that key was made for, and only that one. A non-recursive helper is
 * spliced into each body that calls it and the copies are one arm the author wrote, because the
 * condition is the helper's own. A combinator's fork applies a closure the call site supplied, so
 * what tells its copies apart is which predicate each was handed — and that is what an arm is
 * counted under beside the fork itself.
 *
 * <p>The model below runs the first predicate and never runs the second: {@code b} is empty, so the
 * fork under it is not entered once. It used to be reported as every arm covered.
 */
class AnArmOfALibraryForkIsNotTheAuthorsPredicateTest {

    private static final String MODULE = "example.people";

    private static final String MODEL = """
            module example.people

            data Age = Int
                invariant value >= 0
            data Person =
                { age: Age
                }

            behavior twice : (a: List<Person>, b: List<Person>) -> List<Person>
            let twice (a, b) =
                List.filter(x -> x.age.value >= 18, a)
                    ++ List.filter(y -> y.age.value >= 65, b)

            example twice
                | "the second predicate is never reached"
                    : ([ Person { age = Age(20) }, Person { age = Age(10) } ], [ ])
                        -> [ Person { age = Age(20) } ]
            """;

    private static Adequacy.BranchEvidence armsOfTwice() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.BranchEvidence> arms =
                compilation.db().ask(new Adequacy.BranchCoverage(MODULE)).value();
        assertNotNull(arms, "the model under test compiles");
        Adequacy.BranchEvidence twice = arms.get("twice");
        assertNotNull(twice, "twice has arms to measure");
        return twice;
    }

    /** Four occurrences and four keys: each call's arms are its own to cover. */
    @Test
    void twoCallsOfOneCombinatorDoNotShareTheirArms() {
        Adequacy.BranchEvidence twice = armsOfTwice();
        assertEquals(4, twice.arms().all().size(), "each call is emitted and probed on its own");
        assertEquals(4, twice.arms().obligations(),
                "and each is a thing to cover, since each decides a different predicate");
    }

    /** So the predicate nothing ran is named, rather than marked by the row beside it. */
    @Test
    void aPredicateNothingRanIsNamed() {
        Adequacy.BranchEvidence twice = armsOfTwice();
        assertEquals(2, twice.arms().coveredObligations(),
                "the row reached the first call's two arms and no others");
        assertEquals(2, twice.unreached().orElseThrow().size(),
                () -> "and the second call's are named: " + twice.unreached().orElseThrow());
    }

    /**
     * And a helper of the author's own still counts its copies as one.
     *
     * <p>The other side of the rule, and the case the key was made for. The condition is the
     * helper's own comparison however many times it is spliced in, so a row through one call
     * establishes what a row through the next would.
     */
    @Test
    void aHelpersOwnForkIsOneArmHoweverManyTimesItIsSplicedIn() {
        Compilation compilation = Compilation.ofSource("""
                module example.people

                data Age = Int
                    invariant value >= 0
                data Person =
                    { age: Age
                    }
                data Verdict = Yes | No

                let grown (n: Age): Bool = if n.value >= 18 then true else false

                behavior both : (a: Person, b: Person) -> Verdict
                let both (a, b) = if grown(a.age) && grown(b.age) then Yes else No

                example both
                    | "both grown" : (Person { age = Age(20) }, Person { age = Age(30) }) -> Yes
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.BranchEvidence both = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("both");
        assertNotNull(both, "the model under test compiles");

        assertTrue(both.arms().all().size() > both.arms().obligations(),
                () -> "the helper is spliced in twice and its arms are one: "
                        + both.arms().all().size() + " occurrences, " + both.arms().obligations() + " keys");
    }
}
