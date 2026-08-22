package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What an arm is counted under is the rule its fork decides, after the call site has had its say.
 *
 * <p>Where it was written cannot be that. A construct keeps its identity through being spliced — it
 * is what lets the copies of a helper's arm be one obligation — so it is the same at every copy by
 * design, and a key made of it cannot tell one specialisation of a rule from another. Two calls of
 * {@code oldEnough(18, ·)} and {@code oldEnough(65, ·)} write one comparison and decide two things.
 *
 * <p>What is left out is which position the rule is about. {@code grown(a.age)} and
 * {@code grown(b.age)} are one rule at two subjects, and covering it once is covering it — which is
 * the answer this had before and keeps.
 */
class ARuleIsWhatItSaysAfterTheCallSiteHasSaidItsPartTest {

    private static Adequacy.BranchEvidence armsOf(String module, String behavior, String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).toList(), "the model under test compiles");
        Adequacy.BranchEvidence arms = compilation.db()
                .ask(new Adequacy.BranchCoverage(module)).value().get(behavior);
        assertNotNull(arms, behavior + " has arms to measure");
        return arms;
    }

    /**
     * One comparison in a helper, given two thresholds.
     *
     * <p>The rows run the first predicate both ways and never enter the second: {@code b} is empty.
     * Counted under where the comparison was written, the two came out as one pair of arms and the
     * behavior was complete over a threshold nothing had compared anything against.
     */
    @Test
    void oneComparisonSpecialisedTwoWaysIsTwoRules() {
        Adequacy.BranchEvidence twice = armsOf("example.ages", "twice", """
                module example.ages

                data Age = Int
                data Person = { age: Age }
                data Count = Int

                let oldEnough (limit: Int, p: Person): Bool = p.age.value >= limit

                behavior twice : (a: List<Person>, b: List<Person>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(List.filter(x -> oldEnough(18, x), a))
                        + List.length(List.filter(y -> oldEnough(65, y), b)))

                example twice
                    | "one under and one over, and the second never entered"
                        : ([ Person { age = Age(20) }, Person { age = Age(10) } ], [ ]) -> Count(1)
                """);

        assertEquals(4, twice.obligations(), "two thresholds, two arms each");
        assertEquals(2, twice.coveredObligations(),
                () -> "and only the first threshold's: " + twice.unreached());
    }

    /** A comparison a predicate binds to a name before answering with it is still what it decides. */
    @Test
    void aComparisonBoundToANameFirstIsStillWhatTheForkDecides() {
        Adequacy.BranchEvidence twice = armsOf("example.bound", "twice", """
                module example.bound

                data Age = Int
                data Person = { age: Age }
                data Count = Int

                behavior twice : (a: List<Person>, b: List<Person>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(List.filter(x -> {
                            let adult = x.age.value >= 18
                            adult
                        }, a))
                        + List.length(List.filter(y -> {
                            let retired = y.age.value >= 65
                            retired
                        }, b)))

                example twice
                    | "the second is never entered"
                        : ([ Person { age = Age(20) }, Person { age = Age(10) } ], [ ]) -> Count(1)
                """);

        assertEquals(4, twice.obligations(), "two predicates, two arms each");
        assertEquals(2, twice.coveredObligations(),
                () -> "and only the first's: " + twice.unreached());
    }

    /**
     * And a helper of this module's own that applies what it was handed, which is the same shape.
     *
     * <p>Whether a fork's copies decide alike is not a question about where the fork was written. A
     * rule that asked that would have answered for the library and said nothing about the helper
     * beside it.
     */
    @Test
    void aHelperOfThisModulesOwnApplyingWhatItWasHandedIsTheSameShape() {
        Adequacy.BranchEvidence both = armsOf("example.decide", "both", """
                module example.decide

                data Person =
                    { active: Bool
                    , retired: Bool
                    }
                data Yes
                data No
                data Verdict = Yes | No

                let decide (p: (Person) -> Bool, x: Person): Verdict =
                    if p(x) then Yes else No

                behavior both : (x: Person) -> Verdict
                let both (x) =
                    if decide(a -> a.active, x) == Yes then decide(b -> b.retired, x) else No

                example both
                    | "active and not retired"
                        : (Person { active = true, retired = false }) -> No
                """);

        assertEquals(6, both.obligations(),
                "the two calls decide different things, and the fork above them is its own");
    }

    /**
     * And a helper whose decision is its own is still one arm, however many call it.
     *
     * <p>The other side of the rule. What differs between the two calls is which position the rule
     * is about, and that is not part of what it says — so a row through one establishes what a row
     * through the next would.
     */
    @Test
    void aHelperWhoseDecisionIsItsOwnIsStillOneArm() {
        Adequacy.BranchEvidence both = armsOf("example.grown", "both", """
                module example.grown

                data Age = Int
                data Person = { age: Age }
                data Yes
                data No
                data Verdict = Yes | No

                let grown (n: Age): Bool = if n.value >= 18 then true else false

                behavior both : (a: Person, b: Person) -> Verdict
                let both (a, b) = if grown(a.age) && grown(b.age) then Yes else No

                example both
                    | "both grown" : (Person { age = Age(20) }, Person { age = Age(30) }) -> Yes
                """);

        assertEquals(4, both.obligations(),
                () -> "the helper's two calls are one arm, beside the fork that calls them: "
                        + both.all().size() + " occurrences");
    }
}
