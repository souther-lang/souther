package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What one arm is owed for turns on who owns the rule its fork decides by.
 *
 * <p>A non-recursive helper is spliced into every body that calls it, so one arm the author wrote is
 * several arms in the tree that runs. They are one thing to cover while the helper decides for
 * itself: covering it through a second call site establishes nothing the first did not, and asking
 * an author for that row is asking for work already done. Where the caller hands the rule in, each
 * call decides by a different rule and a row through one says nothing about the next.
 *
 * <p>Which of the two a fork is, the declaration says. A parameter of function type is the caller
 * handing in a rule; a parameter of any other type is the caller handing in what that rule reads.
 * Worked out instead from the shape of the condition after expansion, the two cannot be told apart
 * at all — the argument is standing where the parameter was either way — and the readings that
 * tried it either called two rules one, which reports a rule nothing exercised as covered, or
 * called one rule two, which asks for a row that establishes nothing.
 */
class WhoOwnsTheRuleAForkDecidesBySaysWhatOneObligationIsTest {

    private static final String MODULE = "example.rules";

    private static Adequacy.BranchEvidence arms(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Adequacy.BranchEvidence said = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get(behavior);
        assertNotNull(said, () -> "the model under test compiles: " + behavior);
        return said;
    }

    /** A helper deciding by a value it was handed is one fork however many bodies call it. */
    @Test
    void aHelperDecidingByAValueIsOneObligation() {
        Adequacy.BranchEvidence both = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No

                let decide (b: Bool): Verdict = if b then Yes else No

                behavior both : (p: Bool, q: Bool) -> Verdict
                let both (p, q) = if decide(p) == Yes then decide(q) else No

                example both
                    | "the first holds and the second does not" : (true, false) -> No
                """, "both");

        assertEquals(4, both.obligations(),
                "the helper's two calls are one fork, beside the fork of the body itself");
        assertEquals(List.of(), both.countedTogether(),
                () -> "and nothing about them is uncertain: " + both.countedTogether());
    }

    /**
     * And the arm the rows certainly do not reach is still reported.
     *
     * <p>The same model. Its one row takes the body's own {@code then}, so its {@code else} is an
     * arm nothing reaches and nothing about it is in doubt. Read off a number that fell to partial
     * because a helper somewhere else could not be told apart, it went unreported.
     */
    @Test
    void andAnArmNothingReachesIsStillOwedARow() {
        Adequacy.BranchEvidence both = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No

                let decide (b: Bool): Verdict = if b then Yes else No

                behavior both : (p: Bool, q: Bool) -> Verdict
                let both (p, q) = if decide(p) == Yes then decide(q) else No

                example both
                    | "the first holds and the second does not" : (true, false) -> No
                """, "both");

        assertEquals(List.of("ELSE"),
                both.unreached().stream().map(site -> site.name().toString()).toList(),
                () -> "the body's own else, which the one row does not take: " + both.unreached());
    }

    /** A value the call site specialises the helper with is not the rule either. */
    @Test
    void aHelperSpecialisedByANumberIsStillOneObligation() {
        Adequacy.BranchEvidence pick = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No

                let atLeast (limit: Int, x: Int): Verdict = if x >= limit then Yes else No

                behavior pick : (a: Int, b: Int) -> Verdict
                let pick (a, b) = if atLeast(18, a) == Yes then atLeast(65, b) else No

                example pick
                    | "over the first and under the second" : (20, 1) -> No
                """, "pick");

        assertEquals(4, pick.obligations(),
                "one fork written once, whatever number each call hands it");
        assertEquals(List.of(), pick.countedTogether(),
                () -> "and nothing uncertain about it: " + pick.countedTogether());
    }

    /** A rule the call site writes is the rule, and two of them are two obligations. */
    @Test
    void twoRulesHandedToOneFunctionParameterAreTwoObligations() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let less (a: Int, b: Int): Bool = a < b

                behavior twice : (xs: List<Int>, ys: List<Int>) -> Count
                    constructs Count
                let twice (xs, ys) =
                    Count(List.length(List.filter(x -> less(x, 18), xs))
                        + List.length(List.filter(y -> less(18, y), ys)))

                example twice
                    | "one under the first line and under the second" : ([ 1 ], [ 1 ]) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(),
                "two calls of one combinator, each deciding by the rule it was handed");
        assertEquals(2, twice.covered().size(),
                "and the one row reaches one arm of each");
        assertEquals(List.of(), twice.countedTogether(),
                () -> "neither is in doubt: " + twice.countedTogether());
    }

    /** Told apart by the rule and not by what the rule compares: the same shape, two subjects. */
    @Test
    void andTheSameComparisonAtTwoSubjectsIsStillTwoRules() {
        Adequacy.BranchEvidence sift = arms("""
                module example.rules

                data Count = Int

                let oldEnough (limit: Int, n: Int): Bool = n >= limit

                behavior sift : (xs: List<Int>, ys: List<Int>) -> Count
                    constructs Count
                let sift (xs, ys) =
                    Count(List.length(List.filter(x -> oldEnough(18, x), xs))
                        + List.length(List.filter(y -> oldEnough(65, y), ys)))

                example sift
                    | "one over the first line and under the second" : ([ 20 ], [ 20 ]) -> Count(1)
                """, "sift");

        assertEquals(4, sift.obligations(),
                "one comparison, specialised twice, handed in as two rules");
    }

    /**
     * A rule handed on through a helper is still the rule the call site wrote.
     *
     * <p>The fork is the combinator's and the parameter it names is the combinator's, and neither
     * of those is where the rule was written. A reading that looked for the innermost declaration's
     * own parameter name would find nothing here and call the two call sites alike.
     */
    @Test
    void aRuleForwardedThroughAHelperIsTheOneTheCallSiteWrote() {
        Adequacy.BranchEvidence sift = arms("""
                module example.rules

                data Count = Int

                let keeping (p: (Int) -> Bool, xs: List<Int>): List<Int> =
                    List.filter(p, xs)

                behavior sift : (xs: List<Int>, ys: List<Int>) -> Count
                    constructs Count
                let sift (xs, ys) =
                    Count(List.length(keeping(x -> x < 18, xs))
                        + List.length(keeping(y -> 18 < y, ys)))

                example sift
                    | "one under the first line and under the second" : ([ 1 ], [ 1 ]) -> Count(1)
                """, "sift");

        assertEquals(4, sift.obligations(),
                "two rules written at two call sites, whatever they were handed through");
        assertEquals(2, sift.covered().size(), "and the one row reaches one arm of each");
    }
}
