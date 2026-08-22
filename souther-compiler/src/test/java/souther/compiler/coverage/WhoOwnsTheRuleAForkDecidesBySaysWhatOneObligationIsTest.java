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

    /**
     * A fork resting on a supplied rule through another helper is still the caller's to decide.
     *
     * <p>The condition applies {@code ask} and not {@code p}, so a reading asking whether a
     * function parameter is applied here comes back with the declaration deciding for itself — and
     * the two rules the call sites wrote are counted as one. That is a rule nothing exercised
     * reported as covered, and it is what asking about the whole condition rather than about one
     * application answers.
     */
    @Test
    void aForkRestingOnASuppliedRuleThroughAHelperIsTheCallersToDecide() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let ask (p: (Int) -> Bool, x: Int): Bool = p(x)

                let decide (p: (Int) -> Bool, x: Int): Verdict =
                    if ask(p, x) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "under the first line and under the second" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(8, twice.obligations(),
                "the helper's fork is one obligation per rule handed to it, beside the two here");
        assertEquals(4, twice.covered().size(), "and the one row reaches half of them");
    }

    /** And so is one resting on it through a name the body bound it to. */
    @Test
    void andThroughANameTheBodyBoundItTo() {
        Adequacy.BranchEvidence pick = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let decide (p: (Int) -> Bool, x: Int): Verdict = {
                    let q = p
                    if q(x) then Yes else No
                }

                behavior pick : (a: Int) -> Count
                    constructs Count
                let pick (a) =
                    Count(if decide(n -> n < 18, a) == Yes then 1 else 0)

                example pick
                    | "under the line" : (1) -> Count(1)
                """, "pick");

        assertEquals(4, pick.obligations(),
                "the name stands for the rule, so the fork is the caller's to decide");
    }

    /**
     * One declaration named at two call sites is one rule.
     *
     * <p>The author wrote one rule and handed it over twice; a row through the arms of one call is
     * a row through that rule. Told apart by where each hand-over happened, the second call site is
     * owed a row establishing what the first already does — and a name reaching a function parameter
     * is wrapped in a lambda written at the call site before the expansion sees it, so what arrives
     * there says two where the source says one.
     */
    @Test
    void oneDeclarationNamedAtTwoCallSitesIsOneRule() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let adult (x: Int): Bool = x >= 18

                behavior twice : (a: List<Int>, b: List<Int>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(List.filter(adult, a))
                        + List.length(List.filter(adult, b)))

                example twice
                    | "one over and one under" : ([ 20 ], [ 1 ]) -> Count(1)
                """, "twice");

        assertEquals(2, twice.obligations(), "one rule, handed over twice");
        assertEquals(2, twice.covered().size(), "and both its arms are reached");
    }

    /** Two declarations named at two call sites are two. */
    @Test
    void andTwoDeclarationsNamedAtTwoCallSitesAreTwo() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let adult (x: Int): Bool = x >= 18
                let senior (x: Int): Bool = x >= 65

                behavior twice : (a: List<Int>, b: List<Int>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(List.filter(adult, a))
                        + List.length(List.filter(senior, b)))

                example twice
                    | "one over the first and under the second" : ([ 20 ], [ 20 ]) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(), "two rules, one apiece");
    }

    /**
     * And a rule handed to a helper whose answer does not rest on it decides nothing.
     *
     * <p>The other half of following a call. Asked as "is a rule mentioned anywhere in this
     * condition", a rule handed to a helper that never reads it makes every copy of the fork its
     * own obligation, and each call site is owed a row for a rule that decides nothing there. What
     * the helper answers with is what settles it.
     */
    @Test
    void aRuleAHelpersAnswerDoesNotRestOnDecidesNothing() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let ignore (p: (Int) -> Bool, x: Int): Bool = x > 0

                let decide (p: (Int) -> Bool, x: Int): Verdict =
                    if ignore(p, x) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "both over" : (1, 1) -> Count(2)
                """, "twice");

        assertEquals(6, twice.obligations(),
                "the helper's fork is one obligation, beside the two written here");
    }

    /**
     * A rule bound to a name a line above the fork is in force where the fork stands.
     *
     * <p>Read afresh at each fork, the environment the {@code let} put the rule in is gone and the
     * condition names something the reading knows nothing about — so the fork is called the
     * declaration's own, and the rules two call sites wrote are counted as one.
     */
    @Test
    void aRuleBoundAboveTheForkIsInForceAtIt() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let decide (p: (Int) -> Bool, x: Int): Verdict = {
                    let q = p
                    if q(x) then Yes else No
                }

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "under and under" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(8, twice.obligations(),
                "the helper's fork is one obligation per rule handed to it, beside the two here");
    }

    /**
     * And so are the guards of a comprehension, which are forks the lowering makes.
     *
     * <p>Read after the lowering, the rule has been substituted in and the guard is a fork nothing
     * declared — so every copy of it is counted as one, whatever each call site supplied.
     */
    @Test
    void andSoAreTheGuardsOfAComprehension() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let choose (p: (Int) -> Bool, x: Int): List<Int> = [ x | p(x) ]

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(choose(n -> n < 18, a))
                        + List.length(choose(m -> 65 <= m, b)))

                example twice
                    | "under the first and under the second" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(), "one guard per rule handed to it");
        assertEquals(2, twice.covered().size(), "and the one row reaches one arm of each");
    }

    /**
     * A rule wrapped in a lambda and handed to a helper that never reads it decides nothing.
     *
     * <p>The wrapper is not a name, so a reading that descended into every argument that is not one
     * found the rule inside it and called the fork above the caller's to decide — which owes each
     * call site a row for a rule that settles nothing there.
     */
    @Test
    void aRuleWrappedAndHandedToAHelperThatIgnoresItDecidesNothing() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let ignore (p: (Int) -> Bool, x: Int): Bool = x > 0

                let decide (p: (Int) -> Bool, x: Int): Verdict =
                    if ignore(y -> p(y), x) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "both over" : (1, 1) -> Count(2)
                """, "twice");

        assertEquals(6, twice.obligations(),
                "the helper's fork is one obligation, beside the two written here");
    }

    /** One rule copied into two bodies is one rule, wherever the copy is stamped. */
    @Test
    void oneRuleCopiedIntoTwoBodiesIsOneRule() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let evens (xs: List<Int>): List<Int> = List.filter(x -> x > 0, xs)

                behavior twice : (a: List<Int>, b: List<Int>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(evens(a)) + List.length(evens(b)))

                example twice
                    | "one each" : ([ 1 ], [ 1 ]) -> Count(2)
                """, "twice");

        assertEquals(2, twice.obligations(), "one rule, copied twice");
    }

    /**
     * A rule reaching a fork through an argument of any type is still the caller's.
     *
     * <p>Whether an argument reaches the answer is about the flow of values, and a reading that
     * followed only the parameters carrying a rule stepped over a helper answering out of a
     * {@code Bool}. What the fork rested on was there and was not followed, so the rules two call
     * sites wrote were counted as one.
     */
    @Test
    void aRuleReachingTheForkThroughAPlainArgumentIsStillTheCallers() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let relay (b: Bool): Bool = b

                let decide (p: (Int) -> Bool, x: Int): Verdict =
                    if relay(p(x)) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "under and under" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(8, twice.obligations(),
                "the helper's fork is one obligation per rule handed to it, beside the two here");
    }

    /**
     * And a {@code match} decides by its subject as an {@code if} decides by its condition.
     *
     * <p>Every construct that bears arms is asked the same question. Asked of the {@code if} alone,
     * the arms of a {@code match} over what a supplied rule answered were one obligation however
     * many rules were handed in — the same silent count, one construct over.
     */
    @Test
    void aMatchOverASuppliedRulesAnswerIsTheCallersToDecide() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data A
                data B
                data Choice = A | B
                data Count = Int

                let decide (p: (Int) -> Choice, x: Int): Int =
                    match p(x) with
                        | A -> 1
                        | B -> 0

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(decide(n -> A, a) + decide(m -> B, b))

                example twice
                    | "one each" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(), "one match per rule handed in");
        assertEquals(2, twice.covered().size(), "and the one row reaches one arm of each");
    }

    /**
     * A name a body binds a rule to is where the rule was put, and is not the rule.
     *
     * <p>There are as many bindings as there are copies of the body that made them, and two names
     * for one declaration are two bindings — so a rule read off the binding is as many rules as
     * that, and each call site is owed a row establishing what another already does.
     */
    @Test
    void twoNamesForOneRuleAreOneRule() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let adult (x: Int): Bool = x >= 18

                behavior twice : (a: List<Int>, b: List<Int>) -> Count
                    constructs Count
                let twice (a, b) = {
                    let p = adult
                    let q = adult
                    Count(List.length(List.filter(p, a)) + List.length(List.filter(q, b)))
                }

                example twice
                    | "one over and one under" : ([ 20 ], [ 1 ]) -> Count(1)
                """, "twice");

        assertEquals(2, twice.obligations(), "one rule, bound under two names");
        assertEquals(List.of(), twice.countedTogether(),
                () -> "and nothing about it is uncertain: " + twice.countedTogether());
    }

    /**
     * A rule reaching a fork through a call nothing was read about is still the caller's.
     *
     * <p>What a call answers out of is read off declarations that were written out, and the
     * language implements some of its own and writes others as sugar over one another. Answered
     * "this call rests on none of its arguments" where nothing was read, the rule reaching the fork
     * through one was not followed — so the rules two call sites wrote were counted as one.
     */
    @Test
    void aRuleReachingTheForkThroughACallNothingWasReadAboutIsStillTheCallers() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let decide (p: (Int) -> String, x: Int): Verdict =
                    if String.length(p(x)) > 0 then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> "x", a) == Yes then 1 else 0)
                        + (if decide(m -> "", b) == Yes then 1 else 0))

                example twice
                    | "one each" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(8, twice.obligations(),
                "the helper's fork is one obligation per rule handed to it, beside the two here");
    }

    /** And so is one reaching it through a name the body bound a function to. */
    @Test
    void andThroughANameTheBodyBoundAFunctionTo() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let relay (b: Bool): Bool = b

                let decide (p: (Int) -> Bool, x: Int): Verdict = {
                    let f = relay
                    if f(p(x)) then Yes else No
                }

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "under and under" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(8, twice.obligations(), "one obligation per rule handed in");
    }

    /**
     * A fork a helper wrote inside a block it hands away is still that helper's to be a copy of.
     *
     * <p>What stands nearest round it is then the copy of whatever the block was handed to, and the
     * parameters the declaration named are not that one's. Read off the nearest copy alone, a fork
     * whose rule the call site is holding says nothing about which rule it was.
     */
    @Test
    void aForkWrittenInsideABlockItHandsAwayIsStillTheHelpersCopy() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let classify (p: (Int) -> Bool, xs: List<Int>): List<Int> =
                    List.map(x -> if p(x) then 1 else 0, xs)

                behavior twice : (a: List<Int>, b: List<Int>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(classify(n -> n < 18, a))
                        + List.length(classify(m -> 18 < m, b)))

                example twice
                    | "one each" : ([ 1 ], [ 1 ]) -> Count(2)
                """, "twice");

        assertEquals(4, twice.obligations(), "one fork per rule handed to the helper");
        assertEquals(2, twice.covered().size(), "and the one row reaches one arm of each");
    }

    /** And it says so wherever the value it stands in reaches. */
    @Test
    void andItSaysSoWhereverTheValueItStandsInReaches() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Box = { value: Int }
                data Count = Int

                let decide (p: (Int) -> Bool, x: Int): Box =
                    Box { value = if p(x) then 1 else 0 }

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count, Box
                let twice (a, b) =
                    Count(decide(n -> n < 18, a).value + decide(m -> 18 < m, b).value)

                example twice
                    | "under and under" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(),
                "the fork is in the helper's copy, whatever it was written into");
    }

    /**
     * Which copy owns the fork is a copy of that declaration, and not one spelling its parameters.
     *
     * <p>A parameter's name says which of one declaration's parameters it is and nothing more, and
     * two declarations name one alike as often as not. Asked by the names, a copy of whatever the
     * fork was handed to answers first where it happens to spell one the same way — with its own
     * rule, which is one rule at every call site, so the rules the call sites wrote are counted as
     * one.
     */
    @Test
    void theCopyThatOwnsTheForkIsOneOfThatDeclaration() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Count = Int

                let apply (p: (Int) -> Int, x: Int): Int = p(x)

                let decide (p: (Int) -> Bool, x: Int): Int =
                    apply(y -> if p(y) then 1 else 0, x)

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(decide(n -> n < 18, a) + decide(m -> 65 <= m, b))

                example twice
                    | "different sides" : (1, 1) -> Count(1)
                """, "twice");

        assertEquals(4, twice.obligations(),
                "one fork per rule the call sites handed `decide`, not one per lambda it writes");
        assertEquals(2, twice.covered().size(), "and the one row reaches one arm of each");
    }

    /**
     * And what a call answers out of does not turn on where the callee is written down.
     *
     * <p>Every declaration being read starts at resting on nothing, so one this has not got to yet
     * is told from a callable it will never read. Started at nothing known, a call to something
     * declared below is read as resting on every argument, and nothing takes that back — so a fork
     * resting on none of the rules is owed a row at every call site.
     */
    @Test
    void andWhatACallAnswersOutOfDoesNotTurnOnWhereItIsWritten() {
        Adequacy.BranchEvidence twice = arms("""
                module example.rules

                data Yes
                data No
                data Verdict = Yes | No
                data Count = Int

                let relay (p: (Int) -> Bool, x: Int): Bool = ignore(p, x)

                let ignore (p: (Int) -> Bool, x: Int): Bool = x > 0

                let decide (p: (Int) -> Bool, x: Int): Verdict =
                    if relay(p, x) then Yes else No

                behavior twice : (a: Int, b: Int) -> Count
                    constructs Count
                let twice (a, b) =
                    Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                        + (if decide(m -> 18 < m, b) == Yes then 1 else 0))

                example twice
                    | "both over" : (1, 1) -> Count(2)
                """, "twice");

        assertEquals(6, twice.obligations(),
                "the helper's fork rests on none of the rules, so it is one obligation");
    }
}
