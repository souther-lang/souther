package souther.compiler.query;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.WhyKept;
import souther.compiler.reading.PathAccess;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;
import souther.compiler.semantics.HowAClosureIsApplied;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of two classes is owed where some run reads both, in those classes, and nowhere
 * else.
 *
 * <p>Read a way at a time. A plan that is {@code Flat} answers the same whatever the usage, because
 * no run down that arm asks the usage anything: a row for {@code Flat} past a hundred shows nothing
 * the {@code Flat} row and the usage rows apart do not, and a build that refuses until it is written
 * asks for a row that can catch no defect. Under {@code Metered} the usage is asked, and each class
 * of it beside {@code Metered} is owed.
 *
 * <p>What a run reads is what it decides on its way and what the value it answers owes itself to. A
 * value decided under a {@code let} and handed into an arm further on is read together with the
 * decision that takes the arm, though no fork is reached by both.
 *
 * <p>And what the reading could not say keeps every combination. A way written without something
 * that holds on it, ways past the bound the walk reads, a rule the body wrote that no decision reads:
 * none of them shows that two positions are read apart, so none of them narrows what is owed.
 */
class ACombinationIsOwedWhereARunReadsBothTest {

    /** The model of the issue: only {@code Metered} asks the usage anything. */
    private static final String CHARGE = """
            module probe.charge

            data Flat
            data Metered
            data Plan = Flat | Metered
            data Usage = Int
                invariant value >= 0
            data Fee = Int

            behavior charge : (plan: Plan, usage: Usage) -> Fee
                constructs Fee

            let charge (plan, usage) =
                match plan with
                    | Flat -> Fee(1000)
                    | Metered -> if usage.value <= 100 then Fee(300) else Fee(800)

            example charge
                | "flat"              : (Flat, Usage(0))      -> Fee(1000)
                | "metered, at 100"   : (Metered, Usage(100)) -> Fee(300)
                | "metered, past 100" : (Metered, Usage(101)) -> Fee(800)
            """;

    @Test
    void aPlanThatNeverAsksTheUsageOwesNoCombinationWithIt() {
        Measured charge = measured(CHARGE, "charge");

        assertInstanceOf(CombinationCriterion.PairFallback.class, charge.criterion(),
                "the decisions meet nowhere, so the combinations of the positions are the measure");
        assertEquals(Set.of("Metered × usage/0 <= x <= 100", "Metered × usage/100 < x"),
                charge.owed(), "only Metered asks the usage, so only Metered is paired with it");
        assertEquals(List.of(), charge.left(), "the Metered rows reach both");
        assertEquals(List.of(), charge.pairGaps(), "and a strict build has nothing to refuse");
    }

    /**
     * Where the plan is decided first and its answer handed on into the arms of a fork on the usage,
     * the arm that uses it reads both, and the one that does not reads the usage alone.
     */
    @Test
    void aValueHandedIntoAnArmIsReadWithTheDecisionThatTakesTheArm() {
        Measured handed = measured("""
                module probe.handed

                data Flat
                data Metered
                data Plan = Flat | Metered
                data Usage = Int
                    invariant value >= 0
                data Fee = Int

                behavior charge : (plan: Plan, usage: Usage) -> Fee
                    constructs Fee

                let charge (plan, usage) = {
                    let base = match plan with
                        | Flat -> 1000
                        | Metered -> 300
                    if usage.value <= 100 then Fee(base) else Fee(0)
                }

                example charge
                    | (Flat, Usage(0))      -> Fee(1000)
                    | (Metered, Usage(101)) -> Fee(0)
                """, "charge");

        assertEquals(Set.of("Flat × usage/0 <= x <= 100", "Metered × usage/0 <= x <= 100"),
                handed.owed(), "the plan is read where its answer is used, under the usage's line");
    }

    /** The right of an {@code &&} runs only where the left held, and is read only with that. */
    @Test
    void theRightOfAnOperatorThatStopsEarlyIsReadOnlyWhereTheLeftLetItRun() {
        Measured both = measured("""
                module probe.both

                data In = { a: Int, b: Int }
                data Out = Int

                behavior both : (i: In) -> Out
                    constructs Out

                let both (i) = if i.a > 5 && i.b > 10 then Out(1) else Out(0)

                example both
                    | (In { a = 0, b = 0 }) -> Out(0)
                """, "both");

        assertEquals(Set.of("i.a/5 < x × i.b/x <= 10", "i.a/5 < x × i.b/10 < x"), both.owed(),
                "a run whose left came out false never asks the right anything");
    }

    /**
     * Conditions on a name the cases of two sums share are chosen apart, and a run reads both where
     * it reads the second under the first.
     *
     * <p>What each choice of case reads, and not what the choices joined stand at: the join is what
     * the way admits at a position, and says nothing of which choice stood there.
     */
    @Test
    void conditionsUnderTheCasesOfTwoSumsAreReadTogetherAcrossThem() {
        Measured sums = measured("""
                module probe.sums

                data Sized = { amount: Int }
                    invariant amount >= 0 && amount <= 1000
                data Small = { ...Sized }
                    invariant amount <= 10
                data Large = { ...Sized }
                    invariant amount >= 100
                data Kind = Small | Large
                data Order = { left: Kind, right: Kind }

                behavior both : (o: Order) -> String
                let both (o) =
                    if o.left.amount <= 5 then
                        if o.right.amount <= 5 then "a" else "b"
                    else "c"

                example both
                    | (Order { left = Small { amount = 1 }, right = Small { amount = 1 } }) -> "a"
                """, "both");

        assertEquals(Set.of(
                        "o.left@Small.amount/0 <= x <= 5 × o.right@Small.amount/0 <= x <= 5",
                        "o.left@Small.amount/0 <= x <= 5 × o.right@Small.amount/5 < x <= 10"),
                sums.owed(), "the right is asked only under a left at or below the line");
    }

    /**
     * Whether a construction holds its rules is a step on the way this reading has no words for,
     * and may turn on any position, so the ways under it narrow nothing.
     */
    @Test
    void aWayUnderAStepNothingStatesKeepsEveryCombination() {
        Measured attempted = measured("""
                module probe.attempted

                data Flat
                data Metered
                data Plan = Flat | Metered
                data Usage = Int
                    invariant value >= 0
                data Positive = Int
                    invariant value > 0
                data Fee = Int

                behavior charge : (plan: Plan, usage: Usage) -> Fee
                    constructs Fee, Positive

                let charge (plan, usage) = {
                    guard Positive(usage.value - 50) as p else Fee(0)
                    match plan with
                        | Flat -> Fee(1000)
                        | Metered -> if usage.value <= 100 then Fee(300) else Fee(800)
                }

                example charge
                    | (Flat, Usage(60)) -> Fee(1000)
                """, "charge");

        assertEquals(Set.of("Flat × usage/0 <= x <= 100", "Flat × usage/100 < x",
                        "Metered × usage/0 <= x <= 100", "Metered × usage/100 < x"),
                attempted.owed(), "what the reading could not say is no proof of reading apart");
    }

    /**
     * A {@code match} on a name bound over several cases is a decision nothing could name the
     * subject of, and may be about any position — here it is about the usage, which no way says.
     *
     * <p>Read whole, the plan's ways under it are no proof that the plan is read apart from the
     * usage, and every combination stays.
     */
    @Test
    void aDecisionAboutNoNamedPositionKeepsEveryCombination() {
        Measured tier = measured("""
                module probe.tier

                data Flat
                data Metered
                data Plan = Flat | Metered
                data Low
                data High
                data Tier = Low | High
                data Usage = Int
                    invariant value >= 0
                data Fee = Int

                behavior charge : (plan: Plan, usage: Usage) -> Fee
                    constructs Fee

                let charge (plan, usage) = {
                    let tier = if usage.value <= 100 then Low else High
                    match tier with
                        | Low -> match plan with
                            | Flat -> Fee(1000)
                            | Metered -> Fee(300)
                        | High -> Fee(800)
                }

                example charge
                    | (Flat, Usage(0)) -> Fee(1000)
                """, "charge");

        assertEquals(Set.of("Flat × usage/0 <= x <= 100", "Flat × usage/100 < x",
                        "Metered × usage/0 <= x <= 100", "Metered × usage/100 < x"),
                tier.owed(), "which position the tier is decided on was not read");
    }

    /** An answer settled more ways than the reading holds apart says nothing of what a run read
     *  together, which narrows nothing. */
    @Test
    void anAnswerSettledMoreWaysThanAreHeldApartKeepsEveryCombination() {
        Measured many = measured("""
                module probe.many

                data Flat
                data Metered
                data Plan = Flat | Metered
                data In = { plan: Plan, a: Int, b: Int, c: Int, d: Int, e: Int, usage: Int }
                data Fee = Int

                behavior charge : (i: In) -> Fee
                    constructs Fee

                let charge (i) = {
                    guard i.a > 1 || i.a < -1 else Fee(1)
                    guard i.b > 1 || i.b < -1 else Fee(2)
                    guard i.c > 1 || i.c < -1 else Fee(3)
                    guard i.d > 1 || i.d < -1 else Fee(4)
                    guard i.e > 1 || i.e < -1 else Fee(5)
                    match i.plan with
                        | Flat -> Fee(1000)
                        | Metered -> if i.usage <= 100 then Fee(300) else Fee(800)
                }

                example charge
                    | (In { plan = Flat, a = 2, b = 2, c = 2, d = 2, e = 2, usage = 0 }) -> Fee(1000)
                """, "charge");

        assertEquals(Set.of("Flat × i.usage/x <= 100", "Flat × i.usage/100 < x",
                        "Metered × i.usage/x <= 100", "Metered × i.usage/100 < x"),
                many.owedBetween("i.plan", "i.usage"),
                "which ways the answer was settled by was not read, so nothing is read apart");
    }

    /**
     * A fork reached more ways than the walk reads is read without what held above it, so its own
     * ways stand beside every class of everything else.
     *
     * <p>Only the ways past the bound. The answer is still settled ways this reading holds apart,
     * and the arm of the fork reached within the bound is read with what held above it.
     */
    @Test
    void aForkReachedMoreWaysThanAreReadKeepsEveryCombinationOfItsOwnWays() {
        Measured fork = measured("""
                module probe.fork

                data Flat
                data Metered
                data Plan = Flat | Metered
                data In = { plan: Plan, a: Int, b: Int, c: Int, usage: Int }
                data Fee = Int

                behavior charge : (i: In) -> Fee
                    constructs Fee

                let charge (i) = {
                    guard i.a > 1 || i.a < -1 else Fee(1)
                    guard i.b > 1 || i.b < -1 else Fee(2)
                    guard i.c > 1 || i.c < -1 else Fee(3)
                    match i.plan with
                        | Flat -> Fee(1000)
                        | Metered ->
                            if i.usage <= 100 || i.usage > 1000 || i.usage == 500
                            then Fee(300) else Fee(800)
                }

                example charge
                    | (In { plan = Flat, a = 2, b = 2, c = 2, usage = 0 }) -> Fee(1000)
                """, "charge");

        assertEquals(Set.of("Flat × i.usage/x <= 100", "Flat × i.usage/= 500",
                        "Flat × i.usage/1000 < x",
                        "Metered × i.usage/x <= 100", "Metered × i.usage/= 500",
                        "Metered × i.usage/100 < x <= 1000 and x /= 500",
                        "Metered × i.usage/1000 < x"),
                fork.owedBetween("i.plan", "i.usage"),
                "the ways into the first arm were read without the plan above them, and the"
                        + " other arm with it");
    }

    /**
     * A predicate handed to an operation divides its position where no way shows it, so what it is
     * read beside is not known and every combination of the position stays.
     */
    @Test
    void aRuleNoDecisionReadsKeepsEveryCombinationOfItsPosition() {
        Measured few = measured("""
                module probe.few

                import List ( all, length )

                data Item = { quantity: Int }
                data Cart = { items: List<Item> }
                data Out = Int

                behavior few : (c: Cart) -> Out
                    constructs Out

                let few (c) = {
                    guard length(c.items) <= 1 else Out(0)
                    guard all(i -> i.quantity >= 1, c.items) else Out(1)
                    Out(2)
                }

                example few
                    | (Cart { items = [Item { quantity = 1 }] }) -> Out(2)
                """, "few");

        assertEquals(Set.of(
                        "List.length(c.items)/0 <= x <= 1 × c.items[*].quantity/x < 1",
                        "List.length(c.items)/0 <= x <= 1 × c.items[*].quantity/1 <= x",
                        "List.length(c.items)/1 < x × c.items[*].quantity/x < 1",
                        "List.length(c.items)/1 < x × c.items[*].quantity/1 <= x"),
                few.owed(), "a list longer than one is sent away before the predicate on any run"
                        + " the ways show, and the predicate is read on none of them");
    }

    /** With no body there is nothing to read, and every combination is owed. */
    @Test
    void aBehaviorWithNoBodyKeepsEveryCombination() {
        Measured injected = measured("""
                module probe.injected

                data A
                data B
                data Flag = A | B
                data Res = { n: Int }

                behavior pick : (x: Flag, y: Flag) -> Res

                example pick
                    | "one" : (A, A) -> Res { n = 1 }
                """, "pick");

        assertEquals(Set.of("A × A", "A × B", "B × A", "B × B"), injected.owed());
    }

    /**
     * A run that ends at an {@code unreachable} answers nothing and still decided what took it
     * there, so the two classes it read on the way are owed like any others.
     *
     * <p>No way out of a fork is recorded into such an arm — nothing watches a run through it — and
     * the answer is not settled there either. What the run read is the way to the part that answers
     * nothing.
     */
    @Test
    void aRunThatEndsWithoutAnAnswerReadsWhatTookItThere() {
        Measured blank = measured("""
                module probe.blank

                data X
                data Y
                data A = X | Y
                data P
                data Q
                data B = P | Q

                behavior f : (a: A, b: B) -> Int

                let f (a, b) =
                    match a with
                        | X -> 1
                        | Y -> match b with
                                 | P -> 2
                                 | Q -> unreachable "Y is never asked with Q"

                example f
                    | (X, P) -> 1
                """, "f");

        assertEquals(Set.of("Y × P", "Y × Q"), blank.owed(),
                "a run under Y reads b, whichever way it ends");
    }

    /**
     * A value decided inside a helper the body calls is read where the helper's answer is used, as
     * one decided in the body would be.
     */
    @Test
    void aValueDecidedInAHelperIsReadWhereItsAnswerIsUsed() {
        Measured helper = measured("""
                module probe.helper

                data Flat
                data Metered
                data Plan = Flat | Metered
                data Low
                data High
                data Tier = Low | High
                data Usage = Int
                    invariant value >= 0
                data Fee = Int

                behavior charge : (plan: Plan, usage: Usage) -> Fee
                    constructs Fee

                let tier (u: Usage): Tier = if u.value <= 100 then Low else High

                let feeFor (t: Tier): Fee = match t with
                    | Low -> Fee(300)
                    | High -> Fee(800)

                let charge (plan, usage) =
                    match plan with
                        | Flat -> feeFor(tier(usage))
                        | Metered -> Fee(1000)

                example charge
                    | (Flat, Usage(0)) -> Fee(300)
                """, "charge");

        assertEquals(Set.of("Flat × usage/0 <= x <= 100", "Flat × usage/100 < x"),
                helper.owed(), "only Flat hands the usage to the helpers");
    }

    /**
     * Past what the compilation counts off the rows, the combinations owed are counted and not
     * listed, and the count is still the one the ways make.
     */
    @Test
    void pastTheBudgetWhatIsOwedIsCountedAndNotListed() {
        Compilation compilation = Compilation.ofSource(CHARGE, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(1, Budgets.measures().cellsPerGroup(),
                                PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS,
                                Budgets.measures().rewriteRuns()),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence.PairSpace pairs = compilation.db()
                .ask(new Adequacy.Coverage("probe.charge")).value().get("charge").pairs();

        assertEquals(2, pairs.total(), "Metered with each usage class, whatever was listed");
        assertInstanceOf(PartitionEvidence.PairSpace.Owed.Counted.class,
                pairs.space().getFirst().owed(), () -> "not listed past the budget: " + pairs);
        assertInstanceOf(Measurement.FailedToMeasure.class, pairs.counted(),
                "and not counted off the rows, which is said");
        assertEquals(List.of(), pairs.left("charge"), "a space nobody walked leaves no gap");
    }

    /**
     * A way read in part beside conditions under the cases of a sum reads every position in every
     * class a row taking it may hold — not only in the classes the choices of case that read a
     * position read it in.
     */
    @Test
    void aWayReadInPartUnderTheCasesOfASumNarrowsNothing() {
        Measured cases = measured("""
                module probe.partcases

                data Sized = { amount: Int }
                    invariant amount >= 0 && amount <= 1000
                data Small = { ...Sized }
                    invariant amount <= 10
                data Large = { ...Sized }
                    invariant amount >= 100
                data Kind = Small | Large
                data Order = { kind: Kind, n: Int }
                data Positive = Int
                    invariant value > 0

                behavior both : (o: Order) -> String
                    constructs Positive

                let both (o) = {
                    guard Positive(o.n) as p else "none"
                    if o.kind.amount <= 5 then
                        if o.n <= 50 then "a" else "b"
                    else "c"
                }

                example both
                    | (Order { kind = Small { amount = 1 }, n = 1 }) -> "a"
                """, "both");

        assertEquals(Set.of(
                        "o.kind@Small.amount/0 <= x <= 5 × o.n/x <= 50",
                        "o.kind@Small.amount/0 <= x <= 5 × o.n/50 < x",
                        "o.kind@Small.amount/5 < x <= 10 × o.n/x <= 50",
                        "o.kind@Small.amount/5 < x <= 10 × o.n/50 < x"),
                cases.owedBetween("o.kind@Small.amount", "o.n"),
                "a decision past the construction may read either, whichever side of the line");
    }

    /**
     * A total over line items, with each item charged by a function a run applies once to every
     * item: a premium destination is charged whatever the plan, and a normal one reads it.
     *
     * <p>{@code %s} is the body of {@code total}. The rows hold under every body written for it
     * here.
     */
    private static final String CALLS = """
            module probe.calls

            data Free
            data Paid
            data Plan = Free | Paid
            data Normal
            data Premium
            data Dest = Normal | Premium
            data Call = { dest: Dest, seconds: Int }
            data Yen = Int

            behavior total : (plan: Plan, calls: List<Call>) -> Yen
                constructs Yen

            let total (plan, calls) = %s

            let charge (plan: Plan, call: Call): Yen =
                match call.dest with
                    | Premium -> Yen(call.seconds)
                    | Normal ->
                        match plan with
                            | Free -> Yen(0)
                            | Paid -> Yen(call.seconds)

            let premiumOrPaid (plan: Plan, call: Call): Bool =
                match call.dest with
                    | Premium -> true
                    | Normal ->
                        match plan with
                            | Free -> false
                            | Paid -> true

            example total
                | "premium on free" : (Free, [Call { dest = Premium, seconds = 60 }]) -> Yen(60)
                | "normal on free" : (Free, [Call { dest = Normal, seconds = 60 }]) -> Yen(0)
                | "normal on paid" : (Paid, [Call { dest = Normal, seconds = 60 }]) -> Yen(60)
            """;

    /** What a call to a normal destination reads beside the plan, and nothing else. */
    private static final Set<String> A_NORMAL_CALL_READS_THE_PLAN =
            Set.of("Free × Normal", "Paid × Normal");

    /** Every combination of the plan and the destination. */
    private static final Set<String> EVERY_PLAN_WITH_EVERY_DESTINATION =
            Set.of("Free × Normal", "Free × Premium", "Paid × Normal", "Paid × Premium");

    /**
     * A function an operation applies once to every element of a list the input holds is read an
     * application at a time. What a way inside it was written without is which element the run
     * handed it, and the decision on the element says that already — so a premium call, which no
     * application reads the plan beside, owes no combination with it. A run over a premium call and
     * a normal one reads both, in two applications, and neither of them reads the two together.
     *
     * <p>However the function reaches the operation: written in the call, given a name first, or
     * handed to an operation whose own body the reading of the runs has rewritten.
     */
    @ParameterizedTest
    @ValueSource(strings = {
            "Yen(List.fold((sum, c) -> sum + charge(plan, c).value, 0, calls))",
            "{\n    let f = (sum, c) -> sum + charge(plan, c).value\n    Yen(List.fold(f, 0, calls))\n}",
            "Yen(List.fold((sum, n) -> sum + n, 0, List.map(c -> charge(plan, c).value, calls)))"})
    void aWayInsideAFunctionAppliedToEachElementIsReadWithinOneApplication(String body) {
        Measured total = measured(CALLS.formatted(body), "total");

        assertEquals(A_NORMAL_CALL_READS_THE_PLAN, total.owed(),
                "only a normal call reads the plan, and in the same application");
        assertEquals(List.of(), total.pairGaps(), "and the rows written reach both");
        assertEquals(Map.of(), total.kept(), "every way inside was read whole, so nothing is kept");
    }

    /**
     * What a walk carries from one application to the next is what every application before it
     * read. A decision on it is about no position — any of them, as far as this reading goes — and
     * a run deciding it reads it beside the call it charges, so every combination stays.
     */
    @Test
    void aDecisionOnWhatTheWalkCarriedKeepsEveryCombination() {
        Measured total = measured(CALLS.formatted("""
                Yen(List.fold((sum, c) -> {
                        let x = charge(plan, c).value
                        if sum > 100 then sum else sum + x
                    }, 0, calls))"""), "total");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, total.owed(),
                "the cap reads what the calls before were charged, on whichever plan");
        assertEquals(Map.of("Free × Premium", Set.of(new WhyKept.ADecisionNothingNames()),
                        "Paid × Premium", Set.of(new WhyKept.ADecisionNothingNames())),
                total.kept(), "a normal call reads the plan on a way read whole");
    }

    /**
     * An operation that stops at the first element its function holds of applies it to a later
     * element only where every earlier one failed — which is what those applications read, the
     * plan among it. A way inside is written without that, and every combination stays.
     *
     * <p>The element found is handed out whole, so nothing decides on what the operation answered
     * and what is owed is what the ways inside the function say.
     */
    @Test
    void anOperationThatStopsAtAnAnswerKeepsEveryCombination() {
        Measured pick = measured(PICK, "pick");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, pick.owed(),
                "a premium call is reached past the calls that did not hold on the plan");
    }

    /** A combination picked out of every element by an operation that stops at an answer. */
    private static final String PICK = """
            module probe.pick

            data Free
            data Paid
            data Plan = Free | Paid
            data Normal
            data Premium
            data Dest = Normal | Premium
            data Call = { dest: Dest, seconds: Int }
            data Picked = { call: Call? }

            behavior pick : (plan: Plan, calls: List<Call>) -> Picked
                constructs Picked

            let pick (plan, calls) =
                Picked { call = List.find(c -> premiumOrPaid(plan, c), calls) }

            let premiumOrPaid (plan: Plan, call: Call): Bool =
                match call.dest with
                    | Premium -> true
                    | Normal ->
                        match plan with
                            | Free -> false
                            | Paid -> true

            example pick
                | (Free, [Call { dest = Premium, seconds = 60 }])
                    -> Picked { call = Call { dest = Premium, seconds = 60 } }
                | (Free, [Call { dest = Normal, seconds = 60 }]) -> Picked { }
            """;

    /**
     * A combination kept because the ways inside a function were read as a whole says which
     * function, where it is written and which use of it falls short — under each combination no
     * row is in, and in the document beside every one kept.
     */
    @Test
    void aCombinationKeptByAFunctionReadAsAWholeSaysWhichFunction() {
        Measured pick = measured(PICK, "pick");
        String function = "c -> premiumOrPaid";
        int line = 1;
        int column = 0;
        for (String each : PICK.lines().toList()) {
            if (each.contains(function)) {
                column = each.indexOf(function) + 1;
                break;
            }
            line++;
        }
        String place = line + ":" + column;

        for (Set<WhyKept> why : pick.kept().values()) {
            assertEquals(1, why.size(), () -> "kept by the function alone: " + why);
            WhyKept.AFunctionReadAsAWhole kept = assertInstanceOf(
                    WhyKept.AFunctionReadAsAWhole.class, why.iterator().next());
            assertEquals(List.of(new WhyKept.Shortfall.ToSomeOfTheElements("List.find",
                    HowAClosureIsApplied.UNTIL_ONE_HOLDS)), kept.shortfalls());
        }
        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, pick.kept().keySet(),
                "no way inside the function was read whole");

        List<String> lines = pick.human().lines().toList();
        int gaps = 0;
        for (int at = 0; at < lines.size(); at++) {
            if (lines.get(at).contains("no row is in `") && lines.get(at).contains(" with `")) {
                gaps++;
                assertEquals("          · kept: the ways inside the function at " + place
                                + " were read as a whole: `List.find` applies it to each"
                                + " element only until one application holds",
                        lines.get(at + 1), "under " + lines.get(at));
            }
        }
        assertEquals(2, gaps, "the rows are on Free, so both Paid combinations are gaps");

        JsonNode json = pick.json();
        assertEquals(List.of(), DocumentShape.of(json).wrong(), "what the schema refuses");
        Set<String> written = new LinkedHashSet<>();
        for (JsonNode module : json.get("modules")) {
            for (JsonNode behavior : module.get("behaviors")) {
                for (JsonNode between : behavior.get("partition").get("pairs").get("between")) {
                    for (JsonNode kept : between.get("kept")) {
                        JsonNode by = kept.get("by").get(0);
                        assertEquals("a_function_read_as_a_whole", by.get("reason").asString());
                        JsonNode shortfall = by.get("shortfalls").get(0);
                        assertEquals(List.of("to_some_of_the_elements", "List.find",
                                        "until_one_holds"),
                                List.of(shortfall.get("kind").asString(),
                                        shortfall.get("operation").asString(),
                                        shortfall.get("applied").asString()));
                        assertEquals(place, by.get("at").get("line").asInt() + ":"
                                + by.get("at").get("column").asInt());
                        written.add(kept.get("one").asString() + " × "
                                + kept.get("other").asString());
                    }
                }
            }
        }
        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, written,
                "every combination kept is written, a row in it or not");
    }

    /**
     * Applied to every element of what another operation answered, the function is applied to the
     * elements that operation let through, which its own function decided. A way inside is written
     * without that, and every combination stays.
     *
     * <p>Here the filter reads the plan alone, so nothing but the ways inside the charging
     * function reads the destination: a premium call is charged only on the plan the filter let
     * it through on, and that is what is owed.
     */
    @Test
    void aFunctionOverWhatAnotherOperationAnsweredKeepsEveryCombination() {
        Measured total = measured("""
                module probe.paying

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Call = { dest: Dest, seconds: Int }
                data Yen = Int

                behavior total : (plan: Plan, calls: List<Call>) -> Yen
                    constructs Yen

                let total (plan, calls) = {
                    let kept = List.filter(c -> paying(plan), calls)
                    Yen(List.fold((sum, c) -> sum + charge(plan, c).value, 0, kept)
                            + List.length(kept))
                }

                let paying (plan: Plan): Bool =
                    match plan with
                        | Free -> false
                        | Paid -> true

                let charge (plan: Plan, call: Call): Yen =
                    match call.dest with
                        | Premium -> Yen(call.seconds)
                        | Normal ->
                            match plan with
                                | Free -> Yen(0)
                                | Paid -> Yen(call.seconds)

                example total
                    | (Paid, [Call { dest = Premium, seconds = 60 }]) -> Yen(61)
                    | (Free, [Call { dest = Premium, seconds = 60 }]) -> Yen(0)
                """, "total");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, total.owed(),
                "a call is charged only on the plan the filter let it through on");
        assertEquals(Set.of("List.fold"), total.shortOf(),
                "the filter is applied to each call, and the fold to what the filter let through");
    }

    /**
     * A helper that calls itself over a list stops where an element ends its walk, so it goes on
     * to an element only where the ones before did not — which is what they read, the plan among
     * it. Called inside a function applied to each element, the forks in it are still reached past
     * the elements before, and nothing about them is narrowed: what is owed of the plan with a
     * leg's destination is every combination of them, or nothing where the two are not measured
     * together at all.
     */
    @Test
    void aHelperThatStopsAtAnElementInsideAFunctionNarrowsNothing() {
        Measured total = measured("""
                module probe.legs

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Leg = { dest: Dest }
                data Call = { legs: List<Leg> }
                data Yen = Int

                behavior total : (plan: Plan, calls: List<Call>) -> Yen
                    constructs Yen

                let total (plan, calls) =
                    Yen(List.fold((sum, c) -> sum + firstPaid(plan, c.legs), 0, calls))

                partial let firstPaid (plan: Plan, legs: List<Leg>): Int =
                    match List.get(0, legs) with
                        | Some leg ->
                            match leg.dest with
                                | Premium -> 5
                                | Normal ->
                                    match plan with
                                        | Free -> firstPaid(plan, List.drop(1, legs))
                                        | Paid -> 1
                        | None -> 0

                example total
                    | (Free, [Call { legs = [Leg { dest = Premium }] }]) -> Yen(5)
                """, "total");

        Set<String> owed = total.owed();
        assertTrue(owed.isEmpty() || owed.containsAll(EVERY_PLAN_WITH_EVERY_DESTINATION),
                () -> "a premium leg is reached past the normal legs a free plan went on from: "
                        + owed);
    }

    /**
     * What kept a combination is said in one order whatever order it was found in, so that two
     * readings holding the same reasons say them alike.
     */
    @Test
    void whatKeptACombinationIsSaidInOneOrder() {
        PartitionEvidence.PairSpace.Between between = new PartitionEvidence.PairSpace.Between(
                new AxisId("order", "one"), new AxisId("order", "other"));
        PartitionEvidence.PairSpace.Cell cell =
                new PartitionEvidence.PairSpace.Cell(between, "a", "b");
        WhyKept rule = new WhyKept.ARuleNoDecisionReads(between.one());
        WhyKept named = new WhyKept.ADecisionNothingNames();
        WhyKept unread = new WhyKept.AWayReadInPart(
                PathAccess.Unsupported.Why.MORE_WAYS_IN_THAN_ARE_READ);

        List<WhyKept> one = new PartitionEvidence.PairSpace.Owed.Listed(List.of(cell),
                Map.of(cell, List.of(rule, named, unread))).kept().get(cell);
        List<WhyKept> other = new PartitionEvidence.PairSpace.Owed.Listed(List.of(cell),
                Map.of(cell, List.of(unread, rule, named, unread))).kept().get(cell);

        assertEquals(List.of(unread, named, rule), one);
        assertEquals(one, other, "found in another order, said in the same one, each once");
    }

    /** {@link #CALLS} with {@code body}, and {@code examples} as its rows in place of its own. */
    private static String calls(String body, String examples) {
        String model = CALLS.formatted(body);
        return model.substring(0, model.indexOf("example total")) + "example total\n" + examples;
    }

    /** What the fold over the calls reads, in the words {@link #CALLS} takes. */
    private static final String FOLD =
            "Yen(List.fold((sum, c) -> sum + charge(plan, c).value, 0, calls))";

    /**
     * A row whose list holds nothing makes no application, so it is in no combination of the plan
     * with a destination: no call was charged on it.
     */
    @Test
    void aRowWhoseListHoldsNothingIsInNoCombination() {
        Measured total = measured(calls(FOLD, """
                    | (Free, [Call { dest = Premium, seconds = 60 }]) -> Yen(60)
                    | (Free, [Call { dest = Normal, seconds = 60 }]) -> Yen(0)
                    | (Paid, []) -> Yen(0)
                """), "total");

        assertEquals(A_NORMAL_CALL_READS_THE_PLAN, total.owed());
        assertEquals(List.of(Set.of("Paid", "Normal")), total.leftClasses(),
                "the paid row charged no call, so a normal call on a paid plan is still to write");
    }

    /**
     * A list holding a premium call and a normal one is two applications. What each reads is read
     * apart, so the premium call is not taken as read beside the plan the normal one read.
     */
    @Test
    void twoElementsOfOneListAreTwoApplications() {
        Measured total = measured(calls(FOLD, """
                    | (Free, [Call { dest = Premium, seconds = 60 }, Call { dest = Normal, seconds = 60 }])
                        -> Yen(60)
                    | (Paid, [Call { dest = Premium, seconds = 60 }, Call { dest = Normal, seconds = 60 }])
                        -> Yen(120)
                """), "total");

        assertEquals(A_NORMAL_CALL_READS_THE_PLAN, total.owed(),
                "no application reads the plan beside a premium call");
        assertEquals(List.of(), total.leftClasses(), "each list holds a normal call");
        assertEquals(Map.of(), total.kept());
    }

    /**
     * One function two operations apply is read a use at a time: what keeps it whole is the use
     * that is not each element's, and the one that is is not named for it.
     */
    @Test
    void aFunctionTwoOperationsApplyNamesTheOneThatFallsShort() {
        Measured pick = measured("""
                module probe.both

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Call = { dest: Dest, seconds: Int }
                data Picked = { call: Call?, flags: List<Bool> }

                behavior pick : (plan: Plan, calls: List<Call>) -> Picked
                    constructs Picked

                let pick (plan, calls) = {
                    let f: (Call) -> Bool = c -> premiumOrPaid(plan, c)
                    Picked { call = List.find(f, calls), flags = List.map(f, calls) }
                }

                let premiumOrPaid (plan: Plan, call: Call): Bool =
                    match call.dest with
                        | Premium -> true
                        | Normal ->
                            match plan with
                                | Free -> false
                                | Paid -> true

                example pick
                    | (Free, [Call { dest = Premium, seconds = 60 }])
                        -> Picked { call = Call { dest = Premium, seconds = 60 }, flags = [true] }
                """, "pick");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, pick.owed(),
                "the find reaches a premium call past the calls that did not hold on the plan");
        assertEquals(Set.of("List.find"), pick.shortOf(),
                "the map applies it to each call, and is not why it is read as a whole");
    }

    /**
     * A function applied directly as well as by an operation is applied by something that needs
     * no element, and narrows nothing: every combination stays, and no operation is named as what
     * kept it — the fold applies it to each call and is not why.
     *
     * <p>The application written out is expanded where it is written, and what it decides there
     * is about the call it was handed, which no position names.
     */
    @Test
    void aFunctionAlsoAppliedDirectlyNarrowsNothing() {
        Measured total = measured(calls("""
                {
                    let step = (sum, c) -> sum + charge(plan, c).value
                    match List.get(0, calls) with
                        | Some first -> Yen(List.fold(step, 0, calls) + step(0, first))
                        | None -> Yen(0)
                }""", """
                    | (Free, [Call { dest = Premium, seconds = 60 }]) -> Yen(120)
                    | (Paid, [Call { dest = Normal, seconds = 60 }]) -> Yen(120)
                """), "total");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, total.owed());
        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION, total.kept().keySet(),
                "no way read whole reads any of them");
        assertTrue(total.shortOf().stream().noneMatch("List.fold"::equals),
                () -> "the fold is not why: " + total.kept());
    }

    /**
     * One function applied to each element of two lists of the input is applied to an element of
     * one of them at a time, and reads within that application what it would over either.
     */
    @Test
    void aFunctionOverTwoListsOfTheInputIsReadAnApplicationAtATime() {
        Measured total = measured("""
                module probe.two

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Call = { dest: Dest, seconds: Int }
                data Yen = Int

                behavior total : (plan: Plan, calls: List<Call>, more: List<Call>) -> Yen
                    constructs Yen

                let total (plan, calls, more) = {
                    let step = (sum, c) -> sum + charge(plan, c).value
                    Yen(List.fold(step, 0, calls) + List.fold(step, 0, more))
                }

                let charge (plan: Plan, call: Call): Yen =
                    match call.dest with
                        | Premium -> Yen(call.seconds)
                        | Normal ->
                            match plan with
                                | Free -> Yen(0)
                                | Paid -> Yen(call.seconds)

                example total
                    | (Free, [Call { dest = Premium, seconds = 60 }], []) -> Yen(60)
                """, "total");

        assertEquals(Map.of(), total.kept(), () -> "kept: " + total.kept());
    }

    /**
     * A use that falls short is said by the operation the author wrote: {@code Set.fold}, and not
     * the fold over a list the library makes of the set, which no author wrote.
     *
     * <p>Over a set made of the input's list, whose elements are no position of the input, so the
     * ways inside are read as a whole.
     */
    @Test
    void aFunctionIsSaidToBePassedToTheOperationTheAuthorWrote() {
        Measured total = measured("""
                module probe.rates

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Yen = Int

                behavior total : (plan: Plan, dests: List<Dest>) -> Yen
                    constructs Yen

                let total (plan, dests) =
                    Yen(Set.fold((sum, d) -> sum + rate(plan, d), 0, Set.fromList(dests)))

                let rate (plan: Plan, dest: Dest): Int =
                    match dest with
                        | Premium -> 5
                        | Normal ->
                            match plan with
                                | Free -> 0
                                | Paid -> 1

                example total
                    | (Free, [Premium]) -> Yen(5)
                """, "total");

        assertEquals(Set.of("Set.fold"), total.shortOf(), () -> "kept: " + total.kept());
    }

    /**
     * And a helper of another module is expanded where the author called it, so the operation its
     * body hands the function to is one the author did not write: what they passed it to is the
     * helper.
     */
    @Test
    void aFunctionHandedOnByAnotherModulesHelperIsSaidToBePassedToTheHelper() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module probe.pickers

                let firstOver (p: (Int) -> Bool, xs: List<Int>): Option<Int> = List.find(p, xs)
                """, """
                module probe.picking

                import probe.pickers ( firstOver )

                data Free
                data Paid
                data Plan = Free | Paid
                data Picked = { amount: Int? }

                behavior pick : (plan: Plan, amounts: List<Int>) -> Picked
                    constructs Picked

                let pick (plan, amounts) =
                    Picked { amount = firstOver(a -> paidOver(plan, a), amounts) }

                let paidOver (plan: Plan, amount: Int): Bool =
                    match plan with
                        | Free -> false
                        | Paid -> amount > 100

                example pick
                    | (Paid, [101]) -> Picked { amount = 101 }
                """), ModulePath.EMPTY);
        Measured pick = measured(compilation, "probe.picking", "pick");

        assertEquals(Set.of("probe.pickers.firstOver"), pick.shortOf(),
                () -> "kept: " + pick.kept());
    }

    /**
     * A function inside one whose applications are not each element's is inside that one's as
     * well, and a way to a fork in it is written without what that one was written without.
     */
    @Test
    void aFunctionInsideOneThatStopsAtAnAnswerKeepsEveryCombination() {
        Measured pick = measured("""
                module probe.orders

                data Free
                data Paid
                data Plan = Free | Paid
                data Normal
                data Premium
                data Dest = Normal | Premium
                data Call = { dest: Dest, seconds: Int }
                data Order = { calls: List<Call> }
                data Picked = { order: Order? }

                behavior pick : (plan: Plan, orders: List<Order>) -> Picked
                    constructs Picked

                let pick (plan, orders) = Picked { order = List.find(
                        o -> List.fold((last, c) -> premiumOrPaid(plan, c), false, o.calls),
                        orders) }

                let premiumOrPaid (plan: Plan, call: Call): Bool =
                    match call.dest with
                        | Premium -> true
                        | Normal ->
                            match plan with
                                | Free -> false
                                | Paid -> true

                example pick
                    | (Free, [Order { calls = [Call { dest = Premium, seconds = 60 }] }])
                        -> Picked { order = Order { calls = [Call { dest = Premium, seconds = 60 }] } }
                """, "pick");

        assertEquals(EVERY_PLAN_WITH_EVERY_DESTINATION,
                pick.owedBetween("plan", "orders[*].calls[*].dest"),
                "an order's calls are read only where the orders before it held on none");
        assertEquals(Set.of("List.find"), pick.shortOf(),
                "the fold is applied to each call, inside the function the find stops at");
    }

    /**
     * Inside a function applied to each element, a fork reached more ways than are read is read
     * without what held above it, as anywhere else — the destination's arm among it. A way read so
     * is written without more than the element, so every combination with what it reads stays.
     */
    @Test
    void aForkInsideAFunctionReachedMoreWaysThanAreReadKeepsEveryCombination() {
        Measured fork = measured("""
                module probe.forks

                data Normal
                data Premium
                data Dest = Normal | Premium
                data Call = { dest: Dest }
                data In = { a: Int, b: Int, c: Int, usage: Int }
                data Fee = Int

                behavior total : (i: In, calls: List<Call>) -> Fee
                    constructs Fee

                let total (i, calls) = Fee(List.fold((sum, c) -> sum + charge(i, c).value, 0, calls))

                let charge (i: In, call: Call): Fee = {
                    guard i.a > 1 || i.a < -1 else Fee(1)
                    guard i.b > 1 || i.b < -1 else Fee(2)
                    guard i.c > 1 || i.c < -1 else Fee(3)
                    match call.dest with
                        | Premium -> Fee(1000)
                        | Normal ->
                            if i.usage <= 100 || i.usage > 1000 || i.usage == 500
                            then Fee(300) else Fee(800)
                }

                example total
                    | (In { a = 2, b = 2, c = 2, usage = 0 }, [Call { dest = Premium }]) -> Fee(1000)
                """, "total");

        assertEquals(Set.of("i.usage/x <= 100 × Normal", "i.usage/= 500 × Normal",
                        "i.usage/100 < x <= 1000 and x /= 500 × Normal",
                        "i.usage/1000 < x × Normal",
                        "i.usage/x <= 100 × Premium", "i.usage/= 500 × Premium",
                        "i.usage/100 < x <= 1000 and x /= 500 × Premium",
                        "i.usage/1000 < x × Premium"),
                fork.owedBetween("i.usage", "calls[*].dest"),
                "the ways into the usage's arm were read without the destination above them");
        // And by the usage's rules, which no decision on a way read whole reads: the ways to them
        // are the ones past the bound.
        Set<WhyKept> pastTheBound = Set.of(
                new WhyKept.AWayReadInPart(PathAccess.Unsupported.Why.MORE_WAYS_IN_THAN_ARE_READ),
                new WhyKept.ARuleNoDecisionReads(new AxisId("total", "i.usage")));
        assertTrue(!fork.kept().isEmpty()
                        && fork.kept().values().stream().allMatch(pastTheBound::equals),
                () -> "kept by the ways past the bound: " + fork.kept());
    }

    private record Measured(String behavior, Compilation compilation,
                            PartitionEvidence evidence) {

        /** Every combination owed, as the two classes it is of. */
        Set<String> owed() {
            Set<String> out = new LinkedHashSet<>();
            for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
                out.addAll(cellsOf(pair));
            }
            return out;
        }

        /** The combinations owed between the two numbers named. */
        Set<String> owedBetween(String one, String other) {
            for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
                if (pair.between().one().term().equals(one)
                        && pair.between().other().term().equals(other)) {
                    return cellsOf(pair);
                }
            }
            throw new AssertionError("no relation between " + one + " and " + other + ": "
                    + evidence.pairs());
        }

        private static Set<String> cellsOf(PartitionEvidence.PairSpace.AxisPair pair) {
            Set<String> out = new LinkedHashSet<>();
            PartitionEvidence.PairSpace.Owed.Listed listed = assertInstanceOf(
                    PartitionEvidence.PairSpace.Owed.Listed.class, pair.owed());
            for (PartitionEvidence.PairSpace.Cell cell : listed.cells()) {
                out.add(cell.one() + " × " + cell.other());
            }
            return out;
        }

        /** What kept each combination no way read whole reads, as the two classes it is of. */
        Map<String, Set<WhyKept>> kept() {
            Map<String, Set<WhyKept>> out = new LinkedHashMap<>();
            for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
                PartitionEvidence.PairSpace.Owed.Listed listed = assertInstanceOf(
                        PartitionEvidence.PairSpace.Owed.Listed.class, pair.owed());
                listed.kept().forEach((cell, why) ->
                        out.put(cell.one() + " × " + cell.other(), Set.copyOf(why)));
            }
            return out;
        }

        /** The uses that fall short of each function read as a whole that kept a combination:
         *  the operation that does, or {@code elsewhere} for a use that is no operation's. */
        Set<String> shortOf() {
            Set<String> out = new LinkedHashSet<>();
            for (Set<WhyKept> why : kept().values()) {
                for (WhyKept each : why) {
                    if (each instanceof WhyKept.AFunctionReadAsAWhole function) {
                        for (WhyKept.Shortfall shortfall : function.shortfalls()) {
                            out.add(switch (shortfall) {
                                case WhyKept.Shortfall.NotOnlyByOperations() -> "elsewhere";
                                case WhyKept.Shortfall.ToSomeOfTheElements(var operation,
                                        var _) -> operation;
                                case WhyKept.Shortfall.OverNoPosition(var operation) ->
                                        operation;
                            });
                        }
                    }
                }
            }
            return out;
        }

        String human() {
            return AdequacyReport.of(compilation).human(
                    SourceRendering.namedByIdentity(compilation.texts()));
        }

        JsonNode json() {
            return JsonMapper.builder().build().readTree(AdequacyReport.of(compilation).json(
                    SourceRendering.namedByIdentity(compilation.texts())));
        }

        List<?> left() {
            return evidence.pairs().left(behavior);
        }

        /** The combinations no row is in, each as its two classes. */
        List<Set<String>> leftClasses() {
            return evidence.pairs().left(behavior).stream()
                    .map(each -> each.classes().stream()
                            .map(ClassOfAPosition::classId)
                            .collect(Collectors.toSet()))
                    .toList();
        }

        CombinationCriterion criterion() {
            String module = compilation.modules().get(0);
            return CombinationCriterion.of(compilation.db().ask(new Adequacy.Interacts(module))
                    .value().get(behavior), evidence);
        }

        List<String> pairGaps() {
            return AdequacyReport.of(compilation).adequacyGaps().stream()
                    .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                    .map(each -> each.about().toString())
                    .toList();
        }
    }

    private static Measured measured(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        return measured(compilation, compilation.modules().get(0), behavior);
    }

    private static Measured measured(Compilation compilation, String module, String behavior) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles and its rows hold");
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(module)).value();
        assertNotNull(all, "the model under test is measured");
        return new Measured(behavior, compilation, all.get(behavior));
    }
}
