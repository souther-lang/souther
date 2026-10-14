package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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

        List<?> left() {
            return evidence.pairs().left(behavior);
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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles and its rows hold");
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test is measured");
        return new Measured(behavior, compilation, all.get(behavior));
    }
}
