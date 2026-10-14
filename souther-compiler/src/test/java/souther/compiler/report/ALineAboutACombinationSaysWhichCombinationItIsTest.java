package souther.compiler.report;

import souther.compiler.coverage.SourceOutcome;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionRuleReading;
import souther.compiler.reading.Condition;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line about a combination of a body's decisions says which combination it is, and the one it
 * says is the one the line is about.
 *
 * <p>Held against the combination's identity, which is what the document's {@code obligationId}
 * is written from, and not against the ways the conditions were read off: those are the readings'
 * own source, and a check built from them would agree with whatever they said.
 */
class ALineAboutACombinationSaysWhichCombinationItIsTest {

    /** Two decisions meeting at one value, six combinations: two no row makes, and one only the
     *  row that does not hold makes. */
    private static final String MEETING = """
            module example.meeting

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Fee = Int

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(1)
            """;

    /** One value called on both inputs: the decisions are one construct in two calls. */
    private static final String TWICE = """
            module example.twice

            data Gold
            data Plain
            data Kind = Gold | Plain
            data Fee = Int

            behavior pairFee : (first: Kind, second: Kind) -> Fee
                constructs Fee

            let pairFee (first, second) =
                Fee(price(first) + price(second))

            let price (kind: Kind): Int =
                match kind with
                    | Gold -> 10
                    | Plain -> 1

            example pairFee
                | (Gold, Gold)   -> Fee(20)
            """;

    /**
     * Each combination a line is about is said by exactly the conditions it settles: a case by the
     * arm written for it, a comparison by the comparison and the way it came out, each in the copy
     * the condition is of.
     */
    @Test
    void whatALineSaysIsTheCombinationItIsAbout() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MEETING);
        Set<ObligationIdentity.OfACombinationOfDecisions> about = aboutOf(behavior);
        assertEquals(3, about.size(), () -> "two no row makes and one only a failing row makes: "
                + about);

        for (ObligationIdentity.OfACombinationOfDecisions combination : about) {
            List<List<AdequacyReport.ShownCondition>> ways = behavior.waysOf(combination);
            assertEquals(1, ways.size(), () -> "one way to " + combination + ": " + ways);
            assertEquals(said(combination.settled()), said(ways.getFirst()),
                    () -> "the lines under " + combination + " say what it settles");
        }
    }

    /**
     * Three combinations through one value called twice read as three, and the page prints three
     * different blocks.
     *
     * <p>The case and the place it is written are the same in both calls, so what tells
     * {@code (Gold, Plain)} from {@code (Plain, Gold)} is which call each case was taken in.
     */
    @Test
    void combinationsThroughOneValueCalledTwiceReadApart() {
        Compilation compilation = measured(TWICE);
        AdequacyReport.BehaviorReport behavior = AdequacyReport.of(compilation).modules()
                .getFirst().behaviors().getFirst();
        Set<ObligationIdentity.OfACombinationOfDecisions> about = aboutOf(behavior);
        assertEquals(3, about.size(), () -> "the three combinations with a `Plain`: " + about);

        // As sets, because the order a way met its conditions in is no part of which combination
        // it is: (Gold, Plain) said in one order and (Plain, Gold) in the other read alike.
        Set<Set<AdequacyReport.ShownCondition>> read = new HashSet<>();
        for (ObligationIdentity.OfACombinationOfDecisions combination : about) {
            read.add(Set.copyOf(behavior.waysOf(combination).getFirst()));
        }
        assertEquals(about.size(), read.size(), () -> "each reads as its own: " + read);

        List<Set<String>> blocks = blocksOf(AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())));
        assertEquals(3, blocks.size(), () -> "a block per combination: " + blocks);
        assertEquals(3, new HashSet<>(blocks).size(), () -> "and no two alike: " + blocks);
    }

    /**
     * The warning about a rule through one value called twice marks each call with the arm the
     * rule goes through in it, so the rules that go one way in one call and the other way in the
     * next are told apart where the page tells the combinations apart.
     *
     * <p>A warning cannot write a place into its words, so the construct alone is marked with both
     * arms for both rules; what pairs each arm with its call is the mark on the call.
     */
    @Test
    void theWarningAboutARuleThroughAValueCalledTwiceMarksEachCall() {
        Compilation compilation = Compilation.ofSource(TWICE, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        List<Set<String>> calls = new ArrayList<>();
        for (Located each : compilation.warnings()) {
            if (!(each.diagnostic().said() instanceof ExampleMessage.NoRowTakesADecisionRule)) {
                continue;
            }
            Set<String> marked = new HashSet<>();
            for (LabeledRegion label : each.diagnostic().secondary()) {
                if (label.said() instanceof ExampleMessage.TheRuleGoesThroughAnArmInThisCall) {
                    marked.add(label.place() + " " + label.said());
                }
            }
            calls.add(marked);
        }
        assertEquals(3, calls.size(), () -> "the three rules with a `Plain`: " + calls);
        for (Set<String> marked : calls) {
            assertEquals(2, marked.size(), () -> "each call marked with its arm: " + marked);
        }
        assertEquals(3, new HashSet<>(calls).size(), () -> "and no two alike: " + calls);
    }

    /** Two ways naming the same conditions in two orders are said once, in the first one's order. */
    @Test
    void aWayThatReadsLikeAnEarlierOneIsSaidOnce() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MEETING);
        List<AdequacyReport.ShownCondition> way =
                behavior.waysOf(aboutOf(behavior).iterator().next()).getFirst();
        assertTrue(way.size() > 1, () -> "a way of more than one condition: " + way);

        assertEquals(List.of(way), AdequacyReport.distinctWays(List.of(way, way.reversed())));
        assertEquals(List.of(way.reversed()),
                AdequacyReport.distinctWays(List.of(way.reversed(), way)));
    }

    /**
     * What each condition of a combination is, in the words a reading of it is checked by: which
     * construct, which way, and which copy.
     */
    private static Set<String> said(Set<Condition> settled) {
        Set<String> out = new LinkedHashSet<>();
        for (Condition each : settled) {
            out.add(switch (each) {
                case Condition.Case(var _, var names) -> "case " + names;
                case Condition.Side side -> "comparison "
                        + side.statedAt().origin() + " " + side.held() + " "
                        + ModelOccurrence.statedAt(side.statedAt()).orElseThrow().lineage();
                case Condition.Arm arm -> "arm " + arm.arm().origin() + " " + arm.arm().part();
            });
        }
        return out;
    }

    /** The same words, read off what a page was handed. */
    private static Set<String> said(List<AdequacyReport.ShownCondition> way) {
        Set<String> out = new LinkedHashSet<>();
        for (AdequacyReport.ShownCondition each : way) {
            out.add(switch (each.read()) {
                case DecisionRuleReading.AForkTookAnArm(var arm, var _)
                        when arm.outcome() instanceof SourceOutcome.Matched(var cases) ->
                        "case " + cases.stream().map(TypeSymbol::name).sorted().toList();
                case DecisionRuleReading.AForkTookAnArm(var arm, var _) ->
                        "arm " + arm.obligation().origin() + " " + arm.obligation().part();
                case DecisionRuleReading.AComparisonCameOut(var comparison, var held, var within) ->
                        "comparison " + comparison.obligation().origin() + " " + held + " "
                                + within;
                default -> "nothing to send a reader to: " + each.read();
            });
        }
        return out;
    }

    /** The combinations a line under {@code behavior} is about. */
    private static Set<ObligationIdentity.OfACombinationOfDecisions> aboutOf(
            AdequacyReport.BehaviorReport behavior) {
        Set<ObligationIdentity.OfACombinationOfDecisions> out = new LinkedHashSet<>();
        for (AdequacyReport.ReportedFinding each : behavior.reported()) {
            if (each.finding().about() instanceof About.ACombinationNoRowMakes(var combination)) {
                out.add(combination);
            }
        }
        for (CoveredOnlyByRowsThatDoNotHold.Covered<ObligationIdentity.OfACombinationOfDecisions>
                each : CoveredOnlyByRowsThatDoNotHold.combinationsOf(
                        behavior.evidence().combinations())) {
            out.add(each.obligation());
        }
        return out;
    }

    /** The lines a page writes under each line about a combination, in no order. */
    private static List<Set<String>> blocksOf(String page) {
        List<Set<String>> out = new ArrayList<>();
        Set<String> block = null;
        for (String line : page.lines().toList()) {
            if (line.contains("this combination of the decisions")) {
                block = new HashSet<>();
                out.add(block);
            } else if (block != null && line.startsWith("          ")) {
                block.add(line.strip());
            } else {
                block = null;
            }
        }
        return out;
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String source) {
        return AdequacyReport.of(measured(source)).modules().getFirst().behaviors().getFirst();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
