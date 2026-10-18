package souther.compiler.check;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard whose departure the guards above it have already ruled out is proven unreachable.
 *
 * <p>The reading this asks was already being made — the invariant-discharge check threads the same
 * conditions and stops at a place they cannot all hold — and it stopped there rather than saying so,
 * while every measure derived the same question again from the declarations alone. Nothing arrives
 * at {@code a.value >= 6000} when everything that got this far is under 5000, and the declarations
 * cannot see that: they say only that an {@code Amount} runs from 0 to a million.
 *
 * <p>The second guard is what the first one leaves, so this is measured against the first: one
 * model, two departures, and only the second of them is proven. A model where nothing is proven
 * would pass a reading that proves everything, and a model where everything is would pass one that
 * proves nothing.
 */
class AGuardTheGuardsAboveItRuleOutIsProvenTest {

    private static final String TWO_GUARDS = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                guard a.value < 6000 else Free
                Charged { yen = 500 }
            }
            """;

    /** The same, with a second guard the first one does not settle. */
    private static final String TWO_LIVE_GUARDS = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                guard a.value > 100 else Free
                Charged { yen = 500 }
            }
            """;

    /** A guard whose departure is outside what the declaration admits at all. */
    private static final String OUTSIDE_THE_DECLARATION = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 2000000 else Free
                Charged { yen = 500 }
            }
            """;

    /**
     * What was said about every arm of {@code charge}.
     *
     * <p>Read as a collection and not by position. The walk numbers an inner fork while it is
     * inside the arm that holds it, so which index a departure lands on is a fact about the
     * traversal; what is being measured is which arms are proven, and that is the same however
     * they are ordered.
     */
    private static List<Reachability> armsOf(String source) {
        return armsOf(source, "charge");
    }

    private static List<Reachability> armsOf(String source, String behavior) {
        Compilation c = Compilation.ofSource(source, "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        assertTrue(byBehavior != null && byBehavior.containsKey(behavior),
                "the module answers nothing about `" + behavior + "`");
        return byBehavior.get(behavior).found().entrySet().stream()
                .filter(each -> each.getKey() instanceof ControlPlace.Arm)
                .map(Map.Entry::getValue)
                .toList();
    }

    private static List<Proof> provenIn(String source) {
        return provenIn(source, "charge");
    }

    private static List<Proof> provenIn(String source, String behavior) {
        return armsOf(source, behavior).stream()
                .filter(Reachability.Unreachable.class::isInstance)
                .map(each -> ((Reachability.Unreachable) each).proof())
                .toList();
    }

    @Test
    void aDepartureNothingCanTakeIsProvenAndNothingElseIs() {
        assertEquals(4, armsOf(TWO_GUARDS).size(), "two guards make two forks of two arms");
        List<Proof> proven = provenIn(TWO_GUARDS);
        assertEquals(1, proven.size(),
                "the second guard's departure, and not the first's and neither of the arms it "
                        + "guards");
        assertEquals(2, WhatAnAnswerSays.conditionsIn(proven.get(0)).size(),
                "both guards are on the way to it, and the proof says which they are");
    }

    @Test
    void aSecondGuardTheFirstDoesNotSettleIsLeftAsItIs() {
        assertEquals(4, armsOf(TWO_LIVE_GUARDS).size());
        assertEquals(List.of(), provenIn(TWO_LIVE_GUARDS),
                "a value between 100 and 5000 takes neither departure, and one under 100 takes the "
                        + "second — so nothing here is an arm nothing reaches");
    }

    /**
     * And it is shown by what the position holds, not by the conditions on the way.
     *
     * <p>Two things can contradict a branch and they send an author to different places. Nothing
     * stands above this guard, so "the conditions on the way cannot all hold" would send them
     * looking for a guard that is not there; what rules it out is the declaration, and the proof
     * names it and what it leaves.
     */
    @Test
    void aDepartureOutsideWhatTheDeclarationAdmitsIsShownByTheDeclaration() {
        assertEquals(2, armsOf(OUTSIDE_THE_DECLARATION).size(),
                "one guard makes one fork of two arms");
        List<Proof> proven = provenIn(OUTSIDE_THE_DECLARATION);
        assertEquals(1, proven.size(), "an `Amount` stops at a million, so nothing reaches two");
        assertEquals("a 0..1000000",
                WhatAnAnswerSays.positionOutrunIn(proven.get(0)),
                "the position, and what its rules leave it");
    }

    /**
     * A departure between the values a declaration names is shown by those values.
     *
     * <p>{@code 2} lies inside where the three run between, so the range alone would not rule it
     * out; the proof carries the values, which do.
     */
    @Test
    void aDepartureBetweenTheValuesADeclarationNamesIsShownByThem() {
        List<Proof> proven = provenIn("""
                module d

                data Low
                data High
                data Odd = Int
                    invariant value == 1 || value == 3 || value == 7

                behavior charge : (c: Odd) -> Low | High
                let charge (c) = if c.value == 2 then Low else High
                """);

        assertEquals(1, proven.size(), "no `Odd` is two");
        String said = WhatAnAnswerSays.positionOutrunIn(proven.get(0));
        assertTrue(said != null && said.startsWith("c ") && said.endsWith("[1, 3, 7]"),
                () -> "the position, and the values its rule names: " + said);
    }

    /**
     * And a departure at the value a declaration refuses is shown by that refusal.
     *
     * <p>Nothing bounds a {@code Level} at either end, so there is no range to name, and nothing
     * stands above the guard either: said as the conditions on the way, the proof would send an
     * author to look for a guard that is not there.
     */
    @Test
    void aDepartureAtAValueADeclarationRefusesIsShownByTheRefusal() {
        List<Proof> proven = provenIn("""
                module d

                data Level = Int invariant value /= 5
                behavior charge : (x: Level) -> String
                let charge (x) = if x.value == 5 then "never" else "other"
                """);

        assertEquals(1, proven.size(), "no `Level` is five");
        String said = WhatAnAnswerSays.positionOutrunIn(proven.get(0));
        assertTrue(said != null && said.startsWith("x ") && said.endsWith("~[5]"),
                () -> "the position, and the value its rule refuses: " + said);
    }

    /**
     * The two proofs are told apart, and by what does the work rather than by the shape of the
     * model.
     *
     * <p>The guard of #779 is inside what another guard left, and the declaration alone says
     * nothing against it — an `Amount` of 6000 is an ordinary one. So that proof is the conditions
     * on the way, and this one is not, and neither reads as the other.
     */
    @Test
    void andTheOneTheGuardsAboveRuleOutIsNot() {
        assertEquals(null, WhatAnAnswerSays.positionOutrunIn(provenIn(TWO_GUARDS).get(0)),
                "nothing about an `Amount` rules out six thousand; the guard above it does");
    }

    /** The same model with the guard nothing reaches taken out. */
    private static final String ONE_GUARD = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                Charged { yen = 500 }
            }
            """;

    private static String rowsAskedOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "d");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return souther.compiler.report.GeneratedRows.of(compilation, "d", "charge",
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    /**
     * A line the guards above it put nowhere divides nothing, so no class and no boundary comes off
     * it.
     *
     * <p>Measured against the model with that guard taken out rather than against a count. What is
     * being claimed is that the two models ask for the same work, and a count would pass a reading
     * that dropped the wrong two rows.
     */
    @Test
    void theModelAsksForWhatTheModelWithoutThatGuardAsksFor() {
        assertEquals(work(rowsAskedOf(ONE_GUARD)), work(rowsAskedOf(TWO_GUARDS)),
                "a guard whose departure nothing takes draws no line");
    }

    /**
     * The block less the lines that say a decision rule. A rule is said by every condition its way
     * consults, and the second guard is one the way past the first consults whether or not it
     * divides anything — so the two models' rules read differently while the rows asked for, and
     * the classes each is for, are the same.
     */
    private static String work(String block) {
        return block.lines().filter(line -> !line.startsWith("// fills a decision rule"))
                .collect(Collectors.joining("\n"));
    }

    /**
     * A call hands a library's own fork an argument one side of it can never take.
     *
     * <p>{@code Int.max} is a fork, and {@code Int.max(0, c.value)} over a {@code Count} never takes
     * the side that answers zero. It is not this author's to act on: the fork is written in another
     * module, and the same fork is alive wherever else that module is used. Its condition is no
     * rule of the model, but it is what the path runs through, so it is taken in and the arm this
     * call cannot reach is proven unreachable here — and nothing is reported, because the author
     * cannot take a branch out of another module.
     */
    private static final String A_LIBRARY_FORK = """
            module d

            data Count = Int invariant value >= 0
            data Small = Int invariant value >= 0

            behavior mk : (c: Count) -> Count | Small
                constructs Count, Small

            let mk (c) = {
                    guard (Int.max(0, c.value)) >= 1 else Small(0)
                    Count(Int.max(0, c.value))
                }
            """;

    @Test
    void aForkAnotherModuleWroteIsProvenHereAndNotToldAbout() {
        Compilation c = Compilation.ofSource(A_LIBRARY_FORK, "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        List<ControlPlace.Arm> proven = byBehavior.get("mk").found().entrySet().stream()
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .map(each -> each.getKey())
                .filter(ControlPlace.Arm.class::isInstance)
                .map(ControlPlace.Arm.class::cast)
                .toList();
        assertFalse(proven.isEmpty(),
                "the side of the library's fork this call cannot take is proven unreachable");
        assertTrue(c.db().ask(new Adequacy.DeadBranches("d")).reports().stream()
                        .noneMatch(report -> "E1327".equals(report.diagnostic().code())),
                "so nothing is reported: the author cannot take a branch out of another module");
    }

    /**
     * A condition read over a combinator this tree has expanded away leaves the arm as it was.
     *
     * <p>The tree every measure is taken over has the language's own combinators lowered into the
     * folds they are, and the rules about what a combinator does to a value are written against the
     * combinator. So a guard that goes through one is read here as the fold, what it establishes is
     * not what the operation establishes, and the arm comes out unsettled rather than proven either
     * way. That is the fail-open direction and it costs an obligation nobody can meet at worst.
     *
     * <p>The control beside it is a size, which is an intrinsic with no body to expand: a guard on
     * it is read here exactly as it is written, so this measures the combinator and not the reading
     * as a whole.
     */
    private static final String THROUGH_A_COMBINATOR = """
            module d

            data Name = String invariant String.length(value) >= 1
            data Ok
            data No

            behavior mk : (n: Name, xs: List<Int>) -> Ok | No

            let mk (n, xs) = {
                    guard List.length(List.filter(x -> x > 0, xs)) >= 1 else No
                    Ok
                }
            """;

    private static final String THROUGH_A_SIZE = """
            module d

            data Name = String invariant String.length(value) >= 1
            data Ok
            data No

            behavior mk : (n: Name, xs: List<Int>) -> Ok | No

            let mk (n, xs) = {
                    guard String.length(n.value) >= 0 else No
                    Ok
                }
            """;

    @Test
    void aConditionThroughACombinatorLeavesItsArmsUnsettled() {
        assertEquals(List.of(), provenIn(THROUGH_A_COMBINATOR, "mk"),
                "what the fold establishes is not what the operation does, so nothing is proven");
    }

    /**
     * And it says which of the two kinds of nothing it is.
     *
     * <p>A condition no rule here reads and one read to no effect leave what is known identical, so
     * the reading has to say which happened. Without it both come back as a branch nobody built a
     * value for, and this compiler's own limit is reported as a fact about the model.
     */
    @Test
    void andSaysThatItCouldNotReadTheCondition() {
        List<souther.compiler.reach.WhyUnsettled> why =
                armsOf(THROUGH_A_COMBINATOR, "mk").stream()
                        .filter(Reachability.Unsettled.class::isInstance)
                        .map(each -> ((Reachability.Unsettled) each).why())
                        .toList();
        assertTrue(why.stream().anyMatch(WhatAnAnswerSays::isAConditionNotRead),
                () -> "the fold is not a condition this reads: " + why);
    }

    @Test
    void whileASizeIsOneItDoesRead() {
        List<souther.compiler.reach.WhyUnsettled> why = armsOf(THROUGH_A_SIZE, "mk").stream()
                .filter(Reachability.Unsettled.class::isInstance)
                .map(each -> ((Reachability.Unsettled) each).why())
                .toList();
        assertTrue(why.stream().noneMatch(WhatAnAnswerSays::isAConditionNotRead),
                () -> "a size is read as it is written, so nothing here is unread: " + why);
    }

    @Test
    void andASizeIsReadExactlyAsItIsWritten() {
        // A `Name` is at least one character, so the departure at `>= 0` is one nothing takes. The
        // control for the case above: the reading is not silent everywhere, only where the tree has
        // put a fold in the way.
        assertEquals(1, provenIn(THROUGH_A_SIZE, "mk").size(),
                "a size is an intrinsic, so the guard on it is read as it is written");
    }

    @Test
    void nothingIsProvenReachable() {
        // Every route to `Reachable` is about the program — a run that went through, a rule that
        // settles it completely, a value put together — and this reading reads none of them. A
        // state the domains found no contradiction in is a state they had nothing to say about.
        for (String source : List.of(TWO_GUARDS, TWO_LIVE_GUARDS, OUTSIDE_THE_DECLARATION)) {
            for (Reachability each : armsOf(source)) {
                assertTrue(!(each instanceof Reachability.Reachable),
                        "this reading proves nothing arrives, never that something does");
            }
        }
    }

    /**
     * A condition whose shape this could not read may still be the whole of why nothing stands here,
     * and where it is, the proof names it.
     *
     * <p>The two questions this reading answers came apart when every value got an identity. A guard
     * over a value the body bound from something no form reads is a condition whose shape runs out —
     * there is no reading of what {@code Int.floorMod} answers where its divisor is no constant —
     * and it narrows the state all the same, through the subject the binding is. So it is not among
     * the reasons and among them at once: not read, and taken in.
     *
     * <p>Answered from the wrong one of the two, this proof said the readable guard cannot hold, and
     * that guard can hold perfectly well. A proof is a claim about the program; a limit of this
     * compiler is not, and the one must not be written out of the other.
     */
    @Test
    void aProofRestsOnAConditionWhoseShapeWasNotRead() {
        String source = """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged
                let charge (a) = {
                    let x = Int.floorMod(1000, a.value + 1)
                    guard a.value < 900 else Free
                    guard x < 5 else Free
                    guard x < 6 else Free
                    Charged { yen = 1 }
                }
                """;

        List<Proof> proven = provenIn(source, "charge");
        assertEquals(1, proven.size(), "nothing under five is six or more, whatever `x` is");
        List<PathDecision> why = WhatAnAnswerSays.conditionsIn(proven.get(0));
        assertEquals(3, why.size(),
                () -> "the guard over the answer is what rules this out, so it is named: " + why);

        // And the other half: the same guard is still one this reading did not read, which is what
        // an arm it leaves unsettled is owed as an explanation.
        assertTrue(armsOf(source, "charge").stream()
                        .filter(Reachability.Unsettled.class::isInstance)
                        .map(each -> ((Reachability.Unsettled) each).why())
                        .anyMatch(WhatAnAnswerSays::isAConditionNotRead),
                "its shape ran out, and an arm left unsettled by it says so");
    }

    /**
     * A divisor the least or greatest signed 64-bit number is a divisor all the same: what is asked
     * is whether the divisor itself fits, and the least such number is one whose magnitude does not.
     */
    @Test
    void theLeastAndGreatestDivisorsAreReadLikeAnyOther() {
        // How many departures nothing reaches. A remainder by a divisor above nought can be five or
        // six, so only the second guard's departure is out of reach, by the first. One by a divisor
        // below nought is never above nought, so both guards hold of every value.
        Map<String, Integer> unreachable = Map.of("9223372036854775807", 1,
                "0 - 9223372036854775807 - 1", 2);
        for (String divisor : List.of("9223372036854775807", "0 - 9223372036854775807 - 1")) {
            String source = """
                    module d

                    data Amount = Int invariant value >= 0 && value <= 1000
                    data Free
                    data Charged = { yen: Int }

                    behavior charge : (a: Amount) -> Free | Charged
                        constructs Charged
                    let charge (a) = {
                        let x = Int.floorMod(a.value, %s)
                        guard x < 5 else Free
                        guard x < 6 else Free
                        Charged { yen = 1 }
                    }
                    """.formatted(divisor);

            assertEquals(unreachable.get(divisor), provenIn(source, "charge").size(),
                    "what no value reaches, whatever `x` is: " + divisor);
            assertTrue(armsOf(source, "charge").stream()
                            .filter(Reachability.Unsettled.class::isInstance)
                            .map(each -> ((Reachability.Unsettled) each).why())
                            .noneMatch(WhatAnAnswerSays::isAConditionNotRead),
                    "every condition is read: " + divisor);
        }
    }

    /**
     * A remainder of a place moved by a number keeps what the guards say of it, written in the
     * guard or named first.
     *
     * <p>Read as the remainder of the place over two stretches, what a guard over the moved
     * remainder says is one of two things: {@code x < 5} is the place's remainder below four or at
     * six. Both are about one number, so a path holds them as the values of it they leave, and the
     * guards rule the same departure out however the remainder was spelled.
     */
    @Test
    void aGuardOverARemainderOfAMovedPlaceStillRulesOutWhatItRulesOut() {
        String named = """
                let x = Int.floorMod(a.value + 1, 7)
                guard x < 5 else Free
                guard x < 6 else Free
                """;
        String inline = """
                guard Int.floorMod(a.value + 1, 7) < 5 else Free
                guard Int.floorMod(a.value + 1, 7) < 6 else Free
                """;
        for (String guards : List.of(named, inline)) {
            assertEquals(1, provenIn(charging(guards), "charge").size(),
                    () -> "nothing under five is six or more, whatever `x` is:\n" + guards);
        }
        // A control: under four is no less under five, and nothing above settles the second.
        assertEquals(List.of(), provenIn(charging("""
                let x = Int.floorMod(a.value + 1, 7)
                guard x < 5 else Free
                guard x < 4 else Free
                """), "charge"));
    }

    /**
     * And what they say of the place's own remainder: a remainder of six moved by one is nought,
     * whichever of the two the guards name and however the moved one is spelled.
     */
    @Test
    void aGuardOverTheRemainderOfAPlaceRulesOutWhatItLeavesTheMovedRemainder() {
        List<String> eachWay = List.of("""
                guard Int.floorMod(a.value, 7) == 6 else Free
                guard Int.floorMod(a.value + 1, 7) /= 0 else Free
                """, """
                guard Int.floorMod(a.value, 7) == 6 else Free
                let x = Int.floorMod(a.value + 1, 7)
                guard x /= 0 else Free
                """, """
                guard Int.floorMod(a.value, 7) < 3 else Free
                let x = Int.floorMod(a.value + 1, 7)
                guard x == 0 else Free
                """);
        for (String guards : eachWay) {
            assertEquals(1, provenIn(charging(guards), "charge").size(),
                    () -> "the remainder the first leaves is one the second refuses:\n" + guards);
        }
    }

    /**
     * A remainder of a moved place compared with another value is the same stretches of the
     * place's remainder, each with the moved remainder there against the value — so what a guard
     * against a number left it reaches the guard against the value, named or written out.
     */
    @Test
    void aGuardOverAMovedRemainderAgainstAnotherValueKeepsWhatTheGuardsAboveSay() {
        for (String guards : List.of("""
                guard b.value >= 5 else Free
                let x = Int.floorMod(a.value + 1, 7)
                guard x < 5 else Free
                guard x < b.value else Free
                """, """
                guard b.value >= 5 else Free
                guard Int.floorMod(a.value + 1, 7) < 5 else Free
                guard Int.floorMod(a.value + 1, 7) < b.value else Free
                """, """
                guard b.value >= 7 else Free
                guard Int.floorMod(a.value + 3, 7) /= b.value else Free
                """)) {
            String source = """
                    module d

                    data Amount = Int invariant value >= 0 && value <= 1000
                    data Free
                    data Charged = { yen: Int }

                    behavior charge : (a: Amount, b: Amount) -> Free | Charged
                        constructs Charged
                    let charge (a, b) = {
                    %s    Charged { yen = 1 }
                    }
                    """.formatted(guards.indent(4));
            assertEquals(1, provenIn(source, "charge").size(),
                    () -> "under five and at least five, or at least seven, is apart:\n" + guards);
        }
    }

    /**
     * A choice between comparisons of two numbers is no set of values of either: one being small
     * says nothing of the other, so the second guard's departure is taken by a value the first let
     * through on the other number.
     */
    @Test
    void aChoiceOverTwoNumbersIsNotHeldAsTheValuesOfOne() {
        String source = """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount, b: Amount) -> Free | Charged
                    constructs Charged
                let charge (a, b) = {
                    guard a.value < 3 || b.value < 3 else Free
                    guard a.value < 3 || a.value > 10 else Free
                    Charged { yen = 1 }
                }
                """;

        assertEquals(List.of(), provenIn(source, "charge"),
                "a value of five and b of nought takes the second departure");
    }

    /**
     * A remainder by a divisor so large that what a guard leaves it, and what it leaves out, are
     * each hundreds of millions of numbers: what a path holds is the runs, so the same departures
     * are ruled out as by seven.
     */
    @Test
    void aRemainderByALargeDivisorRulesOutWhatItRulesOutBySeven() {
        for (String guards : List.of("""
                let x = Int.floorMod(a.value + 1, 1000000007)
                guard x < 500000000 else Free
                guard x < 600000000 else Free
                """, """
                let x = Int.floorMod(a.value + 1, 1000000007)
                guard x < 1000000005 else Free
                guard x < 1000000006 else Free
                """, """
                guard Int.floorMod(a.value, 1000000007) == 1000000006 else Free
                guard Int.floorMod(a.value + 1, 1000000007) /= 0 else Free
                """)) {
            assertEquals(1, provenIn(charging(guards), "charge").size(),
                    () -> "what the first leaves is what the second refuses:\n" + guards);
        }
        assertEquals(List.of(), provenIn(charging("""
                let x = Int.floorMod(a.value + 1, 1000000007)
                guard x < 600000000 else Free
                guard x < 500000000 else Free
                """), "charge"), "under six hundred million is not all under five hundred million");
    }

    /**
     * What a path rules out does not turn on the order its choices are written in, nor on whether
     * they are written as one condition: with {@code b} at seven or more, the last guard leaves
     * {@code a > 3}, and then neither part of the choice before it holds.
     */
    @Test
    void whatTheChoicesOfAPathRuleOutDoesNotTurnOnTheirOrder() {
        List<String> spellings = List.of("""
                guard b.value >= 7 else Free
                guard a.value < 4 || a.value + b.value == 10 else Free
                guard a.value + b.value == 3 || a.value > 3 else Free
                """, """
                guard b.value >= 7 else Free
                guard a.value + b.value == 3 || a.value > 3 else Free
                guard a.value < 4 || a.value + b.value == 10 else Free
                """, """
                guard b.value >= 7 else Free
                guard (a.value + b.value == 3 || a.value > 3) && (a.value < 4 || a.value + b.value == 10) else Free
                """, """
                guard b.value >= 7 else Free
                guard (a.value < 4 || a.value + b.value == 10) && (a.value + b.value == 3 || a.value > 3) else Free
                """, """
                guard b.value >= 7 else Free
                guard Int.floorMod(3 - a.value, 7) /= b.value else Free
                """);
        for (String guards : spellings) {
            assertFalse(provenIn(charging2(guards), "charge").isEmpty(),
                    () -> "something is proven unreachable:\n" + guards);
        }
        assertEquals(List.of(), provenIn(charging2("""
                guard b.value >= 6 else Free
                guard a.value < 4 || a.value + b.value == 10 else Free
                guard a.value + b.value == 3 || a.value > 3 else Free
                """), "charge"), "a of four and b of six reaches the charge");
    }

    private static String charging2(String guards) {
        return """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount, b: Amount) -> Free | Charged
                    constructs Charged
                let charge (a, b) = {
                %s    Charged { yen = 1 }
                }
                """.formatted(guards.indent(4));
    }

    /** A behavior charging an amount past {@code guards}, which may name {@code a}. */
    private static String charging(String guards) {
        return """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged
                let charge (a) = {
                %s    Charged { yen = 1 }
                }
                """.formatted(guards.indent(4));
    }

    /**
     * What a division leaves of a value is read, and what a guard says of it is taken in as what it
     * says of the call.
     *
     * <p>Named as the call is, so the remainder a guard names and the value the body bound the call
     * to are one number: nothing under five is six or more of it, and what the operation answers is
     * carried with it, so a remainder by seven is never seven.
     */
    @Test
    void aRemainderOfAPlaceIsReadAndTheEndsItsOperationGivesAreCarried() {
        String source = """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged
                let charge (a) = {
                    let x = Int.floorMod(a.value, 7)
                    guard x < 5 else Free
                    guard x < 6 else Free
                    guard x < 7 else Free
                    Charged { yen = 1 }
                }
                """;

        assertEquals(2, provenIn(source, "charge").size(),
                "the second guard's departure by the first, and the third's by the ends of the call");
        assertTrue(armsOf(source, "charge").stream()
                        .filter(Reachability.Unsettled.class::isInstance)
                        .map(each -> ((Reachability.Unsettled) each).why())
                        .noneMatch(WhatAnAnswerSays::isAConditionNotRead),
                "every condition is read");
    }
}
