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

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        assertEquals(rowsAskedOf(ONE_GUARD), rowsAskedOf(TWO_GUARDS),
                "a guard whose departure nothing takes draws no line");
    }

    /**
     * A call hands a library's own fork an argument one side of it can never take.
     *
     * <p>{@code Int.max} is a fork, and {@code Int.max(0, c.value)} over a {@code Count} never takes
     * the side that answers zero. It is not this author's to act on: the fork is written in another
     * module, and the same fork is alive wherever else that module is used. Its condition is no
     * condition of the model, so a path through it takes nothing in there and nothing about its
     * arms is proven — and nothing is reported.
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
    void aForkAnotherModuleWroteIsNotThisModulesToProveOrBeToldAbout() {
        Compilation c = Compilation.ofSource(A_LIBRARY_FORK, "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        List<ControlPlace.Arm> proven = byBehavior.get("mk").found().entrySet().stream()
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .map(each -> each.getKey())
                .filter(ControlPlace.Arm.class::isInstance)
                .map(ControlPlace.Arm.class::cast)
                .toList();
        assertEquals(List.of(), proven,
                "the library's fork is no condition of the model, so nothing of it is proven");
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
     * A remainder of a place moved by a number keeps what the guards say of it.
     *
     * <p>Read as the remainder of the place over two stretches, what a guard over the moved
     * remainder says is one of two things, and a path holds facts that all hold and not one of
     * several. The guards still rule the same departure out, since they are about one value, and
     * what they say of it is taken in as the value they are about.
     */
    @Test
    void aGuardOverARemainderOfAMovedPlaceStillRulesOutWhatItRulesOut() {
        String source = """
                module d

                data Amount = Int invariant value >= 0 && value <= 1000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged
                let charge (a) = {
                    let x = Int.floorMod(a.value + 1, 7)
                    guard x < 5 else Free
                    guard x < 6 else Free
                    Charged { yen = 1 }
                }
                """;

        assertEquals(1, provenIn(source, "charge").size(),
                "nothing under five is six or more, whatever `x` is");
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
