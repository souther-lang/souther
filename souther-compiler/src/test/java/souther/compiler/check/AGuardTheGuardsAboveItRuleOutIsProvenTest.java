package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
                constructs Free, Charged

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
                constructs Free, Charged

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
                constructs Free, Charged

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
                .filter(each -> each.getKey() instanceof ControlPointId.ArmOccurrence)
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
        Proof why = proven.get(0);
        assertInstanceOf(Proof.ConflictingPathConditions.class, why,
                "what makes it unreachable is the conditions on the way to it");
        assertEquals(2, ((Proof.ConflictingPathConditions) why).decisions().size(),
                "both guards are on the way to it, and the proof says which they are");
    }

    @Test
    void aSecondGuardTheFirstDoesNotSettleIsLeftAsItIs() {
        assertEquals(4, armsOf(TWO_LIVE_GUARDS).size());
        assertEquals(List.of(), provenIn(TWO_LIVE_GUARDS),
                "a value between 100 and 5000 takes neither departure, and one under 100 takes the "
                        + "second — so nothing here is an arm nothing reaches");
    }

    @Test
    void aDepartureOutsideWhatTheDeclarationAdmitsIsProvenToo() {
        assertEquals(2, armsOf(OUTSIDE_THE_DECLARATION).size(),
                "one guard makes one fork of two arms");
        List<Proof> proven = provenIn(OUTSIDE_THE_DECLARATION);
        assertEquals(1, proven.size(), "an `Amount` stops at a million, so nothing reaches two");
        assertEquals(1, ((Proof.ConflictingPathConditions) proven.get(0)).decisions().size(),
                "one guard is on the way to it; what it conflicts with is what the input is");
    }

    /** The same model with the guard nothing reaches taken out. */
    private static final String ONE_GUARD = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Free, Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                Charged { yen = 500 }
            }
            """;

    private static String rowsAskedOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "d");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return souther.compiler.report.GeneratedRows.of(compilation, "d", "charge", true,
                SourceNameResolver.identity());
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
     * the side that answers zero. That is true, it is proven, and it is not this author's to act on:
     * the fork is written in another module, and the same fork is alive wherever else that module
     * is used. So the proof is made and the report is not.
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
    void aForkAnotherModuleWroteIsProvenAndIsNotThisModulesToBeToldAbout() {
        Compilation c = Compilation.ofSource(A_LIBRARY_FORK, "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        List<ControlPointId.ArmOccurrence> proven = byBehavior.get("mk").found().entrySet().stream()
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .map(each -> each.getKey())
                .filter(ControlPointId.ArmOccurrence.class::isInstance)
                .map(ControlPointId.ArmOccurrence.class::cast)
                .toList();
        assertTrue(!proven.isEmpty(),
                "the argument makes one side of the library's fork unreachable, and that is proven");
        assertTrue(proven.stream().noneMatch(arm -> arm.writtenBy("d")),
                "none of what is proven here was written by this module");
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
                constructs Ok, No

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
                constructs Ok, No

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
}
