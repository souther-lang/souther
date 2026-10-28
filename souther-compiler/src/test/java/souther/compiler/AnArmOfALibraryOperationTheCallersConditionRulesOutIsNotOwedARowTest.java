package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork inside a copy of a library operation is no arm of the model unless the model made it: the
 * rule the model handed the operation settles the fork.
 *
 * <p>{@code Int.abs} compares at nought and {@code List.take} at the count it keeps, whatever the
 * caller has already found out, so no row is owed through either. The predicate handed to
 * {@code List.filter} is the model's own decision and is owed, and so is any fork the author
 * writes inside a closure handed to an operation.
 */
class AnArmOfALibraryOperationTheCallersConditionRulesOutIsNotOwedARowTest {

    private static final String GUARDED = """
            module p
            data Late = { over: Int }
            behavior f : (left: Int) -> Int | Late
            let f (left) = {
                guard left >= 0 else Late { over = Int.abs(left) }
                left
            }
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> Late { over = 2 }
            """;

    private static final String IF_FORM = """
            module p
            behavior f : (left: Int) -> Int
            let f (left) = if left < 0 then Int.abs(left) else left
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> 2
            """;

    private static final String MAX_FORM = """
            module p
            behavior f : (left: Int) -> Int
            let f (left) = if left < 0 then Int.max(left, 0 - left) else left
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> 2
            """;

    /** Nothing says the argument is negative, and the arms of {@code abs} are still the operation's own. */
    private static final String UNCONDITIONAL = """
            module p
            behavior f : (x: Int) -> Int
            let f (x) = Int.abs(x)
            example f
                | (3) -> 3
                | (0) -> 0
            """;

    @Test
    void anArmTheGuardRulesOutIsNotAGap() {
        assertFalse(report(GUARDED).contains("no row goes through"), () -> report(GUARDED));
    }

    @Test
    void anArmTheIfRulesOutIsNotAGap() {
        assertFalse(report(IF_FORM).contains("no row goes through"), () -> report(IF_FORM));
    }

    @Test
    void anArmOfMaxTheIfRulesOutIsNotAGap() {
        assertFalse(report(MAX_FORM).contains("no row goes through"), () -> report(MAX_FORM));
    }

    @Test
    void anArmTheOperationDecidesForItselfIsNotOwedEither() {
        assertFalse(report(UNCONDITIONAL).contains("no row goes through"),
                () -> report(UNCONDITIONAL));
    }

    /**
     * The operations whose forks the library settles itself.
     *
     * <p>{@code take} and {@code drop} turn at a count they keep, {@code zipShortest} at what
     * {@code List.get} found in the other list, and {@code distinctBy} and {@code groupBy} at what
     * they have gathered so far. The last two are handed a function, and the fork rests on what it
     * answers — but it only projects a key, and the fork is settled by the gathered state.
     */
    private static final String SETTLED_BY_THE_LIBRARY = """
            module exp.ops

            behavior takeTwo : (xs: List<Int>) -> List<Int>
            let takeTwo (xs) = List.take(2, xs)
            example takeTwo
                | "one" : ([1]) -> [1]

            behavior dropTwo : (xs: List<Int>) -> List<Int>
            let dropTwo (xs) = List.drop(2, xs)
            example dropTwo
                | "one" : ([1]) -> []

            behavior pairs : (xs: List<Int>, ys: List<Int>) -> Int
            let pairs (xs, ys) = List.length(List.zipShortest(xs, ys))
            example pairs
                | "same length" : ([1], [2]) -> 1

            behavior unique : (xs: List<Int>) -> List<Int>
            let unique (xs) = List.distinctBy(x -> x, xs)
            example unique
                | "single" : ([1]) -> [1]

            behavior grouped : (xs: List<String>) -> Int
            let grouped (xs) = Map.size(List.groupBy(x -> x, xs))
            example grouped
                | "single" : (["a"]) -> 1
            """;

    @Test
    void aForkTheLibrarySettlesItselfOwesNoArm() {
        Compilation compilation = measured(SETTLED_BY_THE_LIBRARY);
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
        Map<String, Adequacy.BranchEvidence> byBehavior =
                compilation.db().ask(new Adequacy.BranchCoverage("exp.ops")).value();

        for (String behavior : List.of("takeTwo", "dropTwo", "pairs", "unique", "grouped")) {
            assertEquals(Adequacy.BranchEvidence.noArms(
                            Adequacy.BranchEvidence.NoArms.NO_ARM_OBLIGATIONS),
                    byBehavior.get(behavior), behavior);
        }
        String report = report(compilation);
        assertFalse(report.contains("no row goes through"), report);
    }

    /**
     * A rule the library hands an operation is the library's, however the operation settles its
     * fork: {@code Map.intersection} is {@code Map.filterEntries} with a predicate of its own, and
     * the model only chose {@code intersection}.
     */
    @Test
    void aRuleOneLibraryOperationHandsAnotherIsNotTheModels() {
        Compilation compilation = measured("""
                module exp.ops

                behavior common : (a: Map<String, Int>, b: Map<String, Int>) -> Int
                let common (a, b) = Map.size(Map.intersection(a, b))

                behavior onlyInFirst : (a: Map<String, Int>, b: Map<String, Int>) -> Int
                let onlyInFirst (a, b) = Map.size(Map.difference(a, b))
                """);
        Map<String, Adequacy.BranchEvidence> byBehavior =
                compilation.db().ask(new Adequacy.BranchCoverage("exp.ops")).value();

        for (String behavior : List.of("common", "onlyInFirst")) {
            assertEquals(Adequacy.BranchEvidence.noArms(
                            Adequacy.BranchEvidence.NoArms.NO_ARM_OBLIGATIONS),
                    byBehavior.get(behavior), behavior);
        }
    }

    /** The same operation, called by the model with a rule of the model's own, is owed. */
    @Test
    void aRuleTheModelHandsTheSameOperationIsOwed() {
        Compilation compilation = measured("""
                module exp.ops

                behavior positives : (m: Map<String, Int>) -> Int
                let positives (m) = Map.size(Map.filterEntries((k, v) -> v > 0, m))
                """);

        assertNotEquals(Adequacy.BranchEvidence.noArms(
                        Adequacy.BranchEvidence.NoArms.NO_ARM_OBLIGATIONS),
                compilation.db().ask(new Adequacy.BranchCoverage("exp.ops")).value()
                        .get("positives"));
    }

    /** What the model hands the operation to decide by is its own decision, whichever operation. */
    @Test
    void aRuleTheModelHandedTheOperationToDecideByStaysOwed() {
        Compilation compilation = measured("""
                module exp.ops

                behavior positives : (xs: List<Int>) -> List<Int>
                let positives (xs) = List.filter(x -> x > 0, xs)
                example positives
                    | "positive" : ([5]) -> [5]
                """);

        assertTrue(report(compilation).contains("no row goes through `else`"),
                () -> report(compilation));
    }

    /** What the author writes inside a closure handed to a library operation is still owed. */
    @Test
    void aForkTheAuthorWritesInAClosureHandedToTheOperationIsStillOwed() {
        String source = """
                module exp.ops

                behavior signs : (xs: List<Int>) -> List<Int>
                let signs (xs) = List.map((x) -> if x > 0 then 1 else 0, xs)
                example signs
                    | "positive" : ([5]) -> [1]
                """;

        assertTrue(report(source).contains("no row goes through `else`"), () -> report(source));
    }

    private static String report(String source) {
        return report(measured(source));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }
}
