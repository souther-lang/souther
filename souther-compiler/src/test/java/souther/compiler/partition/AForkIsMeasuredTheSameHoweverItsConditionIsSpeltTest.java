package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a fork is owed is what its condition means, and not how it is written.
 *
 * <p>Two measures ask it, each of its own tree: the branch measure counts the arms of the tree that
 * runs, where the library's operations are expanded, and the decision measure the rules of the tree
 * where they stand. Two spellings of one condition are one fork in both, so each comes to the same
 * count for each of them. An arm inside the expansion of an operation is the library's and no arm
 * of the model's.
 *
 * <p>Asked under a rule that keeps the list non-empty, where one arm of each fork is dead, and
 * without it. The branch measure counts only the arms a run can reach, so the rule moves its count,
 * and that is what says the count under the rule is about the rule. The decision measure's rules
 * are read off the body alone — whether a row can stand in one is a search's answer — so the rule
 * moves nothing there, and what is asked of it is that the spellings agree.
 */
class AForkIsMeasuredTheSameHoweverItsConditionIsSpeltTest {

    private static String probe(boolean nonEmpty, String condition, int answer) {
        return """
                module probe

                data Box = { xs: List<Int> }
                %s
                behavior f : (x: Box) -> Int
                let f (x) = if %s then 2 else 1

                example f
                    | (Box { xs = [ 1 ] }) -> %d
                """.formatted(nonEmpty ? "    invariant List.length(xs) >= 1\n" : "", condition,
                answer);
    }

    /** The arms the branch measure counts and the rules the decision measure reads. */
    private record Owed(int arms, int rules) { }

    private static Owed owed(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        int arms = compilation.db().ask(new Adequacy.BranchCoverage(compilation.modules().get(0)))
                .value().get("f").arms().counted();
        return new Owed(arms, DecisionReadings.of(source, "f").rules().size());
    }

    /**
     * That each spelling is owed what the first is, with the rule and without it; {@code answer}
     * is what {@code f} answers for a list of one element.
     */
    private static void sameForEach(String why, int answer, String... spellings) {
        Map<String, List<Owed>> asked = new TreeMap<>();
        for (String each : spellings) {
            asked.put(each, List.of(owed(probe(true, each, answer)),
                    owed(probe(false, each, answer))));
        }
        List<Owed> first = asked.get(spellings[0]);
        Map<String, List<Owed>> expected = new TreeMap<>();
        for (String each : spellings) {
            expected.put(each, first);
        }
        assertEquals(expected, asked, why);
        assertNotEquals(first.get(0).arms(), first.get(1).arms(),
                "the rule leaves one arm dead, so a count of arms it does not move is not about it");
    }

    @Test
    void anEmptinessCheckIsTheSizeComparisonItMeans() {
        sameForEach("a list the rule keeps non-empty is never empty, however that is asked", 1,
                "List.length(x.xs) == 0", "List.isEmpty(x.xs)");
    }

    @Test
    void aDenialIsTheComparisonWithFalse() {
        sameForEach("a denial written as an operation is the comparison written with an operator",
                2, "List.length(x.xs) /= 0", "Bool.not(List.length(x.xs) == 0)",
                "Bool.not(List.isEmpty(x.xs))", "List.isEmpty(x.xs) == false",
                "List.length(x.xs) >= 1");
    }

    /**
     * A denial handed a name, which the copy of {@code Bool.not} takes as the caller wrote it
     * rather than through a binding of its own, owes what the comparison with false owes.
     */
    @Test
    void aDenialOfANameIsTheComparisonWithFalse() {
        String flagged = """
                module probe

                data Box = { ok: Bool }

                behavior f : (x: Box) -> Int
                let f (x) = {
                    let ok = x.ok
                    if %s then 2 else 1
                }

                example f
                    | (Box { ok = true }) -> 1
                """;
        assertEquals(owed(flagged.formatted("ok == false")),
                owed(flagged.formatted("Bool.not(ok)")),
                "the copy forks on the caller's own value, which is the fork above it");
        assertEquals(owed(flagged.formatted("x.ok == false")),
                owed(flagged.formatted("Bool.not(x.ok)")),
                "and so it does where what it is handed is read off a field");
    }

    @Test
    void aWitnessTheRuleProvidesSettlesTheFork() {
        sameForEach("an element the closure holds of exists wherever an element does", 2,
                "List.length(x.xs) >= 1", "List.any(e -> true, x.xs)");
    }
}
