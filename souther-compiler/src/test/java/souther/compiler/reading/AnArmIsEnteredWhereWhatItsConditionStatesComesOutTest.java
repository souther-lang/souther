package souther.compiler.reading;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ModelOccurrence;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which arm of a fork of the model a run can enter is what its condition states, read against
 * the input's rules — however it is spelt and whatever its parts come to where the language's
 * operations are expanded.
 *
 * <p>{@code List.any(e -> true, xs)} is a fold where it runs, and nothing in that fold says a value
 * stands behind either way of it. What it states is that {@code xs} holds something, which is the
 * size comparison {@code List.length(xs) >= 1} states; under a rule that keeps the list non-empty,
 * neither condition can come out false, and the arm it leads to is one no run enters.
 *
 * <p>Asked without the rule too, where both arms are entered whichever spelling: what keeps the
 * arm closed under the rule is the rule.
 */
class AnArmIsEnteredWhereWhatItsConditionStatesComesOutTest {

    private static String model(boolean nonEmpty, String condition) {
        return """
                module probe

                data Box = { xs: List<Int> }
                %s
                behavior f : (x: Box) -> Int
                let f (x) = if %s then 2 else 1
                """.formatted(nonEmpty ? "    invariant List.length(xs) >= 1\n" : "", condition);
    }

    /** Whether the arm the fork of {@code f} takes on false is closed, by how it is reached. */
    private static boolean otherArmClosed(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("probe")).value();
        assertNotNull(checked, "the model under test compiles");
        RuleReadingSource rules = RuleReadings.of(compilation, "probe");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("probe")).value().get("f");
        CoverageRead.Read read = CoverageRead.of("f", checked.run("f"), inputs.reading(rules));
        List<CoverageSites.ArmSite> other = checked.plan().arms("f").stream()
                .filter(site -> site.place().arm().part() == 1
                        && ModelOccurrence.statedAt(site.place().arm().fork()).isPresent())
                .toList();
        assertEquals(1, other.size(), "the model's one fork has one such arm");
        return read.arms().get(other.getFirst().index()) instanceof PathAccess.Unreachable;
    }

    @Test
    void anArmIsClosedWhereNoInputTheRulesAdmitLeadsToIt() {
        Map<String, List<Boolean>> closed = new TreeMap<>();
        for (String condition : List.of("List.length(x.xs) >= 1", "List.any(e -> true, x.xs)")) {
            closed.put(condition, List.of(otherArmClosed(model(true, condition)),
                    otherArmClosed(model(false, condition))));
        }
        assertEquals(Map.of("List.length(x.xs) >= 1", List.of(true, false),
                        "List.any(e -> true, x.xs)", List.of(true, false)), closed,
                "closed under the rule and open without it, in either spelling");
    }
}
