package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Reachability;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison is read under what holds where it stands, wherever that is.
 *
 * <p>The reading walked a fork's condition and nothing else, so a comparison given a name a line
 * above the fork was numbered and then never asked about — and a question nothing answered reads,
 * everywhere below, exactly like a question answered "nothing is known". What the guards above rule
 * out is the same fact under either spelling.
 */
class AComparisonIsReadWhereverItStandsTest {

    /** The second comparison is written in the condition of the fork that tests it. */
    private static final String IN_THE_CONDITION = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 5000 else Free

                if a.value >= 6000 then Free else Charged { yen = 500 }
            }
            """;

    /** The same model, with the second comparison given a name before the fork tests it. */
    private static final String NAMED_BEFORE_THE_FORK = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Charged

            let charge (a) = {
                guard a.value < 5000 else Free

                let over = a.value >= 6000

                if over then Free else Charged { yen = 500 }
            }
            """;

    /** Which ways out of a comparison this reading proved nothing arrives at. */
    private static List<Boolean> comparisonsProvenUnreachable(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Map<String, PathReachability.Answers> answers = compilation.db()
                .ask(new Adequacy.PathReached("d")).value();
        assertNotNull(answers, "the model under test compiles");
        return answers.get("charge").found().entrySet().stream()
                .filter(each -> each.getKey() instanceof ControlPointId.ComparisonPoint)
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .map(each -> ((ControlPointId.ComparisonPoint) each.getKey()).held())
                .toList();
    }

    /**
     * Nothing at or above 6000 got past a guard that kept everything under 5000, and the comparison
     * saying so is read whether or not a name stands between it and the fork.
     *
     * <p>Held as an equality against the inline spelling. A count of its own would pass for a
     * reading that answered about some other comparison, and what is being said here is that the two
     * models state the same rule.
     */
    @Test
    void aComparisonNamedBeforeTheForkIsProvenWhereTheInlineOneIs() {
        assertEquals(List.of(true), comparisonsProvenUnreachable(IN_THE_CONDITION),
                "the guard above rules out the way the second comparison holds");
        assertEquals(comparisonsProvenUnreachable(IN_THE_CONDITION),
                comparisonsProvenUnreachable(NAMED_BEFORE_THE_FORK),
                "and giving it a name is not a fact about what arrives at it");
    }
}
