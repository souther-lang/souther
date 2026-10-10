package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value written down is told from a call that answers with one, and the type does not tell them
 * apart.
 *
 * <p>Which line a comparison draws is read off the value on the other side, and the only expressions
 * that carry one are the ones a model writes the value with. A call to something else answers a
 * value nobody here knows: the text inside {@code openingAt("16:00:00")} is an argument, and what
 * comes back is whatever the implementation makes of it.
 *
 * <p>Read off the answer's type instead, the argument became the line. That is a boundary this
 * compiler made up — the position was reported divided at a value no rule in the model states, and
 * the rows generated for it name a class nothing said exists. Which is worse than the position
 * coming back unread, because a reader has no way to tell it from a line the model drew.
 *
 * <p>Both readers are here. A {@code guard} reaches the comparison as {@code Core} and an invariant
 * as {@code Hir}, so a rule read at one and not the other is a rule about the representation.
 */
class ACallIsAValueOnlyWhenItIsTheConstructionTest {

    private static String model(String primitive, String written) {
        return """
                module demo

                data Ok
                data No

                behavior openingAt : (spelled: String) -> PRIM

                behavior pick : (t: PRIM) -> Ok | No
                    depends on openingAt

                let pick (t, openingAt) =
                    if t < openingAt("WRITTEN")
                        then Ok
                        else No
                """.replace("PRIM", primitive).replace("WRITTEN", written);
    }

    private static GuardThresholds.Guards read(String primitive, String written) {
        String source = model(primitive, written);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + primitive);
        Core body = checked.behaviorBodies().get("pick");
        assertNotNull(body);
        CoverageSites.Plan plan = checked.plan();
        return ThresholdFixtures.guardsOf("pick", checked.analysisBodies().get("pick"), body, plan,
                compilation.db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get("pick"), rules);
    }

    /** The one this branch could have introduced, and the two it would have introduced it beside. */
    @Test
    void aCallAnsweringWithATemporalIsNotTheTemporalItWasHandedTest() {
        for (String[] each : new String[][] {
                {"Time", "16:00:00"},
                {"Date", "2026-08-01"},
                {"DateTime", "2026-08-01T16:00:00"},
                {"Instant", "2026-08-01T16:00:00Z"}}) {
            GuardThresholds.Guards guards = read(each[0], each[1]);

            assertEquals(List.of(), guards.thresholds(),
                    each[0] + ": an implementation nothing here has read draws no line");
            // The rule is over what the dependency answered about the written string, which a row
            // stands in: the decision table holds it, and the position holds no rule left unread.
            assertEquals(List.of(), guards.noLine().unclassified(),
                    each[0] + ": and the position is left nothing unread");
            assertTrue(DecisionReadings.readToTheEnd(model(each[0], each[1]), "pick").stream()
                            .flatMap(rule -> rule.consulted().keySet().stream())
                            .anyMatch(condition -> condition.toString().contains(
                                    "demo.openingAt(\"" + each[1] + "\")")),
                    each[0] + ": the decision table holds a column over that answer");
        }
    }
}
