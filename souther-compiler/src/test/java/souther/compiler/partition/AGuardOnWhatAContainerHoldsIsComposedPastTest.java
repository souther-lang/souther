package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is composed past a guard on whether a container holds a value, and a rule on either side of
 * one is offered a row that takes that side.
 *
 * <p>The row for a class the guard is not about is first composed from the classes alone, run,
 * and seen stopping at the guard; what gets it past is the guard coming out the other way, which
 * is a container written holding the value — or kept from it. A rule is composed for on the way
 * to it, and a container a helper answers is the field it answers.
 */
class AGuardOnWhatAContainerHoldsIsComposedPastTest {

    private static final String HOLDING = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, lead: Lead, priority: Name) -> Done | Refused
                constructs Done

            let settle (kind, lead, priority) = {
                guard Set.contains(priority, lead.campaigns) else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    /** The campaigns hold one at the fewest, so a row composed from the classes alone holds the
     *  very value the guard keeps out. */
    private static final String KEPT_OUT = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }
                invariant Set.size(campaigns) >= 1

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, lead: Lead, priority: Name) -> Done | Refused
                constructs Done

            let settle (kind, lead, priority) = {
                guard Bool.not(Set.contains(priority, lead.campaigns)) else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    private static final String SCORED = """
            module example.settle

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }

            data Score = { points: Int }

            let campaignsOf (lead: Lead): Set<Name> = lead.campaigns

            behavior settle : (lead: Lead, priority: Name) -> Score

            let settle (lead, priority) =
                Score { points = if Set.contains(priority, campaignsOf(lead)) then 25 else 0 }
            """;

    /** The rows about {@code kind} are past the guard: the campaigns hold the priority. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastTheGuard() {
        for (String kind : List.of("kind=Plain", "kind=Express")) {
            List<String> row = generatedOf(HOLDING).classes().get(kind);
            assertNotNull(row, () -> "a row is offered for " + kind);
            assertTrue(holds(row.get(1), row.get(2)), () -> "the row holds the priority: " + row);
        }
    }

    /** And past a guard on its not holding it: the campaigns are kept from the priority. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastAGuardThatKeepsTheValueOut() {
        for (String kind : List.of("kind=Plain", "kind=Express")) {
            List<String> row = generatedOf(KEPT_OUT).classes().get(kind);
            assertNotNull(row, () -> "a row is offered for " + kind);
            assertFalse(holds(row.get(1), row.get(2)),
                    () -> "the row keeps the priority out: " + row);
        }
    }

    /** A rule on each side of the membership is offered a row on that side. */
    @Test
    void eachSideOfTheMembershipIsOfferedARowThatTakesIt() {
        Rows rows = generatedOf(SCORED);
        assertEquals(2, rows.rules().size(), () -> "a row for each side: " + rows.rules());
        for (Map.Entry<Boolean, List<String>> each : rows.rules().entrySet()) {
            List<String> row = each.getValue();
            assertEquals(each.getKey(), holds(row.get(0), row.get(1)),
                    () -> "the row for the side coming out " + each.getKey() + ": " + row);
        }
    }

    /** What one module's behavior was offered: a row per class, and one per side of the
     *  membership a rule turns on. */
    private record Rows(Map<String, List<String>> classes, Map<Boolean, List<String>> rules) {}

    private static Rows generatedOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, "the model under test compiles");
        Adequacy.Filling filling = all.get("settle");
        Map<String, List<String>> classes = new LinkedHashMap<>();
        for (Generator.GeneratedRow row : filling.composed().rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass) {
                    classes.put(forAClass.label(), written(row));
                }
            }
        }
        Map<Boolean, List<String>> rules = new LinkedHashMap<>();
        filling.rules().byRule().forEach((rule, row) -> rule.consulted().values().stream()
                .filter(each -> each instanceof DecidedCondition.Unread)
                .forEach(each -> rules.put(((DecidedCondition.Unread) each).held(),
                        written(row))));
        return new Rows(classes, rules);
    }

    private static List<String> written(Generator.GeneratedRow row) {
        return new ArrayList<>(row.inputs().stream().map(FixtureTemplate::text).toList());
    }

    /** Whether the campaigns written in {@code lead} hold {@code value}. */
    private static boolean holds(String lead, String value) {
        Matcher found = Pattern.compile("campaigns = \\[([^]]*)]").matcher(lead);
        assertTrue(found.find(), () -> "the campaigns are written in " + lead);
        String inside = found.group(1).trim();
        return !inside.isEmpty() && Arrays.stream(inside.split(",")).map(String::trim)
                .anyMatch(value::equals);
    }
}
