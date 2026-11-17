package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the cases of a line were made is found for the parts the cases are taken apart on even
 * where the loop's variable is gone from a part, and where a quantifier over a set was said part
 * by part.
 *
 * <p>The model is shaped as billing writes its due dates: a search over a few days in one helper,
 * the weekday and the holidays in another, called on each element of a range the behavior walks.
 * Past the figure, the parts of a case are the derivation's comparisons with the range's element
 * put at the values the list starts with ({@link TheWholeNumbersAListStartsWith}), and each
 * holiday comparison said of the element some holiday is ({@link WhereEachLineDecides#lifted}).
 * A part found in no derivation is counted as one nothing made, and most of a heavy case's parts
 * are found in some.
 *
 * <p>A model measured by hand at about two minutes of CPU, so it runs with the nightly ones.
 */
@Nightly
class ThePartsOfALineOverAListsElementsAreFoundInTheDerivationsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module demo exposing (unpayableDueDates, PaymentCalendar, DueDateRule, DueDateViolation)
            data DueDateRule = SameDay | PrecedingBusinessDay | FollowingBusinessDay
            data PaymentCalendar = { holidays: Set<Date>, aSunday: Date, rule: DueDateRule }
            data DueDateViolation = { rule: DueDateRule, nominal: Date, landed: Date }
            let weekday (calendar: PaymentCalendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)
            let isBusinessDay (calendar: PaymentCalendar, d: Date): Bool =
                weekday(calendar, d) >= 1 && weekday(calendar, d) <= 5
                    && Bool.not(Set.contains(d, calendar.holidays))
            let firstBusinessDay (calendar: PaymentCalendar, from: Date, step: Int): Date =
                List.rangeInclusive(0, 7)
                    |> List.map(n -> Date.addDays(n * step, from))
                    |> List.find(d -> isBusinessDay(calendar, d))
                    |> Option.withDefault(from)
            let onABusinessDay (calendar: PaymentCalendar, nominal: Date): Date =
                match calendar.rule with
                    | SameDay -> nominal
                    | PrecedingBusinessDay -> firstBusinessDay(calendar, nominal, 0 - 1)
                    | FollowingBusinessDay -> firstBusinessDay(calendar, nominal, 1)
            behavior unpayableDueDates : (calendar: PaymentCalendar, from: Date, days: Int,
                                          rules: List<DueDateRule>) -> List<DueDateViolation>
                constructs DueDateViolation, PaymentCalendar
            let unpayableDueDates (calendar, from, days, rules) =
                List.flatMap(rule -> {
                    let ruled = PaymentCalendar { ...calendar, rule = rule }
                    List.rangeInclusive(0, days)
                        |> List.map(n -> {
                            let nominal = Date.addDays(n, from)
                            DueDateViolation { rule = rule, nominal = nominal,
                                               landed = onABusinessDay(ruled, nominal) }
                        })
                        |> List.filter(v -> Bool.not(isBusinessDay(ruled, v.landed)))
                    },
                    rules)
            """;

    /**
     * No line of the model is worked out for the cases it would be taken apart into, so each is
     * told what made its parts: for the heaviest, over fifty parts, fewer than half are found in
     * no derivation. Before the element was put on the derivations' conclusions, and before a
     * holiday comparison was said of the element some holiday is, more than half were.
     */
    @Test
    void mostPartsOfTheHeaviestCasesAreFoundInSomeDerivation() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main").allowing(
                Allowances.DECLARED.with(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO, 0));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        JsonNode partition = JSON.readTree(AdequacyReport.of(ACompiledModel.compiles(compilation))
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .path("modules").get(0).path("behaviors").get(0).path("partition");
        List<String> heavy = new ArrayList<>();
        partition.path("caseExpansions").forEach(each -> each.path("readings")
                .forEach(reading -> {
                    JsonNode expansion = reading.path("caseExpansion");
                    if (expansion.path("partsSplitOn").asInt() > 50) {
                        heavy.add(expansion.toString());
                        assertTrue(2 * expansion.path("unattributed").asInt()
                                        < expansion.path("partsSplitOn").asInt(),
                                "most parts are found in a derivation: " + expansion);
                    }
                }));
        assertFalse(heavy.isEmpty(), "some line is past the figure with over fifty parts: "
                + partition);
    }
}
