package souther.compiler;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import souther.compiler.inputs.RuleSite;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.WrittenOwner;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A comparison whose arithmetic stopped is reported at the call the arithmetic stopped at, and
 * that call is the same whichever operation made the value it was handed.
 *
 * <p>The date a weekday is counted of is a value some operation answered in the models here — one
 * a search found, one a month was added to — and the word for the rule changes with it. The
 * expression the reading stopped at does not: it is the remainder in {@code weekday}, written
 * once, and every rule over a date that reaches it is sent there.
 *
 * <p>One module holds all the behaviors, because what is asked of each is its own and compiling
 * the library once for each of them says nothing more.
 */
class AnArithmeticStopIsReportedAtTheCallItStoppedAtTest {

    private static final String MODEL = """
            module probe.stop

            data PaymentCalendar = { holidays: Set<Date>, aSunday: Date }

            let weekday (calendar: PaymentCalendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)

            let isBusinessDay (calendar: PaymentCalendar, d: Date): Bool =
                weekday(calendar, d) >= 1 && weekday(calendar, d) <= 5

            behavior found : (c: PaymentCalendar, from: Date, xs: List<Date>) -> Bool
            let found (c, from, xs) = isBusinessDay(c,
                Option.withDefault(from, List.find(d -> d == from, xs)))

            behavior monthAdded : (c: PaymentCalendar, from: Date) -> Bool
            let monthAdded (c, from) = isBusinessDay(c, Date.addMonths(1, from))

            behavior daysAdded : (c: PaymentCalendar, from: Date) -> Bool
            let daysAdded (c, from) = isBusinessDay(c, Date.addDays(3, from))
            """;

    private static final Map<String, List<PartitionEvidence.NotRead.AnUnclassifiedRule>> STOPPED =
            new HashMap<>();

    @BeforeAll
    static void compileTheModelOnce() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            STOPPED.put(each.name(), each.partition().notRead().stream()
                    .filter(PartitionEvidence.NotRead.AnUnclassifiedRule.class::isInstance)
                    .map(PartitionEvidence.NotRead.AnUnclassifiedRule.class::cast)
                    .toList());
        }
    }

    /** The call in {@code weekday} that every stopped rule in these models is sent to. */
    private static void assertSentToTheRemainderInWeekday(String behavior) {
        List<PartitionEvidence.NotRead.AnUnclassifiedRule> said = STOPPED.get(behavior);
        assertEquals(false, said.isEmpty(), "the model stops the reading, or this checks nothing");
        for (PartitionEvidence.NotRead.AnUnclassifiedRule each : said) {
            RuleSite.AConstructTheAuthorWrote at = assertInstanceOf(
                    RuleSite.AConstructTheAuthorWrote.class, each.sentTo(),
                    () -> "a rule that stopped on a call its author wrote is sent to it: " + each);
            assertEquals(SourceConstruct.CALL, at.origin().kind());
            assertEquals(new WrittenOwner.Body("probe.stop", "weekday"), at.origin().owner());
        }
    }

    @Test
    void aDateASearchFoundIsSentToTheRemainderItWasHandedTo() {
        assertSentToTheRemainderInWeekday("found");
    }

    @Test
    void aDateAMonthWasAddedToIsSentToTheSameCall() {
        assertSentToTheRemainderInWeekday("monthAdded");
    }

    /**
     * Where the date is a position and the weekday is read to the end, nothing stopped the
     * arithmetic, and no rule is sent to a call.
     */
    @Test
    void aDateThatIsAPositionStopsNothingAndIsSentNowhere() {
        assertEquals(List.of(), STOPPED.get("daysAdded"));
    }
}
