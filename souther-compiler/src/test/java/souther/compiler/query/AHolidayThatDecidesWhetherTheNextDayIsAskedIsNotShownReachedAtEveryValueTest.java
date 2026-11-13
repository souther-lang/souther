package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.partition.UndividedPosition;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The next day is asked of the holidays only where the day before is one, or on every run. A stop
 * on the step turns on neither the start nor the holidays, so beside it both are read as a run
 * that gets to the question; where the way is that the start is a holiday, a run gets to the
 * question only at the values of both that make it so, and neither is read at every value.
 */
class AHolidayThatDecidesWhetherTheNextDayIsAskedIsNotShownReachedAtEveryValueTest {

    private static final String SOURCE = """
            module probe

            data Calendar = { start: Int, step: Int, holidays: List<Int> }
            data Out = { n: Int }

            behavior beside : (c: Calendar) -> Out
            let beside (c) = {
                let spread = Int.floorMod(100, c.step - 2)
                Out { n = spread + (if List.any(h -> h == c.start + 1, c.holidays) then 1 else 0) }
            }

            behavior afterAHoliday : (c: Calendar) -> Out
            let afterAHoliday (c) = {
                let spread = Int.floorMod(100, c.step - 2)
                if List.any(h -> h == c.start, c.holidays)
                then Out { n = spread + (if List.any(h -> h == c.start + 1, c.holidays)
                    then 1 else 0) }
                else Out { n = spread }
            }
            """;

    @Test
    void aStopOnAnotherPlaceLeavesTheHolidaysReadAndTheWayThatTurnsOnThemDoesNot() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();

        assertEquals(Map.of("c.holidays[*]", UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                "c.start", UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                reasonsOf(evidence.get("beside")));
        assertEquals(Map.of(
                "c.holidays[*]", UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE,
                "c.start", UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                reasonsOf(evidence.get("afterAHoliday")));
        ACompiledModel.compiles(compilation);
    }

    private static Map<String, UndividedPosition.Reason> reasonsOf(PartitionEvidence evidence) {
        Map<String, UndividedPosition.Reason> reasons = new LinkedHashMap<>();
        evidence.notRead().forEach(each -> reasons.put(each.at(), each.reason()));
        return reasons;
    }
}
