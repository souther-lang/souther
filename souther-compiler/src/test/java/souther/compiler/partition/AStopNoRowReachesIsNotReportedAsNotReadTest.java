package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison the compiler could not read is reported as not read where a run can reach it, and
 * not where the conditions on the way to it hold no row. "Could not read" and "had no need to read"
 * are different facts: the second owes no question, and the first keeps it for every way the
 * compiler cannot show empty.
 */
class AStopNoRowReachesIsNotReportedAsNotReadTest {

    private static final String MODEL = """
            module demo
            data Yes = { n: Int }
            data No = { n: Int }
            data Terms = Net15 | Net30 | Eom
            let weekday (c: Date, d: Date): Int = Int.floorMod(Date.daysBetween(c, d), 7)
            behavior f : (c: Date, d: Date, t: Terms) -> Yes | No
            let f (c, d, t) = %s
            """;

    /** The month a date moves into is a stop of the reading, whatever it is compared with. */
    private static final String STOP = "weekday(c, Date.addMonths(1, d)) >= 1";

    private static final String YES = "Yes { n = 1 }";

    private static final String NO = "No { n = 0 }";

    @Test
    void aStopTheRunsReachingItAreAllTurnedAwayBeforeIsNotRead() {
        assertEquals(Set.of(), notRead("if t == Eom then " + NO + " else if t == Eom && " + STOP
                + " then " + YES + " else " + NO));
    }

    @Test
    void theSameStopWhereTheWayToItIsNotShownEmptyIsStillNotRead() {
        Set<String> stopped = Set.of("c", "d");
        assertEquals(stopped, notRead("if " + STOP + " then " + YES + " else " + NO));
        assertEquals(stopped, notRead("if t == Eom && " + STOP + " then " + YES + " else " + NO));
        assertEquals(stopped, notRead("if t == Eom then " + NO + " else if " + STOP + " then "
                + YES + " else " + NO));
    }

    /** A part of a statement of several that stopped is turned away with the rest of it. */
    @Test
    void aStatementOfSeveralLinesNoRowReachesOwesNothing() {
        String several = "Int.max(" + "weekday(c, Date.addMonths(1, d)), weekday(c, d)) >= 3";
        assertEquals(Set.of(), notRead("if t == Eom then " + NO + " else if t == Eom && "
                + several + " then " + YES + " else " + NO));
        assertEquals(Set.of("c", "d"), notRead("if t == Eom && " + several + " then " + YES
                + " else " + NO));
    }

    private static Set<String> notRead(String body) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), body);
        PartitionEvidence evidence = compilation.db().ask(new Adequacy.Coverage("demo"))
                .value().get("f");
        Set<String> out = new TreeSet<>();
        evidence.notRead().forEach(each -> out.add(each.at().toString()));
        return out;
    }
}
