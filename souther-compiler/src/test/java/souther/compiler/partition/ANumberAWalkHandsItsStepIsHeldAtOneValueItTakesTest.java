package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison over a whole number a walk of every number between two ends hands its step is read
 * like one over a number of the input: the number is held at one value it takes, and what is
 * asked of the others is asked of the rows with it there.
 *
 * <p>Held for a date as for an {@code Int}. A date moved by the walk's number is an operation over
 * that number, told as the one it is, so the rows the relation is asked of are the rows where the
 * date stays inside the calendar; and the representation running out at either end of the
 * calendar is no line the model draws, as it is not for a date moved by a number written down.
 * What a stop on the way to the relation turns on is what it reads, and a place it does not read is
 * not shown unreached because some stop may turn on the walk.
 */
class ANumberAWalkHandsItsStepIsHeldAtOneValueItTakesTest {

    /** The places the report says nothing is read of. */
    private static List<String> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .sorted()
                .toList();
    }

    /** A date moved by the walk's number, against a date: nothing divides either. */
    @Test
    void aDateMovedByTheWalksNumberIsReadAgainstAnotherDate() {
        assertEquals(List.of(), unread("""
                module demo

                behavior f : (to: Date, from: Date, n: Int) -> Bool

                let f (to, from, n) =
                    List.rangeInclusive(0, n)
                        |> List.any(k -> Date.addDays(k, from) > to)
                """));
    }

    /** The same moved date as the element a set is asked to hold: an equality of two dates. */
    @Test
    void aSetHoldingADateMovedByTheWalksNumberIsReadAtEveryElement() {
        assertEquals(List.of(), unread("""
                module demo

                behavior f : (holidays: Set<Date>, from: Date, n: Int) -> Bool

                let f (holidays, from, n) =
                    List.rangeInclusive(0, n)
                        |> List.any(k -> Set.contains(Date.addDays(k, from), holidays))
                """));
    }

    /** The moved date made first, by a {@code map}, and compared by the next step of the pipe. */
    @Test
    void aDateTheWalkMadeIsReadWhereThePipeComparesIt() {
        assertEquals(List.of(), unread("""
                module demo

                behavior f : (to: Date, from: Date, n: Int) -> Bool

                let f (to, from, n) =
                    List.rangeInclusive(0, n)
                        |> List.map(k -> Date.addDays(k, from))
                        |> List.any(d -> d > to)
                """));
    }

    /** The made date as the element a set is asked to hold. */
    @Test
    void aDateTheWalkMadeIsReadWhereASetIsAskedToHoldIt() {
        assertEquals(List.of(), unread("""
                module demo

                behavior f : (holidays: Set<Date>, from: Date, n: Int) -> Bool

                let f (holidays, from, n) =
                    List.rangeInclusive(0, n)
                        |> List.map(k -> Date.addDays(k, from))
                        |> List.any(d -> Set.contains(d, holidays))
                """));
    }

    /**
     * The sum made before the comparison is read as the one written in it: what the comparison
     * reads of the value is its own arithmetic whether the value is made in the step that compares
     * it or in one before.
     */
    @Test
    void aSumTheWalkMadeIsReadAsOneWrittenInTheComparison() {
        String written = unread("""
                module demo

                behavior f : (a: Int, b: Int, n: Int) -> Bool

                let f (a, b, n) =
                    List.rangeInclusive(0, n)
                        |> List.any(k -> k + a > b)
                """).toString();
        assertEquals(written, unread("""
                module demo

                behavior f : (a: Int, b: Int, n: Int) -> Bool

                let f (a, b, n) =
                    List.rangeInclusive(0, n)
                        |> List.map(k -> k + a)
                        |> List.any(d -> d > b)
                """).toString());
    }
}
