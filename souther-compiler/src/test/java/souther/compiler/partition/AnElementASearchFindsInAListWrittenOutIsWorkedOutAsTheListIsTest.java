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
 * What a search finds in a list written out is worked out as the list is: a run builds every
 * element before the search looks at any, so what working an element out may stop a run at is
 * told of the comparison that reads the one found, and of the membership that decides which one
 * it is.
 *
 * <p>A date moved by a number written down stops only where the calendar does, which is no line
 * the model draws, so a comparison of the date found is read over every value; and where the run
 * may stop there before the comparison, the report says so of the places it may stop on.
 */
class AnElementASearchFindsInAListWrittenOutIsWorkedOutAsTheListIsTest {

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

    /** The day after, where it is no holiday, and the day itself otherwise. */
    @Test
    void aDateFoundAmongDatesMovedByANumberWrittenDownIsReadOverEveryValue() {
        assertEquals(List.of(), unread("""
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [Date.addDays(1, from)]))), 7) >= 1
                """));
    }

    /**
     * Found as the first of two, the date is the day itself, and the run has worked out the day
     * after as well: at the last day of the calendar it stops there, on an element the
     * comparison does not read. The comparison is read all the same, every reading of the
     * membership that decides which one is found telling the list built whole; and the day and
     * the holidays are said to be places a run may stop on the way to it, and nothing else.
     */
    @Test
    void anElementTheComparisonDoesNotReadIsAStopOnTheWayAndNoLine() {
        String model = """
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [from, Date.addDays(1, from)]))), 7) >= 1
                """;
        assertEquals(List.of("from", "holidays[*]"), unread(model));
        assertEquals(List.of(), reasonsOtherThanAStop(model));
    }

    /** The lines of the report saying what was not read for any reason but a run that may stop
     *  on the way to the comparison. */
    private static List<String> reasonsOtherThanAStop(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:")
                        && !line.contains("a run may stop on the way to it"))
                .toList();
    }
}
