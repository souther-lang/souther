package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a search finds in a list written out is worked out as the list is: a run builds every
 * element before the search looks at any, so what working an element out may stop a run at is
 * told of the comparison that reads the one found, and of the membership that decides which one
 * it is.
 *
 * <p>A date moved by a number written down stops only where the calendar does, which is no line
 * the model draws, so a comparison of the date found is read over every value. An element whose
 * working out may stop elsewhere is not told so, and the comparison is not read there.
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
     * comparison does not read, and the day is not shown to get to the comparison at every value.
     */
    @Test
    void anElementTheComparisonDoesNotReadKeepsWhatWorkingItOutMayStop() {
        assertNotEquals(List.of(), unread("""
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [from, Date.addDays(1, from)]))), 7) >= 1
                """));
    }
}
