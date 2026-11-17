package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation of a comparison that may end a run is told as such wherever the comparison is
 * read: where the arithmetic of the relation cancels it, where it is an element of a list
 * written out, and where it stands in an arm of a choice. Each is told the note the same
 * operation gives in a comparison that restates nothing, and an operation no run works out is
 * told of none.
 */
class AStopInWhatAReadingRestatesIsToldAsTheUnrestatedSpellingToldItTest {

    private static final String THE_STOP = "every run stops in q + 1 where q is at least "
            + "9223372036854775807";

    /** The control: nothing is cancelled or substituted. */
    @Test
    void anOperationInAComparisonThatRestatesNothingIsTold() {
        assertTrue(stops("q + 1 <= 10").stream().anyMatch(note -> note.endsWith(THE_STOP)),
                stops("q + 1 <= 10").toString());
    }

    @Test
    void anOperationTheRelationCancelsIsToldAsTheControlTellsIt() {
        for (String condition : List.of("q + 1 >= q", "q + 1 > q", "(q + 1) - q >= 3",
                "1 + q - q >= 3")) {
            assertEquals(1, stops(condition).size(), condition);
            assertTrue(stops(condition).getFirst().endsWith(THE_STOP),
                    condition + " " + stops(condition));
        }
    }

    @Test
    void anOperationInAListWrittenOutIsToldAsTheControlTellsIt() {
        for (String condition : List.of("List.all(r -> r >= 4, [q + 1, 3])",
                "List.any(r -> r >= 4, [q + 1, 3])", "List.length([q + 1, 3]) >= 2")) {
            assertEquals(1, stops(condition).size(), condition);
            assertTrue(stops(condition).getFirst().endsWith(THE_STOP),
                    condition + " " + stops(condition));
        }
    }

    /** Where the operation is in one arm only, a run that takes that arm may stop; which rows
     *  stop is not said of the others. */
    @Test
    void anOperationInOneArmOfAChoiceIsToldAsOneAMayStop() {
        for (String condition : List.of("(if q > 5 then q + 1 else 3) >= q",
                "Int.max(q + 1, 3) >= q")) {
            assertEquals(1, stops(condition).size(), condition);
        }
    }

    /** Two steps of one list: the first is worked out before the second, so a row is not said
     *  to stop in the second where it stopped in the first. */
    @Test
    void anOperationInAStepComposedWithAnotherIsToldAsTheStepAloneIs() {
        String alone = stops("List.all(r -> r <= 10, List.map(y -> y * 2, ds))").getFirst();
        List<String> composed =
                stops("List.all(r -> r <= 10, List.map(x -> x + 1, List.map(y -> y * 2, ds)))");
        assertEquals(1, composed.size(), composed.toString());
        assertTrue(composed.getFirst().contains("in 2 * ds[*] where ds[*] is at least"),
                composed + " beside " + alone);
    }

    /** The other side of a comparison of a walk is worked out whatever the walk answers. */
    @Test
    void anOperationBesideAWalkThatEndsNoRunIsToldAsTheControlTellsIt() {
        for (String condition : List.of(
                "List.fold((w, l) -> if l > w then l else w, 0, ds) <= q + 1",
                "q + 1 >= List.fold((w, l) -> if l > w then l else w, 0, ds)")) {
            assertEquals(1, stops(condition).size(), condition);
            assertTrue(stops(condition).getFirst().endsWith(THE_STOP),
                    condition + " " + stops(condition));
        }
    }

    @Test
    void nothingIsToldWhereNoRunWorksTheOperationOut() {
        assertEquals(List.of(), stops("q >= q"));
        assertEquals(List.of(), stops("(if q > 5 then q - 1 else 3) >= q"));
    }

    private static List<String> stops(String condition) {
        Compilation compilation = ACompiledModel.measured("""
                module m
                behavior role : (ds: List<Int>, q: Int) -> Int
                let role (ds, q) = if %s then 1 else 2
                """.formatted(condition), new Adequacy.Asked(Adequacy.Level.OFF, false));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).filter(line -> line.contains("may stop a run")).toList();
    }
}
