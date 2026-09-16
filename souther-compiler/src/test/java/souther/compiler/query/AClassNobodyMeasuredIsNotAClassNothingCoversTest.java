package souther.compiler.query;

import souther.compiler.partition.Generator;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A class this build measured nothing at is not a class the rows were found not to reach.
 *
 * <p>Two of the answers a coverage measure comes to carry no set of classes, and they mean opposite
 * things to whoever is composing rows. A behavior nobody wrote a row for has every class of it
 * still to be written, so a row is offered at each; a build that asked for no measurement looked at
 * none of them, and the rows that would close them may be sitting in the file the author is looking
 * at. Read off the absence of a value, the two are one answer and the second is handed out as the
 * first.
 *
 * <p>What is checked is the rows offered and not the measure, because the two nothings are already
 * told apart where the measure is made. What this is about is the reading of them, and a reader
 * that lost the difference is one no measure can correct.
 */
class AClassNobodyMeasuredIsNotAClassNothingCoversTest {

    private static final String MODULE = "example.classes";

    /** Three classes of one position, with a row in one of them. */
    private static final String ONE_CLASS_COVERED = """
            module example.classes

            data Red
            data Green
            data Blue
            data Colour = Red | Green | Blue

            data Ok

            behavior pick : (c: Colour) -> Ok

            let pick (c) = Ok

            example pick
                | "red" : (Red) -> Ok
            """;

    /** The same model with nothing written about it. */
    private static final String NO_ROWS_AT_ALL = """
            module example.classes

            data Red
            data Green
            data Blue
            data Colour = Red | Green | Blue

            data Ok

            behavior pick : (c: Colour) -> Ok

            let pick (c) = Ok
            """;

    /**
     * A build that measured the rows is offered a row at the classes they missed.
     *
     * <p>The positive side, and what says the two below are about the reading rather than about
     * this model having nothing to offer either way.
     */
    @Test
    void theClassesTheRowsMissedAreOfferedARowEach() {
        assertEquals(List.of("c=Blue", "c=Green"),
                classesOffered(ONE_CLASS_COVERED, Adequacy.Asked.reportOnly(Adequacy.Level.ALL)),
                "a row sits in Red, and the other two are work");
    }

    /**
     * A behavior nobody wrote a row for is owed one at every class.
     *
     * <p>The other measurement that carries no classes. Nothing was read because there was nothing
     * to read, which is this model's answer and not this build's — so every class of the position
     * is still to be written.
     */
    @Test
    void aBehaviorWithNoRowsIsOfferedOneAtEveryClass() {
        assertEquals(List.of("c=Blue", "c=Green", "c=Red"),
                classesOffered(NO_ROWS_AT_ALL, Adequacy.Asked.reportOnly(Adequacy.Level.ALL)),
                "nothing names this behavior, so each of its classes is a row to write");
    }

    /**
     * And a build that asked for no measurement is offered none of them.
     *
     * <p>What separates the two. The rows that would cover these classes may already be written:
     * nobody looked. Offered anyway, the block hands an author a specific row for every class of
     * every behavior of a compile that was measuring nothing.
     */
    @Test
    void aBuildThatMeasuredNothingIsOfferedNoneOfThem() {
        assertEquals(List.of(), classesOffered(ONE_CLASS_COVERED, Adequacy.Asked.NOTHING),
                "nothing was read, so which classes the rows reach is not something to act on");
        assertEquals(List.of(), classesOffered(NO_ROWS_AT_ALL, Adequacy.Asked.NOTHING),
                "and that holds of a model whose rows are missing as well as one whose are not");
    }

    /** The classes the rows this request is offered were composed for, in order. */
    private static List<String> classesOffered(String source, Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(asked);
        compilation.answerEverything();
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(MODULE));
        assertNotNull(offering, "the model under test compiles");
        List<String> out = new ArrayList<>();
        offering.rowsByBehavior().forEach((_, rows) -> {
            for (OfferedRow row : rows) {
                for (Generator.Purpose purpose : row.namedFor()) {
                    if (purpose instanceof Generator.Purpose.ForAClass at) {
                        out.add(at.label());
                    }
                }
            }
        });
        return out.stream().sorted().toList();
    }
}
