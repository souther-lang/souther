package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A location asked for its own value and for a number taken of that value is answered by one value
 * that has both.
 *
 * <p>Two demands at one place, and one of them is the place itself. What may stand there is what
 * the place's own rule admits, and how long the string standing there is is what reading it comes
 * to — so the values to try are the first demand's and the second decides which of them is kept.
 * Nothing is solved out of the pair: the candidates were there to begin with.
 *
 * <p>Which is what the two models below are apart on. A value the rules single out whose length is
 * one the rules also admit is written, and a row is offered at the class of both. The same value
 * with a length the rules do not admit is not written, and neither is anything else — nothing here
 * reads a value of the place as having a length it does not have.
 */
class AValueAndANumberTakenOfItAreAnsweredByOneValueTest {

    /** The value the rule singles out has the length the rule below it asks for. */
    private static final String THE_LENGTH_IT_ASKS_FOR = """
            module example.string

            data Box = { s: String }

            behavior f : (box: Box) -> Bool
            let f (box) = {
                guard box.s == "xxxx" else false

                guard String.length(box.s) > 3 else false

                true
            }
            """;

    /** And the one whose length is not, which no value of the place answers. */
    private static final String A_LENGTH_NO_SUCH_VALUE_HAS = """
            module example.string

            data Box = { s: String }

            behavior f : (box: Box) -> Bool
            let f (box) = {
                guard box.s == "x" else false

                guard String.length(box.s) > 3 else false

                true
            }
            """;

    /** The sentence a group nothing here writes a value for comes back as, which these are not. */
    private static final String THE_POPULATION =
            "the values that answer several of their own numbers";

    /**
     * The value is written, and the row stands at the class of each number of it.
     *
     * <p>Both halves, because a row offered at one of the two classes would be a row written for a
     * demand this dropped. The classes are named in the block beside the row they are filled by.
     */
    @Test
    void oneValueAnswersThePlaceAndTheNumberTakenOfIt() {
        String offered = block(measured(THE_LENGTH_IT_ASKS_FOR));

        assertTrue(offered.contains("| (Box { s = \"xxxx\" })"),
                () -> "the value the rules single out is written: " + offered);
        assertTrue(offered.contains("// fills box.s== xxxx"),
                () -> "and the row stands at the class of the place's own value: " + offered);
        assertTrue(offered.contains("// fills box.s=3 < x"),
                () -> "and at the class of the number taken of it: " + offered);
        assertFalse(offered.contains(THE_POPULATION),
                () -> "so nothing says this is a group nothing writes a value for: " + offered);
    }

    /**
     * And a length the value standing there does not have is not read as one it has.
     *
     * <p>The row for the class the value is in is still offered — its length is a number of it, and
     * the class that length is in is one it fills. What is not offered is a row at the class the
     * rule above asks for, because no value of the place is in it.
     */
    @Test
    void aNumberTheValueDoesNotHaveIsNotAnsweredByIt() {
        String offered = block(measured(A_LENGTH_NO_SUCH_VALUE_HAS));

        assertTrue(offered.contains("| (Box { s = \"x\" })"),
                () -> "the value the rules single out is written: " + offered);
        assertTrue(offered.contains("// fills box.s=0 <= x <= 3"),
                () -> "and the row stands at the class its own length is in: " + offered);
        // Nothing was composed for it, and not a row that was composed and did not arrive. A value
        // of the place put forward for a class its length is not in is a row that says the string
        // is four characters long, and what turns it back is the run it is pasted into.
        assertTrue(offered.contains("no row for `String.length(box.s) = 4` in `f`:"
                        + " nothing here could build a representative"),
                () -> "and no value of the place is offered for a length it does not have: "
                        + offered);
        assertFalse(offered.contains(THE_POPULATION),
                () -> "and the group is not one nothing writes a value for: " + offered);
    }

    /**
     * The length classes the value cannot be in are answered about, and not left unsaid.
     *
     * <p>Held because the answer is the one a reader may act on least: nothing here walked every
     * string, so what the page may say is that this compiler wrote no value for the class — and an
     * author reading it knows the row is theirs to write if the model has one.
     */
    @Test
    void whatWasNotWrittenIsSaidAsSomethingThisCompilerDidNotWrite() {
        String page = report(measured(A_LENGTH_NO_SUCH_VALUE_HAS));

        assertEquals(0, page.lines().filter(line -> line.contains(THE_POPULATION)).count(),
                () -> "nothing here is a group without a way of writing one: " + page);
        assertTrue(page.contains("nothing here could build a representative for"
                        + " String.length(box.s) = 4"),
                () -> "the class no value of the place is in is answered about: " + page);
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.string")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
