package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many pieces a string split at one code point falls into is one more than the times that code
 * point stands in it, and a comparison over that number draws its line on that count of the
 * string.
 *
 * <p>Held by the rows that stand at the points of the line: each is run, so it answers as the run
 * time splits it, and every point is filled only where the line is where the run time puts it. A
 * number of pieces read without the one the string falls into whole, or with a code point counted
 * as two halves, would leave a point owed.
 */
class HowManyPiecesASplitAtOneCodePointAnswersIsReadTest {

    private static String model(String separator, String comparison) {
        return """
                module example.pieces

                data Yes
                data No

                behavior g : (email: String) -> Yes | No
                let g (email) = {
                    guard List.length(String.split(%s, email)) %s else No
                    Yes
                }
                """.formatted(separator, comparison);
    }

    /** At least two pieces is at least one separator: none, one and two of them fill the line. */
    @Test
    void twoPiecesOrMoreIsOneSeparatorOrMore() {
        assertCovered(model("\"@\"", ">= 2") + """

                example g
                    | "none" : ("ab") -> No
                    | "one" : ("a@b") -> Yes
                    | "two" : ("@@") -> Yes
                """, 3);
    }

    /**
     * Three pieces or more, where the line is at two separators: a string of separators alone and
     * one ending in a separator are counted with their empty pieces.
     */
    @Test
    void theEmptyPiecesAreCounted() {
        assertCovered(model("\"@\"", ">= 3") + """

                example g
                    | "none" : ("") -> No
                    | "one at the end" : ("a@") -> No
                    | "two" : ("@a@") -> Yes
                    | "three alone" : ("@@@") -> Yes
                """, 4);
    }

    /** One piece is no separator at all. */
    @Test
    void onePieceIsNoSeparator() {
        assertCovered(model("\"@\"", "== 1") + """

                example g
                    | "none" : ("ab") -> Yes
                    | "one" : ("@") -> No
                    | "two" : ("a@@") -> No
                """, 3);
    }

    /** A separator outside the basic plane is one code point and is counted as one. */
    @Test
    void aSeparatorOutsideTheBasicPlaneIsOneCodePoint() {
        assertCovered(model("\"😀\"", ">= 2") + """

                example g
                    | "none" : ("a") -> No
                    | "one" : ("😀") -> Yes
                    | "two" : ("😀a😀") -> Yes
                """, 3);
    }

    /** A separator of two code points can stand across where one is looked for, and is left. */
    @Test
    void aLongerSeparatorIsNotRead() {
        assertNotRead(model("\"ab\"", ">= 2"));
    }

    /** And so is one that is not written out, which is any of them. */
    @Test
    void aSeparatorThatIsNoConstantIsNotRead() {
        assertNotRead("""
                module example.pieces

                data Yes
                data No

                behavior g : (sep: String, email: String) -> Yes | No
                let g (sep, email) = {
                    guard List.length(String.split(sep, email)) >= 2 else No
                    Yes
                }
                """);
    }

    private static void assertCovered(String model, int obligations) {
        Compilation compilation = measured(model);
        assertEquals(List.of(), compilation.errors(), "the rows hold");
        String report = AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("obligations " + obligations + "/" + obligations), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    private static void assertNotRead(String model) {
        Compilation compilation = measured(model);
        String report = AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("not read: comparison"), report);
        assertTrue(report.contains("how many times one string stands inside another"), report);
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
