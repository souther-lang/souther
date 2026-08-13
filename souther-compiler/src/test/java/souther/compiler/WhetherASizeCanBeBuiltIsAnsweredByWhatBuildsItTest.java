package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Rows at the edges a model draws on a measure taken of a value.
 *
 * <p>A line at {@code String.length = 1} is met by a string of one character, and whether one can be
 * composed is a question about strings. Answered where strings are built, it is an answer every
 * caller has; answered at each caller, it is an assumption that goes on being true only until the
 * builder learns something — which is what happened here, and the boundary went on reporting that
 * nothing composed a value it was by then being handed in another row of the same generation.
 *
 * <p>What is held to is the boundary an author sees, not the helper underneath. A test on the helper
 * would have gone on passing throughout.
 */
class WhetherASizeCanBeBuiltIsAnsweredByWhatBuildsItTest {

    /** A model whose one behavior divides on {@code s}, so that a numeric edge is owed beside whatever
     * the constrained position owes. */
    private static String model(String declaration, String written) {
        return """
                module sz.gen

                data Size = Int
                    invariant value >= 1

                data Tag = Big | Small

                %s

                behavior label : (c: C, s: Size) -> Tag

                let label (c, s) = if s.value >= 5 then Big else Small

                example label
                    | (%s, Size(9)) -> Big
                """.formatted(declaration, written);
    }

    /** What the generator answers for the lines that behavior draws and no row sits on. */
    private static Generator.GenerationResult boundaries(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).toList(), "the model under test compiles");
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the rows come back");
        return all.get("label").boundaries();
    }

    /** The row offered at {@code edge}, as the text an author is handed for its first input. */
    private static String rowAt(Generator.GenerationResult filled, String edge) {
        for (Generator.GeneratedRow row : filled.rows()) {
            if (row.classes().contains(edge)) {
                return row.inputs().get(0).text();
            }
        }
        return null;
    }

    /** Why no row was offered at {@code edge}, or null where one was. */
    private static Generator.UnresolvedCombination.Reason whyNot(Generator.GenerationResult filled,
                                                                 String edge) {
        for (Generator.UnresolvedCombination left : filled.unresolved()) {
            if (left.classes().contains(edge)) {
                return left.reason();
            }
        }
        return null;
    }

    // --- a string as long as the line says --------------------------------------------------------

    /**
     * The edge a minimum on a length draws is a string of that length.
     *
     * <p>The value is the one the same generation writes into every other row it offers, which is how
     * the claim that nothing composed one could be read off the block that made it.
     */
    @Test
    void aLineOnALengthIsMetByAStringOfThatLength() {
        Generator.GenerationResult filled = boundaries(model("""
                data C = String
                    invariant String.length(value) >= 1
                """, "C(\"abc\")"));

        assertEquals("C(\"x\")", rowAt(filled, "String.length(c) = 1"));
    }

    /** A line above the smallest one is met at its own length rather than at the smallest. */
    @Test
    void aLineFurtherUpIsMetAtItsOwnLength() {
        Generator.GenerationResult filled = boundaries(model("""
                data C = String
                    invariant String.length(value) >= 1 && String.length(value) <= 4
                """, "C(\"ab\")"));

        assertEquals("C(\"xxxx\")", rowAt(filled, "String.length(c) = 4"));
    }

    // --- a collection counted the same way --------------------------------------------------------

    /**
     * A count of elements reaches the same builder a count of characters does.
     *
     * <p>Here so that the fix is about what carries a count rather than about strings. Nothing in the
     * corpora draws this line today, and a repair that worked only for the case that showed the defect
     * would leave the next carrier to find it again.
     */
    @Test
    void aLineOnAnElementCountIsMetByACollectionOfThatSize() {
        Generator.GenerationResult filled = boundaries(model("""
                data C = List<Int>
                    invariant List.length(value) >= 2
                """, "C([1, 2, 3])"));

        assertEquals("C([0, 0])", rowAt(filled, "List.length(c) = 2"));
    }

    // --- built, and then refused ------------------------------------------------------------------

    /**
     * A value that was composed and refused is said to have been refused.
     *
     * <p>The two halves of the answer belong to different things: whether a value of that size exists
     * to try is what builds values, and whether the model admits it is the decoder's. Collapsed into
     * one, a type whose format refuses the string a length asked for reports that nothing composes a
     * string of that length — a claim about strings taken from an opinion about this type.
     */
    @Test
    void aSizedValueTheFormatRefusesIsReportedAsRefusedAndNotAsUnbuildable() {
        Generator.GenerationResult filled = boundaries(model("""
                data C = String
                    invariant String.length(value) >= 2 && String.matches("[0-9]+", value)
                """, "C(\"123\")"));

        assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                whyNot(filled, "String.length(c) = 2"));
    }

    // --- the position's own content, unchanged ----------------------------------------------------

    /**
     * A line on the content of a location is still met by writing that number at it.
     *
     * <p>The path this shares nothing with. A number read out of a value and a number counted of one
     * are two questions, and the second learning an answer does not change the first.
     */
    @Test
    void aLineOnTheContentOfALocationIsStillWrittenThere() {
        Generator.GenerationResult filled = boundaries(model("""
                data C = String
                    invariant String.length(value) >= 1
                """, "C(\"abc\")"));

        assertEquals("Size(5)", sizeAt(filled, "s = 5"),
                "the edge on `s` is still the number written at `s`");
        assertEquals("Size(1)", sizeAt(filled, "s = 1"),
                "and so is the edge its invariant draws");
    }

    /** The second input of the row offered at {@code edge}, or null where none was. */
    private static String sizeAt(Generator.GenerationResult filled, String edge) {
        for (Generator.GeneratedRow row : filled.rows()) {
            if (row.classes().contains(edge)) {
                return row.inputs().get(1).text();
            }
        }
        return null;
    }
}
