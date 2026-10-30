package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison between an input and a size, a position or an element is measured by the rows that
 * reach it, end to end: the report is read of a model with its rows written, and not the lines the
 * reading draws.
 *
 * <p>What the reading says a row would show and what a row does show are two claims, and each of
 * the models below is held to the second. A size is the size of a value some row holds, a position
 * is the position of an element some row has, and an element is the one at its index and not one
 * of the others — which is why rows that put the value at another element are written beside the
 * rows that put it at the right one.
 */
class ASizeAPositionOrAnElementIsMeasuredByTheRowsThatReachItTest {

    /** The report of a model measured as the command line measures it: its rows read, and the run
     *  through every arm asked for. */
    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(),
                () -> compilation.errors().stream().map(each -> each.diagnostic().code())
                        .toList() + "\n" + source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static void assertAdequate(String source) {
        String report = reportOf(source);
        assertTrue(report.contains("adequacy: satisfied"), report);
        assertFalse(report.contains("not read"), report);
    }

    /**
     * A position beside the size of a container and one past it, one short of it, and the sizes
     * nought, one and two: the rows the generator offers for {@code k > size}.
     *
     * @param declarations what the container is made of
     * @param container    the type of the input
     * @param size         the size of {@code xs}, as the body writes it
     * @param empty        the value of nought
     * @param one          a value of size one
     * @param two          a value of size two
     */
    private static String pastEnd(String declarations, String container, String size,
                                  String empty, String one, String two) {
        return """
                module p
                %s
                behavior pastEnd : (k: Int, xs: %s) -> Bool

                let pastEnd (k, xs) = k > %s

                example pastEnd
                    | (1, %4$s) -> true
                    | (0, %4$s) -> false
                    | (2, %4$s) -> true
                    | (-1, %4$s) -> false
                    | (2, %5$s) -> true
                    | (2, %6$s) -> false
                """.formatted(declarations, container, size, empty, one, two);
    }

    @Test
    void aListOfPrimitives() {
        assertAdequate(pastEnd("", "List<Int>", "List.length(xs)", "[]", "[0]", "[0, 0]"));
    }

    @Test
    void aListOfANamedRecord() {
        assertAdequate(pastEnd("data Throw = { score: Int }", "List<Throw>", "List.length(xs)",
                "[]", "[Throw { score = 0 }]", "[Throw { score = 0 }, Throw { score = 0 }]"));
    }

    /** The rows of the type's own ends are written beside, as they are for any model. */
    @Test
    void aListOfANamedNumberHeldBetweenEnds() {
        assertAdequate(pastEnd("data Pins = Int invariant value >= 0 && value <= 12",
                "List<Pins>", "List.length(xs)", "[]", "[Pins(0)]", "[Pins(5), Pins(12)]"));
    }

    /** A set of booleans holds at most two, which parts the position at three: a row there is
     *  owed, and is the one a list of any size would not owe. */
    @Test
    void aSetOfBooleansIsCappedAtTwo() {
        assertAdequate(pastEnd("", "Set<Bool>", "Set.size(xs)", "[]", "[true]",
                "[true, false]") + "    | (3, [true, false]) -> true\n");
    }

    @Test
    void aMapKeyedByStrings() {
        assertAdequate(pastEnd("", "Map<String, Bool>", "Map.size(xs)", "[]",
                "[(\"a\", true)]", "[(\"a\", true), (\"b\", false)]"));
    }

    /**
     * Which element, and not the elements. The rows put the value at the first element, at the
     * second, at both and at neither, and the comparison is made of the second: the report names
     * no class and no line of the elements, which rows at the wrong element could be taken to
     * cover, and is the one the rows at the right element earn.
     */
    @Test
    void anElementAtAnIndexIsTheOneThatIsComparedAndNotTheOthers() {
        String model = """
                module p
                behavior f : (xs: List<Int>) -> Bool

                let f (xs) = match List.get(1, xs) with | Some v -> v >= 5 | None -> false

                example f
                    | ([5, 4]) -> false
                    | ([4, 5]) -> true
                    | ([5, 5]) -> true
                    | ([4, 4]) -> false
                    | ([5]) -> false
                    | ([]) -> false
                """;
        String report = reportOf(model);
        assertTrue(report.contains("adequacy: satisfied"), report);
        assertFalse(report.contains("xs[*]: ="), report);
        assertFalse(report.contains("equivalence partitions"), report);
    }

    /** The same rows with the value at the first element only: the comparison reads the second,
     *  which none of them has, and nothing of the elements is said to be covered. */
    @Test
    void rowsAtAnotherElementCoverNothingOfThePickedOne() {
        String report = reportOf("""
                module p
                behavior f : (xs: List<Int>) -> Bool

                let f (xs) = match List.get(1, xs) with | Some v -> v >= 5 | None -> false

                example f
                    | ([5]) -> false
                    | ([4]) -> false
                    | ([]) -> false
                """);
        assertFalse(report.contains("equivalence partitions"), report);
        assertFalse(report.contains("borders"), report);
    }

    /** A position handed to a step beside a number of the input, and moved by a constant. */
    @Test
    void aPositionInAWalkMovedByAConstantIsMeasuredByTheRowsThatReachIt() {
        String report = reportOf("""
                module p
                behavior marks : (n: Int, xs: List<Int>) -> List<Bool>

                let marks (n, xs) = List.mapIndexed((i, _) -> i + 1 == n, xs)

                example marks
                    | (1, [0]) -> [true]
                    | (2, [0]) -> [false]
                    | (0, [0]) -> [false]
                    | (2, [0, 0]) -> [false, true]
                    | (3, [0, 0]) -> [false, false]
                    | (1, []) -> []
                """);
        assertFalse(report.contains("not read: comparison"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }
}
