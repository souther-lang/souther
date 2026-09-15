package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row offered for a point at one position stands where the rules relating that position to the
 * others leave it.
 *
 * <p>Which is what a region bounded by lines over two inputs asks for: every boundary is a rule
 * relating them, and each point of one boundary lies where the other boundaries also hold — so what
 * the companion of a point may be is exactly what the other rules leave. Composed against the
 * position's own range instead, the row carried the point's value, turned back at the guard above,
 * and the search spent its values finding that out (issue #1690).
 */
class ARowForAPointStandsWhereTheRulesRelatingItToTheRestLeaveItTest {

    private static final String RELATED = """
            module m

            behavior f : (x: Int, y: Int) -> Bool

            let f (x, y) = {
                guard y <= 2 * x else false
                guard y >= 100 else false

                true
            }
            """;

    /**
     * Every row offered for a point of the {@code y} border passes the rule relating {@code y} to
     * {@code x}.
     *
     * <p>The points of that border are the ones past the first guard, so a row at one of them holds
     * {@code y <= 2x} or it never arrives. Read off the rows rather than off what the block says is
     * missing: a row offered somewhere the relation refuses is the defect, and a block holding one
     * is as wrong as a block holding none.
     */
    @Test
    void aCompanionStandsWhereTheRelationLeavesIt() {
        List<int[]> offered = pointsOfTheYBorder();

        assertFalse(offered.isEmpty(), "the y border is one this model has points at");
        for (int[] row : offered) {
            assertTrue(row[1] <= 2 * row[0],
                    () -> "(" + row[0] + ", " + row[1] + ") is offered for a point of the y border"
                            + " and turns back at `y <= 2 * x`");
        }
    }

    /**
     * And every point of that border is offered one.
     *
     * <p>Beside the sentence above because they fail apart: a search composing nothing leaves the
     * rows it does offer standing where the relation admits, and the block comes back saying no row
     * was seen reaching the border.
     */
    @Test
    void andNoPointOfItIsLeftWithoutOne() {
        List<String> missed = new ArrayList<>();
        for (Generator.UnresolvedCombination each : OFFERED.unresolved()) {
            missed.addAll(each.classes());
        }

        assertTrue(missed.stream().noneMatch(label -> label.contains("y")),
                () -> "every point of the y border has a row, and these had none: " + missed);
    }

    /** The rows offered for a point the {@code y} border draws, as the pair they stand at. */
    private static List<int[]> pointsOfTheYBorder() {
        List<int[]> out = new ArrayList<>();
        for (Generator.GeneratedRow row : OFFERED.rows()) {
            if (row.purposes().stream().anyMatch(
                    purpose -> purpose instanceof Generator.Purpose.ForAPoint point
                            && aboutYAlone(point.label()))) {
                out.add(pairOf(row));
            }
        }
        return out;
    }

    /** Whether a label names the {@code y} border and not the one both positions are on. */
    private static boolean aboutYAlone(String label) {
        return label.contains("y") && !label.contains("x");
    }

    private static int[] pairOf(Generator.GeneratedRow row) {
        List<FixtureTemplate> inputs = row.inputs();
        if (inputs.size() != 2) {
            throw new AssertionError("a row for `f` stands at two positions, and this one is "
                    + inputs.stream().map(FixtureTemplate::text).toList());
        }
        return new int[] {Integer.parseInt(inputs.get(0).text()),
                Integer.parseInt(inputs.get(1).text())};
    }

    /**
     * What the model is offered, composed once for the whole class.
     *
     * <p>Both sentences here are about one block, and measuring it is what this test costs. Asked
     * per method, the second would compose every row again to read the labels of the points that
     * got none.
     */
    private static final Generator.GenerationResult OFFERED = offeredFor(RELATED);

    private static Generator.GenerationResult offeredFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return OfferedAtTheLines.of(compilation, compilation.modules().get(0), "f");
    }
}
