package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a criterion over a distance asks, read about the other of the two positions.
 *
 * <p>How far {@code a} stands from {@code b} and how far {@code b} stands from {@code a} are one
 * relation and two quantities, and a demand written against either is the same demand against the
 * other with every level negated. Which is an equation and not a shape, so it is held as one: the
 * ends of a run change places along with the levels in them, and a check that listed the shapes
 * would be the reflection written a second time and free to disagree with the first.
 *
 * <p><b>Over the criteria the compiler writes and not over criteria built here.</b> What shapes a
 * border draws is the border's answer — which runs are open at which end, which lines the order
 * names a value at — and a set assembled by hand would be a set of the shapes whoever wrote the
 * check had in mind.
 */
class ADemandOnADistanceReadsTheOtherWayRoundTest {

    /**
     * Reflecting twice asks what was asked.
     *
     * <p>Compared as demands and not as records. A run rebuilt from its ends is the same run
     * however the ends were arrived at, and {@link Criterion#sameAs} is the question this is about.
     */
    @Test
    void reflectingTwiceComesBackToTheSameDemand() {
        List<Criterion> over = criteria();
        assertFalse(over.isEmpty(), "there are demands over a distance to reflect");
        for (Criterion each : over) {
            assertTrue(each.reflected().reflected().sameAs(each),
                    () -> "reflected twice: " + each + " became "
                            + each.reflected().reflected());
        }
    }

    /**
     * A value is at a criterion exactly where its negation is at the reflected one.
     *
     * <p>Which is the whole of what the reflection means, and is what makes the second reading of a
     * pair the same question as the first. Asked over distances the criteria themselves do not
     * name, so a reflection that happened to agree at its own lines and nowhere else fails here.
     */
    @Test
    void aLevelIsAtOneExactlyWhereItsNegationIsAtTheOther() {
        for (Criterion each : criteria()) {
            Criterion reflected = each.reflected();
            for (long at = -4; at <= 4; at++) {
                Level level = Level.OfTheQuantity.of(at);
                assertEquals(each.holds(level), reflected.holds(level.negated()),
                        "at " + at + ": " + each + " against " + reflected);
            }
        }
    }

    /** Negating a distance twice is the distance. */
    @Test
    void negatingALevelTwiceIsTheLevel() {
        for (long at = -4; at <= 4; at++) {
            Level level = Level.OfTheQuantity.of(at);
            assertEquals(level, level.negated().negated(), "negated twice: " + at);
        }
        assertEquals(
                new Level.OfTheQuantity(ExactRatio.of(new java.math.BigDecimal("-2.5"))),
                new Level.OfTheQuantity(ExactRatio.of(new java.math.BigDecimal("2.5"))).negated(),
                "a distance that is not whole negates the same way");
    }

    /**
     * The demands of every border a rule between two positions draws.
     *
     * <p>Both carriers, because which shapes a border has depends on what the order names: whole
     * numbers have a value on either side of a line and strings have one on one side only, so a run
     * open at the end the order supplies is written by the second and not by the first.
     */
    private static List<Criterion> criteria() {
        List<Criterion> out = new ArrayList<>();
        for (String type : List.of("Int", "String")) {
            for (String guard : List.of("a < b", "a > b", "a <= b", "a >= b")) {
                for (BorderAssessment.Point point : pointsOf(type, guard)) {
                    if (point.item() instanceof ItemAssessment.Owed owed) {
                        out.add(owed.criterion());
                    }
                }
            }
        }
        return out;
    }

    private static List<BorderAssessment.Point> pointsOf(String type, String guard) {
        String model = """
                module m

                data Yes = { v: Int }
                data No = { why: Int }

                behavior cmp : (a: %s, b: %s) -> Yes | No
                    constructs Yes
                    constructs No
                let cmp (a, b) = {
                    guard %s else No { why = 1 }
                    Yes { v = 1 }
                }
                """.formatted(type, type, guard);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), "m");
        return BorderAssessment.pointsOf(boundaries.get("cmp"));
    }
}
