package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule relating two positions draws a line, whichever kind of rule wrote it.
 *
 * <p>A {@code guard}'s comparison and a declaration's clause state the same thing about the same two
 * positions, and one of them was measured. The reading that turns a comparison into a line answers
 * about the quantity the rule cuts, and the quantity two positions stand apart on is one it holds;
 * the reading that turns a clause into a line answered with an end on one position, which such a
 * rule places none of. So a model stating the relation on its data was reported as a model stating
 * no rule at all.
 *
 * <p>What the two rules owe at the line they draw is not the same, and that difference is the point
 * of writing the rule on the data. Nothing outside a declaration's bound can be constructed, so the
 * far side of its line holds no value and no row is asked for there; a {@code guard} divides values
 * that all exist and owes a row each side. That answer is read off which rule drew the line and is
 * already right — what was missing is the line.
 */
class ARelationIsALineWhereverItIsWrittenTest {

    private static final String MODULE = "example.relation";

    /**
     * One relation, written twice, beside a bound that already draws its line.
     *
     * <p>The bound is the control. It is a clause of a declaration like the relation above it and it
     * is measured today, so a reading that found nothing for the relation cannot be one that reached
     * no declaration at all.
     */
    private static final String MODEL = """
            module example.relation

            data Reversed

            data Span =
                { lo: Int
                , hi: Int
                }
                invariant lo <= hi

            data RawSpan = { lo: Int, hi: Int }

            data AtLeast =
                { n: Int
                }
                invariant n >= 5

            behavior stated : (s: Span) -> Int
            let stated (s) = s.hi

            behavior guarded : (r: RawSpan) -> Int | Reversed
            let guarded (r) = {
                guard r.lo <= r.hi else Reversed
                r.hi
            }

            behavior bounded : (a: AtLeast) -> Int
            let bounded (a) = a.n

            example stated  | "ordered" : (Span { lo = 1, hi = 3 }) -> 3
            example guarded | "ordered" : (RawSpan { lo = 1, hi = 3 }) -> 3
            example bounded | "enough"  : (AtLeast { n = 7 }) -> 7
            """;

    private static Partitions.Partitioning partitioning(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided(MODULE, behavior)).value();
        assertNotNull(divided, "the model under test compiles and is measured");
        return divided;
    }

    /** Every line the behavior's positions are held to, wherever it was drawn. */
    private static List<Border> lines(String behavior) {
        Partitions.Partitioning divided = partitioning(behavior);
        List<Border> out = new java.util.ArrayList<>(divided.between());
        divided.along().values().forEach(out::addAll);
        return out;
    }

    /** The control: a clause bounding one position draws a line, so a reading did reach the data. */
    @Test
    void aBoundOnOnePositionDrawsItsLine() {
        assertEquals(1, lines("bounded").size(), () -> "the bound is measured: " + lines("bounded"));
    }

    /** The relation a body states draws one, which is the answer the declaration is held to. */
    @Test
    void aRelationAGuardStatesDrawsALine() {
        assertEquals(1, lines("guarded").size(), () -> "the guard is measured: " + lines("guarded"));
    }

    /** And the same relation, stated by the data, draws one too. */
    @Test
    void aRelationADeclarationStatesDrawsALine() {
        assertEquals(1, lines("stated").size(), () -> "the clause is measured: " + lines("stated"));
    }

    /** It is the declaration's line, so what it owes is what a declaration's line owes. */
    @Test
    void whatTheDeclarationsLineOwesIsWhatABoundOwes() {
        Border line = lines("stated").get(0);
        assertTrue(line.demand(PointRole.ON) instanceof Demand.Owed,
                () -> "a row is asked for on the line: " + line.demand(PointRole.ON));
        assertTrue(line.demand(PointRole.OFF).excluded(),
                () -> "and none beyond it, which the rules refuse: " + line.demand(PointRole.OFF));
        assertTrue(line.demand(PointRole.OUT).excluded(),
                () -> "nor further out: " + line.demand(PointRole.OUT));
    }

    /** Where the body states it, both sides hold values, and a row is asked for on each. */
    @Test
    void whatTheBodysLineOwesIsARowEachSide() {
        Border line = lines("guarded").get(0);
        assertTrue(line.demand(PointRole.ON) instanceof Demand.Owed,
                () -> "a row on the line: " + line.demand(PointRole.ON));
        assertTrue(line.demand(PointRole.OFF) instanceof Demand.Owed,
                () -> "and one beyond it: " + line.demand(PointRole.OFF));
        assertFalse(line.demand(PointRole.OFF).excluded(),
                () -> "which the rules do not refuse: " + line.demand(PointRole.OFF));
    }

    /**
     * And the line is between the positions rather than through either of them.
     *
     * <p>The relation says where one position stands against another, and a class here is a set of
     * values of one position. A line placed on an axis would divide a position the model draws no
     * line through, which is the reading the separation between the two exists to prevent.
     */
    @Test
    void theDeclarationsLineDividesNeitherPosition() {
        Partitions.Partitioning divided = partitioning("stated");
        assertEquals(1, divided.between().size(),
                () -> "the line is between the positions: " + divided.between());
        assertTrue(divided.along().values().stream().allMatch(List::isEmpty),
                () -> "and no position is divided by it: " + divided.along());
    }
}
