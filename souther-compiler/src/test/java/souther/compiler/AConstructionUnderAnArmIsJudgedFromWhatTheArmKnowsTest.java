package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A construction under an arm is judged from what the arm's name is known to be: the value the arm
 * opened, read as far as it was written down.
 *
 * <p>An arm over a value handed in knows the case and nothing of the fields, so a construction from
 * a field is owed. An arm over a value written into the source knows the fields too, so the same
 * construction is settled by what was written. And an arm over a construction written with a value
 * handed in knows the shape and not the field: knowing which construction a value is is not knowing
 * what it holds.
 */
class AConstructionUnderAnArmIsJudgedFromWhatTheArmKnowsTest {

    private static final String TYPES = """
            module demo

            data Positive = Int
                invariant value > 0

            data Held = { n: Int }
            data Missing
            data Answer = Held | Missing

            data Box = { p: Positive }
            """;

    /** The scrutinee is a value handed in: nothing here says what its field holds. */
    @Test
    void anArmOverAValueHandedInKnowsNothingOfItsField() {
        assertEquals(1, unproven("""
                behavior boxed : (a: Answer) -> Box constructs Box, Positive
                let boxed (a) =
                    match a with
                        | Held as h -> Box { p = Positive(h.n) }
                        | Missing -> Box { p = Positive(1) }
                """), "a Held handed in may hold any number");
    }

    /** The same construction over a scrutinee written into the source: its field is five. */
    @Test
    void anArmOverAWrittenValueKnowsItsField() {
        assertEquals(0, unproven("""
                behavior boxed : (x: Int) -> Box constructs Box, Positive, Held
                let boxed (x) = {
                    let written: Answer = Held { n = 5 }
                    match written with
                        | Held as h -> Box { p = Positive(h.n) }
                        | Missing -> Box { p = Positive(1) }
                }
                """), "the Held written here holds five, and five is above nought");
    }

    /** A construction written with a value handed in: the arm knows the case, not the field. */
    @Test
    void anArmOverAWrittenShapeOfAValueHandedInKnowsOnlyTheShape() {
        assertEquals(1, unproven("""
                behavior boxed : (x: Int) -> Box constructs Box, Positive, Held
                let boxed (x) = {
                    let written: Answer = Held { n = x }
                    match written with
                        | Held as h -> Box { p = Positive(h.n) }
                        | Missing -> Box { p = Positive(1) }
                }
                """), "the Held written here holds x, and x may be any number");
    }

    /** The rules about a construction left unproven: E2011, and no other warning. */
    private static long unproven(String behavior) {
        return Compiler.compileWithWarnings(TYPES + "\n" + behavior).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()))
                .count();
    }
}
