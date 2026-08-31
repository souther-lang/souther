package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which behavior a subject is about is the subject's own answer.
 *
 * <p>It used to be read back off the first axis, which answers only where the model divides some
 * position. A behavior whose inputs nothing bounds has no axis and still has a name, and every
 * sentence a generation says about the behavior as a whole — what a search limit stopped, which
 * groups went unoffered — had to reach that name through a position that may not be there.
 *
 * <p>Holding the name is half of it. The other half is that it agrees with the axes: a subject
 * assembled from two measurements would have two answers to one question, and whichever sentence
 * read one of them would be right about one behavior and wrong about the other.
 */
class ASubjectNamesTheBehaviorItsAxesAreOfTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    /** The reading of an input of one parameter, which is what a subject is asked its numbers
     *  through. */
    private static souther.compiler.inputs.Quantities readingOf(String... parameters) {
        List<souther.compiler.inputs.InputDomain.Parameter> declared = new java.util.ArrayList<>();
        for (String each : parameters) {
            declared.add(new souther.compiler.inputs.InputDomain.Parameter(each, null, Type.INT));
        }
        return souther.compiler.inputs.InputDomain.of(declared, SYMBOLS,
                ReadAs.THE_COMPILATION_DOES).quantities(SYMBOLS);
    }

    /** A behavior with no divided position, which is where reading the name off an axis ran out. */
    @Test
    void theNameHoldsWhereNothingIsDivided() {
        Generator.Subject subject = new Generator.Subject("fee",
                new BehaviorInputs(List.of("days"), List.of(Type.INT), SYMBOLS,
                        ReadAs.THE_COMPILATION_DOES),
                readingOf("days"), List.of(), HeldCounts.NONE);

        assertEquals("fee", subject.behavior(),
                "the behavior is named whether or not anything divided its positions");
    }

    /** An axis of another behavior, which is what a subject built from two measurements holds. */
    @Test
    void anAxisOfAnotherBehaviorIsRefused() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Generator.Subject("fee",
                        new BehaviorInputs(List.of("days"), List.of(Type.INT), SYMBOLS,
                                ReadAs.THE_COMPILATION_DOES),
                        readingOf("days"), List.of(axisOf("charge", "days")), HeldCounts.NONE));

        assertEquals(true, refused.getMessage().contains("charge"),
                "the refusal names the axis that disagrees: " + refused.getMessage());
    }

    /** And asked of all of them, not of whichever one the check happened to reach first. */
    @Test
    void everyAxisIsAsked() {
        assertThrows(IllegalArgumentException.class,
                () -> new Generator.Subject("fee",
                        new BehaviorInputs(List.of("days", "cap"), List.of(Type.INT, Type.INT),
                                SYMBOLS, ReadAs.THE_COMPILATION_DOES),
                        readingOf("days", "cap"),
                        List.of(axisOf("fee", "days"), axisOf("charge", "cap")), HeldCounts.NONE),
                "an axis of another behavior standing second is still one");
    }

    private static Axis axisOf(String behavior, String position) {
        return new Axis(new AxisId(behavior, position),
                new NumericTerm.ValueOf(TermPath.of(position)), Type.INT, List.of(), List.of());
    }
}
