package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a reading took a value as is read with everything the reading had taken on the way there.
 *
 * <p>A helper called three times over what its earlier calls answered is read through a choice in
 * each of them, one inside the arm of another. The arm a choice is taken as was written where the
 * helper's body stands, and that place knows nothing of the choices taken on the way down; read
 * there, the choice taken before it is met again as if no reading had gone into it, and the
 * comparison under it stops at a value the reading had already gone into.
 */
class AValueTakenOnTheWayStaysTakenInWhatItWasTakenAsTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core node(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    private static InputReads top() {
        return InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE);
    }

    /** Through what the second choice was taken as, the first is still taken. */
    @Test
    void theChoiceTakenFirstIsTakenInsideTheArmOfTheSecond() {
        Core first = node(1);
        Core second = node(2);
        Denotation firstArm = new Denotation(node(10), top());
        Denotation secondArm = new Denotation(node(20), top());
        InputReads reads = top().taking(first, firstArm, 2).taking(second, secondArm, 2);

        Denotation inTheSecond = reads.taken(second);
        assertNotNull(inTheSecond);
        Denotation firstThere = inTheSecond.at().taken(first);
        assertNotNull(firstThere, "the arm of the second is read with the first taken");
        assertSame(firstArm.value(), firstThere.value());
    }

    /**
     * Carried again, what was taken is the same reading.
     *
     * <p>An arm written where a reading had taken something already is carried what the reading
     * took since, and what it holds of both is one taking each. Kept twice, every value carried
     * down a run of choices doubles what it holds at each of them.
     */
    @Test
    void whatIsCarriedTwiceIsTheSameReading() {
        Core first = node(1);
        Core second = node(2);
        InputReads onTheFirst = top().taking(first, new Denotation(node(10), top()), 2);
        Denotation secondArm = new Denotation(node(20), onTheFirst);
        InputReads reads = onTheFirst.taking(second, secondArm, 2);

        InputReads once = reads.taken(second).at();
        InputReads twice = once.taken(second).at();
        assertEquals(once, twice);
    }
}
