package souther.compiler.program;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A behavior of a checked module is called by the boundary its module holds, and a program saying
 * otherwise is not one that can be made.
 *
 * <p>The index a program answers a call from is handed to it rather than built from its modules:
 * the boundaries are made before a module can be, because a row of one is compared against what a
 * dependency takes. So what holds the two together is that they are the same values, and here is
 * where that stops being something an assembler is trusted about.
 *
 * <p>Offered the disagreement directly. The assembler files a boundary and hands that same one to
 * the behavior, so a check reached only through a compile is one that has never been asked its own
 * question — it would go on passing after the day something made a second boundary out of the same
 * two readings, which is exactly the state the two would then disagree in.
 */
class ABehaviorIsCalledByTheBoundaryItsModuleHoldsTest {

    private static final ValueName.Behavior NAMED = new ValueName.Behavior("demo", "measure");

    @Test
    void aBehaviorCalledByABoundaryItsModuleDoesNotHoldIsRefused() {
        BehaviorTarget held = target();
        BehaviorTarget another = target();

        assertEquals("`demo.measure` is called with a boundary that is not the one its module"
                        + " holds",
                assertThrows(IllegalStateException.class,
                        () -> program(held, Map.of(NAMED, another))).getMessage());
    }

    /** And a behavior the index says nothing about is the same disagreement, not a program with a
     *  behavior nothing calls: every behavior of a checked module is one a call may reach. */
    @Test
    void andSoIsOneTheIndexSaysNothingAbout() {
        assertThrows(IllegalStateException.class, () -> program(target(), Map.of()));
    }

    /**
     * And so is the same disagreement the other way round: a behavior of a module of this compile
     * that the module does not declare.
     *
     * <p>Which is what says the two name the same behaviors. Held in one direction, an index could
     * answer for a behavior of a module this program emits that the module has nothing for, and a
     * reader emitting that module would emit a program with a call to a behavior it never wrote.
     */
    @Test
    void andSoIsOneTheModuleThatDeclaresItDoesNotDeclare() {
        BehaviorTarget held = target();
        Map<ValueName.Behavior, BehaviorTarget> index = new LinkedHashMap<>();
        index.put(NAMED, held);
        index.put(new ValueName.Behavior("demo", "nobodyWroteThis"), target());

        assertEquals("this program is callable at 2 behaviors of the modules it emits, which"
                        + " declare 1",
                assertThrows(IllegalStateException.class, () -> program(held, index)).getMessage());
    }

    /** And the program a correct assembler makes is one this admits. */
    @Test
    void aBehaviorCalledByTheBoundaryItsModuleHoldsIsMade() {
        BehaviorTarget held = target();

        CheckedProgram program = program(held, Map.of(NAMED, held));

        assertSame(held, program.behavior(NAMED));
        assertSame(held.signature(), program.module("demo").behavior(NAMED).signature());
    }

    private static CheckedProgram program(BehaviorTarget held,
                                          Map<ValueName.Behavior, BehaviorTarget> index) {
        CheckedBehavior behavior = new CheckedBehavior(NAMED, held,
                EnsuresEnforcement.NoContract.INSTANCE, List.of());
        return new CheckedProgram(
                List.of(new CheckedModule("demo", List.of(behavior), List.of(), List.of())),
                List.of(), List.of(), index, DefaultStdlib.get().kernelSignatures());
    }

    /** One boundary, made afresh each time it is asked for: what tells two of these apart is that
     *  they are two, and not what either of them says. */
    private static BehaviorTarget target() {
        return new BehaviorTarget(new CheckedSignature(List.of(Type.INT), Type.INT),
                new CheckedImplementation.Injected());
    }
}
