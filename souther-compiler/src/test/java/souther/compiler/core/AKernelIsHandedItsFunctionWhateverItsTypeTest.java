package souther.compiler.core;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A function none of whose body is emitted is one the call never applies, and what a kernel is
 * handed it hands the runtime whatever the function's type is.
 *
 * <p>Both answers come from {@link Core.Call#omitsFunctionBody}, which the emitter and the coverage
 * numbering read, so the exception for a kernel is held where it is decided.
 */
class AKernelIsHandedItsFunctionWhateverItsTypeTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private static final Type.FnOf NEVER_APPLIED_FUNCTION =
            new Type.FnOf(List.of(Type.NOTHING), Type.BOOL);
    private static final Type.ListOf NO_ELEMENTS = new Type.ListOf(Type.NOTHING);

    private static final Core.Reached.OfKernel FIND = new Core.Reached.OfKernel(
            new ReachName.OfLibrary(ValueName.Stdlib.operation("List", "find")), Kernel.LIST_FIND);

    private static final Core.Reached.OfDeclaration HELPER = new Core.Reached.OfDeclaration(
            new ReachName.Own(new ValueName.Helper("demo", "pick")));

    private static Core.Read read(String name, int slot, Type type) {
        return new Core.Read(name, new BindingId(OWNER, slot), type, POS);
    }

    private static List<Core> arguments() {
        return List.of(read("xs", 0, NO_ELEMENTS), read("pred", 1, NEVER_APPLIED_FUNCTION));
    }

    @Test
    void aKernelHandsOverAFunctionTakingTheBottom() {
        Core.Call call = new Core.Call(FIND, arguments(), ConstructOccurrence.unwritten(),
                new Core.CallSettlement.AtKernel(List.of(NO_ELEMENTS, NEVER_APPLIED_FUNCTION),
                        Core.KernelFact.None.INSTANCE),
                Type.BOOL, POS);

        assertFalse(call.omitsFunctionBody(1));
        assertEquals(Core.Call.FunctionArgument.HANDED_OVER, call.functionArgument(1, null));
    }

    @Test
    void aDeclarationIsNotHandedAFunctionTakingTheBottom() {
        Core.Call call = new Core.Call(HELPER, arguments(), ConstructOccurrence.unwritten(),
                Core.CallSettlement.None.INSTANCE, Type.BOOL, POS);

        assertTrue(call.omitsFunctionBody(1));
        assertEquals(Core.Call.FunctionArgument.NEVER_APPLIED, call.functionArgument(1, null));
        assertFalse(call.omitsFunctionBody(0), "a list is not a function");
    }
}
