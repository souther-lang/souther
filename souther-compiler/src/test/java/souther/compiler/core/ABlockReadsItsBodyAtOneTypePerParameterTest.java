package souther.compiler.core;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A block holds one type for each of its parameters, and what it answers is its body's type.
 */
class ABlockReadsItsBodyAtOneTypePerParameterTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingId X = new BindingId(new BindingOwner.OfValue("demo", "b"), 0);

    @Test
    void aBlockWithAParameterItHasNoTypeForIsRefused() {
        Core body = new Core.Read("x", X, Type.INT, POS);
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Block(List.of(new Core.Binder("x", X)), List.of(), body, POS));
    }

    @Test
    void theTypesItReadsItsParametersAtAreItsOwn() {
        List<Type> paramTypes = new ArrayList<>(List.of(Type.INT));
        Core.Block block = new Core.Block(List.of(new Core.Binder("x", X)), paramTypes,
                new Core.Read("x", X, Type.INT, POS), POS);
        paramTypes.set(0, Type.BOOL);
        assertEquals(new Type.FnOf(List.of(Type.INT), Type.INT), block.type(),
                "a list the block was built from, changed afterwards, is not the block");
    }
}
