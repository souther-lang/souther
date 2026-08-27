package souther.compiler.sites;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A {@code MetaVar} stands for the type one call settles on and is rewritten as soon as something
 * says what that is. It lives no longer than the elaboration that made it, and no answer the
 * compiler stores holds one — so one arriving at the boundary is a fact taken from the middle of an
 * elaboration, and a reader shown it would render an internal spelling and mean nothing by it.
 *
 * <p>Inside as well as at the top. Most of the shapes an elaboration builds hold their types rather
 * than being one, so a check that read only the outside would pass a list of them, a function
 * answering one, a map keyed by one.
 */
class AVariableOneApplicationLeftOpenDoesNotLeaveItTest {

    private static final Type OPEN =
            new Type.MetaVar(new BindingOwner.OfValue("m", "f"), "'a");

    private static final Evidence DECLARED = new Evidence.Declared();

    @Test
    void oneOnItsOwnIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new TypeFact(OPEN, DECLARED));
    }

    @Test
    void oneInsideAnythingIsRefused() {
        List<Type> holding = List.of(
                new Type.ListOf(OPEN),
                new Type.SetOf(OPEN),
                new Type.OptionOf(OPEN),
                new Type.MapOf(OPEN, Type.INT),
                new Type.MapOf(Type.INT, OPEN),
                new Type.TupleOf(List.of(Type.INT, OPEN)),
                new Type.FnOf(List.of(Type.INT), OPEN),
                new Type.FnOf(List.of(OPEN), Type.INT),
                // and however deep it is
                new Type.ListOf(new Type.OptionOf(new Type.ListOf(OPEN))));
        for (Type each : holding) {
            assertThrows(IllegalArgumentException.class, () -> new TypeFact(each, DECLARED),
                    each + " holds a variable one application left open");
        }
    }

    @Test
    void aVariableADeclarationWroteIsNotOne() {
        // What a declaration wrote stands for any type and every use of the declaration holds for
        // it, so it is a type to say. That an inferred one is not shown under the spelling the
        // compiler minted for it is a rule about rendering and not about what may be carried.
        assertDoesNotThrow(() -> new TypeFact(new Type.Var("'a", false), DECLARED));
        assertDoesNotThrow(() -> new TypeFact(new Type.ListOf(new Type.Var("x", true)), DECLARED));
    }

    @Test
    void aFactIsATypeAndWhatReadIt() {
        assertThrows(IllegalArgumentException.class, () -> new TypeFact(null, DECLARED));
        assertThrows(IllegalArgumentException.class, () -> new TypeFact(Type.INT, null));
    }
}
