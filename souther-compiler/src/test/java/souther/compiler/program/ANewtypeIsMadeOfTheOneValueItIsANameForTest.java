package souther.compiler.program;

import souther.compiler.core.ValueShape;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@link CheckedData.Newtype} is refused a shape that is not one value.
 *
 * <p>What {@link CheckedData.Newtype#wrapped()} rests on. It answers with the type of the one field
 * the shape holds, and a shape holding another number of them would have it answer with whichever
 * field happened to be laid out first — an answer about a type the declaration is not a name for,
 * and one nothing downstream could tell from the right one.
 *
 * <p>Held against a shape the checker made rather than one assembled here, so what is refused is a
 * shape of the kind this arm is handed. Nothing in the front end writes a newtype of more than one
 * field today — the desugaring writes exactly the one — which is why the warrant is stated where the
 * value is made and asked for here: a later producer reaches this constructor, and this is the
 * refusal it meets.
 */
class ANewtypeIsMadeOfTheOneValueItIsANameForTest {

    private static final String MODULE = """
            module demo

            data Amount = Int

            data Common = { id: Int, tag: String }
            """;

    /** The shapes the check settled for {@code demo}, by the declaration each is of. */
    private static Map<TypeSymbol.AtModule, ValueShape> shapes() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        Map<TypeSymbol.AtModule, ValueShape> shapes =
                compilation.db().ask(new Shapes.ValueShapes("demo")).value();
        assertNotNull(shapes, "the check answered what a value of each declaration is made of");
        return shapes;
    }

    private static ValueShape shapeOf(String name) {
        for (Map.Entry<TypeSymbol.AtModule, ValueShape> each : shapes().entrySet()) {
            if (each.getKey().name().equals(name)) {
                return each.getValue();
            }
        }
        throw new AssertionError(name + " is not a declaration of this module");
    }

    @Test
    void aShapeOfMoreThanOneFieldIsNotOneValueUnderAnotherName() {
        ValueShape common = shapeOf("Common");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new CheckedData.Newtype(common));

        assertTrue(refused.getMessage().contains("Common"), refused::getMessage);
    }

    /** And the shape a newtype is declared with is taken, so the refusal is about the shape and not
     *  about the arm. */
    @Test
    void andTheOneItIsDeclaredWithIsTaken() {
        CheckedData.Newtype amount = new CheckedData.Newtype(shapeOf("Amount"));

        assertEquals(shapeOf("Amount").fields().getFirst().type(), amount.wrapped());
    }
}
