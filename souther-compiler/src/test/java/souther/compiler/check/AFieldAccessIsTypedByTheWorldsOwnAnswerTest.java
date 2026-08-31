package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.observe.FieldTypes;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Crossing a {@code .} asks the world the reading is being made in, and answers with what it says.
 *
 * <p>{@link DeclaredTypeEvidence} owns how evidence flows through an expression — a {@code let} it
 * enters, a name it follows, a definition it steps into. What a field of a declaration holds is not
 * that walk's to work out: an accepted program has one answer to it and it is the check's, and a
 * walk deriving a second from the declarations would be the reading a comparison is made against
 * and the reading a projection is typed by coming apart.
 *
 * <p>Held to by a world that answers something the declarations do not. The walk has the
 * declarations in hand — it resolves names against them — so an answer that follows the world it
 * was handed rather than what it could read there is the whole of the property.
 */
class AFieldAccessIsTypedByTheWorldsOwnAnswerTest {

    private static final String MODULE = """
            module demo

            data Line = { amount: Int }
            data Order = { line: Line }

            let sample = Order { line = Line { amount = 1 } }
            let taken = sample.line
            """;

    private final Compilation compilation = compiled();
    private final String module = compilation.modules().get(0);
    private final Symbols symbols = Scopes.derived(compilation.db(), module).value();
    private final Map<String, Hir.FnDef> values =
            compilation.db().ask(new Bodies.ModuleDefinitions(module)).value();

    private static Compilation compiled() {
        Compilation c = Compilation.ofSource(MODULE, "Main");
        c.answerEverything();
        return c;
    }

    /** What the check settled, which is what an accepted program's readers are handed. */
    @Test
    void aFieldIsWhatTheCheckSettledItHolds() {
        Type taken = new DeclaredTypeEvidence(symbols, checked(), values)
                .declaredTypeOf(bodyOf("taken"));
        assertEquals("Line", assertInstanceOf(Type.Ref.class, taken).name().name(),
                "`sample.line` is declared to hold a `Line`");
    }

    /**
     * And a world saying something else is what is answered — the walk keeps no reading of its own
     * to fall back to.
     *
     * <p>A program where {@code Order.line} holds a {@code String} is one no declaration here
     * writes, which is the point: what says the walk is not deriving this is that it answers the
     * one thing it could not have read off the declarations it is resolving names against.
     */
    @Test
    void andNotWhatTheDeclarationsWouldSayBesideIt() {
        FieldTypes saysAString = _ -> Map.of("line", Type.STRING);
        Type taken = new DeclaredTypeEvidence(symbols, saysAString, values)
                .declaredTypeOf(bodyOf("taken"));
        assertEquals(Type.STRING, taken,
                "the walk read the declarations rather than the world it was handed");
    }

    /**
     * A product the check said nothing about is not a product with no such field.
     *
     * <p>Answered as an absence, a value of it would be compared as whatever its parts happen to
     * look like — and a row about it would hold here and fail wherever the shape was in hand. So
     * the accepted reading refuses, and nothing falls back to reading the declaration.
     */
    @Test
    void andAProductWithNoSettledShapeIsRefusedRatherThanAnsweredEmpty() {
        FieldTypes nothingSettled = new CheckedFieldTypes(symbols, _ -> null);
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> nothingSettled.of(orderOf()));
        assertEquals(true, refused.getMessage().contains("Order"),
                "the refusal names the declaration nothing was settled about: " + refused.getMessage());
    }

    /** The declaration {@code Order}, as the reading of this module names it. */
    private TypeSymbol orderOf() {
        Type sample = new DeclaredTypeEvidence(symbols, checked(), values)
                .declaredTypeOf(bodyOf("sample"));
        return assertInstanceOf(Type.Ref.class, sample).name();
    }

    private FieldTypes checked() {
        return Shapes.fieldTypes(compilation.db(), symbols);
    }

    private Hir.Expr bodyOf(String name) {
        return assertInstanceOf(Hir.FnBody.Written.class, values.get(name).body()).expr();
    }
}
