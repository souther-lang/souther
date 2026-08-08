package souther.compiler.check;

import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a number is, asked three ways, of the same six types.
 *
 * <p>They read alike and they are not one question. Arithmetic is closed only over a newtype directly
 * over a number, which the language states and means (spec §newtype-arithmetic). Being an ordered
 * number reaches the recursive base, which is what a comparison reads (ADR-0047). Whether the affine
 * domain can carry a value is the analyser's own capability, and answering it with the first is how a
 * comparison the language accepts stopped reaching the reasoning (#461).
 *
 * <p>Held as a table because the three coincide on most types and part on exactly the ones that
 * matter. A change to any of them shows here as a cell, and which cell says whether the language's
 * capability moved or the analyser's did.
 */
class ThreeQuestionsAboutANumberAndThreeAnswersTest {

    private static final String TYPES = """
            module example.numbers

            data Minute = Int
            data StartMinute = Minute

            data Ratio = Decimal
            data Share = Ratio

            data Label = String
            data Tag = Label
            """;

    private record Answers(Type arithmetic, Type ordered, Type affine) {}

    private static Answers of(String type) {
        Compilation compilation = Compilation.ofSource(TYPES, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        assertNotNull(symbols, "the model did not compile");
        Type t = switch (type) {
            case "Int" -> Type.INT;
            case "Decimal" -> Type.DECIMAL;
            default -> Type.ref(new TypeName(module, type));
        };
        Type base = TypeOps.base(t, symbols);
        return new Answers(
                TypeOps.directNumericNewtypeBase(t, symbols),
                base == Type.INT || base == Type.DECIMAL ? base : null,
                new Terms(symbols).affineScalarBase(t));
    }

    /** A primitive is not a newtype, so arithmetic answers nothing about it as one; it is a number
     * either way. */
    @Test
    void aPrimitiveIsANumberWithoutBeingANewtypeOverOne() {
        assertEquals(new Answers(null, Type.INT, Type.INT), of("Int"));
        assertEquals(new Answers(null, Type.DECIMAL, Type.DECIMAL), of("Decimal"));
    }

    /** One layer over a number: all three agree. */
    @Test
    void aNewtypeDirectlyOverANumberIsANumberEveryWay() {
        assertEquals(new Answers(Type.INT, Type.INT, Type.INT), of("Minute"));
        assertEquals(new Answers(Type.DECIMAL, Type.DECIMAL, Type.DECIMAL), of("Ratio"));
    }

    /**
     * Two layers: arithmetic says no and means it, and the other two say yes.
     *
     * <p>This is the row the three questions part on, and the row #461 was. The language compares
     * such a value because comparison reaches the base; the analyser carries it for the same reason,
     * and used to refuse it by answering with the arithmetic column.
     */
    @Test
    void aNewtypeOverANewtypeIsNoArithmeticAndStillANumber() {
        assertEquals(new Answers(null, Type.INT, Type.INT), of("StartMinute"));
        assertEquals(new Answers(null, Type.DECIMAL, Type.DECIMAL), of("Share"));
    }

    /** And a chain over something that is no number is no number by any of the three. */
    @Test
    void aChainOverSomethingElseIsNotANumberAtAll() {
        assertEquals(new Answers(null, null, null), of("Label"));
        assertEquals(new Answers(null, null, null), of("Tag"));
    }
}
