package souther.compiler;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * How a primitive is written is one table, and a name minted from it is read back through the
 * inverse of that mint.
 *
 * <p>It had been written three times: the shown form inside {@code Type.show}, and two recoveries
 * from the spelling — one in the codec generator, which raised for anything outside its own list,
 * and one in the fixture reader. Three copies of the language's own spelling agreeing was the whole
 * of the guarantee that a primitive case is emitted with the codec that reads it.
 */
class ThePrimitiveAMemberNamesIsReadOffTheNameItWasMintedFromTest {


    @Test
    void aNameMintedFromAPrimitiveReadsBackAsThatPrimitive() {
        for (Type.Prim prim : Type.Prim.values()) {
            assertEquals(prim, TypeName.primitive(prim).primitiveKind(), prim.toString());
            assertEquals(prim.shown(), Type.show(prim), prim.toString());
        }
    }

    /** A primitive-module name that denotes no primitive answers nothing rather than the first thing
     *  a table happens to have, and a declared type is not a primitive at all. */
    @Test
    void aNameThatNamesNoPrimitiveAnswersNothing() {
        assertNull(TypeName.SOME.primitiveKind());
        assertNull(TypeName.NONE.primitiveKind());
        assertNull(new TypeName("demo", "Int").primitiveKind());
    }

    /** `Raw` is a primitive and no scalar a leaf codec exists for, which is the one place the two
     *  questions come apart. */
    @Test
    void theReservedPrimitiveIsAPrimitiveAndNoLeafScalar() {
        assertEquals(Type.Prim.RAW, TypeName.primitive(Type.Prim.RAW).primitiveKind());
        assertNull(LeafScalar.of(Type.Prim.RAW));
    }

    /**
     * And a primitive standing as a member of a behavior's answer is emitted with the leaf codec its
     * name is read back to — the path that recovered the primitive from a spelling of its own.
     */
    @Test
    void aPrimitiveMemberIsEmittedWithItsLeafCodec() throws Exception {
        String source = """
                data A = { x: Int }
                behavior asInt : (n: Int) -> Int | A
                let asInt (n) = n
                behavior asA : (n: Int) -> Int | A constructs A
                let asA (n) = A { x = n }
                """;
        assertEquals("{\"type\":\"Int\",\"value\":7}", Crossing.of(source, "p", "asInt", "7"));
        assertEquals("{\"x\":7,\"type\":\"A\"}", Crossing.of(source, "p", "asA", "7"));
    }
}
