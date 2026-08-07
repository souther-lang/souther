package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.BoundaryMapKey;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Admitting a boundary Map key establishes what its text representation is, and that is what the
 * checker hands on: a witness, not a yes. What a reader that has to build a codec needs is which
 * representation, and it must not have to work that out again from the type.
 *
 * <p>The two questions the one predicate used to answer are separate here. Whether a type may stand
 * as a key in a signature admits a type variable, which the core's generic signatures are written
 * with; whether a concrete key can be converted does not, because a variable is evidence of nothing.
 */
class ABoundaryMapKeyIsClassifiedOnceTest {

    private static final String MODULE = """
            module demo

            data ProductId = String
            data EmployeeNo = Int
            data Price = Decimal
            data Nested = ProductId

            data Won
            data Lost
            data Outcome = Won | Lost

            data Slot = { hour: Int, room: String }
            """;

    private final Symbols symbols = Symbols.of(resolved());

    /** A sum's cases are read by name, so the module has to be resolved before its enumerations can
     *  be asked about. */
    private static Ast.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    private BoundaryMapKey classify(Type key) {
        return TypeOps.classifyConcreteMapKey(key, symbols);
    }

    private Type named(String name) {
        return Type.ref(symbols.own(name));
    }

    @Test
    void aStringKeyIsText() {
        assertEquals(new BoundaryMapKey.Text(), classify(Type.STRING));
    }

    @Test
    void aTemporalKeyIsItsOwnRepresentation() {
        assertEquals(new BoundaryMapKey.Date(), classify(Type.DATE));
        assertEquals(new BoundaryMapKey.DateTime(), classify(Type.DATETIME));
    }

    /** A newtype carries both what it is called and what it is admitted through, so a reader that
     *  wraps a key and a reader that converts the text it wraps take different parts of one answer. */
    @Test
    void aNewtypeCarriesTheRepresentationItIsAdmittedThrough() {
        assertEquals(new BoundaryMapKey.Newtype(symbols.own("ProductId"), new BoundaryMapKey.Text()),
                classify(named("ProductId")));
    }

    @Test
    void anEnumerationIsNamedApartFromANewtype() {
        assertEquals(new BoundaryMapKey.UnitEnum(symbols.own("Outcome")), classify(named("Outcome")));
    }

    /** The representations a newtype may be admitted through are the rule's, not the witness type's.
     *  A newtype over a primitive with no key representation is refused, and the refusal is the
     *  classifier's — nothing downstream repeats it. */
    @Test
    void aNewtypeOverAPrimitiveWithNoKeyRepresentationIsNotClassified() {
        assertNull(classify(named("EmployeeNo")));
        assertNull(classify(named("Price")));
    }

    @Test
    void aNewtypeOverANewtypeIsNotClassified() {
        assertNull(classify(named("Nested")));
    }

    @Test
    void aProductDataIsNotClassified() {
        assertNull(classify(named("Slot")));
    }

    @Test
    void aPrimitiveWithNoKeyRepresentationIsNotClassified() {
        assertNull(classify(Type.INT));
        assertNull(classify(Type.BOOL));
        assertNull(classify(Type.DECIMAL));
    }

    /**
     * A type variable stands for a key rather than being one. The core's {@code Map<'k, 'a>}
     * signatures are written with it, so a signature admits it; it classifies as nothing, because
     * there is no representation to name until it is monomorphised.
     */
    @Test
    void aTypeVariableIsAdmissibleInASignatureAndClassifiesAsNothing() {
        Type var = Type.var("'k");
        assertTrue(TypeOps.isMapKeyAdmissibleInSignature(var, symbols));
        assertNull(classify(var));
    }

    @Test
    void aSignatureAdmitsExactlyWhatClassifiesPlusTheVariable() {
        assertTrue(TypeOps.isMapKeyAdmissibleInSignature(Type.STRING, symbols));
        assertTrue(TypeOps.isMapKeyAdmissibleInSignature(named("Outcome"), symbols));
        assertFalse(TypeOps.isMapKeyAdmissibleInSignature(Type.INT, symbols));
        assertFalse(TypeOps.isMapKeyAdmissibleInSignature(named("EmployeeNo"), symbols));
    }
}
