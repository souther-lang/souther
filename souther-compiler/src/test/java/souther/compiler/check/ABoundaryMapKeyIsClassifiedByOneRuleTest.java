package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.check.BoundaryMapKey;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Admitting a boundary Map key establishes what its text representation is, and that is what the
 * checker answers with: a witness, not a yes. Every reader that has to build a codec asks this one
 * rule which representation it has, rather than writing the kinds out again.
 *
 * <p>The two questions the one predicate used to answer are separate here. Whether a type may stand
 * as a key in a signature admits a type variable, which the core's generic signatures are written
 * with; whether a concrete key can be converted does not, because a variable is evidence of nothing.
 */
class ABoundaryMapKeyIsClassifiedByOneRuleTest {

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

    /** The base a newtype wraps is in the case rather than beside it. Every reader of a named key
     *  delegates to that type's own decoder and to a {@code value()} typed {@code () -> String},
     *  which is true of a String-backed newtype and of nothing else — so a newtype over another base
     *  is a case of its own, and reaches every reader as one. */
    @Test
    void aStringBackedNewtypeIsItsOwnCase() {
        assertEquals(new BoundaryMapKey.StringNewtype(symbols.own("ProductId")),
                classify(named("ProductId")));
    }

    @Test
    void anEnumerationIsNamedApartFromANewtype() {
        assertEquals(new BoundaryMapKey.UnitEnum(symbols.own("Outcome")), classify(named("Outcome")));
    }

    /** Which bases a newtype key may wrap is the rule's, and the refusal is the classifier's —
     *  nothing downstream repeats it. */
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
