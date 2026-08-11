package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.MapKeyRepresentation;
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
 * <p>A newtype is a key exactly when what it wraps is a key, at any depth. Which is why the tests
 * below are a matrix over (base, how many wrappers) rather than a list of admitted types: what is
 * being fixed is the induction, not the four bases it happens to close over today.
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
            data Flag = Bool
            data 貸出日 = Date
            data StampedAt = DateTime

            data Won
            data Lost
            data Outcome = Won | Lost
            data OutcomeKey = Outcome

            data WrappedId = ProductId
            data WrappedDay = 貸出日
            data WrappedNo = EmployeeNo

            data A = Date
            data B = A
            data C = B

            data Slot = { hour: Int, room: String }
            data Priced = { at: Int }
            data Mixed = Won | Priced
            data MixedKey = Mixed
            """;

    private final Symbols symbols = Symbols.of(resolved());

    /** A sum's cases are read by name, so the module has to be resolved before its enumerations can
     *  be asked about. */
    private static Ast.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    private MapKeyRepresentation classify(Type key) {
        return TypeOps.classifyConcreteMapKey(key, symbols);
    }

    private Type named(String name) {
        return Type.ref(symbols.own(name));
    }

    /** What a named key must classify as: the outermost name, whatever it wraps. Reaching for the
     *  base's representation would name a type whose codec is not the one the map's keys go
     *  through. */
    private void assertNamedKey(String name) {
        assertEquals(new MapKeyRepresentation.NamedKey(symbols.own(name)), classify(named(name)));
    }

    // --- the leaves ---------------------------------------------------------------------------

    @Test
    void aStringKeyIsText() {
        assertEquals(new MapKeyRepresentation.Text(), classify(Type.STRING));
    }

    @Test
    void aTemporalKeyIsItsOwnRepresentation() {
        assertEquals(new MapKeyRepresentation.Date(), classify(Type.DATE));
        assertEquals(new MapKeyRepresentation.DateTime(), classify(Type.DATETIME));
    }

    @Test
    void anEnumerationIsANamedKey() {
        assertNamedKey("Outcome");
    }

    // --- one wrapper over each leaf -----------------------------------------------------------

    @Test
    void aNewtypeOverEachKeyableLeafIsANamedKey() {
        assertNamedKey("ProductId");     // String
        assertNamedKey("貸出日");         // Date
        assertNamedKey("StampedAt");     // DateTime
        assertNamedKey("OutcomeKey");    // an enumeration
    }

    // --- two and three wrappers ---------------------------------------------------------------

    @Test
    void aNewtypeOverANewtypeIsANamedKeyUnderItsOwnName() {
        assertNamedKey("WrappedId");     // ProductId -> String
        assertNamedKey("WrappedDay");    // 貸出日 -> Date
    }

    /**
     * Three deep, so what is fixed is that the walk recurses rather than that it unwraps once more
     * than it used to. Each level is a named key under its own name.
     */
    @Test
    void theRuleHoldsAtEveryDepth() {
        assertNamedKey("A");
        assertNamedKey("B");
        assertNamedKey("C");
    }

    // --- negative controls --------------------------------------------------------------------

    /** An {@code Int} is written as a JSON number in a field, so writing it as a string in a key
     *  would make a type's external form depend on where it stands (ADR-0040). Wrapping it does not
     *  change that, which is the same rule read the other way. */
    @Test
    void aLeafWithNoKeyRepresentationIsNotClassified() {
        assertNull(classify(Type.INT));
        assertNull(classify(Type.BOOL));
        assertNull(classify(Type.DECIMAL));
    }

    @Test
    void aNewtypeOverSuchALeafIsNotClassifiedEither() {
        assertNull(classify(named("EmployeeNo")));
        assertNull(classify(named("Price")));
        assertNull(classify(named("Flag")));
    }

    @Test
    void aNewtypeOverThatNewtypeIsStillNotClassified() {
        assertNull(classify(named("WrappedNo")));
    }

    /** One field-bearing case is enough to make a sum a discriminated object, which no JSON key can
     *  be — so neither it nor a newtype over it is a key. */
    @Test
    void aSumWithAFieldBearingCaseIsNotClassified() {
        assertNull(classify(named("Mixed")));
        assertNull(classify(named("MixedKey")));
    }

    @Test
    void aProductDataIsNotClassified() {
        assertNull(classify(named("Slot")));
    }

    // --- what a signature admits ---------------------------------------------------------------

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
        assertTrue(TypeOps.isMapKeyAdmissibleInSignature(named("C"), symbols));
        assertFalse(TypeOps.isMapKeyAdmissibleInSignature(Type.INT, symbols));
        assertFalse(TypeOps.isMapKeyAdmissibleInSignature(named("WrappedNo"), symbols));
    }
}
