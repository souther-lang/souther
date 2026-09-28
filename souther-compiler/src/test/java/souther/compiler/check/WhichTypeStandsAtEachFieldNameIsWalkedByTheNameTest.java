package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Which type stands at each field name is one answer, and two expansions that reach the same
 * fields give it the same way round.
 *
 * <p>A mapping's equality cannot see which order it was filled in, so two of these that agree are
 * one answer to everything that compares them — the store that decides whether downstream work
 * stands, and every reader holding one against another. An answer that came back in the order the
 * expansion happened to walk would be one a reader could take a field layout off while nothing
 * comparing two of them saw any difference between them. So what is checked here is not that the
 * mapping is right but that two equal ones are walked alike.
 *
 * <p>Where a field stands is a separate question with a separate answer, and the second half of
 * this says that separating them did not lose it: the two declarations below do lay their fields
 * out differently, and that is what the layout says.
 */
class WhichTypeStandsAtEachFieldNameIsWalkedByTheNameTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static TypeSymbol.AtModule named(String type) {
        return TypeSymbols.declared(new TypeKey("demo", type));
    }

    private static Hir.Field field(String name, Type type) {
        return new Hir.Field(name, Hir.TypeRef.of(type, POS), POS);
    }

    private static Hir.Data writing(String type, Hir.Field... fields) {
        return new Hir.Data(WrittenName.synthetic(type, POS), named(type),
                false, List.of(), List.of(fields), List.of(), POS);
    }

    private static FieldExpansion.Of spreading(String type, FieldExpansion.Of brought,
                                               Hir.Field... own) {
        return new FieldExpansion.Of(named(type), writing(type, own),
                List.of(new FieldExpansion.Include.Expanded(
                        Hir.Name.resolved(brought.declares(), POS), brought)));
    }

    private static FieldExpansion.Of alone(String type, Hir.Field... own) {
        return new FieldExpansion.Of(named(type), writing(type, own), List.of());
    }

    /**
     * The same three fields reached two ways: one declaration spreads the first of them in and
     * writes the other two, the other writes all three and in another order again.
     */
    @Test
    void twoExpansionsReachingOneSetOfFieldsAreWalkedAlike() {
        FieldExpansion.Of spread = spreading("Spread",
                alone("Brought", field("weight", Type.DECIMAL)),
                field("name", Type.STRING), field("count", Type.INT));
        FieldExpansion.Of written = alone("Written",
                field("count", Type.INT), field("weight", Type.DECIMAL),
                field("name", Type.STRING));

        Map<String, Type> ofSpread = FieldExpansion.types(spread, FieldExpansion.Refusing.NOTHING);
        Map<String, Type> ofWritten = FieldExpansion.types(written, FieldExpansion.Refusing.NOTHING);

        assertEquals(ofSpread, ofWritten,
                "the two reach the same fields, so they are one answer");
        assertEquals(List.copyOf(ofSpread.keySet()), List.copyOf(ofWritten.keySet()),
                "and one answer is walked one way, whichever walk arrived at it");
        assertEquals(List.of("count", "name", "weight"), List.copyOf(ofSpread.keySet()),
                "which is the order of the names it is keyed on");
    }

    /** And where a field stands is still answered, by the question that answers it. */
    @Test
    void andWhereEachFieldStandsIsStillTheOtherAnswer() {
        FieldExpansion.Of spread = spreading("Spread",
                alone("Brought", field("weight", Type.DECIMAL)),
                field("name", Type.STRING), field("count", Type.INT));
        FieldExpansion.Of written = alone("Written",
                field("count", Type.INT), field("weight", Type.DECIMAL),
                field("name", Type.STRING));

        assertEquals(List.of("weight", "name", "count"),
                FieldExpansion.layout(spread, FieldExpansion.Refusing.NOTHING),
                "what a spread brings in stands before what the declaration writes");
        assertNotEquals(FieldExpansion.layout(spread, FieldExpansion.Refusing.NOTHING),
                FieldExpansion.layout(written, FieldExpansion.Refusing.NOTHING),
                "so the two do lay their fields out differently, and it is this that says so");
    }
}
