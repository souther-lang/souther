package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.derive.Deriver;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A named sum the language calls an enumeration is one the boundary writes as a bare tag, and the
 * two are asked of different places.
 *
 * <p>{@link TypeOps#isUnitOnlySum} answers a question about the language — a type whose values can
 * be written out ({@link ValueUniverse}) and whose declaration orders them ({@code TypeOps
 * .orderingEnumeration}). {@link Boundary} answers a question about how a value crosses. They are
 * kept apart on purpose: folding them would make one answer decide both, and the day either moved
 * the other would move with it unasked.
 *
 * <p>Kept apart, they walk the atoms twice, so this holds the relation the spec states between them
 * (spec §sum-discrimination): a unit-only sum crosses as its case's name. It is not a test that two
 * implementations agree — it is the rule that lets them be two. Breaking it deliberately means
 * saying, here, that a sum can be an enumeration in the language and a discriminated object on the
 * wire.
 */
class AnEnumerationIsOneAnswerToTheLanguageAndTheBoundaryTest {

    private static final String MODULE = """
            module m

            data Prospecting
            data Negotiation
            data Won
            data Stage = Prospecting | Negotiation | Won

            data Draft
            data Card = { no: String }
            data Cash = Int
            data Payment = Draft | Card | Cash

            data Domestic
            data Overseas
            data Region = Domestic | Overseas
            data Where  = Region | Draft
            """;

    private final Hir.Module module = derive(MODULE);
    private final Symbols symbols = TypeChecker.symbols(module);

    @Test
    void everyNamedSumIsAnEnumerationToBothOrToNeither() {
        for (Hir.Def def : module.defs()) {
            if (def instanceof Hir.SumData sum) {
                Type type = Type.ref(sum.declares());
                assertEquals(TypeOps.isUnitOnlySum(type, symbols),
                        Boundary.of(type, symbols).representation()
                                instanceof Boundary.Representation.Enumeration,
                        sum.name() + ": the language and the boundary disagree about the form");
            }
        }
    }

    /** And the sums are not all of one kind, so the test above is not two constants agreeing. */
    @Test
    void theModuleHasOneOfEach() {
        assertEquals(true, isEnumeration("Stage"));
        assertEquals(true, isEnumeration("Where"));
        assertEquals(false, isEnumeration("Payment"));
    }

    /**
     * A unit data on its own is not an enumeration, though its only atom is a unit.
     *
     * <p>The atoms alone would say it is. A unit crosses on its own as an empty object — the tag is
     * what admitting it into a sum adds — so being a set of alternatives is a term of the form and
     * not a guard on asking. Held here because it is the one case where reading the atoms without
     * that term gives the wrong answer, and a reader tidying the term away would pass every other
     * test in this file.
     */
    @Test
    void aUnitDataOnItsOwnIsNotAnEnumeration() {
        assertFalse(Boundary.of(Type.ref(named("Draft")), symbols).representation()
                instanceof Boundary.Representation.Enumeration);
        assertFalse(TypeOps.isUnitOnlySum(Type.ref(named("Draft")), symbols));
    }

    private boolean isEnumeration(String sum) {
        return Boundary.of(Type.ref(named(sum)), symbols).representation()
                instanceof Boundary.Representation.Enumeration;
    }

    private souther.compiler.types.TypeSymbol named(String name) {
        for (Hir.Def d : module.defs()) {
            if (d.name().equals(name)) {
                return d.declares();
            }
        }
        throw new AssertionError("the module does not declare " + name);
    }

    private static Hir.Module derive(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        return Deriver.derive(Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY)
                .db().ask(new Names.Resolved("m")).value());
    }
}
