package souther.compiler.check;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The rule is asked of the type, not of the name a source spelling happened to resolve to. Written
 * `Raw` currently denotes a reference rather than the primitive, and asking the reference is what
 * refuses it in a compiled module — but the primitive is the same type, so correcting that
 * representation must not be what decides whether the boundary admits it. Both readings refuse it:
 * no name of the language's namespace is a model's declaration, and `Raw` is no scalar the boundary
 * writes.
 *
 * <p>A primitive is classified without asking the model anything, which is why these pass no symbols:
 * needing them would mean the answer could depend on what a module declared, and it cannot.
 */
class TheBoundaryVocabularyRuleReadsTheTypeTest {

    @Test
    void theReservedPrimitiveIsNoScalarTheBoundaryWrites() {
        assertNull(LeafScalar.of(Type.Prim.RAW));
    }

    /**
     * A Rational is no scalar the boundary writes, and the capability is why.
     *
     * <p>Asserted beside the absence rather than left to the sweep below: `Raw` is absent from the
     * leaves because its spelling is reserved while it still answers yes to having an external form,
     * and a Rational is absent because it answers no (ADR-0116). Two primitives outside one set for
     * two reasons, and reading only the set they are both outside of would not say which.
     */
    @Test
    void anExactQuotientIsNoScalarTheBoundaryWrites() {
        assertNull(LeafScalar.of(Type.Prim.RATIONAL));
        assertFalse(TypeOps.hasExternalForm(Type.Prim.RATIONAL, null));
    }

    /** The primitives no boundary writes, which is what the sweep below is about. Closed here and
     *  read from both sides, so a primitive added to the language is either given a leaf codec or
     *  named here, and one of these growing a codec fails as well. */
    private static final Set<Type.Prim> WRITTEN_BY_NO_BOUNDARY =
            Set.of(Type.Prim.RAW, Type.Prim.RATIONAL);

    @Test
    void theScalarsTheBoundaryWritesAreNamedByALeaf() {
        for (Type.Prim prim : Type.Prim.values()) {
            assertEquals(!WRITTEN_BY_NO_BOUNDARY.contains(prim), LeafScalar.of(prim) != null,
                    prim.toString());
        }
    }

    /**
     * No name of the language's own namespace is a declaration to admit — not the ones standing for a
     * scalar, and not the ones standing for nothing.
     *
     * <p>Held here rather than through a module that names one, because no source reaches it: `Some`
     * and `None` in a union are refused as members before a signature is built (E1613). What the
     * witness says is that a model declared the name, and one minted for `Int` or for `Some` is that
     * sentence being false while every reader below goes on acting as though it were true. Where a
     * scalar's name legitimately arrives — a union's member — the position tells the two apart and
     * holds each to its own rule.
     *
     * <p>Every case of what the language declares is written out, and the two closed sets are read
     * for them rather than a few listed by hand: one added later is refused here or fails.
     * `symbols` is null throughout, so a case reaching the declaration world at all is the failure
     * rather than a wrong answer from it.
     */
    @Test
    void nothingTheLanguageDeclaresIsAModelsDeclaration() {
        for (Type.Prim prim : Type.Prim.values()) {
            assertNull(CrossingNominal.admitted(TypeSymbol.primitive(prim), null), prim.toString());
        }
        for (LanguageCaseId id : LanguageCaseId.values()) {
            assertNull(CrossingNominal.admitted(new TypeSymbol.LanguageCase(id), null),
                    id.toString());
        }
    }
}
