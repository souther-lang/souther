package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two sources a reader below the derivation is answered from are at the same rung.
 *
 * <p>A reader there asks {@link Declarations} for an identity and is answered from the compilation's
 * registry or from the language's own vocabulary. Were the second at the rung below, the only
 * representation both could be in would be the node, no table of derived declarations could be
 * handed out, and every reader below the derivation would hold declarations with nothing saying they
 * had come out.
 */
class WhatTheLanguageDeclaresIsLiftedToTheDerivedWorldTest {

    private static final Stdlib LIBRARY = DefaultStdlib.get();

    /**
     * Every one of them, and which case it lifts to.
     *
     * <p>Written out because the population is what the claim is about: a declaration the library
     * adds tomorrow is one nothing here says anything about unless this fails when it appears.
     */
    @Test
    void everyDeclarationTheLanguageGivesIsLifted() {
        Declarations.Vocabulary<Derived.Def> derived = Declarations.Vocabulary.ofDerived(LIBRARY);

        Map<String, String> lifted = new LinkedHashMap<>();
        LIBRARY.languageDeclarations().forEach((address, def) ->
                lifted.put(address.toString(),
                        derived.declaration(address).getClass().getSimpleName()));

        assertEquals(Map.of(
                        "souther.decimal.RoundingMode", "Sum",
                        "souther.decimal.HALF_UP", "Unit",
                        "souther.decimal.HALF_EVEN", "Unit",
                        "souther.decimal.HALF_DOWN", "Unit",
                        "souther.decimal.UP", "Unit",
                        "souther.decimal.DOWN", "Unit",
                        "souther.decimal.CEILING", "Unit",
                        "souther.decimal.FLOOR", "Unit"),
                lifted,
                "what the language declares is a sum and the units under it, and there is nothing "
                        + "deriving one of those would establish");
    }

    /** And each is the declaration it was lifted from, so nothing was rewritten on the way. */
    @Test
    void aLiftedDeclarationIsTheDeclarationItWasLiftedFrom() {
        Declarations.Vocabulary<Derived.Def> derived = Declarations.Vocabulary.ofDerived(LIBRARY);

        List<String> mismatched = new ArrayList<>();
        LIBRARY.languageDeclarations().forEach((address, def) -> {
            if (!def.equals(derived.declaration(address).declaration().node())) {
                mismatched.add(address.toString());
            }
        });

        assertEquals(List.of(), mismatched);
    }

    /** The vocabulary answers about the library module as a module, which is how a reader that has
     *  a name rather than an address reaches one. */
    @Test
    void theVocabularyAnswersForTheLibraryModule() {
        Declarations.Vocabulary<Derived.Def> derived = Declarations.Vocabulary.ofDerived(LIBRARY);

        Map<String, Derived.Def> inDecimal = derived.declaredIn("souther.decimal");

        assertEquals(8, inDecimal.size());
        assertInstanceOf(Derived.Sum.class, inDecimal.get("RoundingMode"));
        assertEquals(Map.of(), derived.declaredIn("no.such.module"));
    }

    /**
     * A product is refused rather than lifted.
     *
     * <p>The case that needs the derivation and the reason the other two do not: a product's
     * boundary representation is read off its shape and nothing has read it here. Lifted anyway, it
     * would be a declaration this world says came out with nothing having derived it, and the type
     * every reader below holds would say otherwise.
     *
     * <p>A fault in the compiler and not a report, because the library is this compiler's own
     * source.
     */
    @Test
    void aProductTheLanguageDeclaredWouldBeRefused() {
        Normalized.Def product = Normalized.Def.ofLanguage(declared("Probe"));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> Derived.Def.ofLanguage(product));

        assertTrue(refused.getMessage().contains("Probe"), refused.getMessage());
        assertTrue(refused.getMessage().contains("derived"), refused.getMessage());
    }

    /** And a sum and a unit are not, which is what says the refusal is about products and not about
     *  the library. */
    @Test
    void aSumAndAUnitAreLifted() {
        assertInstanceOf(Derived.Sum.class,
                Derived.Def.ofLanguage(Normalized.Def.ofLanguage(declared("Band"))));
        assertInstanceOf(Derived.Unit.class,
                Derived.Def.ofLanguage(Normalized.Def.ofLanguage(declared("Low"))));
    }

    /** One declaration of a module written for these, resolved as any module is. */
    private static Hir.Def declared(String name) {
        souther.compiler.ast.Ast.Module parsed = souther.compiler.frontend.CstFrontend.parse("""
                module probe

                data Probe = { v: Int }
                data Low
                data High
                data Band = Low | High
                """);
        Hir.Module resolved = Resolve.resolving(parsed,
                SyntaxSymbols.of(parsed, LIBRARY)).module();
        for (Hir.Def def : resolved.defs()) {
            if (def.name().equals(name)) {
                return def;
            }
        }
        throw new AssertionError("the probe module declares `" + name + "`");
    }
}
