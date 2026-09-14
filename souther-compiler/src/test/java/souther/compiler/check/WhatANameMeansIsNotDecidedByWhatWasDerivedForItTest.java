package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.WrittenName;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.Denotation;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A scope answers what a name means, and no stage's failure changes that answer.
 *
 * <p>Which declaration a spelling written out in full reaches is worked out by asking a registry
 * whether a declaration is there ({@code Registry.identify}). Asked of the derived declarations,
 * that question comes back "nothing is there" for a product whose field names no type — because no
 * representation could be read off its shape — and the spelling denotes nothing. The name is a
 * declaration its module writes all the same, so the module that wrote it out is told this
 * compilation has no such type, and one mistake is two.
 *
 * <p>So the scope a reader below the derivation holds is resolution's. Held here rather than through
 * a program because no program in the suite reaches this branch today: what resolves the names a
 * source wrote is the resolution itself, and the readers below it hold names already answered. A
 * seam nothing reaches is still a seam a reader may reach tomorrow, and what it would be told then
 * is what is written down here.
 */
class WhatANameMeansIsNotDecidedByWhatWasDerivedForItTest {

    /** `Bad` has no representation to derive, and `Fine` beside it has one. */
    private static final String LIB = """
            module lib exposing ( Bad, Fine )

            data Bad = { v: Nowhere }
            data Fine = { n: Int }
            """;

    private static final String APP = """
            module app exposing ( Out )

            import lib ( Fine )
            import lib as L

            data Out = { n: Int }
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("lib.sou", LIB);
        byId.put("app.sou", APP);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }

    /** Written out in full, and under an alias of this module's own making. */
    @Test
    void aQualifiedNameDenotesWhatResolutionSaysItDenotes() {
        Compilation c = compiled();
        TypeScope derived = Scopes.derived(c.db(), "app").value().scope();
        TypeScope resolved = Scopes.resolved(c.db(), "app").value().scope();

        for (String spelling : List.of("lib.Bad", "L.Bad")) {
            Denotation says = derived.resolve(WrittenName.synthetic(spelling, null));

            assertInstanceOf(Denotation.Denotes.class, says,
                    "`" + spelling + "` is a declaration `lib` writes, whatever could be derived"
                            + " for it");
            assertEquals(resolved.resolve(WrittenName.synthetic(spelling, null)), says,
                    "and it denotes what resolution says it denotes");
        }
    }

    /** And the declaration it reaches is the one with no representation, so this is about the name
     *  a failed derivation would have taken away and not about some other name. */
    @Test
    void theDeclarationItReachesIsTheOneWithNoRepresentation() {
        Compilation c = compiled();
        DerivedSymbols symbols = Scopes.derived(c.db(), "app").value();

        assertNotNull(symbols.declaredNode(new souther.compiler.types.TypeKey("lib", "Bad")),
                "`Bad` is read as the declaration it is");
        assertEquals(List.of("E1023"), c.diagnostics().values().stream().flatMap(List::stream)
                        .map(each -> each.diagnostic().code()).toList(),
                "and the field's type naming nothing is the one mistake");
    }
}
