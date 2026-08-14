package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declaration has a meaning where its names were answered, and not where they merely went
 * unreported.
 *
 * <p>Some names are left unanswered on purpose and said nothing about. A module this compilation
 * has and cannot use is one: what is wrong with it is reported on its own source, and a name it was
 * to have exported stands in the importer's scope as an identity nothing declares, so the importer
 * is not told a second time about a file that is fine.
 *
 * <p>That is an absence, and it is the same absence as a misspelling — it is only the report that
 * differs. Reading "was anything reported while this declaration was being read" as "were its names
 * answered" makes the two come apart, and the declaration made of a name nothing answered is handed
 * to the stages below as one that has a meaning.
 */
class ANameLeftUnansweredCountsWhetherOrNotItWasReportedTest {

    /** Takes a name the compiler ships, which no source may — so the module is here and unusable. */
    private static final String RESERVED = """
            module souther.evil exposing ( X )

            data X = Int
            """;

    private static final String IMPORTER = """
            module app.main exposing ( A, Note )

            import souther.evil ( X )

            data A = { x: X }
            data Note = { text: String }
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("evil.sou", RESERVED);
        byId.put("main.sou", IMPORTER);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    private static boolean has(Compilation c, String declared) {
        return c.db().ask(new Names.Definition(new TypeKey("app.main", declared))).present();
    }

    @Test
    void aDeclarationMadeOfANameNothingAnsweredHasNoMeaningEvenWhereNothingWasSaid() {
        Compilation c = compiled();

        assertFalse(has(c, "A"), "`X` was not answered, whatever was or was not reported about it");
        assertTrue(has(c, "Note"), "and a declaration reaching neither is untouched");
    }
}
