package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.check.ClauseMeaning;
import souther.compiler.check.DeclarationMeaning;
import souther.compiler.check.PublishedDeclarationResult;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule an author wrote reads one place alone where it reads the values at a place, or how many
 * it holds, and reads nothing else.
 *
 * <p>That is a fact about the rule and not about where it is written: the same rule on a record
 * and on the field's own type holds back the same place and relates it to nothing. The unit is the
 * rule and not the clause, because {@code a >= 0 && b >= 0} is two rules and {@code a <= b} is
 * one.
 */
class ARulePartReadsOnePlaceAloneOnlyWhereItReadsThatPlaceAndNothingElseTest {

    private static final String MODULE = """
            module shop.rules exposing ( Independent, Related, Chosen, Doubled, Counted, WholeList, CountAgainst, Summed, Touch, Apart )

            data Independent = { a: Int, b: Int } invariant a >= 0 && b >= 0
            data Related = { a: Int, b: Int } invariant a <= b
            data Chosen = { a: Int, b: Int } invariant a > 0 || b > 0
            data Doubled = { a: Int, b: Int } invariant a >= 0 && a <= 99
            data Counted = { es: List<Int> } invariant List.length(es) <= 5
            data WholeList = { es: List<Int> } invariant List.all(e -> e >= 0, es)
            data CountAgainst = { a: Int, es: List<Int> } invariant List.length(es) > a
            data Summed = { a: Int, b: Int } invariant a + b < 100
            data Touch = { account: String, days: Int }
            data Apart = { touches: List<Touch> } invariant List.allDistinctBy(t -> t.account, touches)
            """;

    @Test
    void eachRuleSaysWhetherItReadsOnePlaceAlone() {
        Compilation c = started();
        Map<String, List<Boolean>> expected = new LinkedHashMap<>();
        expected.put("Independent", List.of(true, true));
        expected.put("Related", List.of(false));
        expected.put("Chosen", List.of(false));
        expected.put("Doubled", List.of(true, true));
        expected.put("Counted", List.of(true));
        expected.put("WholeList", List.of(true));
        expected.put("CountAgainst", List.of(false));
        expected.put("Summed", List.of(false));
        expected.put("Apart", List.of(false));

        Map<String, List<Boolean>> said = new LinkedHashMap<>();
        for (String name : expected.keySet()) {
            said.put(name, readsOnePlaceAlone(c, name));
        }

        assertEquals(expected, said);
    }

    private static List<Boolean> readsOnePlaceAlone(Compilation c, String name) {
        PublishedDeclarationResult said = c.db()
                .ask(new Shapes.MeaningOf(new TypeKey("shop.rules", name))).value();
        DeclarationMeaning meaning = assertInstanceOf(PublishedDeclarationResult.Found.class, said,
                name + " is published").said();
        List<Boolean> out = new ArrayList<>();
        for (ClauseMeaning each : ((DeclarationMeaning.Product) meaning).clauses()) {
            for (ClauseMeaning.Parts.One part : ((ClauseMeaning.Stated) each).parts().leaves()) {
                out.add(part.readsOnePlaceAlone());
            }
        }
        return out;
    }

    private static Compilation started() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("rules.sou", MODULE);
        Compilation c = ACompiledModel.compiles(
                Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY).writtenOn(TestDay.DATE));
        assertTrue(c.db().allReports().isEmpty(), "the module compiles: " + c.db().allReports());
        return c;
    }
}
