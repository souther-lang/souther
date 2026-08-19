package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two rules asking the same question of the same position stay two in the document.
 *
 * <p>Asked of the document and not of the value behind it, because that is where every round of this
 * has gone wrong: the type was right and the seam it crossed was narrower. A question kept its rule
 * as far as {@code PartitionEvidence} and the writer published the words for finding it, so the last
 * hop dropped the identity again.
 *
 * <p>Two arms of one {@code ensures} clause may name the same case, which {@code RuleRef.Ensures}
 * says outright — the author's words for them are the same words. So the handle cannot tell them
 * apart, and the identity beside it is what does. A guard's two comparisons of one condition are the
 * same shape with a different collision: they differ in where they are written, which the handle
 * carries and which the identity carries too.
 */
class TwoRulesAskingAlikeStayTwoInTheDocumentTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static JsonNode standing(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode document = JSON.readTree(
                AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        return document.get("modules").get(0).get("behaviors").get(0)
                .get("partition").get("unanswered");
    }

    /** Every entry as a consumer sees it, whole. */
    private static Set<String> entries(JsonNode standing) {
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode each : standing) {
            out.add(each.toString());
        }
        return out;
    }

    /** And what each says its rule is, which is what tells two of them apart. */
    private static Set<String> identities(JsonNode standing) {
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode each : standing) {
            out.add(each.get("ruleId").toString());
        }
        return out;
    }

    /**
     * Two arms of one clause, named alike by the author and told apart by the document.
     *
     * <p>The handle is `ensures f (Found)` for both: an unnamed clause is called by the case its arm
     * names, and both arms name `Found`. Published on the handle alone, these were two pairs of
     * identical objects — and a consumer could not tell two rules asking alike from one question
     * written twice.
     */
    @Test
    void twoArmsNamedAlikeAreTwoRules() {
        JsonNode standing = standing("""
                module m

                data R = { a: Int }
                data Found
                data Missing

                behavior f : (r: R) -> Found | Missing
                    constructs Found, Missing
                    ensures Found -> r.a <= 10 * 2
                    ensures Found -> r.a >= 20 * 2
                let f (r) = Missing

                example f
                    | "one" : (R { a = 1 }) -> Missing
                """);

        assertEquals(4, standing.size(), () -> "two rules, two questions each: " + standing);
        assertEquals(4, entries(standing).size(),
                () -> "and four entries a consumer can tell apart: " + standing);
        assertEquals(2, identities(standing).size(),
                () -> "which two rules they are: " + standing);
    }

    /** Two comparisons of one condition, which collide on nothing and must still stay two. */
    @Test
    void twoComparisonsOfOneConditionAreTwoRules() {
        JsonNode standing = standing("""
                module m

                data R = { a: Int }
                data X
                data Y

                behavior f : (r: R) -> X | Y
                    constructs X, Y
                let f (r) = if r.a <= 10 * 2 && r.a >= 20 * 2 then X else Y

                example f
                    | "one" : (R { a = 1 }) -> Y
                """);

        assertEquals(4, standing.size(), () -> "two rules, two questions each: " + standing);
        assertEquals(4, entries(standing).size(), () -> "all four distinguishable: " + standing);
        assertEquals(2, identities(standing).size(), () -> "and two rules: " + standing);
    }
}
