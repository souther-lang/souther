package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison in a behavior over a number of a record is read beside a rule of the record tying
 * other places of it together, however the rule is written.
 *
 * <p>The behavior's half of what {@code check.ARuleTyingOtherPlacesTogetherWithholdsNothing
 * BesideThemTest} asks of the record's reading: the line the comparison draws is read, and one
 * clause of two parts says what the same two parts written as two clauses say. A part tying the
 * strings to the number withholds the line, as it should.
 */
class ARelationBesideRulesTyingOtherPlacesIsReadInABehaviorTest {

    private static Compilation measured(String rules) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Yen = Int
                    invariant value >= 0

                data Priced = { total: Yen, subtotal: Yen, a: String, b: String, c: String }
                    invariant total.value <= subtotal.value
                %s

                behavior f : (p: Priced, cap: Int) -> Bool
                let f (p, cap) = p.total.value <= cap
                """.formatted(rules), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** What is said of the relations of the behavior, apart from the rest of a report. */
    private static NavigableSet<String> aboutTheRelation(Compilation compilation) {
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"(relation_[a-z_]+)\"").matcher(
                AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    /** The classes each axis of the behavior is parted into. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    @Test
    void theLineIsReadBesideARuleOverTwoStringsWrittenEitherWay() {
        Compilation bare = measured("");
        Compilation apart = measured("""
                    invariant String.contains(a, b)
                    invariant String.contains("q", c)
                """);
        Compilation joined = measured(
                "    invariant String.contains(a, b) && String.contains(\"q\", c)");

        assertFalse(aboutTheRelation(apart).contains("relation_not_shown_to_reach_every_value"),
                () -> aboutTheRelation(apart).toString());
        assertEquals(classes(bare), classes(apart), "the strings part the total no differently");
        assertEquals(aboutTheRelation(apart), aboutTheRelation(joined),
                "one clause of two parts says what two clauses do");
        assertEquals(classes(apart), classes(joined));
    }

    @Test
    void butNotBesideAPartTyingTheStringsToTheNumber() {
        Compilation tied = measured("""
                    invariant String.contains(a, b)
                    invariant String.length(b) <= total.value
                """);

        assertTrue(aboutTheRelation(tied).contains("relation_not_shown_to_reach_every_value"),
                () -> aboutTheRelation(tied).toString());
    }
}
