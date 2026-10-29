package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string relation is read over a position whose only rule is a bound on the length of its
 * strings, as it is over one held by a pattern: the strings it holds are those of the lengths the
 * bound leaves, where the bounds are shown to be all the rules say. Where they are not shown to be,
 * nothing is said of the strings and the relation is not shown to reach every value of the other
 * side.
 */
class AStringRelationIsReadOverAPositionHeldOnlyByALengthRuleTest {

    private static NavigableSet<String> reasons(String needRule, String relation) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Need = String
                    invariant %s

                data In = { needs: List<Need>, text: String }

                behavior f : (i: In) -> Bool
                let f (i) = List.any(p -> %s, i.needs)
                """.formatted(needRule, relation), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"([a-z_]+)\"").matcher(json);
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    private static final String CONTAINS_LOWERED =
            "String.contains(String.lowercase(p.value), String.lowercase(i.text))";

    /** The relation is read whichever end of the length the rule places, and the strings held at
     *  the position are not asked for by the pattern it is held with. */
    @Test
    void theLengthBoundDoesNotDecideWhetherTheRelationIsRead() {
        for (String rule : List.of("String.length(value) >= 0", "String.length(value) >= 1",
                "String.length(value) >= 2", "String.length(value) > 0",
                "String.length(value) >= 1 && String.length(value) <= 5",
                "String.length(value) == 3", "String.length(value) < 8")) {
            NavigableSet<String> reasons = reasons(rule, CONTAINS_LOWERED);
            assertTrue(reasons.contains("relation_shown_over_a_region"), () -> rule + " " + reasons);
            assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"),
                    () -> rule + " " + reasons);
        }
    }

    /** The shape of the CRM's {@code answersANeed}: the needs are a list of values held only by a
     *  length rule, the business case is any string, and both are lowercased. */
    @Test
    void aBusinessCaseIsReadAgainstNeedsHeldOnlyByALengthRule() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data PainPoint = String invariant String.length(value) >= 1
                data Needs = List<PainPoint>
                    invariant List.length(value) >= 1

                let answersANeed (businessCase: String, Needs(points)): Bool =
                    List.any(p -> String.contains(String.lowercase(p.value),
                                                  String.lowercase(businessCase)), points)

                behavior f : (businessCase: String, needs: Needs) -> Bool
                let f (businessCase, needs) = answersANeed(businessCase, needs)
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(json.contains("relation_not_shown_to_reach_every_value"), json);
        assertTrue(json.contains("relation_shown_over_a_region"), json);
    }

    /** A length tied to a number of another position is a rule the bounds on the length do not
     *  state, so the strings are not shown and the relation is not shown to reach every value. */
    @Test
    void aLengthTiedToAnotherPositionIsNotReadAsTheStringsOfThoseLengths() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Need = { value: String, room: Int }
                    invariant String.length(value) <= room

                data In = { needs: List<Need>, text: String }

                behavior f : (i: In) -> Bool
                let f (i) = List.any(p -> String.contains(p.value, i.text), i.needs)
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(json.contains("\"relation_shown_over_a_region\"")
                && !json.contains("relation_not_shown_to_reach_every_value"), json);
    }

    /** What is said of the relation, apart from the other things a report says of the rules. */
    private static NavigableSet<String> aboutTheRelation(String needRule, String relation) {
        NavigableSet<String> out = new TreeSet<>(reasons(needRule, relation));
        out.removeIf(each -> !each.startsWith("relation_"));
        return out;
    }

    /** A position held by a pattern for the same strings is the control: what is said of the
     *  relation is the same, so the length rule is read as the pattern is. */
    @Test
    void aPatternForTheSameStringsAnswersAsTheLengthRuleDoes() {
        for (String relation : List.of(CONTAINS_LOWERED, "String.contains(p.value, i.text)",
                "String.contains(i.text, p.value)", "String.startsWith(p.value, i.text)",
                "String.endsWith(i.text, p.value)")) {
            assertEquals(aboutTheRelation("String.matches(\".+\", value)", relation),
                    aboutTheRelation("String.length(value) >= 1", relation), relation);
        }
    }
}
