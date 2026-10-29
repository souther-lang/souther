package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
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
 * A string relation is read over a position whose only rule is a bound on the length of its
 * strings, as it is over one held by a pattern for the same strings: the strings it holds are
 * those of the set that have a length the bounds leave, where the bounds are shown to be the whole
 * of the rules. Where they are not shown to be, nothing is said of the strings, and the relation is
 * not shown to reach every value of the other side.
 */
class AStringRelationIsReadOverAPositionHeldOnlyByALengthRuleTest {

    private static final String CONTAINS_LOWERED =
            "String.contains(String.lowercase(p.value), String.lowercase(i.text))";

    private static Compilation measured(String types, String relation) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                %s

                data In = { needs: List<Need>, text: String }

                behavior f : (i: In) -> Bool
                let f (i) = List.any(p -> %s, i.needs)
                """.formatted(types, relation), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Compilation measuredNeed(String rule, String relation) {
        return measured("data Need = String invariant " + rule, relation);
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** Every reason the report gives. */
    private static NavigableSet<String> reasons(Compilation compilation) {
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"([a-z_]+)\"").matcher(json(compilation));
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    /** What is said of the relation, apart from the other things a report says of the rules. */
    private static NavigableSet<String> aboutTheRelation(Compilation compilation) {
        NavigableSet<String> out = reasons(compilation);
        out.removeIf(each -> !each.startsWith("relation_"));
        return out;
    }

    /** The classes each axis of the behavior is parted into. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The relation is read whichever end of the length the rule places. */
    @Test
    void theLengthBoundDoesNotDecideWhetherTheRelationIsRead() {
        for (String rule : List.of("String.length(value) >= 0", "String.length(value) >= 1",
                "String.length(value) >= 2", "String.length(value) > 0",
                "String.length(value) >= 1 && String.length(value) <= 5",
                "String.length(value) == 3", "String.length(value) < 8")) {
            NavigableSet<String> reasons = aboutTheRelation(measuredNeed(rule, CONTAINS_LOWERED));
            assertTrue(reasons.contains("relation_shown_over_a_region"), () -> rule + " " + reasons);
            assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"),
                    () -> rule + " " + reasons);
        }
    }

    /**
     * A position held by a pattern for the same strings is the control, and what is asked of the
     * two is the classes each axis is parted into as well as what is said of the relation: the
     * same reason over different classes would not be the same reading. The pattern is made of
     * every code point, as a dot leaves out the line terminators and so is not the same strings.
     */
    @Test
    void aPatternForTheSameStringsPartsThePlacesAsTheLengthRuleDoes() {
        Map<String, String> sameStrings = new LinkedHashMap<>();
        sameStrings.put("String.length(value) >= 1", "[\\\\s\\\\S]+");
        sameStrings.put("String.length(value) >= 2", "[\\\\s\\\\S]{2,}");
        sameStrings.put("String.length(value) == 3", "[\\\\s\\\\S]{3}");
        sameStrings.put("String.length(value) >= 1 && String.length(value) <= 5",
                "[\\\\s\\\\S]{1,5}");
        for (String relation : List.of(CONTAINS_LOWERED, "String.contains(p.value, i.text)",
                "String.contains(i.text, p.value)", "String.startsWith(p.value, i.text)",
                "String.endsWith(i.text, p.value)")) {
            sameStrings.forEach((lengthRule, regex) -> {
                Compilation byLength = measuredNeed(lengthRule, relation);
                Compilation byPattern = measuredNeed("String.matches(\"" + regex + "\", value)",
                        relation);
                assertEquals(aboutTheRelation(byPattern), aboutTheRelation(byLength),
                        () -> lengthRule + " " + relation);
                assertEquals(classes(byPattern), classes(byLength), () -> lengthRule + " " + relation);
            });
        }
    }

    /**
     * Over a position of at least one code point, the empty string is shown to be no string that
     * holds a need, and the strings that can are another class. The strings shown never to hold
     * one are what the length rule proves; a position this compiler cannot prove the strings of
     * has no such class, and the strings it did not find are not called unreachable.
     */
    @Test
    void aStringTheLengthRuleLeavesNoRoomForIsShownNeverToHoldANeed() {
        Map<String, List<String>> held = classes(
                measuredNeed("String.length(value) >= 1", "String.contains(p.value, i.text)"));
        assertEquals(List.of("i.text/x can be a string holding i.needs[*]",
                "i.text/x is never a string holding i.needs[*]"), held.get("i.text"));

        Compilation tied = measured("""
                data Need = { value: String, room: Int } invariant String.length(value) <= room""",
                "String.contains(p.value, i.text)");
        assertFalse(classes(tied).containsKey("i.text"), () -> classes(tied).toString());
        assertTrue(reasons(tied).contains("relation_not_shown_to_reach_every_value"),
                () -> reasons(tied).toString());
    }

    /**
     * A rule on the order of the strings is a bound the length rule beside it does not state, so
     * the strings are not those of the lengths and the relation is not read over them.
     */
    @Test
    void aRuleOnTheOrderOfTheStringsIsNotReadAsTheStringsOfTheirLengths() {
        for (String rule : List.of("value < \"B\"",
                "value < \"B\" && String.length(value) >= 1")) {
            Compilation order = measuredNeed(rule, "String.contains(p.value, i.text)");
            assertFalse(classes(order).containsKey("i.text"), () -> rule + classes(order));
            assertTrue(reasons(order).contains("relation_not_shown_to_reach_every_value"),
                    () -> rule + " " + reasons(order));
        }
    }

    /** The behavior of a guard, then the relation, over needs held by {@code pain}. */
    private static Compilation guarded(String pain, String guard) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data PainPoint = String invariant %s
                data BusinessCase = String invariant String.length(value) >= 1
                data Needs = List<PainPoint>
                    invariant List.length(value) >= 1
                data Missed

                let answersANeed (businessCase: String, Needs(points)): Bool =
                    List.any(p -> String.contains(String.lowercase(p.value),
                                                  String.lowercase(businessCase)), points)

                behavior f : (needs: Needs, businessCase: String) -> BusinessCase | Missed
                    constructs BusinessCase
                let f (needs, businessCase) = {
                    %s
                    guard answersANeed(businessCase, needs) else Missed
                    let stated = BusinessCase("x")
                    stated
                }
                """.formatted(pain, guard), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * A guard that ends the length of the other string is on the strings and not a count of a
     * container: the relation is read over the strings of the lengths the run gets to it with, and
     * the strings of the other lengths are left open, whether the needs are held by a length rule
     * or by a pattern for the same strings.
     */
    @Test
    void aGuardOnTheLengthOfTheOtherStringLeavesTheRelationReadOverThoseLengths() {
        Map<String, String> openAt = new LinkedHashMap<>();
        openAt.put("guard BusinessCase(businessCase) as stated else Missed", "\"shorterThan\" : 1");
        openAt.put("guard String.length(businessCase) <= 3 else Missed", "\"longerThan\" : 3");
        openAt.forEach((guard, left) -> {
            Compilation byLength = guarded("String.length(value) >= 1", guard);
            Compilation byPattern = guarded("String.matches(\"[\\\\s\\\\S]+\", value)", guard);
            NavigableSet<String> reasons = aboutTheRelation(byLength);
            assertTrue(reasons.contains("relation_shown_over_a_region"), () -> guard + " " + reasons);
            assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"),
                    () -> guard + " " + reasons);
            assertTrue(json(byLength).contains(left), () -> guard + " leaves " + left + " open");
            assertEquals(aboutTheRelation(byPattern), reasons, guard);
            assertEquals(classes(byPattern), classes(byLength), guard);
        });
    }

    /** The operations each report entry names as open, in the order the entries are written. */
    private static List<String> imagesNotShown(Compilation compilation) {
        List<String> out = new ArrayList<>();
        Matcher found = Pattern.compile("\"imagesNotShown\"\\s*:\\s*\\[([^\\]]*)\\]")
                .matcher(json(compilation));
        while (found.find()) {
            out.add(found.group(1).strip());
        }
        return out;
    }

    /**
     * A conversion is open wherever the strings the length rule leaves are strings it is not
     * exactly a map on, and only there: beside a length of one code point or more the lowercase of
     * a need is named open at both places the relation parts, as it is beside a pattern of every
     * code point, and the shown strings do not turn into the whole of them.
     *
     * <p>Nor does a position that holds the empty string alone, which no conversion changes, read
     * differently from the pattern that holds it: that relation is not read over one string, in
     * either form, and so names nothing open.
     */
    @Test
    void aConversionIsNamedOpenWhereTheLengthRuleLeavesStringsItIsNotExactOn() {
        String relation = "String.contains(String.lowercase(p.value), i.text)";
        List<String> byLength = imagesNotShown(measuredNeed("String.length(value) >= 1", relation));
        assertEquals(List.of("\"String.lowercase\"", "\"String.lowercase\""), byLength);
        assertEquals(imagesNotShown(measuredNeed("String.matches(\"[\\\\s\\\\S]+\", value)", relation)),
                byLength);

        Compilation empty = measuredNeed("String.length(value) == 0", relation);
        assertEquals(imagesNotShown(measuredNeed("String.matches(\"\", value)", relation)),
                imagesNotShown(empty));
        assertEquals(List.of(), imagesNotShown(empty));
        assertEquals(aboutTheRelation(measuredNeed("String.matches(\"\", value)", relation)),
                aboutTheRelation(empty));
    }

    /**
     * A string longer than every string the run gets to the relation with on the other side is
     * inside none of them: the strings of one side are parted by the strings of the other that a
     * run reaches, and not by all it holds. Without that, a need of five code points would be
     * shown to be inside a business case the guard keeps to three.
     */
    @Test
    void aStringLongerThanAnyThatReachesTheRelationIsShownInsideNoneOfThem() {
        for (String pain : List.of("String.length(value) >= 1",
                "String.matches(\"[\\\\s\\\\S]+\", value)")) {
            Compilation compilation = Compilation.ofSource("""
                    module demo

                    data PainPoint = String invariant %s
                    data Needs = List<PainPoint>
                        invariant List.length(value) >= 1
                    data Missed

                    behavior f : (needs: Needs, businessCase: String) -> Bool | Missed
                    let f (needs, businessCase) = {
                        guard String.length(businessCase) <= 3 else Missed
                        guard List.any(p -> String.contains(p.value, businessCase), needs.value)
                            else Missed
                        true
                    }
                    """.formatted(pain), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of("needs[*]/x can be a string inside businessCase",
                    "needs[*]/x is never a string inside businessCase"),
                    classes(compilation).get("needs[*]"), pain);
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
        String json = json(compilation);
        assertFalse(json.contains("relation_not_shown_to_reach_every_value"), json);
        assertTrue(json.contains("relation_shown_over_a_region"), json);
    }
}
