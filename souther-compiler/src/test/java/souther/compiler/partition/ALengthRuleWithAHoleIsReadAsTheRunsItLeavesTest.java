package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.Value;
import souther.compiler.values.ValuesAtLengths;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule that takes lengths out from between its ends — a disequality, or a choice between runs
 * of lengths — is read into the strings a position admits as the runs it leaves, as a rule leaving
 * one run is. A relation over the position is then read over the lengths left, and the lengths
 * taken out are no lengths of a value of it.
 */
class ALengthRuleWithAHoleIsReadAsTheRunsItLeavesTest {

    private static String emails(String rule) {
        return """
                module bounded

                data Email = String invariant %s
                data Domains = List<String> invariant List.length(value) >= 1

                behavior f : (email: Email, domains: Domains, emails: List<String>) -> Bool
                let f (Email(email), Domains(domains), emails) =
                    List.any(own -> own == String.lowercase(email), domains)
                        || List.any(own -> own == email, emails)

                example f
                    | "domain" : (Email("a.com"), Domains([ "a.com" ]), []) -> true
                    | "none"   : (Email("x@b.c"), Domains([ "a.com" ]), [ "y@b.c" ]) -> false
                """.formatted(rule);
    }

    private static JsonNode partitionOf(String rule) {
        Compilation model = ACompiledModel.measured(emails(rule),
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        String json = AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        return new ObjectMapper().readTree(json).path("modules").get(0).path("behaviors").get(0)
                .path("partition");
    }

    /** What each place the partition leaves unanswered was asked, and why it stopped. */
    private static List<String> unanswered(String rule) {
        List<String> out = new ArrayList<>();
        partitionOf(rule).path("unanswered").forEach(each -> each.path("stopped").forEach(
                stop -> out.add(each.path("question").asString() + " "
                        + each.path("subject").path("path").asString() + " "
                        + stop.path("reason").asString())));
        return out;
    }

    /**
     * Held to ten code points with a hole in them, the strings are read and the relation is read
     * over the lengths left, as it is with none: what is left unanswered is the lowercase's image
     * past ten code points and nothing about the position's values.
     */
    @Test
    void aHoleInTheLengthsIsReadAsTheOneRunIsRead() {
        List<String> asOneRun = unanswered("String.length(value) <= 10");
        assertEquals(List.of("regionNotDetermined domains[*] relation_shown_over_a_region"),
                asOneRun);
        assertEquals(asOneRun,
                unanswered("String.length(value) <= 10 && String.length(value) /= 7"));
        assertEquals(asOneRun, unanswered("String.length(value) <= 10"
                + " && (String.length(value) < 7 || String.length(value) > 8)"));
    }

    /**
     * A string of a length the rule takes out is none the position holds: of the strings a free
     * one may be equal to, those of seven code points are in the class of strings never the
     * position's, and those of six or eight are in the other.
     */
    @Test
    void aStringOfALengthTakenOutIsNotAValueOfThePosition() {
        assertEquals(List.of("x can be code 6", "x is never code 7", "x can be code 8"),
                classesHolding("String.length(value) <= 10 && String.length(value) /= 7",
                        List.of(6, 7, 8)));
        assertEquals(List.of("x can be code 6", "x is never code 7", "x is never code 8",
                        "x can be code 9"),
                classesHolding("String.length(value) <= 10"
                        + " && (String.length(value) < 7 || String.length(value) > 8)",
                        List.of(6, 7, 8, 9)));
    }

    /** Which class of the other side each string of {@code lengths} is in, as the label and the
     *  length, in the order of {@code lengths}. */
    private static List<String> classesHolding(String rule, List<Integer> lengths) {
        Compilation model = ACompiledModel.answered("""
                module plain

                data Code = String
                    invariant %s

                behavior f : (code: Code, other: String) -> Bool
                let f (Code(code), other) = code == other

                example f
                    | "same"  : (Code("abcd"), "abcd") -> true
                    | "other" : (Code("abcd"), "cd") -> false
                """.formatted(rule));
        Partitions.Partitioning divided =
                model.db().ask(new Adequacy.Divided(model.modules().get(0), "f")).value();
        List<String> holding = new ArrayList<>();
        for (int length : lengths) {
            for (Axis axis : divided.axes()) {
                if (!axis.path().toString().equals("other")) {
                    continue;
                }
                for (PartitionClass each : axis.classes()) {
                    Recognition is =
                            each.recognises() instanceof Recognition.Under(var _, var inner)
                                    ? inner : each.recognises();
                    if (is instanceof Recognition.OfASet(ValuesAtLengths values)
                            && values.has(new Value.Text("a".repeat(length)))) {
                        holding.add(each.label() + " " + length);
                    }
                }
            }
        }
        return holding;
    }

    /**
     * A choice whose alternatives each pair a length with a pattern is not the lengths beside the
     * patterns: a code of two letters beginning with A or one of five beginning with B is not one
     * of either length beginning with either letter. Read as the two apart it would admit
     * {@code "Bz"}, so the rule stays unread.
     */
    @Test
    void aChoiceThatPairsALengthWithAPatternIsNotReadAsTheTwoApart() {
        Compilation model = ACompiledModel.measured("""
                module paired

                data Code = String
                    invariant (String.length(value) == 2 && String.matches("A.", value))
                        || (String.length(value) == 5 && String.matches("B....", value))

                behavior f : (code: Code, other: String) -> Bool
                let f (Code(code), other) = code == other

                example f
                    | "same"  : (Code("Ab"), "Ab") -> true
                    | "other" : (Code("Ab"), "cd") -> false
                """, Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        String json = AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertEquals(true, json.contains("admitted_values"), json);
    }

    /** A choice between runs of lengths is a rule read, whatever its ends. */
    @Test
    void aChoiceBetweenRunsOfLengthsIsARuleRead() {
        for (String rule : List.of(
                "String.length(value) <= 10"
                        + " && (String.length(value) < 7 || String.length(value) > 8)",
                "String.length(value) < 7 || String.length(value) > 8",
                "String.length(value) == 2 || String.length(value) == 5")) {
            assertEquals(List.of(), unanswered(rule).stream()
                    .filter(each -> each.startsWith("admitted_values")).toList(), rule);
        }
    }
}
