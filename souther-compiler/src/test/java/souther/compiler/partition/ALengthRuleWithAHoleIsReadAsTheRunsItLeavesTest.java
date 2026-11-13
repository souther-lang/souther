package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.Value;
import souther.compiler.values.ValuesAtLengths;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /** One string held by {@code rule}, equal to a free one; {@code example} is a string it holds. */
    private static String code(String rule, String example) {
        return """
                module plain

                data Code = String
                    invariant %s

                behavior f : (code: Code, other: String) -> Bool
                let f (Code(code), other) = code == other

                example f
                    | "same"  : (Code("%s"), "%<s") -> true
                    | "other" : (Code("%<s"), "zz") -> false
                """.formatted(rule, example);
    }

    private static JsonNode partitionOf(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        String json = AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        return new ObjectMapper().readTree(json).path("modules").get(0).path("behaviors").get(0)
                .path("partition");
    }

    /** What each place the partition leaves unanswered was asked, and why it stopped. */
    private static List<String> unanswered(String rule) {
        List<String> out = new ArrayList<>();
        partitionOf(emails(rule)).path("unanswered").forEach(each -> each.path("stopped").forEach(
                stop -> out.add(each.path("question").asString() + " "
                        + each.path("subject").path("path").asString() + " "
                        + stop.path("reason").asString())));
        return out;
    }

    private static String a(int length) {
        return "a".repeat(length);
    }

    /**
     * Held to ten code points with a hole in them, the strings are read and the relation is read
     * over the lengths left, as it is with none: what is left unanswered is the lowercase's image
     * past ten code points and nothing about the position's values.
     */
    @Test
    void aHoleInTheLengthsIsReadAsTheOneRunIsRead() {
        // What the same rule leaving one run (`String.length(value) <= 10`) leaves unanswered.
        List<String> asOneRun =
                List.of("regionNotDetermined domains[*] relation_shown_over_a_region");
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
        assertEquals(List.of("x can be code " + a(6), "x is never code " + a(7),
                        "x can be code " + a(8)),
                classesHolding("String.length(value) <= 10 && String.length(value) /= 7", a(4),
                        List.of(a(6), a(7), a(8))));
        assertEquals(List.of("x can be code " + a(6), "x is never code " + a(7),
                        "x is never code " + a(8), "x can be code " + a(9)),
                classesHolding("String.length(value) <= 10"
                        + " && (String.length(value) < 7 || String.length(value) > 8)", a(4),
                        List.of(a(6), a(7), a(8), a(9))));
    }

    /**
     * Where the choice met with a bound leaves one run, the run stops short of the end the bound
     * placed, and the length at that end is one the rules refuse. The lengths are those of the
     * run, as they are of the same rule written with the end where the run stops.
     */
    @Test
    void aRunThatStopsShortOfTheEndABoundPlacedIsTheLengthsOfTheRun() {
        assertEquals(List.of("x can be code " + a(7), "x is never code " + a(8)),
                classesHolding("String.length(value) <= 8"
                        + " && (String.length(value) < 8 || String.length(value) > 8)", a(4),
                        List.of(a(7), a(8))));
        assertEquals(List.of("x is never code " + a(6), "x is never code " + a(7),
                        "x can be code " + a(8)),
                classesHolding("String.length(value) >= 7 && String.length(value) /= 7", a(8),
                        List.of(a(6), a(7), a(8))));
        // The same where nothing but the choice says it: the algebra does not enter an alternative,
        // so the ends are seven and up and the disequality at the end of them is the choice's.
        assertEquals(List.of("x is never code " + a(6), "x is never code " + a(7),
                        "x can be code " + a(8), "x can be code " + a(101)),
                classesHolding("String.length(value) >= 7"
                        + " && (String.length(value) /= 7 || String.length(value) > 100)", a(8),
                        List.of(a(6), a(7), a(8), a(101))));
    }

    /**
     * A disequality of the string beside one of the length is read over the set of every string
     * but one, which is no language: the strings are those of the lengths left that are not that
     * string.
     */
    @Test
    void aStringHeldApartBesideALengthTakenOutIsHeldToBoth() {
        assertEquals(List.of("x is never code x", "x is never code " + a(2),
                        "x can be code " + a(3), "x can be code y"),
                classesHolding("value /= \"x\" && String.length(value) /= 2", a(3),
                        List.of("x", a(2), a(3), "y")));
    }

    /** The same with the lengths one run: the set of every string but one is no language of its
     *  own, and a position holding it beside a bound on the length is read all the same. */
    @Test
    void aStringHeldApartBesideALengthBoundIsHeldToBoth() {
        assertEquals(List.of("x is never code x", "x can be code y", "x is never code " + a(11)),
                classesHolding("value /= \"x\" && String.length(value) <= 10", a(3),
                        List.of("x", "y", a(11))));
    }

    /**
     * Strings of a length taken out are not written for a class that is the position's, and the
     * ones written for the class of strings never the position's are of the lengths taken out or
     * of those past its ends.
     */
    @Test
    void theStringsWrittenAreOfTheLengthsLeft() {
        String rule = "String.length(value) <= 10 && String.length(value) /= 7";
        Compilation model = ACompiledModel.answered(code(rule, a(4)));
        String module = model.modules().get(0);
        Partitions.Partitioning divided =
                model.db().ask(new Adequacy.Divided(module, "f")).value();
        RuleReadingContext reading = RuleReadingContext.unshared(RuleReadings.of(model, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        List<String> written = new ArrayList<>();
        for (Axis axis : divided.axes()) {
            if (!axis.path().toString().equals("other")) {
                continue;
            }
            for (PartitionClass each : axis.classes()) {
                Partitions.standingFor(each.representatives(), reading, Set.of()).values()
                        .forEach(value -> {
                            long length = lengthOf(value.text());
                            boolean left = length <= 10 && length != 7;
                            assertEquals(each.label().contains("can be"), left,
                                    each.label() + " is written at " + length);
                            written.add(each.label());
                        });
            }
        }
        assertTrue(written.stream().anyMatch(each -> each.contains("can be")), written::toString);
        assertTrue(written.stream().anyMatch(each -> each.contains("never")), written::toString);
    }

    /** The code points of the string a literal writes, each escape one. */
    private static long lengthOf(String literal) {
        String inside = literal.substring(1, literal.length() - 1).replaceAll("\\\\.", "x");
        return inside.codePoints().count();
    }

    /**
     * A hole in lengths no machine is made for is a figure the reading stopped at and no strings
     * shown, and the position's values are not read as if the hole were not there.
     */
    @Test
    void aHoleInLengthsPastTheAllowanceIsAFigureTheReadingStoppedAt() {
        JsonNode partition = partitionOf(code("String.length(value) <= 2000000"
                + " && String.length(value) /= 1000000", a(4)));
        List<String> figures = new ArrayList<>();
        partition.path("unanswered").forEach(each -> each.path("stopped").forEach(
                stop -> stop.path("figures").forEach(figure -> figures.add(
                        each.path("subject").path("path").asString() + " "
                                + figure.asString()))));
        assertEquals(List.of("other strings_a_partner_holds_one_machine"), figures);
    }

    /** Which class of the other side each of {@code texts} is in, as the label and the string, in
     *  the order of {@code texts}. */
    private static List<String> classesHolding(String rule, String example,
                                               List<String> texts) {
        Compilation model = ACompiledModel.answered(code(rule, example));
        Partitions.Partitioning divided =
                model.db().ask(new Adequacy.Divided(model.modules().get(0), "f")).value();
        List<String> holding = new ArrayList<>();
        for (String text : texts) {
            for (Axis axis : divided.axes()) {
                if (!axis.path().toString().equals("other")) {
                    continue;
                }
                for (PartitionClass each : axis.classes()) {
                    Recognition is =
                            each.recognises() instanceof Recognition.Under(var _, var inner)
                                    ? inner : each.recognises();
                    if (is instanceof Recognition.OfASet(ValuesAtLengths values)
                            && values.has(new Value.Text(text))) {
                        holding.add(each.label() + " " + text);
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

    /** A choice between runs of lengths with no end above is a rule read all the same. */
    @Test
    void aChoiceBetweenRunsOfLengthsIsARuleReadWhateverItsEnds() {
        String rule = "String.length(value) < 7 || String.length(value) > 8";
        assertEquals(List.of(), unanswered(rule).stream()
                .filter(each -> each.startsWith("admitted_values")).toList(), rule);
    }
}
