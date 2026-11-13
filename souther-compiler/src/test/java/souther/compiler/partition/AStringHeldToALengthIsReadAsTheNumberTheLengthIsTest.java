package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The strings a rule about the length holds a value to are read with the length as the number it
 * is. Written out as one set of strings, every string up to a length is a machine with a state for
 * each code point, and a rule naming a long length was one no relation with the value was read
 * over; held as a number, a value as long as a {@code String} is read as a short one is.
 */
class AStringHeldToALengthIsReadAsTheNumberTheLengthIsTest {

    /** An equality with the email, and one with a lowercase of it, each beside a list. */
    private static String emails(String rule, String left) {
        return """
                module bounded

                data Email = String invariant %s
                data Domains = List<String> invariant List.length(value) >= 1

                behavior f : (email: Email, domains: Domains, emails: List<String>) -> Bool
                let f (Email(email), Domains(domains), emails) =
                    List.any(own -> own == %s, domains)
                        || List.any(own -> own == email, emails)

                example f
                    | "domain" : (Email("a.com"), Domains([ "a.com" ]), []) -> true
                    | "email"  : (Email("x@b.com"), Domains([ "q" ]), [ "x@b.com" ]) -> true
                    | "none"   : (Email("x@b.com"), Domains([ "a.com" ]), [ "y@b.com" ]) -> false
                """.formatted(rule, left);
    }

    /** One string held by {@code rule}, equal to a free one. */
    private static String code(String rule) {
        return """
                module plain

                data Code = String invariant %s

                behavior f : (code: Code, other: String) -> Bool
                let f (Code(code), other) = code == other

                example f
                    | "same"  : (Code("abcd"), "abcd") -> true
                    | "other" : (Code("abcd"), "cd") -> false
                """.formatted(rule);
    }

    private static String report(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        return AdequacyReport.of(model).json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /**
     * Held to a hundred thousand code points, the report is the report of the same model held to
     * 254, with the length and the lengths beside it said in place of 254's: the same classes on
     * the same axes, the same places left open and for the same lengths. Of an equality with the
     * string, with a lowercase of it, and of one string with a free one; held from no fewest code
     * points and from some, where the strings never the partner are those shorter than its fewest
     * and those longer than its most, one class of two runs of lengths.
     */
    @Test
    void aStringHeldLongIsReadAsTheSameStringHeldShortIs() {
        Map<String, String> models = new LinkedHashMap<>();
        String fromOne = "String.length(value) >= 1 && String.length(value) <= %s";
        models.put("email", emails("String.length(value) <= %s", "email"));
        models.put("lowercase", emails("String.length(value) <= %s", "String.lowercase(email)"));
        models.put("code", code("String.length(value) <= %s"));
        models.put("email from one", emails(fromOne, "email"));
        models.put("lowercase from one", emails(fromOne, "String.lowercase(email)"));
        models.put("code from three", code("String.length(value) >= 3"
                + " && String.length(value) <= %s"));
        for (Map.Entry<String, String> each : models.entrySet()) {
            String read = report(each.getValue().formatted("100000"));
            assertEquals(report(each.getValue().formatted("254")),
                    read.replace("100000", "254").replace("100001", "255")
                            .replace("99999", "253"),
                    each.getKey());
        }
    }

    /**
     * The strings longer than the code can be are the class of those never it, and a row is
     * written for that class out of a string of the fewest code points it holds; the strings no
     * longer, out of the shortest.
     */
    @Test
    void theClassOfStringsLongerThanThePartnerIsWrittenAsLongAsItsFewest() {
        assertEquals(List.of("x can be code: 0", "x is never code: 255"),
                writtenFor(code("String.length(value) <= 254"), "other"));
        assertEquals(List.of("x can be code: 3", "x is never code: 0"),
                writtenFor(code("String.length(value) >= 3 && String.length(value) <= 254"),
                        "other"));
    }

    /**
     * A string longer than the email can be, or shorter, is the lowercase of one only through what
     * the lowercase lengthens or what its normalization joins, which is its image not shown: the
     * report says where those strings lie and that the image is why, in the document and in the
     * text a person reads.
     */
    @Test
    void theStringsALowercaseMayMakeOfAPartnerHeldToItsLengthsAreOpenForItsImage() {
        assertEquals(List.of("domains[*] {\"longerThan\":254,\"atAnyLength\":false,"
                        + "\"imagesNotShown\":[\"String.lowercase\"]}"),
                leftOpenIn(emails("String.length(value) <= 254", "String.lowercase(email)")));
        assertEquals(List.of("domains[*] {\"longerThan\":254,\"shorterThan\":1,"
                        + "\"atAnyLength\":false,\"imagesNotShown\":[\"String.lowercase\"]}"),
                leftOpenIn(emails("String.length(value) >= 1 && String.length(value) <= 254",
                        "String.lowercase(email)")));
        Compilation model = ACompiledModel.measured(
                emails("String.length(value) <= 254", "String.lowercase(email)"),
                Adequacy.Asked.fullReport());
        String text = AdequacyReport.of(model)
                .humanInEnglish(SourceRendering.namedByIdentity(model.texts()));
        assertTrue(text.lines().anyMatch(line -> line.contains("domains[*]")
                && line.contains("the image of String.lowercase not shown")), text);
    }

    /**
     * The operations are said beside the values open for them and no others. A sum of the length
     * of {@code b} with a number near the greatest {@code Int} gets a run to the equality only
     * with a {@code b} of two code points or fewer: the longer ones are open for that, and not for
     * the lowercase's image, while the strings of {@code a} the partner holds at those lengths are
     * open for the image.
     */
    @Test
    void theOperationsAreSaidBesideTheValuesOpenForThemAndNoOthers() {
        assertEquals(List.of(
                        "a {\"shorterThan\":3,\"atAnyLength\":false,"
                                + "\"imagesNotShown\":[\"String.lowercase\"]}",
                        "b {\"longerThan\":2,\"atAnyLength\":false}"),
                leftOpenIn("""
                        module reach

                        data N = Int invariant value >= 9223372036854775805
                        data Missed

                        behavior f : (a: String, b: String, n: N) -> Bool | Missed
                        let f (a, b, n) = {
                            guard String.length(b) + n.value > 0 else Missed
                            String.lowercase(a) == b
                        }
                        """));
    }

    /** What each place of the behavior is left open at, as the report writes it. */
    private static List<String> leftOpenIn(String source) {
        JsonNode partition = new ObjectMapper().readTree(report(source)).path("modules").get(0)
                .path("behaviors").get(0).path("partition");
        List<String> open = new ArrayList<>();
        partition.path("unanswered").forEach(each -> each.path("stopped").forEach(stop -> {
            if (!stop.path("leftOpen").isMissingNode()) {
                open.add(each.path("subject").path("path").asString() + " "
                        + stop.path("leftOpen"));
            }
        }));
        return open;
    }

    /**
     * A partner held to one code point by its declarations, beside a way that ties its length to a
     * number near the greatest {@code Int}, is still the other side's only at one code point: the
     * way gets a run past a string of two, and a string of two letters is in the class of strings
     * never the partner all the same.
     */
    @Test
    void aPartnerHeldShortByItsDeclarationsIsHeldSoPastAWayThatTiesItsLength() {
        String model = """
                module example.equal

                data A = String
                    invariant String.matches("[a-z]*", value)

                data B = String
                    invariant String.length(value) <= 1

                data N = Int
                    invariant value >= 9223372036854775805

                behavior f : (a: A, b: B, n: N) -> Bool

                let f (a, b, n) = {
                    guard String.length(b.value) + n.value > 0 else false
                    a.value == b.value
                }
                """;
        assertEquals(List.of("x can be b a", "x is never b ab"),
                classesHolding(model, "a", List.of("a", "ab")));
    }

    /**
     * A partner held to three code points or more by its declarations, and to ten or fewer by a
     * guard the run gets past on the way to the equality, is the other side's at three to ten
     * code points: the guard names no fewest, and the declarations still do.
     */
    @Test
    void aPartnerHeldByItsDeclarationsAndByTheWayIsHeldToTheLengthsOfBoth() {
        String model = """
                module guarded

                data Email = String
                    invariant String.length(value) >= 3 && String.length(value) <= 254

                data Missed

                behavior f : (email: Email, other: String) -> Bool | Missed

                let f (Email(email), other) = {
                    guard String.length(email) <= 10 else Missed
                    email == other
                }
                """;
        assertEquals(List.of("x can be email abc", "x is never email ab",
                        "x is never email abcdefghijk"),
                classesHolding(model, "other", List.of("ab", "abc", "abcdefghijk")));
    }

    /** Which of {@code texts} each class of {@code path} holds, as the label and the text. */
    private static List<String> classesHolding(String source, String path, List<String> texts) {
        Compilation model = ACompiledModel.answered(source);
        Partitions.Partitioning divided =
                model.db().ask(new Adequacy.Divided(model.modules().get(0), "f")).value();
        assertNotNull(divided, "the behavior is divided");
        List<String> holding = new ArrayList<>();
        for (Axis axis : divided.axes()) {
            if (!axis.path().toString().equals(path)) {
                continue;
            }
            for (PartitionClass each : axis.classes()) {
                Recognition is = each.recognises() instanceof Recognition.Under(var _, var inner)
                        ? inner : each.recognises();
                if (is instanceof Recognition.OfASet(ValuesAtLengths values)) {
                    for (String text : texts) {
                        if (values.has(new Value.Text(text))) {
                            holding.add(each.label() + " " + text);
                        }
                    }
                }
            }
        }
        return holding;
    }

    /** The length of the value written for each class of {@code path}, by the class. */
    private static List<String> writtenFor(String source, String path) {
        Compilation model = ACompiledModel.answered(source);
        String module = model.modules().get(0);
        Partitions.Partitioning divided =
                model.db().ask(new Adequacy.Divided(module, "f")).value();
        assertNotNull(divided, "the behavior is divided");
        RuleReadingContext reading = RuleReadingContext.unshared(RuleReadings.of(model, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        List<String> out = new ArrayList<>();
        for (Axis axis : divided.axes()) {
            if (!axis.path().toString().equals(path)) {
                continue;
            }
            for (PartitionClass each : axis.classes()) {
                Partitions.standingFor(each.representatives(), reading, Set.of()).values()
                        .forEach(written -> out.add(each.label() + ": "
                                + lengthOf(written.text())));
            }
        }
        return out;
    }

    /** The code points of the string a literal writes, each escape one. */
    private static long lengthOf(String literal) {
        String inside = literal.substring(1, literal.length() - 1).replaceAll("\\\\.", "x");
        return inside.codePoints().count();
    }

    /**
     * Where a reading needs the partner's strings as one set and the set is past the allowance,
     * what stopped the reading is said with the allowance: a string inside another, and a
     * lowercase on this side of an equality, whose length is not the partner's.
     */
    @Test
    void aPartnersStringsPastTheAllowanceAreSaidAsTheFigureThatStoppedThem() {
        assertEquals(List.of("part strings_a_partner_holds_one_machine"),
                figuresIn(report("""
                        module inside

                        data Email = String invariant String.length(value) <= 100000

                        behavior f : (email: Email, part: String) -> Bool
                        let f (Email(email), part) = String.contains(part, email)

                        example f
                            | "in"  : (Email("a.com"), "com") -> true
                            | "out" : (Email("a.com"), "x") -> false
                        """), "part"));
        assertEquals(List.of("other strings_a_partner_holds_one_machine"),
                figuresIn(report("""
                        module converted

                        data Code = String invariant String.length(value) <= 100000

                        behavior f : (code: Code, other: String) -> Bool
                        let f (Code(code), other) = String.lowercase(other) == code

                        example f
                            | "same"  : (Code("ab"), "AB") -> true
                            | "other" : (Code("ab"), "cd") -> false
                        """), "other"));
    }

    /** The figures each place of {@code json}'s behavior named {@code path} was stopped at. */
    private static List<String> figuresIn(String json, String path) {
        JsonNode report = new ObjectMapper().readTree(json);
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("unanswered")) {
                    if (!each.path("subject").path("path").asString().equals(path)) {
                        continue;
                    }
                    for (JsonNode stop : each.path("stopped")) {
                        stop.path("figures").forEach(figure ->
                                out.add(path + " " + figure.asString()));
                    }
                }
            }
        }
        return out;
    }

    /**
     * A lowercase of an email held to ten thousand code points is read: the strings no longer
     * than the email are parted by what the lowercase answers, and only the longer ones are open.
     */
    @Test
    void aLowercaseOfAStringHeldToTenThousandIsRead() {
        JsonNode report = new ObjectMapper().readTree(report(emails(
                "String.length(value) <= 10000", "String.lowercase(email)")));
        JsonNode partition = report.path("modules").get(0).path("behaviors").get(0)
                .path("partition");
        List<String> axes = new ArrayList<>();
        partition.path("axes").forEach(axis -> axes.add(axis.path("path").asString()));
        assertEquals(List.of("domains[*]", "emails[*]"), axes);
        assertEquals(List.of("domains[*] {\"longerThan\":10000,\"atAnyLength\":false,"
                        + "\"imagesNotShown\":[\"String.lowercase\"]}"),
                leftOpenIn(emails("String.length(value) <= 10000", "String.lowercase(email)")));
    }
}
