package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An exact equality on the right of {@code ||} is reached only past the left, which lowercases the
 * same string inside a closure over another list. The lowercase stops a run only where its answer
 * is longer than a {@code String} holds, which parts no strings: so whether a row may hold that
 * list empty and work out no conversion, or a rule holds the list to an entry and every run that
 * gets there works it out, the equality is reached at every string, and no string of either of its
 * places is left open for the conversion.
 */
class AnEqualityPastAConversionARowNeedNotWorkOutIsReadTest {

    private static final String FREE = """
            module free

            behavior f : (email: String, domains: List<String>, emails: List<String>) -> Bool
            let f (email, domains, emails) =
                List.any(own -> own == String.lowercase(email), domains)
                    || List.any(own -> own == email, emails)

            example f
                | "domain" : ("a.com", [ "a.com" ], []) -> true
                | "email"  : ("x@b.com", [], [ "x@b.com" ]) -> true
                | "none"   : ("x@b.com", [ "a.com" ], [ "y@b.com" ]) -> false
            """;

    private static final String HELD = """
            module held

            data Domains = List<String> invariant List.length(value) >= 1

            behavior f : (email: String, domains: Domains, emails: List<String>) -> Bool
            let f (email, Domains(domains), emails) =
                List.any(own -> own == String.lowercase(email), domains)
                    || List.any(own -> own == email, emails)

            example f
                | "domain" : ("a.com", Domains([ "a.com" ]), []) -> true
                | "email"  : ("x@b.com", Domains([ "q" ]), [ "x@b.com" ]) -> true
                | "none"   : ("x@b.com", Domains([ "a.com" ]), [ "y@b.com" ]) -> false
            """;

    /**
     * The same equality over two lists of one record, with {@code rule} the record's invariant:
     * where it ties the lists, a row holding the one the conversion is worked out over empty
     * may break it beside the entry the other holds for the equality to be reached at.
     */
    private static String paired(String rule) {
        return """
                module paired

                data Pair = { domains: List<String>, emails: List<String> }%s

                behavior f : (email: String, pair: Pair) -> Bool
                let f (email, pair) =
                    List.any(own -> own == String.lowercase(email), pair.domains)
                        || List.any(own -> own == email, pair.emails)

                example f
                    | "domain" : ("a.com", Pair { domains = [ "a.com" ], emails = [ "q" ] }) -> true
                    | "email"  : ("x@b.com", Pair { domains = [ "q" ], emails = [ "x@b.com" ] }) -> true
                    | "none"   : ("x@b.com", Pair { domains = [ "a.com" ], emails = [ "y@b.com" ] }) -> false
                """.formatted(rule);
    }

    /** The places of {@code source}'s behavior a region is left open at, by what the report
     *  asks of them. */
    private static List<String> leftOpenIn(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> open = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("unanswered")) {
                    if (each.path("question").asString().equals("regionNotDetermined")) {
                        open.add(each.path("subject").path("path").asString());
                    }
                }
            }
        }
        return open;
    }

    /**
     * The equality is reached at every string whether the list the conversion is worked out over
     * may be empty, is held to an entry, is one of two lists of a record no rule ties, or is tied
     * by a rule to the list the equality reads: held as long as it, or held to an entry wherever
     * that one holds one.
     */
    @Test
    void theEqualityIsReachedAtEveryStringWhateverTheListTheConversionIsWorkedOverHolds() {
        for (String source : List.of(FREE, HELD)) {
            List<String> open = leftOpenIn(source);
            assertTrue(!open.contains("email") && !open.contains("emails[*]"),
                    () -> source + open);
        }
        for (String rule : List.of("",
                "\n    invariant List.length(domains) == List.length(emails)",
                "\n    invariant List.length(emails) == 0 || List.length(domains) >= 1")) {
            List<String> open = leftOpenIn(paired(rule));
            assertTrue(!open.contains("email") && !open.contains("pair.emails[*]"),
                    () -> rule + " " + open);
        }
    }

    /**
     * What each place is left open for: the place, then the functions whose image is not shown.
     */
    private static List<String> leftOpenFor(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("unanswered")) {
                    for (JsonNode stop : each.path("stopped")) {
                        JsonNode open = stop.path("leftOpen");
                        if (!open.isMissingNode()) {
                            out.add(each.path("subject").path("path").asString() + " image "
                                    + open.path("imagesNotShown"));
                        }
                    }
                }
            }
        }
        return out;
    }

    /**
     * Where the equality is with what the conversion answers, every string the conversion leaves
     * as it stands is its own answer, so the other side holds nothing open for the image.
     */
    @Test
    void anEqualityWithWhatTheConversionAnswersLeavesNothingOpenForItsImage() {
        List<String> open = leftOpenFor("""
                module image

                behavior same : (a: String, b: String) -> Bool
                let same (a, b) = String.lowercase(a) == b

                example same
                    | "equal" : ("ab", "ab") -> true
                    | "differ" : ("ab", "cd") -> false
                """);
        assertEquals(List.of(), open);
    }

    /** A string of the converted side outside the map and not left as it stands, such as
     *  {@code İ}, has an answer only the conversion works out, so its image is still open. */
    @Test
    void anEqualityBetweenTwoConversionsIsOpenForTheStringsOnlyTheConversionAnswers() {
        List<String> open = leftOpenFor("""
                module image

                behavior same : (a: String, b: String) -> Bool
                let same (a, b) = String.lowercase(a) == String.lowercase(b)

                example same
                    | "equal" : ("ab", "ab") -> true
                    | "differ" : ("ab", "cd") -> false
                """);
        assertTrue(open.stream().anyMatch(each -> each.contains("image [\"String.lowercase\"")),
                open.toString());
    }

    /**
     * A way asking the list the equality is read in for two entries is met on a row holding it
     * with as few as the way leaves it, two, and the other list empty: the row holds each
     * container at a count some row takes, and is read as where nothing is asked of the count.
     */
    @Test
    void theWayIsMetWithTheListReadInHoldingAsFewAsItAsksFor() {
        List<String> open = leftOpenIn("""
                module several

                behavior f : (email: String, domains: List<String>, emails: List<String>) -> Bool
                let f (email, domains, emails) =
                    List.length(emails) >= 2
                        && (List.any(own -> own == String.lowercase(email), domains)
                            || List.any(own -> own == email, emails))

                example f
                    | "domain" : ("a.com", [ "a.com" ], [ "p", "q" ]) -> true
                    | "email"  : ("x@b.com", [], [ "x@b.com", "q" ]) -> true
                    | "none"   : ("x@b.com", [ "a.com" ], [ "y@b.com", "q" ]) -> false
                    | "short"  : ("x@b.com", [], [ "x@b.com" ]) -> false
                """);
        assertTrue(!open.contains("email") && !open.contains("emails[*]"), open.toString());
    }

    /**
     * {@link #HELD} with the email held by {@code rule} (about {@code value}) and converted by
     * {@code conversion} (written around {@code %s}), whose answer of {@code a.com} is
     * {@code domain}.
     */
    private static String heldBy(String rule, String conversion, String domain) {
        return """
                module bounded

                data Email = String invariant %s
                data Domains = List<String> invariant List.length(value) >= 1

                behavior f : (email: Email, domains: Domains, emails: List<String>) -> Bool
                let f (Email(email), Domains(domains), emails) =
                    List.any(own -> own == %s, domains)
                        || List.any(own -> own == email, emails)

                example f
                    | "domain" : (Email("a.com"), Domains([ "%s" ]), []) -> true
                    | "email"  : (Email("x@b.com"), Domains([ "q" ]), [ "x@b.com" ]) -> true
                    | "none"   : (Email("x@b.com"), Domains([ "a.com" ]), [ "y@b.com" ]) -> false
                """.formatted(rule, conversion.formatted("email"), domain);
    }

    /** The places of {@code source}'s behavior anything is left unanswered at, whatever the
     *  question: a reading that did not run leaves every place it reads. */
    private static List<String> unansweredIn(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("unanswered")) {
                    out.add(each.path("subject").path("path").asString());
                }
            }
        }
        return out;
    }

    /**
     * An email held to fewer code points than a lowercase answers within a {@code String} at any
     * code points gets the run past it at every string, whether or not the map is exact on it.
     * Nothing is left open for getting past it, and the list read beside it is read whole; the
     * list it is compared with is still open for its image.
     */
    @Test
    void anEmailHeldShortGetsPastTheConversionAtEveryString() {
        assertEquals(List.of("domains[*]"), unansweredIn(heldBy("String.length(value) <= 254",
                "String.lowercase(%s)", "a.com")));
    }

    /** The same where what holds it short is the strings its format admits. */
    @Test
    void anEmailWhoseFormatHoldsItShortGetsPastTheConversionAtEveryString() {
        assertEquals(List.of("domains[*]"), unansweredIn(heldBy(
                "String.matches(\"[^\\\\s]{1,64}\", value)", "String.lowercase(%s)",
                "a.com")));
    }

    /**
     * Whatever holds the email short, the relation is read as where it is held to 254: a length
     * rule is held as a number whatever length it names, where the strings it leaves are no
     * language the reading writes out, and a format is held by the strings it admits, alone or
     * beside a length rule. The places left unanswered are the ones the email held to 254 leaves,
     * so that a relation not read at all, which leaves nothing open for anything, is not taken
     * for one read.
     */
    @Test
    void whateverHoldsTheEmailShortTheRelationIsReadAsWhereItIsHeldTo254() {
        List<String> read = unansweredIn(heldBy("String.length(value) <= 254",
                "String.lowercase(%s)", "a.com"));
        for (String rule : List.of("String.length(value) <= 100000",
                "String.matches(\"[^\\\\s]{1,64}\", value)",
                "String.matches(\"[^\\\\s]+\", value) && String.length(value) <= 254",
                "value == \"a.com\" || value == \"x@b.com\" || value == \"İ\"")) {
            assertEquals(read, unansweredIn(heldBy(rule, "String.lowercase(%s)", "a.com")), rule);
        }
    }

    /**
     * {@code c == a} is reached only where {@code String.lowercase(a) == b} is false, and
     * {@code b} holds {@code "1"} alone: {@code c = "1"} equals {@code a} only at {@code a = "1"},
     * where the left is true and the right is never asked. What the left turns on is {@code a}
     * and {@code b}, though no row is composed toward it, so {@code c} is not parted by every
     * string {@code a} holds.
     */
    @Test
    void aComparisonNoRowIsComposedTowardStillTurnsOnThePlacesItReads() {
        String held = """
                module fixed

                data A = String invariant String.length(value) <= 254
                data B = String invariant value == "1"

                behavior f : (a: A, b: B, c: String) -> Bool
                let f (A(a), B(b), c) = %s == b || c == a

                example f
                    | "left"  : (A("1"), B("1"), "q") -> true
                    | "right" : (A("y"), B("1"), "y") -> true
                    | "none"  : (A("y"), B("1"), "z") -> false
                """;
        for (String left : List.of("String.lowercase(a)", "String.uppercase(a)", "a")) {
            List<String> open = unansweredIn(held.formatted(left));
            assertTrue(open.contains("c"), left + " " + open);
        }
    }

    /**
     * The same way with {@code b} free to be any string: whatever {@code a} is, a row holds
     * {@code b} apart from what the left compares it with, so the right is reached at every
     * {@code a} and {@code c} is parted by every string {@code a} holds — with a conversion on the
     * left and without one.
     */
    @Test
    void aComparisonAFreeStringMeetsLeavesThePlacesItReadsToThePartner() {
        String free = """
                module free

                data A = String invariant String.length(value) <= 254

                behavior f : (a: A, b: String, c: String) -> Bool
                let f (A(a), b, c) = %s == b || c == a

                example f
                    | "left"  : (A("1"), "1", "q") -> true
                    | "right" : (A("y"), "1", "y") -> true
                    | "none"  : (A("y"), "1", "z") -> false
                """;
        for (String left : List.of("String.lowercase(a)", "a")) {
            List<String> open = unansweredIn(free.formatted(left));
            assertTrue(!open.contains("c"), left + " " + open);
        }
    }

    /**
     * A value is free to meet a statement only where nothing else holds it. Here {@code b} is
     * read by a second statement on the way, which holds it to one string: past the two, {@code b}
     * is {@code "1"} and apart from what the left compares it with, so at the {@code a} that is
     * {@code "1"} no run reaches the right, and {@code c} is not shown parted by every string
     * {@code a} holds.
     */
    @Test
    void aValueASecondStatementOnTheWayHoldsIsNotFreeToMeetTheFirst() {
        String held = """
                module held

                data A = String invariant String.length(value) <= 254

                behavior f : (a: A, b: String, c: String) -> Bool
                let f (A(a), b, c) = %s == b || b /= "1" || c == a

                example f
                    | "left"  : (A("1"), "1", "q") -> true
                    | "other" : (A("y"), "2", "q") -> true
                    | "right" : (A("y"), "1", "y") -> true
                    | "none"  : (A("y"), "1", "z") -> false
                """;
        for (String left : List.of("String.lowercase(a)", "a")) {
            List<String> open = unansweredIn(held.formatted(left));
            assertTrue(open.contains("c"), left + " " + open);
        }
    }

    /**
     * No domain equal to what the left compares it with, the domains free to be any strings:
     * every element is held apart from it, so the list read on the right is read whole — with a
     * conversion and without one. Where every domain is one string, nothing is free to be held
     * apart.
     */
    @Test
    void noElementMeetingAComparisonIsMetByElementsFreeToBeAnyString() {
        for (String left : List.of("String.lowercase(email)", "email")) {
            List<String> open = unansweredIn(heldBy("String.length(value) <= 254",
                    left.replace("email", "%s"), "a.com"));
            assertTrue(!open.contains("emails[*]"), left + " " + open);
        }
        String fixed = """
                module fixed

                data A = String invariant String.length(value) <= 254
                data Domains = List<String>
                    invariant List.length(value) >= 1 && List.all(d -> d == "1", value)

                behavior f : (email: A, domains: Domains, emails: List<String>) -> Bool
                let f (A(email), Domains(domains), emails) =
                    List.any(own -> own == String.lowercase(email), domains)
                        || List.any(own -> own == email, emails)

                example f
                    | "domain" : (A("1"), Domains([ "1" ]), []) -> true
                    | "email"  : (A("y"), Domains([ "1" ]), [ "y" ]) -> true
                    | "none"   : (A("y"), Domains([ "1" ]), [ "z" ]) -> false
                """;
        assertTrue(unansweredIn(fixed).contains("emails[*]"), unansweredIn(fixed).toString());
    }

    /**
     * A digit and a combining acute are outside the map and left alone by both conversions, so a
     * string of them is its own answer through any of them done in turn: neither side is open,
     * the other side holding every answer there is. A sharp s is left alone by lowercase and not
     * by uppercase, so through the two it is not shown its own answer, and the other side is open
     * for the uppercase's image.
     */
    @Test
    void aStringEveryConversionDoneInTurnLeavesAloneIsItsOwnAnswer() {
        String model = """
                module image

                data A = String invariant String.matches("%s", value)

                behavior same : (a: A, b: String) -> Bool
                let same (A(a), b) = %s == b

                example same
                    | "equal"  : (A("%s"), "%s") -> true
                    | "differ" : (A("%s"), "cd") -> false
                """;
        String digits = "1́";
        for (String conversion : List.of("String.lowercase(a)",
                "String.lowercase(String.lowercase(a))",
                "String.uppercase(String.lowercase(a))")) {
            List<String> open = leftOpenFor(model.formatted("[0-9]\\\\x{301}", conversion,
                    digits, digits, digits));
            assertTrue(open.isEmpty(), conversion + " " + open);
        }
        List<String> sharp = leftOpenFor(model.formatted("ß", "String.uppercase(String.lowercase(a))",
                "ß", "SS", "ß"));
        assertEquals(List.of("b image [\"String.uppercase\"]"), sharp);
    }

    /** An email of any length is read as one held short: the strings the map is not exact on
     *  stop the run only past what a {@code String} holds, and are open for nothing. */
    @Test
    void anEmailOfAnyLengthIsReadAsOneHeldShort() {
        assertEquals(leftOpenFor(heldBy("String.length(value) <= 254", "String.lowercase(%s)",
                        "a.com")),
                leftOpenFor(heldBy("String.matches(\"[^\\\\s]+\", value)",
                        "String.lowercase(%s)", "a.com")));
    }

    /** Two conversions in turn, the second handed what the first answered: an email held short
     *  and one of any length are read alike, and the list read beside them is read whole. */
    @Test
    void anEmailHeldShortGetsPastTwoConversionsInTurn() {
        String twice = "String.uppercase(String.lowercase(%s))";
        String held = heldBy("String.length(value) <= 254", twice, "A.COM");
        String free = heldBy("true", twice, "A.COM");
        assertEquals(leftOpenFor(held), leftOpenFor(free));
        assertTrue(!unansweredIn(held).contains("emails[*]"), () -> unansweredIn(held).toString());
        assertTrue(!unansweredIn(free).contains("emails[*]"), () -> unansweredIn(free).toString());
    }
}
