package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.semantics.CaseMapping;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An exact equality on the right of {@code ||} is reached only past the left, which lowercases the
 * same string inside a closure over another list. A row holding that list empty works out no
 * conversion, and the equality is reached at every string — so no string of either of its places
 * is left open for the conversion. Where a rule holds the list to an entry, the conversion is
 * worked out on every run that gets there, and the strings it is not exact on stay open.
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
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        model.answerEverything();
        assertEquals(List.of(), model.errors().stream()
                .map(e -> e.diagnostic().code()).toList(), "the model compiles");
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

    @Test
    void theEqualityIsReachedAtEveryStringWhereTheListMayBeEmpty() {
        List<String> open = leftOpenIn(FREE);
        assertTrue(!open.contains("email") && !open.contains("emails[*]"), open.toString());
    }

    @Test
    void theStringsTheConversionIsNotExactOnStayOpenWhereTheListHoldsOne() {
        List<String> open = leftOpenIn(HELD);
        assertTrue(open.contains("email") && open.contains("emails[*]"), open.toString());
    }

    /**
     * What each place is left open for, by why: the place, then the functions whose image is not
     * shown, then those a run is not shown to get past.
     */
    private static List<String> leftOpenFor(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        model.answerEverything();
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
                                    + open.path("imagesNotShown") + " past "
                                    + open.path("notShownGottenPast"));
                        }
                    }
                }
            }
        }
        return out;
    }

    /** The conversion is worked out on every run to the equality, and the strings it is not
     *  exact on are open for whether it gets the run past, not for its image. */
    @Test
    void theStringsAreOpenForGettingPastTheConversionNotForItsImage() {
        List<String> open = leftOpenFor(HELD);
        assertTrue(open.contains("email image  past [\"String.lowercase\"]"), open.toString());
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

    @Test
    void listsOfOneRecordNoRuleTiesAreReadAsListsApart() {
        List<String> open = leftOpenIn(paired(""));
        assertTrue(!open.contains("email") && !open.contains("pair.emails[*]"), open.toString());
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
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        model.answerEverything();
        assertEquals(List.of(), model.errors().stream()
                .map(e -> e.diagnostic().code()).toList(), "the model compiles");
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
     * Whatever holds the email short, nothing is left open for getting past the conversion: a
     * length rule is held as a number whatever length it names, where the strings it leaves are
     * no language the reading writes out, and a format is held by the strings it admits, alone or
     * beside a length rule.
     *
     * <p>And each held by one rule is read: the places left unanswered are the ones the email
     * held to 254 leaves, so that a relation not read at all, which leaves nothing open for
     * anything, is not taken for one that leaves nothing open for getting past. A format beside a
     * length rule is no set of strings the relation is read over, and leaves both lists unread.
     */
    @Test
    void nothingIsOpenForGettingPastTheConversionWhereTheEmailIsHeldShort() {
        List<String> read = unansweredIn(heldBy("String.length(value) <= 254",
                "String.lowercase(%s)", "a.com"));
        Map<String, Boolean> rules = new LinkedHashMap<>();
        rules.put("String.length(value) <= 254", true);
        rules.put("String.length(value) <= 100000", true);
        rules.put("String.matches(\"[^\\\\s]{1,64}\", value)", true);
        rules.put("String.matches(\"[^\\\\s]+\", value) && String.length(value) <= 254", false);
        rules.put("value == \"a.com\" || value == \"x@b.com\" || value == \"İ\"", true);
        rules.forEach((rule, isRead) -> {
            String model = heldBy(rule, "String.lowercase(%s)", "a.com");
            List<String> open = leftOpenFor(model);
            assertTrue(open.stream().allMatch(each -> each.endsWith(" past ")),
                    rule + " " + open);
            if (isRead) {
                assertEquals(read, unansweredIn(model), rule);
            }
        });
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
     * by uppercase, so through the two it is not shown its own answer.
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
        assertTrue(sharp.stream().anyMatch(each -> each.startsWith("a image [")), sharp.toString());
    }

    /** And where it may be any length, the strings the map is not exact on may stop the run. */
    @Test
    void anEmailOfAnyLengthIsOpenForGettingPastTheConversion() {
        List<String> open = leftOpenFor(heldBy("String.matches(\"[^\\\\s]+\", value)",
                "String.lowercase(%s)", "a.com"));
        assertTrue(open.contains("email image  past [\"String.lowercase\"]"), open.toString());
    }

    /** Two conversions in turn, the second handed what the first answered. */
    @Test
    void anEmailHeldShortGetsPastTwoConversionsInTurn() {
        String twice = "String.uppercase(String.lowercase(%s))";
        List<String> held = leftOpenFor(heldBy("String.length(value) <= 254", twice, "A.COM"));
        assertTrue(held.stream().allMatch(each -> each.endsWith(" past ")), held.toString());
        assertTrue(!unansweredIn(heldBy("String.length(value) <= 254", twice, "A.COM"))
                .contains("emails[*]"));
        List<String> free = leftOpenFor(heldBy("true", twice, "A.COM"));
        assertTrue(free.contains("emails[*] image  past [\"String.lowercase\",\"String.uppercase\"]"),
                free.toString());
    }

    /**
     * The longest string a conversion is gotten past at whatever it holds: a {@code String}'s
     * longest over the most one code point comes to in the answer, four for either conversion as
     * written or decomposed, and over that again for each conversion done in turn.
     */
    @Test
    void theLongestStringGottenPastIsAStringsLongestOverWhatEachConversionGrowsBy() {
        long once = Strings.LONGEST_TEXT / 4;
        assertEquals(Strings.LONGEST_TEXT,
                CaseMaps.longestGottenPastAtEveryString(CaseMapping.NONE));
        assertEquals(once, CaseMaps.longestGottenPastAtEveryString(CaseMapping.LOWERCASE));
        assertEquals(once, CaseMaps.longestGottenPastAtEveryString(CaseMapping.UPPERCASE));
        assertEquals(once / 4, CaseMaps.longestGottenPastAtEveryString(
                new CaseMapping.Uppercase(CaseMapping.LOWERCASE)));
    }

    /** As long as each other: an entry for the equality is an entry to work the conversion over. */
    @Test
    void theStringsStayOpenWhereARuleHoldsTheListsToOneLength() {
        List<String> open = leftOpenIn(paired(
                "\n    invariant List.length(domains) == List.length(emails)"));
        assertTrue(open.contains("email") && open.contains("pair.emails[*]"), open.toString());
    }

    /**
     * The same said as a choice, which the region holds as no bound on either list alone: the tie
     * is the rule's, and a row emptying the one beside the other's entry breaks it.
     */
    @Test
    void theStringsStayOpenWhereARuleSaysTheOtherHoldsOneWhereThisDoes() {
        List<String> open = leftOpenIn(paired(
                "\n    invariant List.length(emails) == 0 || List.length(domains) >= 1"));
        assertTrue(open.contains("email") && open.contains("pair.emails[*]"), open.toString());
    }
}
