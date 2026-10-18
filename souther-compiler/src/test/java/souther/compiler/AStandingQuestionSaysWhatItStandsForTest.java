package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A question nothing answered says what it stands for.
 *
 * <p>A rule that raised a question and went unaccounted for used to be printed as the question and
 * the rule alone. An author reading it is told the model asked something and nobody answered, and
 * is left to work out whether what is missing is a capability of this compiler, a rewrite of their
 * own clause, or nothing at all — the three are what a report already promises to tell apart, and
 * the line named none of them.
 *
 * <p>So the reason travels with the question, in the words this document already writes for a
 * position nothing divided. Nothing new is promised: it is the same vocabulary, said of the
 * question rather than of the place.
 */
class AStandingQuestionSaysWhatItStandsForTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * The models here with their stand-in for a rule nothing reads written out.
     *
     * <p>Named rather than written, because which spelling this compiler cannot read is a fact
     * about this compiler and moves ({@link ARuleNoReadingTakesIn}).
     */
    private static String unreadable(String source) {
        return source.replace("UNREAD_A", ARuleNoReadingTakesIn.about("a"))
                .replace("UNREAD_VALUE", ARuleNoReadingTakesIn.about("value"));
    }

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(unreadable(source), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static String reportOf(String source) {
        return measured(source).human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** What the document says stopped the one question of {@code source}. */
    private static List<String> stoppedInDocument(String source) {
        JsonNode document =
                JSON.readTree(measured(source).json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        JsonNode standing = document.get("modules").get(0).get("behaviors").get(0)
                .get("partition").get("unanswered");
        assertEquals(1, standing.size(), "one question, so one entry: " + standing);
        List<String> out = new ArrayList<>();
        standing.get(0).get("stopped")
                .forEach(each -> out.add(each.get("reason").asString()));
        return out;
    }

    /** The one line of the report about the rule {@code named}. */
    private static String about(String report, String named) {
        return report.lines()
                .filter(line -> line.contains("not accounted for: " + named))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "no question of " + named + " stands:\n" + report));
    }

    /**
     * A rule admitting values by a pattern, which is what raised this, and which is now answered.
     *
     * <p>The line this used to hold to is gone, and going was what it was for: it said the question
     * stood because the reading of values had no word for a pattern, and the reading has one. What
     * is asserted is the going — the rule raises a question about which values may stand at the
     * position, and nothing is left standing on it.
     *
     * <p>Held on the report rather than on the reading, because that is where a line would come
     * back. A pattern read into a set of values and then not carried to the answer would leave this
     * question standing again, and it would stand with a different reason and the same hole.
     */
    @Test
    void aPatternInvariantIsAnsweredAndLeavesNothingStanding() {
        String report = reportOf("""
                module probe.regex

                data Number = String
                    invariant String.matches("T[0-9]{13}", value)

                data Held = { n: Number }

                behavior read : (h: Held) -> Ok
                """);

        assertEquals(List.of(), report.lines()
                        .filter(line -> line.contains("not accounted for: invariant Number #1"))
                        .toList(),
                "the pattern says which values stand there, so nothing is left to answer:\n"
                        + report);
    }

    /**
     * Two parts of one clause stopped in two ways, and the line says both.
     *
     * <p>{@code a < b} relates the position to another, which this reading recognised and has no
     * set of one position's values for, and shows nothing of what the other reaches; the other is
     * a form it does not take apart.
     * The two are lifted by different work, so an author told only one of them lifts it and finds
     * the question still standing.
     *
     * <p>In the order the author wrote them, which is the whole reason the reasons are a list. A
     * report that sorted them would answer by a precedence nothing in the model decides.
     */
    @Test
    void aQuestionWithTwoCausesSaysBothOfThemInTheOrderTheyAreWritten() {
        assertEquals("      · not accounted for: invariant Pair (both)"
                        + " — which values may stand at p.a:"
                        + " what it states was read, and it relates the value here to another value"
                        + " not shown to reach every value here, so which values here settle it on"
                        + " their own is not worked out;"
                        + " written in a form this compiler does not read",
                about(reportOf("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = a < b && UNREAD_A

                        behavior read : (p: Pair) -> Ok
                        """), "invariant Pair (both)"));

        assertEquals("      · not accounted for: invariant Pair (both)"
                        + " — which values may stand at p.a:"
                        + " written in a form this compiler does not read;"
                        + " what it states was read, and it relates the value here to another value"
                        + " not shown to reach every value here, so which values here settle it on"
                        + " their own is not worked out",
                about(reportOf("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = UNREAD_A && a < b

                        behavior read : (p: Pair) -> Ok
                        """), "invariant Pair (both)"),
                "and the other way round, since the order is the author's and not a precedence");
    }

    /**
     * Two conjuncts stopped by one limit are one thing to lift, so the line says it once.
     *
     * <p>Both halves of the same rule draw the line on {@code x} and neither number was folded. What
     * a reader is owed is what to lift, and the two want the same reader written — said twice, an
     * author would be shown their own rule as two things.
     *
     * <p>Two products of constants, so that the limit is one. A half whose other side is an
     * operation on the position is a different thing to lift — what it says about the values there
     * takes inverting that operation — and two limits are two entries by design.
     *
     * <p>Which is the projection saying they are one thing and not the report dropping one of them:
     * each reason is put into the words the document promises on its own, and the words are made
     * distinct after that.
     */
    @Test
    void twoConjunctsStoppedByOneLimitAreSaidOnce() {
        String line = about(reportOf("""
                module probe.line

                data N = { x: Int, y: Int }
                    invariant said = x <= 10 * 2 && x <= 3 * 7

                behavior read : (n: N) -> Ok
                """), "invariant N (said)");

        assertTrue(line.endsWith(": written in a form this compiler does not read"), line);
        assertEquals(1, line.split("written in a form", -1).length - 1,
                "one limit, said once: " + line);
    }

    /**
     * A question a rule reaching through a helper leaves says what the same rule written out says.
     *
     * <p>The invariant is a call, and what it comes to is a rule about a field of the value the
     * helper was handed. The reading goes inside the binding the expansion made (ADR-0106), so the
     * position is named and the rule is read at it — and what stands is the reading's own word for
     * the form it could not take apart, which is the word the rule written where the clause is
     * would leave.
     *
     * <p>Held as one line and not as two readings agreeing, because the line is what a person is
     * shown: a word that turned on which of the two spellings an author reached for would be
     * reporting this compiler's arrangement rather than their model.
     */
    @Test
    void aQuestionARuleThroughAHelperLeavesSaysWhatTheRuleWrittenOutSays() {
        String throughAHelper = about(reportOf("""
                module probe.helper

                data Range = { min: String, max: String }

                data Checked = { range: Range }
                    invariant valid(range)

                behavior read : (c: Checked) -> Ok

                let valid (r: Range) : Bool = UNREAD_MAX
                """.replace("UNREAD_MAX", ARuleNoReadingTakesIn.about("r.max"))),
                "invariant Checked #1");

        assertEquals("      · not accounted for: invariant Checked #1"
                        + " — which values may stand at c.range.max:"
                        + " written in a form this compiler does not read",
                throughAHelper);
        assertEquals(about(reportOf("""
                module probe.helper

                data Range = { min: String, max: String }

                data Checked = { range: Range }
                    invariant UNREAD_MAX

                behavior read : (c: Checked) -> Ok
                """.replace("UNREAD_MAX", ARuleNoReadingTakesIn.about("range.max"))),
                "invariant Checked #1"), throughAHelper);
    }

    /** What the report says of a rule about a value an operation made of the position. */
    private static final String MADE_FROM_IT =
            "it is about a value made from this one, and what it says about the values here is not"
                    + " worked out";

    /** What the report says of a rule comparing a product of two values neither of which is a
     *  constant. */
    private static final String A_PRODUCT =
            "it compares a product of two values that are not constants, which no line on the values"
                    + " here says";

    /** Every line of the report saying a question of the rule {@code named} stands. */
    private static List<String> allAbout(String report, String named) {
        return report.lines()
                .filter(line -> line.contains("not accounted for: " + named))
                .toList();
    }

    /**
     * A single value with one invariant, and a behavior that reads it — which is what makes the
     * question of which values may stand there one the report is asked.
     */
    private static String aValueRuledBy(String type, String clause) {
        return """
                module probe.derived

                data V = %s
                    invariant %s

                data Held = { v: V }

                behavior read : (h: Held) -> Ok
                """.formatted(type, clause);
    }

    /**
     * An equality the arithmetic stopped on says where it stopped, as a bound stopped there does.
     *
     * <p>A magnitude, a total of the elements: each is a value an operation made of the position,
     * and nothing here follows that operation back to the values the position may hold. That is
     * what an author is owed — what would have to be read is the operation — and not that the rule
     * is a form this compiler has no word for, which sends them to rewrite a clause every reading
     * recognised.
     */
    @Test
    void anEqualityOnAValueMadeFromThePositionSaysSo() {
        for (String[] each : List.of(
                new String[] {"Int", "Int.abs(value) == 3"},
                new String[] {"List<Int>", "List.sum(value) == 0"})) {
            assertEquals(List.of("      · not accounted for: invariant V #1"
                            + " — which values may stand at h.v: " + MADE_FROM_IT),
                    allAbout(reportOf(aValueRuledBy(each[0], each[1])), "invariant V #1"),
                    each[1]);
        }
    }

    /**
     * And an equality over a product of two values says that, at each of them.
     *
     * <p>{@code net} is the other side of a relation and is not asked here; {@code qty} and
     * {@code price} are each a factor of a product nothing turns into a line or a set, and the word
     * for that is the one a bound over the same product is told.
     */
    @Test
    void anEqualityOverAProductOfTwoValuesSaysSoAtEach() {
        assertEquals(List.of(
                        "      · not accounted for: invariant Line #1 — which values may stand at"
                                + " l.qty: " + A_PRODUCT,
                        "      · not accounted for: invariant Line #1 — which values may stand at"
                                + " l.price: " + A_PRODUCT),
                allAbout(reportOf("""
                        module probe.product

                        data Line = { qty: Int, price: Int, net: Int }
                            invariant net == qty * price

                        behavior read : (l: Line) -> Ok
                        """), "invariant Line #1"));
    }

    /**
     * A bound over a product says the same of which values may stand there as of where they stop.
     *
     * <p>One rule, one arithmetic, one place it stopped: the two questions it raises stand on it
     * alike.
     */
    @Test
    void aBoundOverAProductSaysTheSameOfBothQuestions() {
        assertEquals(List.of(
                        "      · not accounted for: invariant V #1 — which values may stand at h.v: "
                                + A_PRODUCT,
                        "      · not accounted for: invariant V #1 — whether the values stop on h.v: "
                                + A_PRODUCT),
                allAbout(reportOf(aValueRuledBy("Int", "value * value >= 4")),
                        "invariant V #1"));
    }

    /**
     * A conjunct some reading took in is no part of what the question beside it stands on.
     *
     * <p>{@code value >= 0} is taken in by the reading of ends and placed as a line; the magnitude
     * beside it is what nothing took in. The reading of values has no word for an ordering, and
     * that is true and is no account of the magnitude — said beside it, an author rewrites a bound
     * that was read in full.
     */
    @Test
    void aConjunctTakenInIsNoPartOfTheAccountOfTheOneBesideIt() {
        assertEquals(List.of("      · not accounted for: invariant V #1"
                        + " — which values may stand at h.v: " + MADE_FROM_IT),
                allAbout(reportOf(aValueRuledBy("Int",
                                "value >= 0 && Int.abs(value) == 3")),
                        "invariant V #1"));
    }

    /**
     * And a statement taken in is no part of the account of the statement beside it in one conjunct.
     *
     * <p>A helper's body joining two rules is one conjunct stating both, and so is a denied choice.
     * The first statement is taken in by the reading of values; the second is a form nothing takes
     * apart, and that is what the question stands on — however the two were put into one conjunct.
     */
    @Test
    void aStatementTakenInIsNoPartOfTheAccountOfTheOneBesideItInOneConjunct() {
        String formNotRead = "      · not accounted for: invariant V #1"
                + " — which values may stand at h.v: written in a form this compiler does not read";
        assertEquals(List.of(formNotRead), allAbout(reportOf("""
                        module probe.joined
                        data V = String
                            invariant ok(value)
                        data Held = { v: V }
                        behavior read : (h: Held) -> Ok
                        let ok (s: String) : Bool = s /= "abc" && UNREAD_S
                        """.replace("UNREAD_S", ARuleNoReadingTakesIn.about("s"))),
                        "invariant V #1"),
                "a helper's body joining two rules");
        assertEquals(List.of(formNotRead), allAbout(reportOf(aValueRuledBy("String",
                        "Bool.not(value == \"abc\" || Bool.not(UNREAD_VALUE))")),
                        "invariant V #1"),
                "a denied choice");
    }

    /**
     * The control on the ones above: an equality something reads leaves no question standing.
     *
     * <p>A value written out, a count, a value an operation made that the arithmetic reads to the
     * end, and a part of a date and a remainder the values are read back out of. Each is taken in by
     * some reading, and nothing above may have taken that away.
     */
    @Test
    void anEqualitySomethingReadsLeavesNothingStanding() {
        for (String[] each : List.of(
                new String[] {"Int", "value == 7"},
                new String[] {"String", "String.length(value) == 3"},
                new String[] {"Int", "value * 2 == 4"},
                new String[] {"Date", "Date.day(value) == 1"},
                new String[] {"Int", "Int.floorMod(value, 1000) == 0"},
                new String[] {"Int", "value >= 0 && Int.floorMod(value, 1000) == 0"})) {
            assertEquals(List.of(),
                    allAbout(reportOf(aValueRuledBy(each[0], each[1])), "invariant V #1"),
                    each[1]);
        }
    }

    /**
     * The document says what the report says, from the same projection.
     *
     * <p>Two surfaces of one adequacy document. A consumer reading the machine-readable one is owed
     * what a person reading the other is told — written from a second walk, the two would answer one
     * question differently and nothing would say which to believe.
     *
     * <p>The order is part of what is published. It is the author's, and the schema says so, so a
     * consumer may read the first entry as the first thing to lift.
     */
    @Test
    void theDocumentSaysWhatTheReportSays() {
        assertEquals(List.of("unsupported_syntax"), stoppedInDocument("""
                module probe.regex

                data Number = String
                    invariant UNREAD_VALUE

                data Held = { n: Number }

                behavior read : (h: Held) -> Ok
                """));

        assertEquals(List.of("relation_not_shown_to_reach_every_value", "unsupported_syntax"),
                stoppedInDocument("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = a < b && UNREAD_A

                        behavior read : (p: Pair) -> Ok
                        """));

        assertEquals(List.of("unsupported_syntax", "relation_not_shown_to_reach_every_value"),
                stoppedInDocument("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = UNREAD_A && a < b

                        behavior read : (p: Pair) -> Ok
                        """),
                "and the order is the author's here too");

        assertEquals(List.of("rule_about_a_derived_value"),
                stoppedInDocument(aValueRuledBy("Int", "Int.abs(value) == 3")),
                "and where the arithmetic stopped, its word");
        assertEquals(List.of("non_affine_product"),
                stoppedInDocument(aValueRuledBy("Int", "value * value == 4")));
    }
}
