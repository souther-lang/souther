package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleRef;
import souther.compiler.diag.Citation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Sites;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.WayIn;
import souther.compiler.types.SourceConstruct;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork on whether a list is empty draws the line its size against nought draws, and the line is
 * the application the author wrote.
 *
 * <p>The library says {@code List.isEmpty} means a size against nought, and the checker reads it
 * so. Partition read it as a fork about a value made from the list, because a line was drawn only
 * on a comparison the source wrote. What the line is drawn on is what the construct states; what
 * the rule is, where a report sends a reader and where a run through it is seen, is the construct.
 */
class AnEmptinessCheckDrawsTheLineItsSizeDrawsTest {

    private static final String EMPTY = "List.isEmpty(order.lines)";

    private static final String SIZE = "List.length(order.lines) == 0";

    /**
     * What the body tells apart reads the two spellings alike, and the denied two alike.
     *
     * <p>A decision on the check is the application coming out one way, placed on the size's axis
     * the way the comparison it means is: the class of no lines, or the rest.
     */
    @Test
    void whatTheBodyTellsApartIsTheSameForBothSpellings() {
        assertEquals(toldApartOf(SIZE), toldApartOf(EMPTY));
        assertEquals(toldApartOf("List.length(order.lines) /= 0"),
                toldApartOf("Bool.not(List.isEmpty(order.lines))"));
        assertTrue(toldApartOf(EMPTY).getFirst().startsWith("Drawn"),
                () -> "the classes are told apart: " + toldApartOf(EMPTY));
    }

    /** And the decision is the application's, as the plan names where it answers. */
    @Test
    void aDecisionOnTheCheckIsTheApplications() {
        Compilation compilation = compiled(bill(EMPTY));
        CoverageRead.Read read =
                compilation.db().ask(new Adequacy.Meets("demo")).value().get("bill");
        List<SourceConstruct> kinds = new ArrayList<>();
        for (WayIn way : read.taken()) {
            for (Decision each : way.decisions()) {
                if (each.constrains() instanceof souther.compiler.reading.Condition.Side side
                        && side.at().toString().startsWith("List.length")
                        && !kinds.contains(side.statedAt().origin().kind())) {
                    kinds.add(side.statedAt().origin().kind());
                }
            }
        }
        assertEquals(List.of(SourceConstruct.CALL), kinds);
    }

    /** What the body tells apart at each axis, in the order the axes are. */
    private static List<String> toldApartOf(String guard) {
        return measured(bill(guard)).axes().stream()
                .map(axis -> String.valueOf(axis.toldApart())).toList();
    }

    /** The axis, its classes and the line, which is everything the two spellings share. */
    @Test
    void theTwoSpellingsDrawOneLine() {
        assertEquals(geometryOf(SIZE), geometryOf(EMPTY));
        assertEquals(classesOf(SIZE), classesOf(EMPTY));
        assertEquals(List.of("bill/List.length(order.lines): List.length(order.lines) = 0"),
                geometryOf(EMPTY), "a line on the size of what the input holds, at nought");
    }

    /** And the same of the check denied, which is the size held apart from nought. */
    @Test
    void aDeniedCheckDrawsTheLineItsDeniedSizeDraws() {
        assertEquals(geometryOf("List.length(order.lines) /= 0"),
                geometryOf("Bool.not(List.isEmpty(order.lines))"));
    }

    /** The fork the issue was about is not left as a rule nothing read. */
    @Test
    void theForkIsNotLeftAsARuleAboutAValueMadeFromTheList() {
        assertEquals(List.of(), measured(bill(EMPTY)).notRead());
    }

    /**
     * The rule is the application, and a report is sent to where it is written.
     *
     * <p>A comparison in kind, because it puts a line on an order; an application in what was
     * written, which is what tells it from every other rule and where a reader goes.
     */
    @Test
    void theLineIsTheApplicationsRuleAndIsCitedWhereItIsWritten() {
        Compilation compilation = compiled(bill(EMPTY));
        RuleRef.Comparison rule = onlyRuleOnTheSize(compilation);
        assertEquals(SourceConstruct.CALL, rule.origin().kind());
        // Looked up by the construct the rule names, among the applications the module wrote: a
        // place found there is the application, and none would be found among its comparisons.
        assertInstanceOf(Citation.Written.class,
                compilation.db().ask(new Sites.WhereARuleIsWritten(rule)).value(),
                "a reader is sent to where the application is written");
    }

    /** One application in a helper called twice is one rule, however many forks read it. */
    @Test
    void anApplicationInAHelperCalledTwiceIsOneRule() {
        String model = header() + """
                let empty (xs) = List.isEmpty(xs)

                behavior bill : (order: Order) -> NoBill | Discounted | Full
                let bill (order) =
                    if order.coupon >= 10 then (if empty(order.lines) then NoBill else Discounted { total = 1 })
                    else (if empty(order.lines) then NoBill else Full { total = 1 })
                """;
        Set<RuleRef> rules = rulesOnTheSize(compiled(model));
        assertEquals(1, rules.size(), () -> "one written application: " + rules);
    }

    /**
     * A row that never ran the application does not meet its line.
     *
     * <p>Both rows hold no lines and land in {@code Manual}. One asked whether the list was empty
     * and was told yes; the other was settled by the rank before the question was asked. What is
     * watched is the application's answer, which only the first gave.
     */
    @Test
    void aRowThatSkippedTheApplicationDoesNotMeetItsLine() {
        for (String guard : List.of(EMPTY, SIZE)) {
            assertEquals(new ItemAssessment.Coverage.Hit(),
                    coverageAtNought(guard, "0", "Auto"), guard + " ran and answered true");
            assertEquals(new ItemAssessment.Coverage.NoHit(),
                    coverageAtNought(guard, "-1", "Manual"), guard + " never ran");
        }
    }

    /**
     * Where nothing arrives at the check, neither spelling draws a line there.
     *
     * <p>The coupon cannot be above ten and below five, so nothing reaches the check, and a line
     * there is one no row is owed for. Dropped for the comparison by what arrives at it; dropped for
     * the application by the same fact, filed where the application answers.
     */
    @Test
    void whereNothingArrivesNeitherSpellingDrawsALine() {
        for (String guard : List.of(EMPTY, SIZE)) {
            String model = header() + """
                    behavior bill : (order: Order) -> NoBill | Discounted | Full
                    let bill (order) =
                        if order.coupon > 10 then
                            (if order.coupon < 5 then (if %s then NoBill else Discounted { total = 1 })
                             else Discounted { total = 2 })
                        else Full { total = 1 }
                    """.formatted(guard);
            assertEquals(List.of(), rulesOnTheSize(compiled(model)).stream().toList(),
                    guard + " is asked where nothing arrives");
        }
    }

    /** An operation the library says nothing of the size about draws no line of its own. */
    @Test
    void anOperationThatMeansNoComparisonIsNotOne() {
        Compilation compilation =
                compiled(bill("List.any(l -> l.price > 0, order.lines)"));
        for (BorderAssessment each : linesOf(compilation)) {
            assertFalse(each.origin().rule() instanceof RuleRef.Comparison c
                            && c.origin().kind() == SourceConstruct.CALL,
                    () -> "a line drawn by the application itself: " + each.origin());
        }
    }

    /**
     * What a check over a derived list means is the size of that list, not of the input's.
     *
     * <p>{@code List.isEmpty(List.filter(...))} states nothing about how many lines the order has,
     * so no line is drawn on that number.
     */
    @Test
    void aCheckOverAFilteredListDrawsNoLineOnTheInputsSize() {
        assertTrue(rulesOnTheSize(compiled(
                        bill("List.isEmpty(List.filter(l -> l.price > 0, order.lines))")))
                .isEmpty());
    }

    private static ItemAssessment.Coverage coverageAtNought(String guard, String rank, String out) {
        String model = """
                module demo

                data Line = { price: Int }
                data Order = { lines: List<Line>, rank: Int }
                data Auto
                data Manual

                behavior gate : (order: Order) -> Auto | Manual
                let gate (order) = if order.rank >= 0 && %s then Auto else Manual

                example gate
                    | "one row" : (Order { lines = [], rank = %s }) -> %s
                """.formatted(guard, rank, out);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> lines =
                Adequacy.boundariesOf(compilation.db(), "demo");
        assertNotNull(lines, "the model under test compiles");
        return BorderAssessment.pointsOf(lines.get("gate")).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .filter(p -> p.border().axis().equals("gate/List.length(order.lines)")
                        && "0".equals(p.against()))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no line at nought for " + guard))
                .owed().coverage().made().orElseThrow();
    }

    /** The geometry each line has, without the rule that drew it. */
    private static List<String> geometryOf(String guard) {
        return linesOf(compiled(bill(guard))).stream()
                .filter(each -> each.axis().startsWith("bill/List.length"))
                .map(each -> each.axis() + ": " + each.label())
                .toList();
    }

    private static List<List<String>> classesOf(String guard) {
        return measured(bill(guard)).axes().stream()
                .map(axis -> axis.classes().stream().map(Object::toString).toList())
                .toList();
    }

    private static RuleRef.Comparison onlyRuleOnTheSize(Compilation compilation) {
        Set<RuleRef> rules = rulesOnTheSize(compilation);
        assertEquals(1, rules.size(), () -> "one rule on the size: " + rules);
        return (RuleRef.Comparison) rules.iterator().next();
    }

    private static Set<RuleRef> rulesOnTheSize(Compilation compilation) {
        return linesOf(compilation).stream()
                .filter(each -> each.axis().startsWith("bill/List.length"))
                .map(each -> each.origin().rule())
                .collect(Collectors.toSet());
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, () -> "the model under test compiles: " + compilation.errors());
        return read.getOrDefault("bill", List.of());
    }

    private static PartitionEvidence measured(String model) {
        Map<String, PartitionEvidence> coverage =
                compiled(model).db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        return coverage.get("bill");
    }

    private static String header() {
        return """
                module demo

                data Line = { price: Int }
                data Order = { lines: List<Line>, coupon: Int }
                data NoBill
                data Discounted = { total: Int }
                data Full = { total: Int }

                """;
    }

    private static String bill(String guard) {
        return header() + """
                behavior bill : (order: Order) -> NoBill | Discounted | Full
                let bill (order) =
                    if %s then NoBill
                    else if order.coupon >= 10 then Discounted { total = 1 }
                    else Full { total = 1 }
                """.formatted(guard);
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
