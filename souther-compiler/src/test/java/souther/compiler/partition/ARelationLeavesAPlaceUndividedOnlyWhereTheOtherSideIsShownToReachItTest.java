package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation between two values is said to leave a place undivided only where the other side is
 * shown to stand at every value the relation needs it at, beside every value the place may hold.
 *
 * <p>Each model below is one relation, and what is asked is the word the report gives each place
 * it relates. Three things are shown apart and none of them stands in for another: that the other
 * side takes every value of a run (an unrestricted value, a value whose rules are ends on it and
 * nothing else, or a number taken of an unrestricted value whose operation declares every number it
 * could answer is one some value answers), that its run is every value
 * between the ends and not only where the values lie, and that nothing on the way to the relation
 * ties it to another place.
 */
class ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest {

    private static final String RELATES = "relates";

    private static final String NOT_SHOWN = "not shown";

    private static final String OVER_A_RUN = "over a run";

    /** Each model measured once for the class: a test asks the words and the classes of one
     *  model, and only reads it. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    /**
     * The behavior {@code m} taking {@code inputs} and answering {@code body}, read for the lines
     * its rules draw and no row composed at them: what is asked here is the word a place is left
     * with and the classes it is parted into, which no composed row moves.
     */
    private static Compilation measured(String inputs, String declarations, String body) {
        return measured(inputs, declarations, "Bool", body);
    }

    /** The same, for a behavior answering {@code answers}. */
    private static Compilation measured(String inputs, String declarations, String answers,
                                        String body) {
        return MEASURED.computeIfAbsent("""
                module w1
                %s
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(declarations, inputs, answers,
                        inputs.replaceAll(": [A-Za-z<>]+", ""), body),
                source -> {
                    Compilation compilation = Compilation.ofSource(source, "Main");
                    compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
                    compilation.answerEverything();
                    return compilation;
                });
    }

    /**
     * The classes the axis at {@code path} is divided into, where a place the relation does not
     * leave undivided is parted at the values that settle it whatever the rest hold — or none
     * where no axis is there.
     */
    private static List<String> classesAt(String inputs, String declarations, String body,
                                          String path) {
        return classesAt(inputs, declarations, "Bool", body, path);
    }

    /** The same, of a behavior answering {@code answers}. */
    private static List<String> classesAt(String inputs, String declarations, String answers,
                                          String body, String path) {
        Compilation compilation = measured(inputs, declarations, answers, body);
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("w1")).value().get("m");
        return evidence.axes().stream().filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream()).toList();
    }

    /**
     * The word each place is left with by the comparison at {@code at}, by its name. A place the
     * comparison divides — at the values that settle it whatever the rest hold — is left none.
     */
    private static Map<String, String> left(String inputs, String declarations, String body,
                                            String at) {
        return left(inputs, declarations, "Bool", body, at);
    }

    /** The same, of a behavior answering {@code answers}. */
    private static Map<String, String> left(String inputs, String declarations, String answers,
                                            String body, String at) {
        Compilation compilation = measured(inputs, declarations, answers, body);
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, String> out = new LinkedHashMap<>();
        for (String line : report.lines().map(String::strip).toList()) {
            if (!line.contains("comparison@" + at + " ") || !line.contains("about `")) {
                continue;
            }
            if (!line.startsWith("· no line") && !line.startsWith("· not read")) {
                continue;
            }
            String place = line.substring(line.lastIndexOf("about `") + 7, line.length() - 1);
            out.put(place, line.contains("rather than dividing the values here") ? RELATES
                    : line.contains("not shown to reach every value here") ? NOT_SHOWN
                    : line.contains("come to rather than about any one of them") ? OVER_A_RUN
                    : line);
        }
        return out;
    }

    /** An amount at nought or more is never a number below nought, so those numbers settle the
     *  comparison and are a class of their own; from nought on, the amount reaches each. */
    @Test
    void aValueHeldToARunReachesWhatLiesInItAndNoMore() {
        String amount = "data Amount = Int invariant value >= 0";
        assertEquals(Map.of("a", RELATES),
                left("a: Amount, n: Int", amount, "n == a.value", "4:18"));
        assertEquals(List.of("n/x <= -1", "n/-1 < x"),
                classesAt("a: Amount, n: Int", amount, "n == a.value", "n"));
    }

    /**
     * Two amounts held at nought or more, the one at or above the other. Every gross has a
     * deduction at it and one above it, so the comparison leaves the gross undivided; a deduction
     * of nought has no gross below it, and settles the comparison whatever the gross is. Written
     * the other way round, it is the same comparison.
     */
    @Test
    void anAmountHeldAtNoughtOrMoreReachesEveryOtherAmountFromItsEndOn() {
        String yen = "data Yen = Int invariant value >= 0";
        assertEquals(Map.of("g", RELATES),
                left("g: Yen, d: Yen", yen, "g.value >= d.value", "4:24"));
        assertEquals(Map.of("g", RELATES),
                left("g: Yen, d: Yen", yen, "d.value <= g.value", "4:24"));
        assertEquals(List.of("d/0 <= x <= 0", "d/0 < x"),
                classesAt("g: Yen, d: Yen", yen, "g.value >= d.value", "d"));
    }

    private static final String CODED = """
            data Yen = Int invariant value >= 0
            data Code = String invariant String.matches("[a-z]{3}", value)""";

    /**
     * A rule the bounds cannot state, about a field nothing relates to the amount, leaves the
     * amount every value its own rules leave it: a code it refuses is replaced by one it does not,
     * and the amount stays where it was. So whether the code is the field's own type, written on
     * the record, or the same type at two fields, the amount reaches every gross from nought on —
     * and a deduction of nought settles the comparison, as beside a gross alone.
     */
    @Test
    void aRuleTheBoundsCannotStateLeavesAnAmountItNamesNothingBesideAlone() {
        for (String record : List.of("data Rec = { c: Code, d: Yen }",
                "data Rec = { c: String, d: Yen } invariant String.matches(\"[a-z]{3}\", c)",
                "data Rec = { c: Code, k: Code, d: Yen }")) {
            assertEquals(Map.of("g", RELATES),
                    leftAt("g: Yen, r: Rec", CODED + "\n" + record, "g.value >= r.d.value", 24),
                    record);
        }
    }

    /**
     * A rule the bounds cannot state that names the amount as well can refuse a value of it, so
     * the amount reaches nothing it is not shown to: here the code is free only where the amount
     * is thirty or more.
     */
    @Test
    void aRuleTheBoundsCannotStateThatAlsoNamesTheAmountKeepsItBack() {
        assertEquals(Map.of("g", NOT_SHOWN),
                leftAt("g: Yen, r: Rec", CODED + "\ndata Rec = { c: String, d: Yen } invariant"
                                + " String.matches(\"[a-z]{3}\", c) || d.value >= 30",
                        "g.value >= r.d.value", 24));
    }

    /**
     * Two amounts held equal take the same values, however much of the rules beside one of them
     * was read: a rule of the record over another of its fields leaves the amount's ends not shown
     * to be all the rules say, and the amount still every value the other amount is.
     */
    @Test
    void twoAmountsTakeTheSameValuesHoweverMuchOfTheRulesBesideOneWasRead() {
        assertEquals(Map.of("e", RELATES, "r.c", RELATES),
                leftAt("e: Yen, r: Rec", "data Yen = Int invariant value >= 0"
                                + "\ndata Rec = { c: Yen, n: Int } invariant n * n >= 4",
                        "e.value == r.c.value", 24));
    }

    /** Held to nought through ten, the greatest gross has no deduction above it, as the least
     *  deduction has no gross below it. */
    @Test
    void anAmountHeldBetweenTwoEndsIsDividedAtTheEndNothingReachesPast() {
        String yen = "data Yen = Int invariant value >= 0 && value <= 10";
        assertEquals(Map.of(), left("g: Yen, d: Yen", yen, "g.value >= d.value", "4:24"));
        assertEquals(List.of("g/0 <= x < 10", "g/10 <= x <= 10"),
                classesAt("g: Yen, d: Yen", yen, "g.value >= d.value", "g"));
        assertEquals(List.of("d/0 <= x <= 0", "d/0 < x <= 10"),
                classesAt("g: Yen, d: Yen", yen, "g.value >= d.value", "d"));
    }

    /**
     * Ends that are not all the rules say leave the value no run shown: a value taken out of the
     * middle, values held to a class of whole numbers, a rule no reading of ends took in — under
     * which no deduction is nought, so a gross of nought is below every one — and an end on another
     * number of the position: a string of one character has no string above the greatest of them,
     * however far up from {@code "b"} its order runs.
     *
     * <p>The last is kept back twice. The region shows no run of a string's own order whole, ends
     * or none, so a string held at {@code "b"} or above is not shown to reach anything either; the
     * end on its length is what keeps it back where the region shows one.
     */
    @Test
    void endsThatAreNotAllTheRulesSayLeaveTheValueReachingNothingShown() {
        Map<String, Map<String, String>> eachRule = new LinkedHashMap<>();
        for (String rule : List.of("value >= 0 && value /= 5",
                "value >= 0 && Int.floorMod(value, 2) == 0",
                "value >= 0 && value * value >= 4")) {
            eachRule.put(rule, leftAt("g: Amount, d: Yen", "data Amount = Int invariant value >= 0"
                    + "\ndata Yen = Int invariant " + rule, "g.value >= d.value", 24));
        }
        // Where what the gross reaches is shown, a deduction of nought settles the comparison
        // whatever the gross is, and is a class of its own.
        assertEquals(Map.of("value >= 0 && value /= 5", Map.of("g", NOT_SHOWN, "d", NOT_SHOWN),
                "value >= 0 && Int.floorMod(value, 2) == 0", Map.of("g", NOT_SHOWN),
                "value >= 0 && value * value >= 4", Map.of("g", NOT_SHOWN)), eachRule);
        for (String rule : List.of("value >= \"b\" && String.length(value) <= 1",
                "value >= \"b\"")) {
            assertEquals(Map.of("g", NOT_SHOWN, "d", NOT_SHOWN),
                    left("g: Letter, d: Letter", "data Letter = String invariant " + rule,
                            "g.value >= d.value", "4:24"), rule);
        }
    }

    /** Held at nought or more, a number reaches every length, as a length reaches every number
     *  it is held to. */
    @Test
    void aLengthReachesEveryNumberAtOrAboveNoughtAndNothingBelow() {
        assertEquals(Map.of("String.length(s)", RELATES),
                left("n: Int, s: String", "data Unused = Int", "n == String.length(s)", "4:18"));
        assertEquals(List.of("n/x <= -1", "n/-1 < x"), classesAt("n: Int, s: String",
                "data Unused = Int", "n == String.length(s)", "n"));
        assertEquals(Map.of("n", RELATES, "String.length(s)", RELATES),
                left("n: N, s: String", "data N = Int invariant value >= 0",
                        "n.value == String.length(s)", "4:24"));
    }

    private static final String NAT = "data Nat = Int invariant value >= 0";

    private static final String TOTAL = "List.sum(List.map(n -> n.value, ns))";

    /**
     * A total of numbers held at nought or more is a term of the relation beside it, as the count
     * of them is. Every value of the total has a gross on either side, so the total is left
     * undivided. A list of one element totals that element, so the total takes every value the
     * element does: never below nought, and every value from there. So a gross below nought fails
     * whatever the total is, and every other gross has a total on either side. Doubled, the total
     * is still never below nought and never odd: what each element is made into is not what it
     * takes, and nothing is shown of the gross.
     */
    @Test
    void aTotalOverARunIsATermOfTheRelationAsTheCountIs() {
        assertEquals(Map.of("List.length(ns)", RELATES, "gross", NOT_SHOWN),
                leftAt("gross: Int, ns: List<Nat>", NAT, "gross >= List.length(ns)", 27));
        assertEquals(Map.of("List.sum(ns[*])", RELATES),
                leftAt("gross: Int, ns: List<Nat>", NAT, "gross >= " + TOTAL, 27));
        assertEquals(List.of("gross/x <= -1", "gross/-1 < x"), classesAt("gross: Int, ns: List<Nat>",
                NAT, "gross >= " + TOTAL, "gross"));
        assertEquals(Map.of("List.sum({2·the element itself + 0 | ns[*]})", RELATES,
                        "gross", NOT_SHOWN),
                leftAt("gross: Int, ns: List<Nat>", NAT,
                        "gross >= List.sum(List.map(n -> 2 * n.value, ns))", 27));
    }

    /**
     * A total of one element is that element, and of none is nought. Elements from one up total
     * every value from one, and nought where the list may be empty, so a gross below nought fails
     * whatever the total. Held to one element or more, the total takes every value from one and
     * not nought; where it may lie is still read from nought, so a gross of nought is neither
     * shown to fail nor shown to be left either way, and nothing is shown of the gross. Elements
     * that are even are not every value from nought, and the total is shown to take nothing, so
     * nothing is shown of the gross; the total is left either way by a gross taking every value,
     * wherever it may lie, as the totals above are.
     */
    @Test
    void aTotalTakesWhatOneElementTakesAndNoughtWhereTheListMayBeEmpty() {
        String positive = "data Pos = Int invariant value >= 1\n";
        assertEquals(List.of("gross/x <= -1", "gross/-1 < x"), classesAt(
                "gross: Int, ns: List<Pos>", positive, "gross >= " + TOTAL, "gross"));
        assertEquals(NOT_SHOWN, leftAt("gross: Int, ns: Ps",
                positive + "data Ps = List<Pos> invariant List.length(value) >= 1",
                "gross >= List.sum(List.map(n -> n.value, ns.value))", 27).get("gross"));
        assertEquals(Map.of("List.sum(ns[*])", RELATES, "gross", NOT_SHOWN),
                leftAt("gross: Int, ns: List<Even>",
                        "data Even = Int invariant Int.floorMod(value, 2) == 0",
                        "gross >= " + TOTAL, 27));
    }

    private static final String ITS_TOTAL = "List.sum(List.map(n -> n.value, ns.value))";

    /**
     * Reached along a way holding the list to two elements or more, no list there totals one
     * element, and which totals two reach is not asked. Along a way holding every element to five
     * or less, an element is not every value the declarations leave it. Held by a rule of the list
     * to a total of ten or less, an element is not every value it takes alone. Each time the total
     * is shown to take nothing, and nothing is shown of the gross — though under the third a gross
     * of eleven or more holds whatever a total is.
     */
    @Test
    void aTotalIsWhatOneElementTakesOnlyWhereOneElementStandsAlone() {
        String inputs = "gross: Int, ns: List<Nat>";
        String body = "if List.length(ns) >= 2 then gross >= " + TOTAL + " else false";
        assertEquals(NOT_SHOWN, left(inputs, NAT, body,
                atThe(">= List.sum", NAT, inputs, body)).get("gross"));
        String small = "if List.all(n -> n.value <= 5, ns) then gross >= " + TOTAL + " else false";
        assertEquals(NOT_SHOWN, left(inputs, NAT, small,
                atThe(">= List.sum", NAT, inputs, small)).get("gross"));
        assertEquals(NOT_SHOWN, leftAt("gross: Int, ns: Ns",
                NAT + "\ndata Ns = List<Nat> invariant List.sum(List.map(n -> n.value, value)) <= 10",
                "gross >= " + ITS_TOTAL, 27).get("gross"));
    }

    /** Where {@code operator} stands in the body of a behavior over {@code inputs}, below
     *  {@code declarations}. */
    private static String atThe(String operator, String declarations, String inputs,
                                String body) {
        String head = "let m (" + inputs.replaceAll(": [A-Za-z<>]+", "") + ") = ";
        return (declarations.lines().count() + 3) + ":" + (head.length() + body.indexOf(operator)
                + 1);
    }

    private static final String CREDITED =
            "Decimal.compare(Decimal.add(net.value, tax.value),"
                    + " Decimal.subtract(gross.value, List.sum(List.map(n -> n.value, ns)))) <= 0";

    /**
     * What is asked against what is left of a gross once the notes so far are taken off it. At a
     * gross of nought it holds only with the ask, the tax and the total of the notes all at
     * nought in one row, and each of them is apart from the others and takes nought, a list of
     * none totalling nought. Held above nought, none of them takes nought, and nothing is shown of
     * the gross: that a value as near nought as asked of is taken shows no row at nought.
     */
    @Test
    void aTotalHeldStillBesideOtherTermsAtNoughtLeavesTheRestEitherWay() {
        String inputs = "gross: Amount, ns: List<Amount>, net: Amount, tax: Amount";
        String closed = "data Amount = Decimal invariant value >= 0.0m";
        String at = atThe("<=", closed, inputs, CREDITED);
        assertEquals(Map.of("List.sum(ns[*])", RELATES, "gross", RELATES, "net", RELATES,
                        "tax", RELATES), left(inputs, closed, CREDITED, at));
        assertEquals(NOT_SHOWN,
                left(inputs, "data Amount = Decimal invariant value > 0.0m", CREDITED, at)
                        .get("gross"));
    }

    /** The same, with the ask and its tax held together to one or more: no row holds both at
     *  nought, and holding either still holds the other too. */
    @Test
    void termsNoRowHoldsAtNoughtTogetherAreNotHeldThere() {
        String body = CREDITED.replace("net.value, tax.value", "ask.net.value, ask.tax.value");
        String inputs = "gross: Amount, ns: List<Amount>, ask: Ask";
        String declarations = "data Amount = Decimal invariant value >= 0.0m\n"
                + "data Ask = { net: Amount, tax: Amount }"
                + " invariant Decimal.add(net.value, tax.value) >= 1.0m";
        assertEquals(NOT_SHOWN, left(inputs, declarations, body,
                atThe("<=", declarations, inputs, body)).get("gross"));
    }

    private static final String LABELLED = """
            data Issue = { id: String, labels: Set<String> }
            let counts (issues: List<Issue>): Map<String, Int> =
                List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                    List.flatMap(i -> Set.toList(i.labels), issues))""";

    private static final String BUSY =
            "Map.size(Map.filterEntries((_, count) -> count >= atLeast, counts(issues))) == 0";

    /**
     * How many issues carry a label, held at a bar: a list of that one issue over again, each
     * carrying the label alone, carries it as many times as the list holds issues, so the count
     * takes every value from one. A bar of one or less is met by every label, and above that each
     * bar has counts on either side: one line, at one.
     *
     * <p>Kept apart by their ids, issues alike are no list, and as many issues as a count needs
     * would need as many ids. Each held to two labels or more — by a rule of the issue, or along a
     * way — no issue carries the label alone. Each time the count is shown to take nothing, and
     * no line is drawn on the bar.
     */
    @Test
    void howOftenAValueOccursTakesEveryCountItsListMayHoldElementsTo() {
        assertEquals(List.of("atLeast/x <= 1", "atLeast/1 < x"),
                classesAt("issues: List<Issue>, atLeast: Int", LABELLED, BUSY, "atLeast"));
        assertEquals(List.of(), classesAt("board: Board, atLeast: Int", LABELLED + """

                data Board = { issues: List<Issue> }
                    invariant List.allDistinctBy(i -> i.id, issues)""",
                BUSY.replace("counts(issues)", "counts(board.issues)"), "atLeast"));
        assertEquals(List.of(), classesAt("issues: List<Issue>, atLeast: Int",
                LABELLED.replace("labels: Set<String> }",
                        "labels: Set<String> }\n    invariant Set.size(labels) >= 2"),
                BUSY, "atLeast"));
        assertEquals(List.of(), classesAt("issues: List<Issue>, atLeast: Int", LABELLED,
                "if List.all(i -> Set.size(i.labels) >= 2, issues) then " + BUSY + " else false",
                "atLeast"));
    }

    /**
     * The count itself: at the greatest count no bar is greater, so the comparison holds there
     * whatever the bar is, and below it there are bars either side of every count. That line is
     * where the bar's type stops and no class of the model's, so the count is read and no line is
     * drawn on it; the bar is parted by its line at one. A rule putting the bar at the greatest
     * {@code Int} at most draws the same line as the model's, and a count has no position to draw
     * it at.
     */
    @Test
    void aCountSettledOnlyWhereTheOtherTypeStopsIsRead() {
        String inputs = "issues: List<Issue>, atLeast: Int";
        assertEquals(Map.of("occurrences(issues[*].labels[*])", RELATES),
                left(inputs, LABELLED, BUSY, atThe(">=", LABELLED, inputs, BUSY)));

        String barred = "issues: List<Issue>, atLeast: Bar";
        String ruled = LABELLED + "\ndata Bar = Int invariant value <= 9223372036854775807";
        String body = BUSY.replace("atLeast", "atLeast.value");
        assertEquals(Map.of("occurrences(issues[*].labels[*])", NOT_SHOWN),
                left(barred, ruled, body, atThe(">=", ruled, barred, body)));
    }

    /**
     * {@code x <= Int.min(s, t)}: at the least {@code x} it holds whatever the two are, only because
     * the least of two {@code Int}s is no less than the least {@code Int}; and the least of them
     * holds it whatever {@code x} is only at the greatest {@code Int}, where both stop. Both are
     * where the type stops, and every place is read with no line drawn on it.
     */
    @Test
    void aValueSettledOnlyWhereTheAnswerStopsWithItsTypeIsRead() {
        assertEquals(Map.of("x", RELATES, "s", RELATES, "t", RELATES),
                left("x: Int, s: Int, t: Int", "data Unused = Int", "x <= Int.min(s, t)",
                        "4:21"));
    }

    /**
     * A way keeping {@code b} from nought where it already keeps it above nought, as a quotient's
     * way keeps its divisor, leaves {@code b} every value from one: the line on {@code a} it
     * draws is the one {@code b > 0} alone draws. Kept from five instead, {@code b} runs with a
     * gap, and every value of {@code a} between the settling ones is not shown reached.
     */
    @Test
    void aValueHeldApartOutsideTheRunTakesNothingFromIt() {
        Map<String, String> above = keptAbove("");
        assertFalse(above.containsKey("a"), () -> "a is parted at what settles it: " + above);
        assertEquals(above, keptAbove(" && b /= 0"));
        assertEquals(NOT_SHOWN, keptAbove(" && b /= 5").get("a"));
    }

    /** What {@code a >= 100 * b} leaves its places along a way keeping {@code b} above nought and
     *  saying {@code also} of it besides. */
    private static Map<String, String> keptAbove(String also) {
        String inputs = "a: Int, b: Int";
        String body = "if b > 0" + also + " then a >= 100 * b else false";
        return left(inputs, "data Unused = Int", body,
                atThe(">=", "data Unused = Int", inputs, body));
    }

    /** Beside a total, two positions are each a term of the relation and not of the run. The
     *  adjustment held at nought, the gross stands at every value the total takes. */
    @Test
    void positionsBesideATotalAreAskedOfTheRelation() {
        assertEquals(Map.of("List.sum(ns[*])", RELATES, "adjustment", NOT_SHOWN,
                        "gross", NOT_SHOWN),
                leftAt("gross: Int, adjustment: Int, ns: List<Nat>", NAT,
                        "gross + adjustment >= " + TOTAL, 52));
    }

    /** A count of the elements meeting a statement, held against a position, divides that
     *  position as far as the relation shows, and says nothing of the run of it. */
    @Test
    void aPositionBesideACountOfWhatMeetsAStatementIsAskedOfTheRelation() {
        assertEquals(Map.of("gross", NOT_SHOWN, "ns[*]", NOT_SHOWN),
                leftAt("gross: Int, ns: List<Nat>", NAT,
                        "gross >= List.length(List.filter(n -> n.value > 3, ns))", 27));
    }

    private static final String UNUSED = "data Unused = Int";

    /** Each element of {@code xs} answered one where {@code test} holds of where it stands. */
    private static final String STANDING = "List.mapIndexed((i, x) -> if %s then 1 else 0, xs)";

    /**
     * Where an element stands in a walk over a list lies from nought to one below how many the
     * list holds, and a row of so many hands the walk every one of those. So at a list of one the
     * one element is the last, and every longer list has a last element and one before it: the
     * comparison is parted on the length at one, and where the element stands is not asked apart
     * from it. Moved by two, the line moves with it; held two below, the list of one is the one
     * whose element is never there.
     */
    @Test
    void whereAnElementStandsPartsHowManyItsListHoldsWhereEveryPositionComesOutOneWay() {
        String inputs = "xs: List<Int>";
        for (String test : List.of("i == List.length(xs) - 1", "i + 1 >= List.length(xs)",
                "i == List.length(xs) - 2")) {
            assertEquals(List.of("List.length(xs)/0 <= x <= 1", "List.length(xs)/1 < x"),
                    classesAt(inputs, UNUSED, "List<Int>", STANDING.formatted(test),
                            "List.length(xs)"), test);
        }
        assertEquals(List.of("List.length(xs)/0 <= x <= 2", "List.length(xs)/2 < x"),
                classesAt(inputs, UNUSED, "List<Int>",
                        STANDING.formatted("List.length(xs) - i <= 2"), "List.length(xs)"));
        String body = STANDING.formatted("i == List.length(xs) - 1");
        assertEquals(Map.of(), left(inputs, UNUSED, "List<Int>", body,
                atThe("==", UNUSED, inputs, body)));
    }

    /**
     * Against another list's length, where an element of the walked list stands is no number
     * of it, and nothing is shown. Nor where the way picks out some of the elements: the walk is
     * handed every position, and the comparison is asked at those of the elements the way lets
     * through, which may leave out the last.
     */
    @Test
    void whereAnElementStandsIsReadOnlyAgainstItsOwnListAllOfWhichTheWayLeaves() {
        String inputs = "xs: List<Int>, ys: List<Int>";
        String another = STANDING.formatted("i == List.length(ys) - 1");
        assertEquals(Map.of("List.length(ys)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>",
                another, atThe("==", UNUSED, inputs, another)));
        String picked = "if List.all(x -> x > 0, xs) then "
                + STANDING.formatted("i == List.length(xs) - 1") + " else []";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left("xs: List<Int>", UNUSED,
                "List<Int>", picked, atThe("== List", UNUSED, "xs: List<Int>", picked)));
    }

    /**
     * A relation that comes out one way at every value a term may hold comes out that way in every
     * row, so it divides none of its places, as one a way decides does not: every element of a
     * list stands below its length, and two lengths of strings add up to nought or more.
     */
    @Test
    void aRelationSettledOneWayAtEveryValueDividesNothing() {
        String body = STANDING.formatted("i < List.length(xs)");
        assertEquals(Map.of("List.length(xs)", RELATES), left("xs: List<Int>", UNUSED,
                "List<Int>", body, atThe("<", UNUSED, "xs: List<Int>", body)));
        String lengths = "String.length(s) + String.length(t) >= 0";
        assertEquals(Map.of("String.length(s)", RELATES, "String.length(t)", RELATES),
                left("s: String, t: String", UNUSED, lengths,
                        atThe(">=", UNUSED, "s: String, t: String", lengths)));
    }

    /** A total held against a number, or against another total, is about what the runs come to
     *  and divides none of their values. */
    @Test
    void aTotalWithNoPositionBesideItIsAboutTheRun() {
        assertEquals(Map.of("List.sum(ns[*])", OVER_A_RUN),
                leftAt("ns: List<Nat>", NAT, TOTAL + " >= 10", 51));
        assertEquals(Map.of("List.sum(ms[*])", OVER_A_RUN, "List.sum(ns[*])", OVER_A_RUN),
                leftAt("ms: List<Nat>, ns: List<Nat>", NAT,
                        "List.sum(List.map(m -> m.value, ms)) >= " + TOTAL, 55));
    }

    /** A string held to two values takes two lengths with a gap between them. */
    @Test
    void aLengthOfAStringARuleHoldsReachesNothingShown() {
        assertEquals(Map.of("String.length(s)", RELATES, "n", NOT_SHOWN),
                left("n: Int, s: S", "data S = String invariant value == \"a\" || value == \"aaa\"",
                        "n == String.length(s.value)", "4:18"));
    }

    /** An hour is one of twenty-four, which a number running past them is not, and a number held
     *  to them is. */
    @Test
    void anHourReachesTheHoursOfADay() {
        assertEquals(Map.of("Time.hour(t)", RELATES),
                left("n: Int, t: Time", "data Unused = Int", "n == Time.hour(t)", "4:18"));
        assertEquals(List.of("n/x <= -1", "n/-1 < x < 24", "n/24 <= x"),
                classesAt("n: Int, t: Time", "data Unused = Int", "n == Time.hour(t)", "n"));
        assertEquals(Map.of("h", RELATES, "Time.hour(t)", RELATES),
                left("h: H, t: Time", "data H = Int invariant value >= 0 && value <= 23",
                        "h.value == Time.hour(t)", "4:24"));
    }

    /** The years a date can be written in stop somewhere, and a number past them is one no date
     *  is in; a year past the ones a number is held to is one no such number is; and a date held
     *  to two first days of January is in two years with one between. */
    @Test
    void aYearReachesTheYearsADateCanBeWrittenInAndNoGapARuleLeaves() {
        assertEquals(Map.of("Date.year(d)", RELATES),
                left("y: Int, d: Date", "data Unused = Int", "y == Date.year(d)", "4:18"));
        assertEquals(List.of("y/x <= -1000000000", "y/-1000000000 < x < 1000000000",
                "y/1000000000 <= x"), classesAt("y: Int, d: Date", "data Unused = Int",
                "y == Date.year(d)", "y"));
        String heldYear = "data Y = Int invariant value >= 1 && value <= 9999";
        assertEquals(Map.of("y", RELATES),
                left("y: Y, d: Date", heldYear, "y.value == Date.year(d)", "4:24"));
        assertEquals(List.of("Date.year(d)/-999999999 <= x <= 0", "Date.year(d)/0 < x < 10000",
                        "Date.year(d)/10000 <= x <= 999999999"),
                classesAt("y: Y, d: Date", heldYear, "y.value == Date.year(d)", "Date.year(d)"));
        assertEquals(Map.of("Date.year(d)", RELATES, "y", NOT_SHOWN),
                left("y: Int, d: D", "data D = Date invariant value == Date(\"2020-01-01\")"
                        + " || value == Date(\"2022-01-01\")", "y == Date.year(d.value)", "4:18"));
    }

    /**
     * A day apart, the last date has no date after it and the first none before; that is where the
     * dates stop and no line the model draws. Moved together, two dates are a day apart wherever
     * they stand, and only how far apart they are settles it. A date and a count of days are not
     * moved together: a count past the days from the first date to the last or short of those to
     * the first settles the comparison, which is where the dates stop and no line the model
     * draws, so the count is read; the days to a date past which no count runs are not shown.
     */
    @Test
    void twoValuesADayApartRelateEachOther() {
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int", "Date.daysBetween(a, b) == 1",
                        "4:39"));
        assertEquals(Map.of("a", NOT_SHOWN, "n", RELATES),
                left("a: Date, n: Int", "data Unused = Int",
                        "Date.daysBetween(Date(\"2026-01-01\"), a) <= n", "4:56"));
    }

    /**
     * The last case of an enumeration, the empty string and the last second of a day are values a
     * model holds, and a relation that comes out one way only there divides them: {@code a < b} is
     * false at the last stage whatever {@code b} is, and at the empty {@code b} whatever {@code a}
     * is. No string is the greatest, so every {@code a} has strings either side. The ends of an
     * {@code Int} are where the representation stops, and two of them relate each other; so do two
     * stages held equal, since every stage has one equal to it and one not.
     */
    @Test
    void anEndAModelHoldsIsAValueTheRelationDivides() {
        String stage = "data Stage = Prospecting | Negotiation | Won | Lost";
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Stage, b: Stage", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Stage, b: Stage", stage, "if a <= b then a < b else false", "4:33"));
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Stage, b: Stage", stage, "a == b", "4:18"));
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("a: String, b: String", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Time, b: Time", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Int, b: Int", stage, "a < b", "4:18"));
    }

    /**
     * Two enumerations each count where a case comes in their own declaration, so a stage and a
     * late stage held equal are compared as values and stand on no one order: {@code Won} is the
     * third stage and the first late one. Where one stands says nothing of where the other does,
     * and nothing is shown of either. A stage held equal to a stage is shown.
     */
    @Test
    void aCaseOfOneEnumerationHasNoPlaceOnAnothersOrder() {
        String cases = "data Prospecting\ndata Negotiation\ndata Won\ndata Lost\n"
                + "data Stage = Prospecting | Negotiation | Won | Lost\ndata Late = Won | Lost";
        assertEquals(Map.of("a", NOT_SHOWN, "w", NOT_SHOWN),
                leftAt("a: Stage, w: Late", cases, "a == w", 18));
        assertEquals(Map.of("a", RELATES, "w", RELATES),
                leftAt("a: Stage, w: Stage", cases, "a == w", 18));
    }

    /**
     * A record holding a stage and a late stage as one value is read: the block the rule holds as
     * one stands on no one order, so what it admits is not worked out on either, and each field
     * keeps the classes its own enumeration gives it.
     */
    @Test
    void aRuleHoldingCasesOfTwoEnumerationsAsOneValueIsRead() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                data Prospecting
                data Negotiation
                data Won
                data Lost
                data Stage = Prospecting | Negotiation | Won | Lost
                data Late = Won | Lost
                data Pair = { a: Stage, w: Late }
                    invariant a == w
                behavior m : (p: Pair) -> Bool
                let m (p) = true
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("p.a holds 4 classes"), report);
        assertTrue(report.contains("p.w holds 2 classes"), report);
    }

    /** {@link #left} at {@code column} of the line the body is written on, below every line of
     *  {@code declarations}. */
    private static Map<String, String> leftAt(String inputs, String declarations, String body,
                                              int column) {
        return left(inputs, declarations, body,
                (declarations.lines().count() + 3) + ":" + column);
    }

    /**
     * No two dates are ten trillion days apart, so the comparison holds for none of them; and
     * four hundred billion days apart are only dates nearer the two ends than the middle is.
     * Three hundred billion days leave the middle date partners either side.
     */
    @Test
    void aDifferenceHasToBeOneTheMiddleOfTheTypeReachesBothWays() {
        for (String apart : List.of("10000000000000", "400000000000")) {
            assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                    left("a: Date, b: Date", "data Unused = Int",
                            "Date.daysBetween(a, b) > " + apart, "4:39"), apart);
        }
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int",
                        "Date.daysBetween(a, b) > 300000000000", "4:39"));
    }

    /**
     * A rule between two stages of a record is measured to the end: a row for it is composed by
     * moving one stage by how far apart the rule leaves the two, and a move past the last stage is
     * a run reaching as far as the stages do, or no run, never a place with nothing at it.
     */
    @Test
    void aRuleBetweenTwoStagesIsMeasuredToTheEnd() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                data Stage = Prospecting | Negotiation | Won | Lost
                data Deal = { from: Stage, to: Stage }
                    invariant from < to
                behavior m : (d: Deal) -> Bool
                let m (d) = true
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        for (String place : List.of("d.from", "d.to")) {
            assertTrue(report.lines().anyMatch(line -> line.contains("invariant Deal #1")
                    && line.contains("not shown to reach every value here")
                    && line.endsWith("about `" + place + "`")), report);
        }
    }

    /**
     * The model the question was asked with: how many days are left before a deadline, held at
     * nought or more and then at fourteen or less. Both comparisons are about how far apart the
     * two dates are, so neither date is divided by either and what is measured is the two borders
     * on the difference.
     */
    @Test
    void howManyDaysAreLeftBeforeADeadlineDividesNeitherDate() {
        Compilation compilation = Compilation.ofSource("""
                module check

                data TooLate = { days: Int }
                data TooEarly = { days: Int }
                data Fine = { days: Int }

                behavior check : (deadline: Date, today: Date) -> Fine | TooLate | TooEarly

                let check (deadline, today) = {
                    let left = Date.daysBetween(today, deadline)
                    guard left >= 0 else TooLate { days = left }
                    guard left <= 14 else TooEarly { days = left }
                    Fine { days = left }
                }

                example check
                    | (Date("2026-08-01"), Date("2026-07-25")) -> Fine { days = 7 }
                    | (Date("2026-07-20"), Date("2026-07-25")) -> TooLate { days = -5 }
                    | (Date("2026-09-01"), Date("2026-07-25")) -> TooEarly { days = 38 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not shown to reach every value here"), report);
        for (String place : List.of("deadline", "today")) {
            assertEquals(2, report.lines().filter(line -> line.contains("· no line: comparison@")
                    && line.contains("rather than dividing the values here")
                    && line.endsWith("about `" + place + "`")).count(), report);
        }
    }

    /**
     * A guard on how far apart two dates are leaves them moved together: at nought or more, the
     * difference is at fourteen or less and past it. A guard on one of them alone keeps it from
     * values of its own, and a guard holding the difference to ten or less leaves it never past
     * fourteen.
     */
    @Test
    void aGuardOnHowFarApartTwoValuesAreLeavesThemMovedTogether() {
        String apart = "Date.daysBetween(a, b)";
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int",
                        "if " + apart + " >= 0 then " + apart + " <= 14 else false", "4:75"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Date, b: Date", "data Unused = Int",
                        "if a >= Date(\"2020-01-01\") then " + apart + " <= 14 else false",
                        "4:71"));
        Map<String, String> under = left("a: Date, b: Date", "data Unused = Int",
                "if " + apart + " <= 10 then " + apart + " <= 14 else false", "4:76");
        assertEquals(Set.of("a", "b"), under.keySet());
        assertFalse(under.containsValue(RELATES), under.toString());
    }

    @Test
    void twoValuesOfOneDeclaredTypeReachEachOther() {
        assertEquals(Map.of("c", RELATES, "e", RELATES),
                left("c: Code, e: Code",
                        "data Code = String invariant String.matches(\"[A-Z]{2}\", value)",
                        "e.value == c.value", "4:24"));
    }

    /**
     * A guard on one place narrows where it runs and ties it to nothing: the other place still
     * reaches it. What it reaches is the narrowed run, which a value of the other place below it
     * is not on.
     */
    @Test
    void aGuardOnOnePlaceNarrowsItAndTiesItToNothing() {
        assertEquals(Map.of("a", RELATES),
                left("a: Int, b: Int", "data Unused = Int", "if a > 0 then a < b else false",
                        "4:32"));
        assertEquals(List.of("b/x <= 1", "b/1 < x"), classesAt("a: Int, b: Int",
                "data Unused = Int", "if a > 0 then a < b else false", "b"));
    }

    /**
     * What a weighed term has to stand at is the rest over its weight: under {@code 2h + y < 0}
     * with {@code y} at most minus five, {@code y} at minus five needs an {@code h} below two and a
     * half, which an {@code h} from four on never is.
     */
    @Test
    void aWeighedTermHasToStandAtTheRestOverItsWeight() {
        String declarations = "data Y = Int invariant value >= -10 && value <= -5";
        String fromFour = "if h >= 4 && h <= 11 then 2 * h + y.value < 0 else false";
        assertEquals(Map.of(), left("h: Int, y: Y", declarations, fromFour, "4:58"));
        assertEquals(List.of("h/x < 4", "h/4 <= x < 5", "h/5 <= x <= 11", "h/11 < x"),
                classesAt("h: Int, y: Y", declarations, fromFour, "h"));
        assertEquals(List.of("y/-10 <= x < -8", "y/-8 <= x <= -5"),
                classesAt("h: Int, y: Y", declarations, fromFour, "y"));
        String fromNought = "if h >= 0 && h <= 20 then 2 * h + y.value < 0 else false";
        assertEquals(Map.of("y", RELATES), left("h: Int, y: Y", declarations, fromNought, "4:58"));
        assertEquals(List.of("h/x < 0", "h/0 <= x <= 2", "h/2 < x < 5", "h/5 <= x <= 20",
                "h/20 < x"), classesAt("h: Int, y: Y", declarations, fromNought, "h"));
    }

    /**
     * A month against a number a guard holds to the months: December is at or above every such
     * number, and a number of one has every month at or above it, so each is a class of its own.
     * Held to nought through thirteen, the number reaches past every month, which leaves the month
     * undivided, and nought, one and thirteen settle the comparison whatever the month is.
     */
    @Test
    void aMonthIsDividedAtTheEndOfTheNumbersAGuardHoldsTheOtherSideTo() {
        String months = "if k >= 1 && k <= 12 then Date.month(d) >= k else false";
        assertEquals(Map.of(), left("d: Date, k: Int", "data Unused = Int", months, "4:56"));
        assertEquals(List.of("Date.month(d)/1 <= x < 12", "Date.month(d)/12 <= x <= 12"),
                classesAt("d: Date, k: Int", "data Unused = Int", months, "Date.month(d)"));
        assertEquals(List.of("k/x < 1", "k/1 <= x <= 1", "k/1 < x <= 12", "k/12 < x"),
                classesAt("d: Date, k: Int", "data Unused = Int", months, "k"));
        String wider = "if k >= 0 && k <= 13 then Date.month(d) >= k else false";
        assertEquals(Map.of("Date.month(d)", RELATES),
                left("d: Date, k: Int", "data Unused = Int", wider, "4:56"));
        assertEquals(List.of("k/x < 0", "k/0 <= x <= 1", "k/1 < x < 13", "k/13 <= x <= 13",
                "k/13 < x"), classesAt("d: Date, k: Int", "data Unused = Int", wider, "k"));
    }

    /**
     * A way that keeps the rows off the relation's own line leaves each side the rows either side
     * of it. Past {@code p == g}, a payment of nought is below every gross a row can hold, since a
     * gross of nought is the line; and a gross of nought is below no payment. So each is parted at
     * nought, and every other value of either has a row on each side.
     */
    @Test
    void aWayKeepingTheRowsOffTheLineLeavesEachSideTheRowsEitherSideOfIt() {
        String amount = "data Amount = Decimal invariant value >= 0.0m";
        String body = "if p.value == g.value then false else p.value < g.value";
        assertEquals(Map.of(), left("p: Amount, g: Amount", amount, body, "4:62"),
                "neither is left unshown: each is parted at the value that settles it");
        assertEquals(List.of("p/0 <= x <= 0", "p/0 < x"),
                classesAt("p: Amount, g: Amount", amount, body, "p"));
        assertEquals(List.of("g/0 <= x <= 0", "g/0 < x"),
                classesAt("p: Amount, g: Amount", amount, body, "g"));
    }

    /** And a way stating anything beside that is a way the line is not all it takes away, which
     *  ties the sides as it did. */
    @Test
    void aWayStatingMoreThanThatTheRowsAreOffTheLineTiesTheSides() {
        assertEquals(Map.of("p", NOT_SHOWN, "g", NOT_SHOWN),
                left("p: Amount, g: Amount", "data Amount = Decimal invariant value >= 0.0m",
                        "if p.value == g.value || p.value > 100.0m then false"
                                + " else p.value < g.value", "4:82"));
    }

    /**
     * A way that chooses is proved along each choice: under {@code x == 0 || x == 1} a row holds
     * {@code x} at nought or at one, so a {@code y} of two makes {@code x == y} false wherever the
     * row arrives, though the two choices together leave {@code x} anything a whole number can be
     * between them.
     */
    @Test
    void aWayThatChoosesIsProvedAlongEachChoice() {
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if x == 0 || x == 1 then x == y else false", "4:43"));
    }

    /**
     * Two choices on places apart are proved along every way of taking them together, and not
     * along each alternative once: {@code y} reaches every {@code x} along three of the four.
     * Along the last — {@code x} from twenty, {@code y} up to twenty-five — the values of
     * {@code x} past twenty-five come out false whatever {@code y} is, and those below come out
     * either way, so {@code x} is parted there and not left undivided. With {@code y} up to ten
     * instead, the last comes out false in every row along it, and divides no value of {@code x}
     * any more than a way deciding it does.
     */
    @Test
    void choicesOnPlacesApartAreProvedAlongEveryWayOfTakingThemTogether() {
        String body = "if (x >= 0 && x <= 10 || x >= 20 && x <= 30)"
                + " && (y >= 0 && y <= 30 || y >= 0 && y <= 25)"
                + " then x == y else false";
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int", body, "4:112"));
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        body.replace("y <= 25", "y <= 10"), "4:112"));
    }

    /**
     * A run whose end the rules put at a third is handed over from a hair below it, which no
     * value of {@code x} is, so it is not taken as a run {@code x} fills — here, where the values
     * asked of it are all above a third, as anywhere. An end at a half is written as it is.
     *
     * <p>The places named are the ones left unshown or related: {@code x} is neither, being parted
     * by lines at the ends of the run {@code y} takes.
     */
    @Test
    void anEndRoundedPastTheRulesIsNotTakenAsOneTheTermReaches() {
        String declarations = "data Y = Decimal invariant value >= 0.6m && value <= 0.9m";
        assertEquals(Map.of("y", NOT_SHOWN),
                left("x: Decimal, y: Y", declarations,
                        "if x + x + x >= 1m && x <= 1m then x == y.value else false", "4:53"));
        assertEquals(Map.of("y", RELATES),
                left("x: Decimal, y: Y", declarations,
                        "if x + x >= 1m && x <= 1m then x == y.value else false", "4:49"));
    }

    /** An end a run of dense values does not take is no value asked of where every value asked of
     *  is inside it: between nought and one, {@code x} is at every value from a fifth to a half. */
    @Test
    void anEndADenseRunDoesNotTakeIsNoGapInsideIt() {
        assertEquals(Map.of("y", RELATES),
                left("x: Decimal, y: Y", "data Y = Decimal invariant value >= 0.2m && value <= 0.5m",
                        "if x > 0m && x < 1m then x == y.value else false", "4:43"));
    }

    /** A way over the sum of two places ties them, however each runs on its own: moved together,
     *  the two are no longer as far from nought as they were. */
    @Test
    void aWayOverTwoPlacesTiesThem() {
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if x + y <= 1 then x == y else false", "4:37"));
    }

    /**
     * A way relating the value compared to a place it leaves free narrows nothing of it: past
     * {@code a >= b}, {@code b} can be anything, so {@code a} still runs over every value. It is
     * tied to {@code b} and to nothing else, so {@code c} and {@code a} each reach every value the
     * other holds.
     */
    @Test
    void aWayRelatingTheValueComparedToAFreePlaceLeavesItEveryValue() {
        assertEquals(Map.of("a", RELATES, "c", RELATES),
                left("a: Int, b: Int, c: Int", "data Unused = Int",
                        "if a >= b then a < c else false", "4:36"));
    }

    /**
     * A way relating the value compared to a place held at nought or more leaves it the run that
     * gives: past {@code b >= 0 && a >= b}, no {@code a} is below nought, so a {@code c} at nought
     * or below is above no {@code a} and settles the comparison, which divides {@code c} there.
     */
    @Test
    void aWayRelatingTheValueComparedToABoundedPlaceLeavesItTheRunThatBoundGives() {
        String body = "if b >= 0 && a >= b then a < c else false";
        assertEquals(Map.of("a", RELATES),
                left("a: Int, b: Int, c: Int", "data Unused = Int", body, "4:46"));
        assertEquals(List.of("c/x <= 0", "c/0 < x"),
                classesAt("a: Int, b: Int, c: Int", "data Unused = Int", body, "c"));
    }

    /**
     * An end on a case's place in its enumeration's order is a relation the region holds as any
     * other: past {@code level >= Low}, which keeps no level out, {@code level} still takes every
     * case and is equal to every {@code cap}; past {@code level >= Mid} it is never {@code Low},
     * so a {@code cap} of {@code Low} settles the comparison.
     */
    @Test
    void anEndOnACasesPlaceInItsOrderNarrowsItAsTheRegionSays() {
        String declarations = "data Level = Low | Mid | High";
        assertEquals(Map.of("level", RELATES, "cap", RELATES),
                left("level: Level, cap: Level", declarations,
                        "if level >= Low then level == cap else false", "4:49"));
        assertEquals(Map.of("level", RELATES, "cap", NOT_SHOWN),
                left("level: Level, cap: Level", declarations,
                        "if level >= Mid then level == cap else false", "4:49"));
    }

    /** A way over another number of the date a year is taken of ties the year to it: a date on
     *  the twenty-ninth of February is in a leap year. */
    @Test
    void aWayOverAnotherNumberOfTheSamePlaceTiesTheNumberTakenOfIt() {
        assertEquals(List.of(NOT_SHOWN), List.copyOf(left("y: Int, d: Date", "data Unused = Int",
                "if Date.month(d) == 2 && Date.day(d) == 29 then y == Date.year(d) else false",
                "4:66").entrySet().stream()
                .filter(each -> each.getKey().equals("y")).map(Map.Entry::getValue).toList()));
    }

    private static final String EMPLOYEE = "data EmpId = String invariant String.length(value) >= 1";

    /** A rule of the record over two of its other fields holds back neither the field compared
     *  nor anything beside it, however many such rules there are and however they are written. */
    @Test
    void aRuleOfTheRecordOverItsOtherFieldsTiesTheFieldComparedToNothing() {
        Map<String, String> reached = Map.of("approver", RELATES, "p.boss", RELATES);
        for (String rules : List.of("", "invariant low <= high",
                "invariant low <= high && high >= low", "invariant ordered(low, high)")) {
            assertEquals(reached, left("p: Pending, approver: EmpId", EMPLOYEE
                    + "\nlet ordered (a: Int, b: Int): Bool = a <= b"
                    + "\ndata Pending = { me: EmpId, boss: EmpId, low: Int, high: Int } " + rules,
                    "approver == p.boss", "6:32"), rules);
        }
    }

    /** Rows that cover the comparison still satisfy the model once the record carries a rule over
     *  two of its other fields. */
    @Test
    void rowsCoveringTheComparisonSatisfyAModelWhoseRecordRulesOverItsOtherFields() {
        Compilation compilation = Compilation.ofSource("""
                module eqrepro

                data EmpId = String
                    invariant String.length(value) >= 1

                data Pending = { me: EmpId, boss: EmpId, low: Int, high: Int }
                    invariant low <= high
                data Granted
                data Denied

                behavior approve : (p: Pending, approver: EmpId) -> Granted | Denied

                let approve (p, approver) = {
                    guard approver == p.boss else Denied
                    Granted
                }

                example approve
                    | "boss" : (Pending { me = EmpId("a"), boss = EmpId("b"), low = 1, high = 2 }, EmpId("b")) -> Granted
                    | "other" : (Pending { me = EmpId("a"), boss = EmpId("b"), low = 1, high = 2 }, EmpId("c")) -> Denied
                    | "equal bounds" : (Pending { me = EmpId("xx"), boss = EmpId("x"), low = 0, high = 0 }, EmpId("x")) -> Granted
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors(), "the rows hold");
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** A rule of the record that names the field compared may hold it back, whether it ties it to
     *  another field or bounds it alone. */
    @Test
    void aRuleOfTheRecordNamingTheFieldComparedIsNotShownToLeaveItReachingEveryValue() {
        for (String rule : List.of("invariant boss == me",
                "invariant String.length(boss.value) >= 2")) {
            assertEquals(Map.of("approver", NOT_SHOWN, "p.boss", NOT_SHOWN),
                    left("p: Pending, approver: EmpId", EMPLOYEE
                            + "\ndata Pending = { me: EmpId, boss: EmpId } " + rule,
                            "approver == p.boss", "5:32"), rule);
        }
    }

    private static final String QUOTE = "data Quote = { issuedOn: Int, expiresOn: Int } invariant ";

    /**
     * A rule of the record relating the field compared to another field it leaves free leaves the
     * field every value, and the field and a value of another parameter, which no declaration
     * relates to it, each reach every value the other may hold.
     */
    @Test
    void aRuleRelatingTheFieldComparedToAFreeFieldLeavesItEveryValue() {
        for (String rule : List.of("expiresOn >= issuedOn", "expiresOn == issuedOn")) {
            assertEquals(Map.of("today", RELATES, "q.expiresOn", RELATES),
                    leftAt("q: Quote, today: Int", QUOTE + rule, "today <= q.expiresOn", 26),
                    rule);
        }
    }

    /**
     * The field the rule relates to is held at nought or more, so the field compared is too: a
     * day before nought is before every expiry, and settles the comparison. The expiry still
     * reaches every day from nought on.
     */
    @Test
    void aRuleRelatingTheFieldComparedToABoundedFieldLeavesItTheRunThatBoundGives() {
        String rules = QUOTE + "issuedOn >= 0 && expiresOn >= issuedOn";
        assertEquals(Map.of("q.expiresOn", RELATES),
                leftAt("q: Quote, today: Int", rules, "today <= q.expiresOn", 26));
        assertEquals(List.of("today/x <= 0", "today/0 < x"),
                classesAt("q: Quote, today: Int", rules, "today <= q.expiresOn", "today"));
    }

    /**
     * A rule beside the relation that the bounds do not hold — a value taken out of the field
     * compared, a square of it — leaves nothing shown of what it takes, and so does an end the
     * relation carries over at a value no decimal writes, which is handed on rounded past it.
     */
    @Test
    void aRuleRelatingTheFieldComparedBesideOneItsBoundsDoNotHoldShowsNothingOfIt() {
        for (String rule : List.of("expiresOn >= issuedOn && expiresOn /= 5",
                "expiresOn >= issuedOn && expiresOn * expiresOn >= 4")) {
            assertEquals(Map.of("today", NOT_SHOWN, "q.expiresOn", RELATES),
                    leftAt("q: Quote, today: Int", QUOTE + rule, "today <= q.expiresOn", 26),
                    rule);
        }
        assertEquals(Map.of("today", NOT_SHOWN, "q.expiresOn", RELATES), leftAt(
                "q: Quote, today: Decimal",
                "data Quote = { issuedOn: Decimal, expiresOn: Decimal } invariant "
                        + "issuedOn * 3m >= 1m && expiresOn >= issuedOn",
                "today <= q.expiresOn", 26));
    }

    /**
     * Two fields the record relates each take every value up to ten, and are not apart: no row
     * has {@code y} below {@code x}, so an {@code x} of ten is beside a {@code y} of ten alone and
     * settles the comparison.
     */
    @Test
    void twoFieldsTheRecordRelatesAreNotTakenToReachEachOther() {
        assertEquals(Map.of("p.x", NOT_SHOWN, "p.y", NOT_SHOWN), leftAt("p: P",
                "data P = { x: Int, y: Int } invariant x <= y && y <= 10", "p.x == p.y", 17));
    }

    /**
     * A way relating the day to the field the rule relates the expiry to ties the expiry to the
     * day: past {@code q.issuedOn == today} every expiry is at or after the day and none is past
     * ten, so a day of ten is beside an expiry of ten alone and settles the comparison.
     */
    @Test
    void aWayOverAFieldTheRuleRelatesTiesTheFieldCompared() {
        assertEquals(Map.of("today", NOT_SHOWN, "q.expiresOn", NOT_SHOWN),
                leftAt("q: Quote, today: Int", QUOTE + "expiresOn >= issuedOn && expiresOn <= 10",
                        "if q.issuedOn == today then today == q.expiresOn else false", 54));
    }

    /**
     * A rule relating how long the string compared is to how long a field held to three
     * characters is holds the string compared to three as well, which no end on the string itself
     * says: a string of four is equal to none of them.
     *
     * <p>Kept back twice. The set of strings at the place is not read whole beside a rule over
     * their lengths, so the strings are not taken to be every string; and where they were, the end
     * on the length would keep them back.
     */
    @Test
    void aRuleRelatingAnotherNumberOfTheFieldComparedLeavesItWhatThatNumberIsLeft() {
        assertEquals(Map.of("w.a", RELATES, "s", NOT_SHOWN), leftAt("w: W, s: String",
                "data W = { a: String, b: String } invariant String.length(a) <= String.length(b)"
                        + " && String.length(b) <= 3", "w.a == s", 20));
    }

    private static final String STAGES = """
            data Lead
            data Won
            data Lost
            data Stage = Lead | Won | Lost""";

    /**
     * Held above another stage, a stage is never the first one, though the relation places no
     * end on it: the first stage is equal to no stage held there, and settles the comparison.
     */
    @Test
    void aStrictRelationKeepsAnOrderedValueOffTheEndOfItsOrder() {
        assertEquals(NOT_SHOWN, leftAt("q: Q, x: Stage", STAGES
                        + "\ndata Q = { a: Stage, b: Stage } invariant a > b", "q.a == x", 20)
                .get("x"));
    }

    /** Twice another field, a field holds even numbers alone, and an odd number is none of them. */
    @Test
    void aRelationLeavingAFieldEveryOtherNumberLeavesItNoRun() {
        assertEquals(NOT_SHOWN, leftAt("q: Q, t: Int",
                "data Q = { e: Int, i: Int } invariant e == 2 * i", "t == q.e", 18).get("t"));
    }

    /**
     * A name the cases of a sum share takes every value where every case leaves it every value,
     * one of them by a rule relating it to a field of its own it leaves free.
     */
    @Test
    void aNameTheCasesShareTakesEveryValueWhereOneCaseRelatesItToAFreeField() {
        assertEquals(Map.of("s.d", RELATES, "n", RELATES), leftAt("s: S, n: Int", """
                data C = { d: Int }
                data A = { ...C, e: Int } invariant d >= e
                data B = { ...C }
                data S = A | B""", "s.d >= n", 20));
    }

    /**
     * The words each place of {@code name} is left with by its invariant {@code rule}, the rule's
     * place in the declaration counted from one.
     */
    private static Map<String, Set<String>> leftByTheInvariant(String declaration, String name,
                                                              int rule) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                behavior m : (v: %s) -> Bool
                let m (v) = true
                """.formatted(declaration, name), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, Set<String>> out = new LinkedHashMap<>();
        Pattern about = Pattern.compile("about `([^`]+)`$");
        for (String line : report.lines().map(String::strip).toList()) {
            Matcher place = about.matcher(line);
            if (!line.contains("invariant " + name + " #" + rule + " ") || !place.find()
                    || !(line.startsWith("· no line") || line.startsWith("· not read"))) {
                continue;
            }
            out.computeIfAbsent(place.group(1), _ -> new TreeSet<>()).add(
                    line.contains("rather than dividing the values here") ? RELATES
                            : line.contains("not shown to reach every value here") ? NOT_SHOWN
                            : line);
        }
        return out;
    }

    /**
     * A conjunct relating two places another conjunct relates to a free place: what it is asked of
     * is what the rest of the rules leave them, and {@code b >= c} with {@code c} free leaves
     * {@code b} every value beside the {@code a} no other conjunct names, as {@code a >= b} with
     * {@code a} free leaves it beside {@code c}. Held at nought, {@code b} reaches only the values
     * of {@code a} from nought on, and an {@code a} below nought settles the rule.
     */
    @Test
    void aConjunctIsAskedWhatTheRestOfTheRulesLeaveThePlacesItRelates() {
        assertEquals(Map.of("v.a", Set.of(RELATES), "v.b", Set.of(RELATES), "v.c", Set.of(RELATES)),
                leftByTheInvariant("data Q = { a: Int, b: Int, c: Int } invariant b >= c && a >= b",
                        "Q", 1));
        assertEquals(Map.of("v.a", Set.of(NOT_SHOWN), "v.b", Set.of(RELATES)),
                leftByTheInvariant("data Q = { a: Int, b: Int } invariant b >= 0 && a >= b",
                        "Q", 1));
    }

    /**
     * Two places the rest of the rules hold together each take every value and are not apart:
     * held one or two apart, {@code x >= y} holds at every {@code x}, which settles it.
     */
    @Test
    void twoPlacesTheRestOfTheRulesHoldTogetherAreNotTakenToReachEachOther() {
        Map<String, Set<String>> left = leftByTheInvariant("""
                data T = { x: Int, y: Int }
                    invariant x >= y + 1
                    invariant x <= y + 2
                    invariant x >= y""", "T", 3);
        assertEquals(Map.of("v.x", Set.of(NOT_SHOWN), "v.y", Set.of(NOT_SHOWN)), left);
    }

    /**
     * A rule of a value two out reads places, not fields: a record's rule over
     * {@code pending.low} and a newtype's over {@code value.low} read beside {@code boss}, and the
     * same rules over {@code boss} read it.
     */
    @Test
    void aRuleFurtherOutReadsThePlacesItNamesAndNotTheFieldTheyStartAt() {
        String pending = EMPLOYEE + "\ndata Pending = { me: EmpId, boss: EmpId, low: Int, high: Int }";
        assertEquals(Map.of("approver", RELATES, "e.pending.boss", RELATES),
                left("e: Envelope, approver: EmpId", pending
                        + "\ndata Envelope = { pending: Pending } invariant pending.low <= pending.high",
                        "approver == e.pending.boss", "6:32"));
        assertEquals(Map.of("approver", NOT_SHOWN, "e.pending.boss", NOT_SHOWN),
                left("e: Envelope, approver: EmpId", pending
                        + "\ndata Envelope = { pending: Pending } invariant pending.boss == pending.me",
                        "approver == e.pending.boss", "6:32"));
        assertEquals(Map.of("approver", RELATES, "p.boss", RELATES),
                left("p: WrappedPending, approver: EmpId", pending
                        + "\ndata WrappedPending = Pending invariant value.low <= value.high",
                        "approver == p.value.boss", "6:32"));
        assertEquals(Map.of("approver", NOT_SHOWN, "p.boss", NOT_SHOWN),
                left("p: WrappedPending, approver: EmpId", pending
                        + "\ndata WrappedPending = Pending invariant value.boss == value.me",
                        "approver == p.value.boss", "6:32"));
    }

    /** How many a set holds, read down a chain of fields from a newtype wrapping a record. */
    @Test
    void aRuleOverHowManyASetFurtherDownHoldsBackNoElement() {
        assertEquals(Map.of("champ", RELATES, "w.members[*]", RELATES), left("champ: EmpId, w: Wrapped",
                EMPLOYEE + "\ndata Inner = { members: Set<EmpId> }"
                        + "\ndata Wrapped = Inner invariant Set.size(value.members) >= 1",
                "Set.contains(champ, w.value.members)", "6:20"));
    }

    /** How many a set holds is shown of the count, however little the rules of the record it
     *  sits in are shown of the rest: a pattern a field beside it is held to, which no range
     *  states, says nothing of the count. */
    @Test
    void aSetsCountIsShownOfItselfBesideAFieldWhoseRuleNoRangeStates() {
        assertEquals(Map.of("champ", RELATES, "o.makers[*]", RELATES), left("champ: EmpId, o: Opp",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) >= 1"
                        + "\ndata Code = String invariant String.matches(\"[A-Z]{2}\", value)"
                        + "\ndata Opp = { code: Code, makers: Ds }",
                "Set.contains(champ, o.makers.value)", "7:20"));
    }

    /** A rule of a record a field sits in, two records out, over another of its fields. */
    @Test
    void aRuleOfARecordFurtherOutOverAnotherOfItsFieldsTiesTheFieldComparedToNothing() {
        assertEquals(Map.of("approver", RELATES, "o.p.boss", RELATES),
                left("o: Outer, approver: EmpId", EMPLOYEE
                        + "\ndata Pending = { me: EmpId, boss: EmpId }"
                        + "\ndata Outer = { p: Pending, n: Int } invariant n >= 0",
                        "approver == o.p.boss", "6:32"));
    }

    /** How many a set holds says nothing of which values its elements take, so long as it may
     *  hold one; held to none, its elements are values it never holds. */
    @Test
    void aRuleOverHowManyASetHoldsHoldsBackNoElementUnlessItHoldsNone() {
        assertEquals(Map.of("champ", RELATES, "ds[*]", RELATES), left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) >= 1",
                "Set.contains(champ, ds.value)", "5:21"));
        assertEquals(Map.of("champ", RELATES, "ds.members[*]", RELATES), left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = { members: Set<EmpId> } invariant Set.size(members) >= 1",
                "Set.contains(champ, ds.members)", "5:21"));
        assertEquals(NOT_SHOWN, left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) <= 0",
                "Set.contains(champ, ds.value)", "5:21").get("champ"));
    }

    /** Held to more than one, a set's elements are that many values apart, which is a question
     *  of the element's type this does not ask: not shown, though a type of strings has them. */
    @Test
    void aSetHeldToMoreThanOneIsNotShownToLeaveItsElementsEveryValue() {
        assertEquals(NOT_SHOWN, left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) == 2",
                "Set.contains(champ, ds.value)", "5:21").get("champ"));
    }
}
