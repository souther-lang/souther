package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.Figure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.RowObservation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
     * The behavior {@code m} taking {@code inputs} and answering {@code body}, of type
     * {@code answers}.
     */
    private static Compilation measured(String inputs, String declarations, String answers,
                                        String body) {
        return measured("""
                module w1
                %s
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(declarations, inputs, answers,
                        inputs.replaceAll(": [A-Za-z<>]+", ""), body));
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
        return leftIn(measured(inputs, declarations, answers, body), at);
    }

    /** The same, of a model of module {@code w1} written out whole, whose behavior is {@code m}. */
    private static Map<String, String> leftIn(String source, String at) {
        return leftIn(measured(source), at);
    }

    /** The classes the axis at {@code path} of a model written out whole is divided into. */
    private static List<String> classesIn(String source, String path) {
        PartitionEvidence evidence = measured(source).db()
                .ask(new Adequacy.Coverage("w1")).value().get("m");
        return evidence.axes().stream().filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream()).toList();
    }

    /**
     * A model written out whole, read for the lines its rules draw and no row composed at them:
     * what is asked here is the word a place is left with and the classes it is parted into, which
     * no composed row moves.
     */
    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source, written -> {
            Compilation compilation = Compilation.ofSource(written, "Main");
            compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
            compilation.answerEverything();
            return compilation;
        });
    }

    private static Map<String, String> leftIn(Compilation compilation, String at) {
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

    /** A record holding the amount beside a field of type {@code Held}, whose rule is
     *  {@code rule}. */
    private static String besideAHeld(String held, String rule) {
        return """
                data Yen = Int invariant value >= 0
                data Held = %s invariant %s
                data Rec = { h: Held, d: Yen }""".formatted(held, rule);
    }

    /**
     * A rule saying only where one part of a date falls leaves the amount beside it alone: every
     * part of a date the calendar has is a part of some date, so the first of any month is a
     * value of the field, and the amount reaches every gross from nought on.
     */
    @Test
    void aRuleOnOnePartOfADateLeavesAnAmountBesideItAlone() {
        assertEquals(Map.of("g", RELATES), leftAt("g: Yen, r: Rec",
                besideAHeld("Date", "Date.day(value) == 1"), "g.value >= r.d.value", 24));
    }

    /**
     * A rule asking for two parts of a date at once is not shown to leave the field a value: each
     * part the calendar has is a part of some date, and two of them are not thereby one date. So
     * the amount is not shown to reach every gross, whether the parts are in two comparisons or in
     * one.
     */
    @Test
    void twoPartsOfADateAreNotShownToBeOneDate() {
        for (String rule : List.of("Date.day(value) == 1 && Date.month(value) == 2",
                "Date.day(value) == Date.month(value)")) {
            assertEquals(Map.of("g", NOT_SHOWN), leftAt("g: Yen, r: Rec",
                    besideAHeld("Date", rule), "g.value >= r.d.value", 24), rule);
        }
    }

    /**
     * A rule working something out beside the part it takes is not shown to leave the field a
     * value, whatever it comes to. Under {@code Date.day(value) + 1 == 2} the first of a month is
     * a date the sum gets through, and the rule is not shown to be that alone. What the bounds read
     * of {@code Date.day(value) + M > 0} is a day above nought less the greatest {@code Int}, and
     * no date gets through working it out, so the field holds nothing and nothing is said of the
     * amount beside it. Cancelled away, as in {@code + M - M}, it is still worked out. A part held
     * against a number as it is written — the length of a string, the year of a date — leaves one.
     */
    @Test
    void aRuleWorkingSomethingOutBesideThePartIsNotShownToLeaveAValue() {
        assertEquals(Map.of("g", NOT_SHOWN), leftAt("g: Yen, r: Rec",
                besideAHeld("Date", "Date.day(value) + 1 == 2"), "g.value >= r.d.value", 24));
        for (String rule : List.of("Date.day(value) + 9223372036854775807 > 0",
                "Date.day(value) + 9223372036854775807 - 9223372036854775807 == 1")) {
            assertEquals(Map.of(), leftAt("g: Yen, r: Rec",
                    besideAHeld("Date", rule), "g.value >= r.d.value", 24), rule);
        }
        assertEquals(Map.of("g", RELATES), leftAt("g: Yen, r: Rec",
                besideAHeld("String", "String.length(value) == 3"), "g.value >= r.d.value", 24));
        assertEquals(Map.of("g", RELATES), leftAt("g: Yen, r: Rec",
                besideAHeld("Date", "Date.year(value) == 99999"), "g.value >= r.d.value", 24));
    }

    /**
     * A row whose run stops before the comparison is no row at it. Under {@code a + 1 == 0} the
     * only row holding {@code b} at the greatest {@code Int} true is {@code a} there too, which
     * stops at {@code a + 1}, so that {@code b} settles the comparison false.
     */
    @Test
    void aRowThatStopsBeforeTheComparisonIsNoRowAtIt() {
        String yen = "data Yen = Int invariant value >= 0";
        String body = "if a.value + 1 == 0 then false else a.value == b.value";
        assertEquals(Map.of("a", RELATES), left("a: Yen, b: Yen", yen, body, "4:60"));
        assertTrue(classesAt("a: Yen, b: Yen", yen, body, "b").stream()
                        .anyMatch(each -> each.contains("9223372036854775807")),
                "the greatest Int settles the comparison false");
    }

    /**
     * The left operand of {@code &&} is worked out before the right one is reached, and the right
     * operand of {@code ||} is worked out only where the left came out false: the comparison on
     * the left of the second is reached by every row, so what stops in the operand beside it
     * takes none out.
     */
    @Test
    void aLeftOperandIsWorkedOutBeforeTheRightIsReachedAndNeverTheOtherWayAbout() {
        String yen = "data Yen = Int invariant value >= 0";
        assertEquals(Map.of("a", RELATES), left("a: Yen, b: Yen", yen,
                "a.value + 1 >= 0 && a.value == b.value", "4:44"));
        assertEquals(Map.of("a", RELATES, "b", RELATES), left("a: Yen, b: Yen", yen,
                "a.value == b.value || a.value + 1 == 0", "4:24"));
    }

    /**
     * A {@code let} is worked out whether or not anything reads its name: the value of one nothing
     * reads stops a run at {@code a + 1} as much as one the comparison is over.
     */
    @Test
    void aLetNothingReadsStopsARunAsMuchAsOneThatIsRead() {
        String yen = "data Yen = Int invariant value >= 0";
        String body = "{\n    let unused = a.value + 1\n    a.value == b.value\n}";
        assertEquals(Map.of("a", RELATES), left("a: Yen, b: Yen", yen, body, "6:13"));
        assertTrue(classesAt("a: Yen, b: Yen", yen, body, "b").stream()
                        .anyMatch(each -> each.contains("9223372036854775807")),
                "the greatest Int settles the comparison false");
    }

    /**
     * A number the run itself narrows is not free to meet a disequality: past
     * {@code let unused = p + M}, {@code p} is nought, and {@code a != p} then takes the one
     * value of {@code b} away that {@code a} could not meet: nought is no value of {@code b} the
     * comparison holds at. Every {@code a} left meets some {@code b}, so {@code a} is not divided,
     * and {@code b} is not shown to reach its true side at every value.
     */
    @Test
    void aNumberTheRunNarrowsIsNotFreeToMeetADisequality() {
        String body = "{\n    let unused = p.value + 9223372036854775807\n"
                + "    if a.value == p.value\n    then false\n    else a.value == b.value\n}";
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN), left("p: Yen, a: Yen, b: Yen",
                "data Yen = Int invariant value >= 0", body, "8:18"));
    }

    /**
     * Nor is one an operation the run works out reads where nothing says when it answers:
     * {@code 1 / p} stops at nought, so past it {@code p} is one, and {@code a != p} takes
     * {@code a} away from one. {@code b} is not shown to reach its true side at every value,
     * where a free {@code p} would have left it related.
     */
    @Test
    void aNumberAnUnsaidOperationReadsIsNotFreeToMeetADisequality() {
        String body = "{\n    let unused = 1 / p.value\n"
                + "    if a.value == p.value\n    then false\n    else a.value == b.value\n}";
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN), left("p: Bit, a: Bit, b: Bit",
                "data Bit = Int invariant value >= 0 && value <= 1", body, "8:18"));
    }

    /**
     * Where what a run gets past leaves a place no value, no row arrives at the comparison, and
     * it is read so: the reason says the rows that arrive hold no value at its line, and no class
     * of either side is drawn. The region of the way is left as it was there, since the proof
     * that nothing arrives is the walk's and is made from the same operators.
     */
    @Test
    void aRunNoRowGetsPastLeavesTheComparisonNoRowAtIt() {
        String body = "{\n    let unused = a.value + 9223372036854775807\n    a.value == b.value\n}";
        String yen = "data Yen = Int invariant value >= 1";
        Map<String, String> left = left("a: Yen, b: Yen", yen, body, "6:13");
        assertEquals(Set.of("a", "b"), left.keySet());
        left.values().forEach(each -> assertTrue(each.contains("no row that arrives at it"), each));
        assertEquals(List.of(), classesAt("a: Yen, b: Yen", yen, body, "a"));
        assertEquals(List.of(), classesAt("a: Yen, b: Yen", yen, body, "b"));
    }

    /**
     * What the comparison works out itself narrows its numbers by one another as much as by
     * themselves: {@code a + b + M - M} is an {@code Int} at every step only where {@code a + b}
     * is nought, so the only row that reaches {@code >= 1} is the one at nought, and it fails.
     * No line is drawn on either number, which would be drawn at the rows that stop.
     */
    @Test
    void aSumTheComparisonWorksOutItselfNarrowsItsNumbersByEachOther() {
        String bit = "data Small = Int invariant value >= 0 && value <= 1";
        String body = "a.value + b.value + 9223372036854775807 - 9223372036854775807 >= 1";
        assertEquals(List.of(), classesAt("a: Small, b: Small", bit, body, "a"));
        assertEquals(List.of(), classesAt("a: Small, b: Small", bit, body, "b"));
    }

    /**
     * A sum the run worked out narrows both its numbers by the other: {@code a + b} is an
     * {@code Int} only where {@code b} is nought or one, for an {@code a} one below the greatest,
     * so a {@code b} above it is no row of the comparison {@code a < b} and no line is drawn
     * there. Two amounts the sum cannot stop on narrow nothing, and the comparison reads each as
     * it does without the sum.
     */
    @Test
    void aSumTheRunWorkedOutNarrowsItsTwoNumbersByEachOther() {
        String almost = "data AlmostMax = Int invariant value == 9223372036854775806\n"
                + "data NonNegative = Int invariant value >= 0";
        String body = "{\n    let unused = a.value + b.value\n    a.value < b.value\n}";
        assertEquals(List.of(),
                classesAt("a: AlmostMax, b: NonNegative", almost, body, "b"));
        String small = "data Yen = Int invariant value >= 0 && value <= 1000000";
        assertEquals(classesAt("a: Yen, b: Yen", small,
                        "{\n    let unused = 0\n    a.value < b.value\n}", "b"),
                classesAt("a: Yen, b: Yen", small, body, "b"));
    }

    /**
     * A closure handed to an operation of the library is applied by it, so what its body may stop
     * on is what the run may stop on: {@code Int.floorMod(x, p)} applied to each of two numbers
     * stops at {@code p} nought, as it does written out.
     */
    @Test
    void whatTheBodyOfAClosureAppliedByTheLibraryMayStopOnIsWhatTheRunMayStopOn() {
        String bits = "data Bit = Int invariant value >= 0 && value <= 1";
        String body = "{\n    let unused = List.map(x -> Int.floorMod(x, p.value), [1, 2])\n"
                + "    if a.value == p.value\n    then false\n    else a.value == b.value\n}";
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("p: Bit, a: Bit, b: Bit", bits, body, "8:18"));
    }

    /**
     * What may stop a run is asked of the one owner of it, at every node and not only those that
     * always run: a call of a kernel, a part worked out where a condition came out one way, and
     * an arm of a branch, each stop the run on the number they read, and past each of them
     * {@code p} is the one value that lets a row on, which {@code a != p} then takes from
     * {@code a}.
     */
    @Test
    void whatMayStopARunIsAskedOfWhatEndsARunWhereverItIsWorkedOut() {
        String bits = "data Bit = Int invariant value >= 0 && value <= 1";
        Map<String, String> notShown = Map.of("a", RELATES, "b", NOT_SHOWN);
        for (String unused : List.of(
                "Int.floorMod(1, p.value)",
                "p.value == 0 && p.value + 9223372036854775807 + 1 > 0",
                "if p.value == 0 then p.value + 9223372036854775807 + 1 else 0")) {
            String body = "{\n    let unused = " + unused + "\n"
                    + "    if a.value == p.value\n    then false\n    else a.value == b.value\n}";
            assertEquals(notShown, left("p: Bit, a: Bit, b: Bit", bits, body, "8:18"), unused);
        }
    }

    /**
     * What the comparison works out itself is worked out on a row at it: {@code a + M - M} is
     * {@code a} as a form and stops at every {@code a} above nought as written.
     */
    @Test
    void aRowThatStopsInTheComparisonsOwnArithmeticIsNoRowAtIt() {
        String yen = "data Yen = Int invariant value >= 0 && value <= 1000000";
        assertEquals(List.of(), classesAt("a: Yen, b: Yen", yen,
                "a.value + 9223372036854775807 - 9223372036854775807 + b.value >= 30", "a"));
    }

    /**
     * Parts no date has leave the field no value, and the record with it: no row reaches the
     * comparison, and nothing is said of the amount or drawn on the gross.
     */
    @Test
    void partsNoDateHasLeaveNothingToSayOfTheAmount() {
        for (String rule : List.of("Date.day(value) == 31 && Date.month(value) == 2",
                "Date.year(value) == 2023 && Date.month(value) == 2 && Date.day(value) == 29")) {
            assertEquals(Map.of(), leftAt("g: Yen, r: Rec", besideAHeld("Date", rule),
                    "g.value >= r.d.value", 24), rule);
            assertEquals(List.of(), classesAt("g: Yen, r: Rec", besideAHeld("Date", rule),
                    "g.value >= r.d.value", "g"), rule);
        }
    }

    /** What {@code a.value + b.value >= 30} leaves {@code a} and {@code b} past a way where
     *  {@code kept} does not hold, the behavior taking {@code inputs}. */
    private static Map<String, String> pastAWayOffAValue(String inputs, String declarations,
                                                         String kept) {
        String body = "if " + kept + " then false else a.value + b.value >= 30";
        String head = "let m (" + inputs.replaceAll(": [A-Za-z<>]+", "") + ") = ";
        Map<String, String> out = new LinkedHashMap<>(leftAt(inputs, declarations, body,
                head.length() + body.indexOf(">= 30") + 1));
        for (String place : List.of("a", "b")) {
            List<String> classes = classesAt(inputs, declarations, body, place);
            if (classes.size() == 2 && classes.get(0).equals(place + "/0 <= x < 30")
                    && classes.get(1).startsWith(place + "/30 <= x")) {
                out.putIfAbsent(place, "divided at 30");
            }
        }
        return out;
    }

    private static final String DIVIDED = "divided at 30";

    /**
     * A way keeping a sum off a number nothing else reads leaves the sum every value: whatever the
     * sum is, the number holds some other value. So the comparison past it divides each side where
     * it does without the way — a fixed wage held unequal to the one before it, and an amount beside
     * the wage. A number of three terms leaves the rows' region no run it can show of a side, so the
     * region is the one the rest of the way leaves. A sum is taken off only where it is worked out
     * on every row, as two amounts each held below a million are.
     */
    @Test
    void aWayKeepingASumOffAFreeNumberLeavesTheSidesAsTheyAre() {
        String yen = "data Yen = Int invariant value >= 0";
        assertEquals(Map.of("a", DIVIDED, "b", DIVIDED),
                pastAWayOffAValue("p: Yen, a: Yen, b: Yen", yen, "a.value == p.value"));
        assertEquals(Map.of("a", DIVIDED, "b", DIVIDED),
                pastAWayOffAValue("p: Yen, a: Yen, b: Yen, c: Yen",
                        "data Yen = Int invariant value >= 0 && value <= 1000000",
                        "a.value + c.value == p.value"));
    }

    /**
     * A sum a row may not work out is not taken off the way: past {@code a + c != p}, a row whose
     * {@code a} and {@code c} pass the greatest {@code Int} together stops before the comparison,
     * whatever {@code p} is. And past {@code a + Date.day(d) != 0} no day lets a row with {@code a}
     * at the greatest {@code Int} through, though the day takes every value from one to
     * thirty-one and is read nowhere else.
     */
    @Test
    void aSumARowMayNotWorkOutKeepsTheSidesBack() {
        String yen = "data Yen = Int invariant value >= 0";
        assertEquals(Map.of("a", DIVIDED, "b", NOT_SHOWN),
                pastAWayOffAValue("p: Yen, a: Yen, b: Yen, c: Yen", yen,
                        "a.value + c.value == p.value"));
        assertEquals(Map.of("a", DIVIDED, "b", NOT_SHOWN),
                pastAWayOffAValue("d: Date, a: Yen, b: Yen", yen, "a.value + Date.day(d) == 0"));
    }

    /**
     * What the source works out and not what its form comes to is what a statement taken off the
     * way is asked of. {@code a + M - M != p} is {@code a != p} as a form, and every {@code a}
     * above nought stops at the first sum: the way holds that as a statement of {@code a}, so the
     * comparison past it is not divided as it would be for all the {@code a}. And
     * {@code p + a + (M - 10) - (M - 10) != 0} stops wherever {@code p + a} is above ten, though
     * the form fits for amounts up to a million: no row has {@code a} above ten, so {@code a} is
     * related to {@code b} and not divided at thirty as it would be for all the {@code a}, and
     * {@code b} is not shown to take every value.
     */
    @Test
    void aStatementTheSourceMayNotWorkOutIsNotTakenOffTheWay() {
        String yen = "data Yen = Int invariant value >= 0 && value <= 1000000";
        assertEquals(Map.of("a", RELATES), pastAWayOffAValue("p: Yen, a: Yen, b: Yen", yen,
                "a.value + 9223372036854775807 - 9223372036854775807 == p.value"));
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                pastAWayOffAValue("p: Yen, a: Yen, b: Yen", yen,
                        "p.value + a.value + 9223372036854775797 - 9223372036854775797 == 0"));
    }

    /**
     * Nor is a number something the way declined may name: what a dependency answered, held once
     * to the length of {@code s} and once to one, holds the length at one, though neither reading
     * names it. Past {@code x != String.length(s)}, {@code x} is then never one, and
     * {@code x + y >= 2} is not shown to be reached on its true side: nothing is said of
     * {@code x}, which only nought is left, and {@code y} is not shown to take every value.
     */
    @Test
    void aNumberWhatTheWayDeclinedMayNameIsNotFree() {
        String source = """
                module w1
                data Bit = Int invariant value >= 0 && value <= 1
                data Row = { n: Int }
                behavior look : (k: Int) -> List<Row>
                behavior m : (s: String, x: Bit, y: Bit) -> Bool
                    depends on look
                let m (s, x, y, look) = {
                    let rows = look(0)
                    if List.any(r -> r.n == String.length(s), rows) && List.all(r -> r.n == 1, rows)
                    then (if x.value == String.length(s) then false else x.value + y.value >= 2)
                    else false
                }
                """;
        List<String> lines = source.lines().toList();
        int line = 0;
        while (!lines.get(line).contains("x.value + y.value >= 2")) {
            line++;
        }
        String at = (line + 1) + ":" + (lines.get(line).indexOf(">= 2") + 1);
        assertEquals(Map.of("y", NOT_SHOWN), leftIn(source, at));
    }

    /**
     * And not where the number is not free: one value of it, a side of the relation, a number a
     * rule of the record around it names, or one another statement of the way reads. Then the way
     * may take values of the side away, and nothing is shown of either side.
     */
    @Test
    void aWayKeepingASideOffANumberThatIsNotFreeKeepsTheSidesBack() {
        String yen = "data Yen = Int invariant value >= 0";
        Map<String, String> notShown = Map.of("a", NOT_SHOWN, "b", NOT_SHOWN);
        Map<String, String> aDividedOnly = Map.of("a", DIVIDED, "b", NOT_SHOWN);
        assertEquals(Map.of("b", NOT_SHOWN), pastAWayOffAValue("p: Seven, a: Yen, b: Yen",
                yen + "\ndata Seven = Int invariant value == 7", "a.value == p.value"));
        assertEquals(notShown, pastAWayOffAValue("a: Yen, b: Yen", yen, "a.value == b.value"));
        assertEquals(aDividedOnly, pastAWayOffAValue("r: R, a: Yen, b: Yen",
                yen + "\ndata R = { p: Yen, q: Yen } invariant p.value <= q.value",
                "a.value == r.p.value"));
        assertEquals(aDividedOnly, pastAWayOffAValue("p: Yen, a: Yen, b: Yen", yen,
                "a.value == p.value || p.value > 5"));
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
        assertEquals(Map.of("value >= 0 && value /= 5", Map.of("g", NOT_SHOWN),
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

    private static final String FORECAST = """
            module w1

            data CurrencyCode = String
                invariant String.matches("[A-Z]{3}", value)

            data ConversionRate = Decimal
                invariant value > 0.0m

            data RateTable =
                { base: CurrencyCode
                , rates: Map<CurrencyCode, ConversionRate>
                }
                invariant baseIsUnity = baseAtOne(base, rates)

            let baseAtOne (base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>): Bool =
                Map.get(base, rates)
                    |> Option.map(r -> Decimal.compare(r.value, 1.0m) == 0)
                    |> Option.withDefault(false)

            let yenRates = RateTable { base = CurrencyCode("JPY"), rates = Map.fromList(
                [ (CurrencyCode("JPY"), ConversionRate(1.0m))
                , (CurrencyCode("USD"), ConversionRate(150.0m)) ]) }

            data Deal = { currency: CurrencyCode, amount: Decimal }

            behavior m : (deals: List<Deal>, rates: RateTable) -> Bool

            let m (deals, rates) = {
                let kept = List.filterMap(d -> Map.get(d.currency, rates.rates), deals)
                List.length(kept) == List.length(deals)
            }
            """;

    /**
     * How many deals a rate is kept for, against how many deals there are. A run on the rates the
     * model names, of one deal in a currency they rate and one in a currency they do not, shows
     * the kept count holding of one element and not of another, so every count from nought to the
     * length is reached and the comparison leaves the length undivided wherever there is a deal.
     * With no deal the count is nought as the length is, and that settles the comparison: the
     * length is parted at nought and the values above it. A step weighing each deal by its rate
     * may stop on a product nothing here bounds, and is applied to the witness's elements alone,
     * on which it answered: the same is shown of it.
     *
     * <p>With no rates named, nothing the model writes is a rate table its rule admits, no run
     * shows the count, and nothing is shown of the length.
     */
    @Test
    void aCountAfterAFilterReachesEveryValueUpToTheLengthWhereARunShowsItHoldingAndFailing() {
        String weighed = FORECAST.replace("d -> Map.get(d.currency, rates.rates)",
                "d -> Option.map(r -> r.value * d.amount, Map.get(d.currency, rates.rates))");
        for (String model : List.of(FORECAST, weighed)) {
            Compilation named = reported(model);
            assertEquals(Map.of(), leftIn(named, whereWritten(model, "== List")), model);
            assertEquals(List.of("List.length(deals)/0 <= x <= 0", "List.length(deals)/0 < x"),
                    named.db().ask(new Adequacy.Coverage("w1")).value().get("m").axes().stream()
                            .filter(axis -> axis.path().equals("List.length(deals)"))
                            .flatMap(axis -> axis.classes().stream()).toList(), model);
        }
        String unnamed = FORECAST.substring(0, FORECAST.indexOf("let yenRates"))
                + FORECAST.substring(FORECAST.indexOf("data Deal"));
        assertEquals(Map.of("List.length(deals)", NOT_SHOWN),
                leftIn(reported(unnamed), whereWritten(unnamed, "== List")));
    }

    /**
     * A witness is one run, and the rows the count is read over are its elements over again, so
     * whatever stands between it and those rows leaves the length as nothing is shown of it. A
     * helper calling itself on the deals before the comparison may stop a run on some list of them
     * where nothing here says. A way that asks every deal for an amount above nought lets through
     * some of the deals the witness's elements make, and one asking how many rates there are asks
     * what the statement reads outside the element. A way through a value of a third parameter is
     * met by a witness only where some run is found meeting it, which no value tried here does.
     * And deals held in a record whose rule is that no two share a currency are not every list of
     * the witness's elements over again: what a witness is found for is a list standing as a
     * parameter on its own, which no rule of a value around it reads.
     */
    @Test
    void aCountIsReadOverTheWitnessesElementsOverAgainOnlyWhereNothingStandsBetween() {
        String stops = FORECAST.replace("behavior m :", """
                partial let walked (ds: List<Deal>): Int =
                    match List.get(0, ds) with
                        | None -> 0
                        | Some first -> 1 + walked(List.drop(1, ds))

                behavior m :""").replace("    List.length(kept) == List.length(deals)",
                "    let n = walked(deals)\n"
                        + "    if List.length(kept) == List.length(deals) then n >= 0 else false");
        String picked = FORECAST.replace("    List.length(kept) == List.length(deals)",
                "    if List.all(d -> d.amount > 0.0m, deals) then"
                        + " List.length(kept) == List.length(deals) else false");
        String unique = FORECAST.replace("(deals: List<Deal>,", "(book: Book,")
                .replace("let m (deals, rates)", "let m (book, rates)")
                .replace("rates.rates), deals)", "rates.rates), book.deals)")
                .replace("List.length(deals)", "List.length(book.deals)")
                .replace("behavior m :", """
                        data Book = { deals: List<Deal> }
                            invariant List.length(List.distinct(List.map(d -> d.currency, deals)))
                                == List.length(deals)

                        behavior m :""")
                + """

                example m
                    | "one deal a rate is kept for and one it is not" :
                        (Book { deals = [ Deal { currency = CurrencyCode("USD"), amount = 1.0m }
                                        , Deal { currency = CurrencyCode("AAA"), amount = 1.0m } ] },
                         yenRates) -> false
                """;
        String third = FORECAST.replace("rates: RateTable) -> Bool", "rates: RateTable, flag: Int)"
                        + " -> Bool")
                .replace("let m (deals, rates)", "let m (deals, rates, flag)")
                .replace("    List.length(kept) == List.length(deals)",
                        "    if Int.floorMod(flag, 7919) == 5000 then"
                                + " List.length(kept) == List.length(deals) else false");
        String ratesAsked = FORECAST.replace("    List.length(kept) == List.length(deals)",
                "    if Map.size(rates.rates) >= 2 then"
                        + " List.length(kept) == List.length(deals) else false");
        for (String model : List.of(stops, picked, third, ratesAsked)) {
            Compilation compilation = reported(model);
            assertEquals(List.of(), compilation.errors(), model);
            assertEquals(Map.of("List.length(deals)", NOT_SHOWN),
                    leftIn(compilation, whereWritten(model, "== List.length(deals")), model);
        }
        Compilation once = reported(unique);
        assertEquals(List.of(), once.errors(), unique);
        assertEquals(Map.of("List.length(book.deals)", NOT_SHOWN),
                leftIn(once, whereWritten(unique, "== List.length(book")));
    }

    /**
     * Two more parameters, each of a type the model names some values of, and a way through a sum
     * of them no pair of those values meets. With one named of each, the search tries every row it
     * has and finds none, and the length is not shown. With seventeen of each, the pairs are more
     * rows than it tries, it stops short of the last of them, and the place says which figure it
     * stopped at — a run allowed more may find what this one did not.
     */
    @Test
    void aSearchForAWitnessThatStoppedShortSaysWhereItStopped() {
        assertEquals(List.of(), figuresSaidOfTheLength(1));
        assertEquals(List.of("VALUES_AN_ELEMENT_IS_CHOSEN_AMONG"), figuresSaidOfTheLength(17));
    }

    /** The figures the report names beside what nothing is shown of at the length, where the
     *  model names {@code named} values of each of two more parameters. */
    private static List<String> figuresSaidOfTheLength(int named) {
        StringBuilder tags = new StringBuilder("data Tag = Int\n\n");
        for (int i = 1; i <= named; i++) {
            tags.append("let tag").append(i).append(" = Tag(").append(i).append(")\n");
        }
        String model = FORECAST.replace("rates: RateTable) -> Bool",
                        "rates: RateTable, a: Tag, b: Tag) -> Bool")
                .replace("behavior m :", tags + "\nbehavior m :")
                .replace("let m (deals, rates)", "let m (deals, rates, a, b)")
                .replace("    List.length(kept) == List.length(deals)",
                        "    if a.value + b.value == 1000 then"
                                + " List.length(kept) == List.length(deals) else false");
        return figuresSaidOf(model, "deals");
    }

    /**
     * The figures the report names beside what nothing is shown of at how many {@code container}
     * holds, where the comparison of the count against it is written {@code == List.length(}.
     */
    private static List<String> figuresSaidOf(String model, String container) {
        String length = "List.length(" + container + ")";
        Compilation compilation = reported(model);
        assertEquals(List.of(), compilation.errors(), model);
        assertEquals(NOT_SHOWN, leftIn(compilation, whereWritten(model, "== List.length("))
                .get(length), model);
        String at = "comparison@" + whereWritten(model, "== List.length(") + " ";
        List<String> figures = new ArrayList<>();
        AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()))
                .lines().map(String::strip)
                .filter(line -> line.startsWith("· not read: " + at)
                        && line.endsWith("about `" + length + "`"))
                .forEach(line -> {
                    Matcher stopped = Pattern.compile("\\(([A-Z_]+), \\d+\\)").matcher(line);
                    while (stopped.find()) {
                        figures.add(stopped.group(1));
                    }
                });
        return figures;
    }

    /**
     * Whatever cut short the values a witness is sought among is named, and the elements tried are
     * held to the figure however each is come by. None of the numbers written is above a thousand,
     * so the search finds no element the count holds of and tries all it has. A row of ten is
     * all of it, and no figure is named. A row of sixty-five was kept only so far by the run that
     * read it, and the figure it was cut at is named. Five rows of sixty, each kept whole, write
     * more elements between them than the search tries, and its own figure is named.
     */
    @Test
    void whatCutTheValuesAWitnessIsSoughtAmongShortIsNamed() {
        assertEquals(List.of(), figuresSaidOf(numbersInRows(1, 10), "xs"));
        assertEquals(List.of("OBSERVED_ELEMENTS"), figuresSaidOf(numbersInRows(1, 65), "xs"));
        assertEquals(List.of("VALUES_AN_ELEMENT_IS_CHOSEN_AMONG"),
                figuresSaidOf(numbersInRows(5, 60), "xs"));
    }

    /** How many of a list of numbers are above a thousand, against how many it holds, and
     *  {@code rows} rows each writing the next {@code each} numbers from nought. */
    private static String numbersInRows(int rows, int each) {
        StringBuilder written = new StringBuilder();
        for (int row = 0; row < rows; row++) {
            StringBuilder numbers = new StringBuilder();
            for (int i = 0; i < each; i++) {
                numbers.append(i == 0 ? "" : ", ").append(row * each + i);
            }
            written.append("    | \"numbers ").append(row).append("\" : ([ ").append(numbers)
                    .append(" ]) -> false\n");
        }
        return """
                module w1
                behavior m : (xs: List<Int>) -> Bool
                let m (xs) = {
                    let kept = List.filter(x -> x > 1000, xs)
                    List.length(kept) == List.length(xs)
                }

                example m
                %s""".formatted(written);
    }

    /** A list of small numbers, how many of which are above some bound, and a row of one above
     *  every bound below and one below, which the search takes the elements of. */
    private static final String SMALL = """
            module w1
            data Small = Int invariant value >= 0 && value <= 5
            behavior m : (xs: List<Small>) -> Bool
            let m (xs) = %s

            example m
                | "one above and one below" : ([ Small(5), Small(0) ]) -> false
            """;

    /** The count bound to a name before the comparison, kept by {@code keep}. */
    private static String countedAfterALet(String keep) {
        return SMALL.formatted("{\n    let kept = List.filter(x -> " + keep + ", xs)\n"
                + "    List.length(kept) == List.length(xs)\n}");
    }

    /** The same count written inside the comparison. */
    private static String countedInline(String keep) {
        return SMALL.formatted("List.length(List.filter(x -> " + keep + ", xs))"
                + " == List.length(xs)");
    }

    /**
     * A count is read alike however it is written. Of the numbers above two, bound to a name
     * first or written inside the comparison, a row of five and of nought is a witness, and the
     * length is parted at nought. Of the numbers above how many there are, the statement reads the
     * container as well as the element: the rows made of the witness hold more elements than it
     * does, and what the statement says of the same element changes with them, so nothing is
     * shown, written either way.
     */
    @Test
    void aCountIsReadOfAStatementAboutTheElementAloneHoweverItIsWritten() {
        for (String model : List.of(countedAfterALet("x.value > 2"), countedInline("x.value > 2"))) {
            Compilation compilation = reported(model);
            assertEquals(List.of(), compilation.errors(), model);
            assertEquals(List.of("List.length(xs)/0 <= x <= 0", "List.length(xs)/0 < x"),
                    compilation.db().ask(new Adequacy.Coverage("w1")).value().get("m").axes()
                            .stream().filter(axis -> axis.path().equals("List.length(xs)"))
                            .flatMap(axis -> axis.classes().stream()).toList(), model);
        }
        for (String model : List.of(countedAfterALet("x.value > List.length(xs)"),
                countedInline("x.value > List.length(xs)"))) {
            Compilation compilation = reported(model);
            assertEquals(List.of(), compilation.errors(), model);
            assertEquals(NOT_SHOWN, leftIn(compilation, whereWritten(model, "== List.length("))
                    .get("List.length(xs)"), model);
        }
    }

    /**
     * A witness found, the count of a statement about the element alone is read against the
     * length, which it leaves either way wherever there is an element and settles at none; the
     * count of one that also reads the container shows nothing of the length, witness or none. The
     * rows made of the witness hold its elements over again, and a statement reading how many
     * there are, or another of them, may say something else of the same element in each.
     *
     * <p>Asked of the relation itself, handed a witness for every count: a body whose statement
     * reads the container reads it in the step that keeps the elements too, and what is worked out
     * before the comparison would refuse that first.
     */
    @Test
    void aCountOfAStatementReadingTheContainerIsReadOfNoRowsMadeOfAWitness() {
        Compilation compilation = reported(FORECAST);
        InputReading read = compilation.db().ask(new Adequacy.Inputs("w1")).value().get("m")
                .reading(RuleReadings.of(compilation, "w1"));
        TermPath deals = TermPath.of("deals");
        Type list = read.domain().typeAt(deals, read.rules());
        NumericTerm.TakenOf length = NumericTerm.TakenOf.howManyHeldAt(
                NumericMeasures.takenOf(list, read.rules().inners()), deals, list,
                read.rules().inners(), read.rules().symbols());
        CountWitnesses.Lookup everyCount = _ -> new CountWitnesses.Sought(Optional.of(
                new CountWitnesses.Witness(List.of(), 0, FixtureTemplate.integer(0),
                        FixtureTemplate.integer(1))), Set.of());
        DecisionSubject.AnInput currency =
                new DecisionSubject.AnInput(deals.element().then("currency"));
        Map<Proposition, Boolean> undividedBy = new LinkedHashMap<>();
        undividedBy.put(new Proposition.SameValue(currency,
                new DecisionSubject.AnInput(TermPath.of("rates").then("base")), true), true);
        undividedBy.put(new Proposition.SameValue(currency,
                new DecisionSubject.AnInput(deals), true), false);
        undividedBy.forEach((statement, expected) -> {
            Quantity.HowManyMeet count =
                    new Quantity.HowManyMeet(new DecisionSubject.AnInput(deals), statement);
            UndividedByARelation relation = UndividedByARelation.ofAForm(
                    new LinearForm<>(ExactRatio.ZERO, Map.of(count, ExactRatio.ONE,
                            new DecisionAtom.OfTheInput(length), ExactRatio.ONE.negated())),
                    Rel.EQ);
            UndividedByARelation.WhatItLeaves left = relation.left(read, everyCount);
            assertEquals(expected, left.undivided().contains(FilingCoordinate.of(length))
                    || left.settled().containsKey(length), statement.toString());
        });
    }

    /**
     * A figure a search stopped at is said at the places of the relation it searched for, and at
     * no other. Of two relations read of one comparison, about two places, the count's search for
     * a witness stops at a figure and the other relation asks for none: the length the count is
     * read against is shown nothing of at that figure, and the other place is told nothing of it.
     */
    @Test
    void aFigureASearchStoppedAtIsSaidOnlyAtThePlacesOfTheRelationItSearchedFor() {
        Compilation compilation = reported(FORECAST);
        InputReading read = compilation.db().ask(new Adequacy.Inputs("w1")).value().get("m")
                .reading(RuleReadings.of(compilation, "w1"));
        NumericTerm.TakenOf deals = lengthOf(TermPath.of("deals"), read);
        NumericTerm.TakenOf rates = lengthOf(TermPath.of("rates").then("rates"), read);
        Quantity.HowManyMeet count = new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(TermPath.of("deals")),
                new Proposition.SameValue(new DecisionSubject.AnInput(
                        TermPath.of("deals").element().then("currency")),
                        new DecisionSubject.AnInput(TermPath.of("rates").then("base")), true));
        Figure stopped = CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure();
        CountWitnesses.Lookup stoppedShort =
                _ -> new CountWitnesses.Sought(Optional.empty(), Set.of(stopped));
        UndividedByARelation counted = UndividedByARelation.ofAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(count, ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(deals), ExactRatio.ONE.negated())),
                Rel.EQ);
        UndividedByARelation sized = UndividedByARelation.ofAForm(
                new LinearForm<>(ExactRatio.of(-3), Map.of(new DecisionAtom.OfTheInput(rates),
                        ExactRatio.ONE)), Rel.GE);
        ComparisonAssessment.AgainstAnotherValue both =
                new ComparisonAssessment.AgainstAnotherValue(
                        List.of(FilingCoordinate.of(deals), FilingCoordinate.of(rates)),
                        List.of(counted, sized), Set.of(), List.of(), Optional.empty(), Map.of())
                        .whereRowsArrive(read, List.of(), stoppedShort);
        Map<FilingCoordinate, BlockReason> left = new LinkedHashMap<>();
        both.whatEachPlaceIsLeftWith().forEach(each -> left.put(each.at(), each.why()));
        assertEquals(new BlockReason.RelationNotShownWhereTheSearchStopped(List.of(stopped)),
                left.get(FilingCoordinate.of(deals)));
        assertFalse(left.get(FilingCoordinate.of(rates))
                instanceof BlockReason.RelationNotShownWhereTheSearchStopped, left.toString());
    }

    /** How many {@code container} holds, as a term read off the position. */
    private static NumericTerm.TakenOf lengthOf(TermPath container, InputReading read) {
        Type list = read.domain().typeAt(container, read.rules());
        return NumericTerm.TakenOf.howManyHeldAt(
                NumericMeasures.takenOf(list, read.rules().inners()), container, list,
                read.rules().inners(), read.rules().symbols());
    }

    /**
     * What a run works out inside the comparison is worked out as what it works out before it is.
     * Sizes taken one more than the count and the length are worked out by an operator that may
     * end a run on what nothing here bounds, on a container the witness never held; and a step
     * written inline that walks the whole container beside reading its element — what it keeps
     * turns on the element alone — is applied on containers the witness never held. Nothing is
     * shown of either.
     */
    @Test
    void whatTheComparisonWorksOutIsHeldToWhatIsWorkedOutBeforeIt() {
        String oneMore = countedAfterALet("x.value > 2").replace(
                "List.length(kept) == List.length(xs)",
                "List.length(kept) + 1 == List.length(xs) + 1");
        String stepWalksIt = countedInline("{\n        let n = walked(xs)\n        x.value > 2 }")
                + """

                partial let walked (ys: List<Small>): Int =
                    match List.get(0, ys) with
                        | None -> 0
                        | Some first -> 1 + walked(List.drop(1, ys))
                """;
        for (String model : List.of(oneMore, stepWalksIt)) {
            Compilation compilation = reported(model);
            assertEquals(List.of(), compilation.errors(), model);
            assertEquals(NOT_SHOWN, leftIn(compilation, whereWritten(model, "== List.length("))
                    .get("List.length(xs)"), model);
        }
    }

    /**
     * A count is let through for the call the reading says it was read off, and no other. The
     * count of what a filter keeps, read off that filter, gets through. A count of the same list
     * the reading names no call for gets through nowhere: nothing then says which walk the rows
     * made of a witness are walked by.
     *
     * <p>Not the only thing that refuses it today: every operation of the language handed a
     * function is one whose ending nothing here says ({@link
     * souther.compiler.check.WhatARunMayEndFor}), so a walk the count is not named for is refused
     * as well. What is held here is that the count is let through for the walk the reading names
     * and not for whichever one is found.
     */
    @Test
    void aCountIsLetThroughOnlyForTheCallTheReadingSaysItWasReadOff() {
        CountWitnesses.Sought found = new CountWitnesses.Sought(Optional.of(
                new CountWitnesses.Witness(List.of(), 0, FixtureTemplate.integer(0),
                        FixtureTemplate.integer(1))), Set.of());
        CountWitnesses.AtComparisons always = _ -> _ -> found;
        String filtered = countedInline("x.value > 2");
        ReadComparisons read = ReadComparisons.ofTheAnalysis(filtered, "m", always);
        List<Boolean> through = new ArrayList<>();
        for (ComparisonReadings.Reading each : read.comparisons()) {
            if (each.statement() instanceof ComparisonReadings.Stated.AComparison(var comparison)) {
                Pullback.ofAComparisonOnTheInput(comparison, each.reads(),
                        read.inputs().reading(read.rules())).readOff().keySet()
                        .forEach(count -> through.add(
                                each.witnesses().of(count).found().isPresent()));
            }
        }
        assertEquals(List.of(true), through, filtered);
        Quantity.HowManyMeet namedNowhere = new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(TermPath.of("xs")),
                new Proposition.SameValue(new DecisionSubject.AnInput(TermPath.of("xs").element()),
                        new DecisionSubject.AnInput(TermPath.of("limit")), true));
        assertEquals(List.of(), read.comparisons().stream()
                .filter(each -> each.witnesses().of(namedNowhere).found().isPresent())
                .map(each -> each.at().toString()).toList(), filtered);
    }

    /** {@code source} measured as a report of what the rules say, with the rows it runs recording
     *  where they went, which a witness of a count is found by. No value is composed at a point:
     *  nothing here asks what a row at one would be. */
    private static Compilation reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.observe(RowObservation.RECORD_ARMS);
        compilation.answerEverything();
        return compilation;
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
     *  adjustment held at nought, the gross stands at every value the total takes; and the total
     *  held at nought, the gross and the adjustment stand at each other's values wherever a row is
     *  computed, which leaves out only those beside the ends of the type. */
    @Test
    void positionsBesideATotalAreAskedOfTheRelation() {
        assertEquals(Map.of("List.sum(ns[*])", RELATES, "adjustment", RELATES, "gross", RELATES),
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
     * What is said of a length is said of every position a row of it compares. With K a third of
     * the greatest {@code Int} less one, {@code i + K * List.length(xs) - (M - 1) <= 0} holds at
     * every position of a list of one or two. A list of three compares its first two positions —
     * the third passes the type, and the walk stops there — and those come out one each way. A
     * list of four passes it at its first. So the length is parted at two: a list of three is a row
     * the comparison comes out both ways in, though not every position of it computes.
     */
    @Test
    void aLengthSomeOfWhosePositionsComputeIsReadAtThose() {
        String inputs = "xs: List<Int>";
        String body = STANDING.formatted(
                "i + 3074457345618258602 * List.length(xs) - 9223372036854775806 <= 0");
        assertEquals(List.of("List.length(xs)/0 <= x <= 2", "List.length(xs)/2 < x"),
                classesAt(inputs, UNUSED, "List<Int>", body, "List.length(xs)"));
    }

    /**
     * And a line the model draws stands however long the lists at it are.
     * {@code i - List.length(xs) + M - 1 <= 0}, M the greatest {@code Int}, fails at every
     * position of a list shorter than M - 1: past two elements a list passes the type at its third
     * position, and the first two it compares come out false. Only the lists that long hold it at
     * the first, so the length is parted at M - 2. The line at M that the walk stopping draws is
     * the arithmetic's, and none of the model's.
     */
    @Test
    void aLineTheModelDrawsWhereFewPositionsComputeIsDrawn() {
        String inputs = "xs: List<Int>";
        String body = STANDING.formatted("i - List.length(xs) + 9223372036854775806 <= 0");
        assertEquals(List.of("List.length(xs)/0 <= x <= 9223372036854775805",
                        "List.length(xs)/9223372036854775805 < x"),
                classesAt(inputs, UNUSED, "List<Int>", body, "List.length(xs)"));
    }

    /** A string of two characters that is three letters, which no value is, and which the reading
     *  of the declarations does not refuse on its own. */
    private static final String NO_STRING = "data Never = String invariant String.length(value) == 2"
            + " && String.matches(\"[a-z]{3}\", value)";

    /**
     * How many a container holds is a count rows take only where an element can be written. The
     * rules on the numbers leave a list of any length, and a list of elements no value is holds
     * none: no row has a last element, so nothing is shown of the length, and no line is drawn on
     * it.
     */
    @Test
    void aCountOfElementsNoValueIsTakesNothingButNought() {
        String inputs = "xs: List<Never>";
        String body = STANDING.formatted("i == List.length(xs) - 1");
        assertEquals(List.of(), classesAt(inputs, NO_STRING, "List<Int>", body,
                "List.length(xs)"));
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, NO_STRING, "List<Int>",
                body, atThe("==", NO_STRING, inputs, body)));
    }

    /**
     * A rule reading inside the elements says how many can stand together, which no number does:
     * every element one, and no two alike, leave a box one element at most. So nothing is shown of
     * the lengths past that, and no line is drawn on them.
     */
    @Test
    void aRuleReadingInsideTheElementsLeavesHowManyTheyCanBeUnshown() {
        String box = "data Box = { xs: List<Int> }\n"
                + "    invariant List.all(x -> x == 1, xs) && List.allDistinctBy(x -> x, xs)";
        String inputs = "box: Box";
        String body = "List.mapIndexed((i, x) -> if i == List.length(box.xs) - 1 then 1 else 0,"
                + " box.xs)";
        assertEquals(Map.of("List.length(box.xs)", NOT_SHOWN), left(inputs, box, "List<Int>",
                body, atThe("==", box, inputs, body)));
    }

    /**
     * Where the step works something else out of the position, that may stop the walk at a
     * position before the comparison is reached there: {@code Int.max + i} passes the type at the
     * second. Nothing is shown.
     */
    @Test
    void aPositionWorkedOutBeforeTheComparisonLeavesTheLengthNotShown() {
        String inputs = "xs: List<Int>";
        String body = "List.mapIndexed((i, x) -> { let total = 9223372036854775807 + i\n"
                + "    if i == List.length(xs) - 1 then total else 0 }, xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>",
                body, "5:10"));
    }

    /**
     * Anything else the step works out stops the walk where it stops, made of the position or
     * not: of the element, of the length, of nothing. A position past the first is compared only
     * where the step got through at every position before, so where something says the step
     * answers only somewhere, the length is not parted. Where the way to the comparison shows no
     * row of a list holding anything gets there — past {@code Int.max} plus its length — that is
     * what is said of it.
     */
    @Test
    void anythingElseTheStepWorksOutLeavesTheLengthNotShownWhereItMayStop() {
        String inputs = "xs: List<Int>";
        for (String worked : List.of("9223372036854775807 + x",
                "9223372036854775807 + List.length(xs)", "9223372036854775807 + 1")) {
            String body = ("List.mapIndexed((i, x) -> { let total = %s\n"
                    + "    if i == List.length(xs) - 1 then total else 0 }, xs)").formatted(worked);
            Map<String, String> left = left(inputs, UNUSED, "List<Int>", body, "5:10");
            assertTrue(left.containsKey("List.length(xs)"), () -> worked + ": " + left);
        }
        String ofAnElement = "List.mapIndexed((i, x) -> { let total = 9223372036854775807 + x\n"
                + "    if i == List.length(xs) - 1 then total else 0 }, xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>",
                ofAnElement, "5:10"));
        String after = "List.mapIndexed((i, x) -> (if i == List.length(xs) - 1 then 1 else 0)"
                + " + (9223372036854775807 + x), xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>",
                after, atThe("==", UNUSED, inputs, after)));
    }

    /**
     * Where nothing says where it stops — a product of two values nothing bounds — the length is
     * read, and what may stop the walk is on the way to the comparison as what may stop a run
     * there, which is where it is for a comparison anywhere else.
     */
    @Test
    void aStepNothingSaysWhereItStopsIsReadAndMayStopOnTheWay() {
        String inputs = "xs: List<Int>";
        String body = "List.mapIndexed((i, x) -> (if i == List.length(xs) - 1 then 1 else 0)"
                + " + x * x, xs)";
        assertEquals(Map.of(), left(inputs, UNUSED, "List<Int>", body,
                atThe("==", UNUSED, inputs, body)));
    }

    /**
     * And after it: the second position compares and then stops the walk, so no position past it
     * is compared.
     */
    @Test
    void aPositionWorkedOutAfterTheComparisonLeavesTheLengthNotShown() {
        String inputs = "xs: List<Int>";
        String body = "List.mapIndexed((i, x) -> (if i == List.length(xs) - 1 then 1 else 0)"
                + " + (9223372036854775807 + i), xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>",
                body, atThe("==", UNUSED, inputs, body)));
    }

    /** A list of one value over again, counted for how often it occurs, is no row either where the
     *  value is none: no bar is parted by it. */
    @Test
    void howOftenAValueNoValueIsOccursTakesNothing() {
        assertEquals(List.of(), classesAt("issues: List<Issue>, atLeast: Int",
                LABELLED.replace("Set<String>", "Set<Never>")
                        .replace("Set.toList(i.labels)", "List.map(l -> l.value, Set.toList(i.labels))")
                        + "\n" + NO_STRING, BUSY, "atLeast"));
    }

    /**
     * A way stating something of where the element stands picks some positions out as a way
     * stating something of the elements does: under {@code i > 0} a list of one never reaches the
     * comparison, and a list of two reaches it at its last position only. Nothing is shown.
     */
    @Test
    void aWayStatingWhereTheElementStandsLeavesTheLengthNotShown() {
        String inputs = "xs: List<Int>";
        String body = "List.mapIndexed((i, x) -> if i > 0 then (if i == List.length(xs) - 1"
                + " then 1 else 0) else 0, xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Int>", body,
                atThe("==", UNUSED, inputs, body)));
    }

    /**
     * Where the step reads the position is asked of the one account of what runs when: in an arm
     * of a match, or on the right of an operator that stops once its answer is settled, it is read
     * at the applications that get there, and nothing is shown; in the body of a {@code let} it is
     * read whenever the step runs, and the length is parted as with no {@code let} around it.
     */
    @Test
    void aPositionReadInAnArmIsReadAtTheApplicationsThatEnterIt() {
        String inputs = "xs: List<Int>";
        String places = "data Later = { at: Int }\ndata First = { at: Int }\n"
                + "data Place = Later | First";
        String inAnArm = "List.mapIndexed((i, x) -> match (if i > 0 then Later { at = i } else"
                + " First { at = i }) with | Later -> (if i == List.length(xs) - 1 then 1 else 0)"
                + " | First -> 0, xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, places, "List<Int>",
                inAnArm, atThe("== List", places, inputs, inAnArm)));
    }

    /** The same on the right of an operator that stops once its answer is settled. */
    @Test
    void aPositionReadOnTheRightOfAStopEarlyOperatorIsReadWhereTheLeftLetsItRun() {
        String inputs = "xs: List<Int>";
        String onTheRight = "List.mapIndexed((i, x) -> x > 0 && i == List.length(xs) - 1, xs)";
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN), left(inputs, UNUSED, "List<Bool>",
                onTheRight, atThe("== List", UNUSED, inputs, onTheRight)));
    }

    /** And in the body of a {@code let}, which runs whenever the step does. */
    @Test
    void aPositionReadInTheBodyOfALetIsReadWheneverTheStepRuns() {
        String inputs = "xs: List<Int>";
        String inALet = "List.mapIndexed((i, x) -> { let last = List.length(xs) - 1\n"
                + "    if i == last then 1 else 0 }, xs)";
        assertEquals(List.of("List.length(xs)/0 <= x <= 1", "List.length(xs)/1 < x"),
                classesAt(inputs, UNUSED, "List<Int>", inALet, "List.length(xs)"));
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

    /** A rate a dependency keeps for each kind, and the one in force on a day. */
    private static final String RATED = """
            module w1
            data Change = { from: Int, rate: Int }
            behavior changesOf : (kind: Int) -> List<Change>
            let rateAsOf (changes: List<Change>, on: Int): Option<Int> =
                Option.map(c -> c.rate, List.find(c -> c.from <= on, changes))
            behavior m : (xs: List<Int>, kind: Int, on: Int) -> List<Int>
                depends on changesOf
            let m (xs, kind, on, changesOf) =
                match rateAsOf(changesOf(kind), %s) with
                    | Some r -> List.mapIndexed((i, x) -> if i == List.length(xs) - 1 then r else 0, xs)
                    | None -> []
            """;

    /**
     * The arm a rate is found in is entered by what the dependency answered and the day asked
     * about, which no row writes and nothing here takes in. That says nothing of the list the
     * comparison inside it is about: the day is another parameter, and no declaration relates one
     * parameter to another, so the list is parted at one as it is with no arm around it. Asked
     * about the list's own length, the arm says something of the list nothing reads, and nothing
     * is shown.
     */
    @Test
    void anArmADependencysAnswerEntersLeavesTheParametersItNamesNothingOfAsTheyWere() {
        String onADay = RATED.formatted("on");
        assertEquals(List.of("List.length(xs)/0 <= x <= 1", "List.length(xs)/1 < x"),
                classesIn(onADay, "List.length(xs)"));
        assertEquals(Map.of(), leftIn(onADay, whereWritten(onADay, "== List")));
        String onTheLength = RATED.formatted("List.length(xs)");
        assertEquals(Map.of("List.length(xs)", NOT_SHOWN),
                leftIn(onTheLength, whereWritten(onTheLength, "== List")));
    }

    /** Where {@code text} is first written in {@code source}, as a report names a place. */
    private static String whereWritten(String source, String text) {
        List<String> lines = source.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int column = lines.get(i).indexOf(text);
            if (column >= 0) {
                return (i + 1) + ":" + (column + 1);
            }
        }
        throw new IllegalArgumentException("`" + text + "` is not written in the model");
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
        assertEquals(Map.of(), left("a: Stage, b: Stage", stage, "a < b", "4:18"));
        assertEquals(Map.of(),
                left("a: Stage, b: Stage", stage, "if a <= b then a < b else false", "4:33"));
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Stage, b: Stage", stage, "a == b", "4:18"));
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("a: String, b: String", stage, "a < b", "4:18"));
        assertEquals(Map.of(), left("a: Time, b: Time", stage, "a < b", "4:18"));
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

    /** Five choices of two ways each on values no relation below reads: thirty-two ways
     *  together, more than a way is looked along each of. */
    private static final String FIVE_APART = "(b1 || c1) && (b2 || c2) && (b3 || c3)"
            + " && (b4 || c4) && (b5 || c5)";

    private static final String THE_FIVE = ", b1: Bool, c1: Bool, b2: Bool, c2: Bool,"
            + " b3: Bool, c3: Bool, b4: Bool, c4: Bool, b5: Bool, c5: Bool";

    /**
     * The words the comparison {@code comparison} leaves each place with, under {@code guard} —
     * and, where {@code beside} is true, under the five choices apart as well.
     */
    private static Map<String, String> leftPast(String inputs, String declarations, String guard,
                                                String comparison, boolean beside) {
        String taking = beside ? inputs + THE_FIVE : inputs;
        String body = "if " + (beside ? FIVE_APART + " && " : "") + guard + " then " + comparison
                + " else false";
        int at = ("let m (" + taking.replaceAll(": [A-Za-z<>]+", "") + ") = ").length()
                + body.indexOf(comparison) + comparison.indexOf("==") + 1;
        return left(taking, declarations, body, "4:" + at);
    }

    /**
     * A way past more choices than are looked along is read, for a relation, as what the choices
     * leave the values it reads: ways that differ only in values it does not read are one way to
     * it. With five choices on {@code Bool}s beside it, {@code x == y} leaves each where it does
     * without them — and so it does with a choice one of whose ways asks for an {@code Int} no
     * value is, where the other is met.
     */
    @Test
    void aWayPastTheFigureIsReadAsWhatItLeavesTheValuesTheRelationReads() {
        Map<String, String> free = Map.of("x", RELATES, "y", RELATES);
        assertEquals(free, leftPast("x: Int, y: Int", "data Unused = Int", "true", "x == y",
                true));
        assertEquals(free, leftPast("x: Int, y: Int, z: Int, w: Bool", "data Unused = Int",
                "(z > 0 && z < 1 || w)", "x == y", true));
    }

    /**
     * A way open is not a way some value takes. Where the only way of a choice asking nothing of
     * what the relation reads asks for an {@code Int} above nought and below one, no row takes
     * it, so a row past the choice holds {@code x} at five or more and {@code y} below five never
     * stands beside one: the choice is kept as it is, and read as it is without the five beside
     * it. So it is where what holds the value out is written on the way beside the choice.
     */
    @Test
    void aChoiceWhoseWayApartNoValueIsShownToMeetIsKeptAsItIs() {
        for (String apart : List.of("z > 0 && z < 1",
                "z >= 0 && z <= 1 && z /= 0 && z /= 1")) {
            String guard = "(" + apart + " || x >= 5)";
            Map<String, String> alone = leftPast("x: Int, y: Int, z: Int, v: Int",
                    "data Unused = Int", guard, "x == y", false);
            assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone, apart);
            assertEquals(alone, leftPast("x: Int, y: Int, z: Int, v: Int", "data Unused = Int",
                    guard, "x == y", true), apart);
        }
        String heldOutOnTheWay = "(z >= 0 && z <= 1 || x >= 5) && z /= 0 && z /= 1";
        Map<String, String> alone = leftPast("x: Int, y: Int, z: Int", UNUSED, heldOutOnTheWay,
                "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone);
        assertEquals(alone, leftPast("x: Int, y: Int, z: Int", UNUSED, heldOutOnTheWay, "x == y",
                true), "and so where what holds it out is on the way beside the choice");
    }

    /**
     * A value held out is passed over for the next: {@code z /= 0} is met at one, and
     * {@code z + w /= 0} at nought and one, so past the five a choice with such a way apart comes
     * to nothing for {@code x == y}, which leaves each where it does with no condition at all. So
     * do five such choices on a way of their own, past the figure without anything beside them.
     */
    @Test
    void aValueAWayApartHoldsOutIsPassedOverForTheNext() {
        String inputs = "x: Int, y: Int, z: Int, w: Int";
        Map<String, String> free = leftPast(inputs, UNUSED, "true", "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", RELATES), free);
        for (String apart : List.of("z /= 0", "z /= 0 && z /= 1", "z + w /= 0")) {
            assertEquals(free, leftPast(inputs, UNUSED, "(" + apart + " || x >= 5)", "x == y",
                    true), apart);
        }

        String fiveOfTheirOwn = "x: Int, y: Int, z1: Int, z2: Int, z3: Int, z4: Int, z5: Int";
        String each = "(z1 /= 0 || x >= 5) && (z2 /= 0 || x >= 5) && (z3 /= 0 || x >= 5)"
                + " && (z4 /= 0 || x >= 5) && (z5 /= 0 || x >= 5)";
        assertEquals(leftPast(fiveOfTheirOwn, UNUSED, "true", "x == y", false),
                leftPast(fiveOfTheirOwn, UNUSED, each, "x == y", false));
    }

    /**
     * A way read again for a relation is read for it alone. Past the five, {@code (z >= 1 || w)}
     * written twice comes to nothing for {@code x == y}, which leaves each where it does with no
     * condition at all — and each writing is still a condition of its own, owed a row at each
     * point of its line.
     */
    @Test
    void aConditionWrittenTwiceOnAWayReadAgainIsOwedAtEachWriting() {
        String inputs = "x: Int, y: Int, z: Int, w: Bool" + THE_FIVE;
        String body = "if (z >= 1 || w) && " + FIVE_APART + " && (z >= 1 || w) then x == y"
                + " else false";
        int from = ("let m (" + inputs.replaceAll(": [A-Za-z<>]+", "") + ") = ").length() + 1;
        Compilation compilation = measured(inputs, UNUSED, "Bool", body);
        assertEquals(Map.of("x", RELATES, "y", RELATES),
                leftIn(compilation, "4:" + (from + body.indexOf("=="))));
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        for (int writing : List.of(body.indexOf(">="), body.lastIndexOf(">="))) {
            String at = "point (comparison@4:" + (from + writing) + ")";
            assertEquals(List.of("ON", "OFF", "IN", "OUT"), report.lines()
                    .filter(line -> line.contains("whether a row is at the ") && line.contains(at))
                    .map(line -> line.substring(line.indexOf("at the ") + 7,
                            line.indexOf(" point")))
                    .toList(), at);
        }
    }

    /**
     * A value given a number apart is one its type holds. {@code z + w} at the greatest
     * {@code Int} with {@code w} at minus one puts {@code z} one past it, which no {@code Int} is,
     * so no row takes that way and the choice is kept as it is, read as it is without the five.
     */
    @Test
    void aValueGivenANumberApartIsOneItsTypeHolds() {
        String inputs = "x: Int, y: Int, z: Int, w: Int";
        String guard = "(z + w == 9223372036854775807 && w == -1 || x >= 5)";
        Map<String, String> alone = leftPast(inputs, UNUSED, guard, "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone);
        assertEquals(alone, leftPast(inputs, UNUSED, guard, "x == y", true));
    }

    /**
     * Numbers a way apart fixes together are worked out from one another: {@code z + w == 2}
     * puts {@code z} at {@code 2 - w}, so {@code z - w == 0} puts {@code w} at one. A choice with
     * such a way apart comes to nothing for {@code x == y} past the five. Where no whole numbers
     * are fixed so — {@code z} and {@code w} a half each, or {@code z} half an odd number once
     * {@code w} and {@code v} are one value — it is kept as it is, and read as it is without the
     * five.
     */
    @Test
    void numbersAWayApartFixesTogetherAreWorkedOutFromOneAnother() {
        String inputs = "x: Int, y: Int, z: Int, w: Int, v: Int";
        Map<String, String> free = leftPast(inputs, UNUSED, "true", "x == y", false);
        for (String apart : List.of("z + w == 2 && z - w == 0",
                "z + w == 2 && w + v == 2 && z + v == 2", "2 * z + 3 * w == 7 && z - w == 1")) {
            assertEquals(free, leftPast(inputs, UNUSED, "(" + apart + " || x >= 5)", "x == y",
                    true), apart);
        }
        for (String apart : List.of("z + w == 1 && z - w == 0",
                "2 * z + w + v == 1 && w - v == 0")) {
            String guard = "(" + apart + " || x >= 5)";
            Map<String, String> alone = leftPast(inputs, UNUSED, guard, "x == y", false);
            assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone, apart);
            assertEquals(alone, leftPast(inputs, UNUSED, guard, "x == y", true), apart);
        }
    }

    /**
     * Numbers a way apart bounds together are given values where the bounds together leave them.
     * {@code z + w} at two or more and at two or less, and {@code z - w} at nought or more and at
     * nought or less, put each at one, though no one of the four does: such a choice comes to
     * nothing for {@code x == y} past the five, as it does written with two equalities, however the
     * bounds are written and in whatever order, and so it does with {@code 2z + 3w} held at five
     * from both sides. Where the bounds together leave no whole numbers — {@code z + w} above
     * nought and below one, or {@code z} one past every {@code Int} — or a value they leave is held
     * out, the choice is kept as it is, and read as it is without the five.
     */
    @Test
    void numbersAWayApartBoundsTogetherAreGivenValuesWhereTheBoundsTogetherLeaveThem() {
        String inputs = "x: Int, y: Int, z: Int, w: Int, v: Int";
        Map<String, String> free = leftPast(inputs, UNUSED, "true", "x == y", false);
        for (String apart : List.of("z + w >= 2 && z + w <= 2 && z - w >= 0 && z - w <= 0",
                "z - w <= 0 && z + w <= 2 && z - w >= 0 && z + w >= 2",
                "2 - w <= z && z + w < 3 && w - z <= 0 && z <= w",
                "2 * z + 3 * w >= 5 && 2 * z + 3 * w <= 5 && 3 * z - 3 * w >= 0 && z <= w")) {
            assertEquals(free, leftPast(inputs, UNUSED, "(" + apart + " || x >= 5)", "x == y",
                    true), apart);
        }
        for (String apart : List.of("z + w > 0 && z + w < 1",
                "z - w >= 9223372036854775807 && z - w <= 9223372036854775807 && w >= 1",
                "z + w >= 2 && z + w <= 2 && z - w >= 0 && z - w <= 0 && z + 2 * w /= 3")) {
            String guard = "(" + apart + " || x >= 5)";
            Map<String, String> alone = leftPast(inputs, UNUSED, guard, "x == y", false);
            assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone, apart);
            assertEquals(alone, leftPast(inputs, UNUSED, guard, "x == y", true), apart);
        }
    }

    /** Four choices of two ways each on numbers a way apart holds below {@code z}: sixteen ways
     *  together, which beside a choice of two that bear on {@code x} are more than a way is looked
     *  along each of. */
    private static final String BELOW_Z = " && w1 <= z + 100 && w2 <= z + 100"
            + " && w3 <= z + 100 && w4 <= z + 100 && (w1 <= 0 || w1 >= 1) && (w2 <= 0 || w2 >= 1)"
            + " && (w3 <= 0 || w3 >= 1) && (w4 <= 0 || w4 >= 1)";

    private static final String WITH_Z = "x: Int, y: Int, z: Int, w1: Int, w2: Int, w3: Int,"
            + " w4: Int";

    /**
     * Where every way of a choice names what the relation reads and what it does not, each way
     * is met apart by a value of its own: no {@code z} is at or below nought and at twenty or
     * above, and each alternative of {@code (x <= 0 && z <= 0 || x >= 10 && z >= 20)} has its
     * own beside the choices below {@code z}. So the choice comes to its parts naming {@code x},
     * and the way to what {@code (x <= 0 || x >= 10)} leaves.
     */
    @Test
    void eachWayOfAChoiceIsMetApartByAValueOfItsOwn() {
        Map<String, String> named = leftPast(WITH_Z, UNUSED, "(x <= 0 || x >= 10)", "x == y",
                false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), named);
        assertEquals(named, leftPast(WITH_Z, UNUSED,
                "(x <= 0 && z <= 0 || x >= 10 && z >= 20)" + BELOW_Z, "x == y", false));
    }

    /**
     * A way of taking two choices' alternatives together that no row takes asks nothing of the
     * values apart: past {@code (x <= 0 && z <= 0 || x >= 10 && z >= 20)} and
     * {@code (x <= 3 && z <= 0 || x >= 7 && z >= 20)}, no {@code z} is at or below nought and at
     * twenty or above, and no {@code x} at or below nought and at seven or above either.
     */
    @Test
    void aWayOfTheAlternativesNoRowTakesAsksNoValueApart() {
        Map<String, String> named = leftPast(WITH_Z, UNUSED,
                "(x <= 0 || x >= 10) && (x <= 3 || x >= 7)", "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), named);
        assertEquals(named, leftPast(WITH_Z, UNUSED, "(x <= 0 && z <= 0 || x >= 10 && z >= 20)"
                + " && (x <= 3 && z <= 0 || x >= 7 && z >= 20)" + BELOW_Z, "x == y", false));
    }

    /**
     * A choice on a place the declarations tie to one the relation reads bears on the relation,
     * and so does one on a place tied to it through another the way relates both to: the choice
     * on {@code z} is read as it is, past the five as without them.
     */
    @Test
    void aChoiceOnAPlaceTiedToTheRelationsIsReadAsItIs() {
        String tied = "data P = { x: Int, z: Int } invariant x <= z";
        for (String onZ : List.of("(p.z <= 3 || p.z >= 10)", "p.z <= 3")) {
            Map<String, String> byTheRule = leftPast("p: P, y: Int", tied, onZ, "p.x == y",
                    false);
            assertEquals(Map.of("p.x", RELATES, "y", NOT_SHOWN), byTheRule, onZ);
            assertEquals(byTheRule, leftPast("p: P, y: Int", tied, onZ, "p.x == y", true), onZ);
        }

        String through = "w <= z && x <= w && (z <= 3 || z >= 10)";
        Map<String, String> onTheWay = leftPast("x: Int, y: Int, w: Int, z: Int",
                "data Unused = Int", through, "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), onTheWay);
        assertEquals(onTheWay, leftPast("x: Int, y: Int, w: Int, z: Int", "data Unused = Int",
                through, "x == y", true));
    }

    /**
     * A choice naming what the relation reads and what it does not comes to the first, where a
     * value is shown to meet the second: past {@code !(x >= 70 && a && !d)}, {@code a} false
     * lets every {@code x} through, so {@code y} reaches every value as {@code x} does. Where no
     * value is — a number held at nought or above is never below it — the choice still keeps
     * {@code x} below seventy, and {@code y} from seventy on stands beside no {@code x}. And
     * where every way of it names both, it comes to the parts naming {@code x}, each a way of
     * its own: {@code x} from seventy or up to ten, and no {@code x} between for {@code y}.
     */
    @Test
    void aChoiceNamingBothComesToWhatItLeavesTheRelationOnlyWhereTheRestIsMet() {
        assertEquals(Map.of("x", RELATES, "y", RELATES),
                leftPast("x: Int, y: Int, a: Bool, d: Bool", "data Unused = Int",
                        "Bool.not(x >= 70 && a && Bool.not(d))", "x == y", true));
        String eachNamesBoth = "(x >= 70 && a || x <= 10 && d)";
        Map<String, String> alone = leftPast("x: Int, y: Int, a: Bool, d: Bool",
                "data Unused = Int", eachNamesBoth, "x == y", false);
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN), alone);
        assertEquals(alone, leftPast("x: Int, y: Int, a: Bool, d: Bool", "data Unused = Int",
                eachNamesBoth, "x == y", true));
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN),
                leftPast("x: Int, y: Int, z: N", "data N = Int invariant value >= 0",
                        "Bool.not(x >= 70 && z.value >= 0)", "x == y", true));
    }

    /**
     * A condition nothing was read of may hold anything beside anything, so a way with one on it
     * is not read as less than it is: the relation is shown nothing of past the five, as it is
     * without them.
     */
    @Test
    void aWayWithAConditionNothingWasReadOfIsNotReadAsLess() {
        String guard = "(String.startsWith(\"a\", s) || w)";
        Map<String, String> alone = leftPast("x: Int, y: Int, s: String, w: Bool",
                "data Unused = Int", guard, "x == y", false);
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN), alone);
        assertEquals(alone, leftPast("x: Int, y: Int, s: String, w: Bool", "data Unused = Int",
                guard, "x == y", true));
    }

    /**
     * Ways that leave the relation's values apart are each still a way to it: past the five, the
     * choices on {@code x} and {@code y} are proved along every way of taking them together, as
     * {@link #choicesOnPlacesApartAreProvedAlongEveryWayOfTakingThemTogether} has them without.
     * And ways more than are looked along that each leave the relation's values something of
     * their own are shown nothing of, as before.
     */
    @Test
    void waysLeavingTheRelationsValuesApartAreStillApart() {
        String guard = "(x >= 0 && x <= 10 || x >= 20 && x <= 30)"
                + " && (y >= 0 && y <= 30 || y >= 0 && y <= 25)";
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                leftPast("x: Int, y: Int", "data Unused = Int", guard, "x == y", true));
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN),
                leftPast("x: Int, y: Int", "data Unused = Int", guard.replace("y <= 25", "y <= 10"),
                        "x == y", true));

        String eachItsOwn = "(x1 >= 0 || x1 <= -5) && (x2 >= 0 || x2 <= -5)"
                + " && (x3 >= 0 || x3 <= -5) && (x4 >= 0 || x4 <= -5) && (x5 >= 0 || x5 <= -5)";
        Map<String, String> summed = leftPast("x1: Int, x2: Int, x3: Int, x4: Int, x5: Int, y: Int",
                "data Unused = Int", eachItsOwn, "x1 + x2 + x3 + x4 + x5 == y", true);
        assertEquals(Map.of("x1", NOT_SHOWN, "x2", NOT_SHOWN, "x3", NOT_SHOWN, "x4", NOT_SHOWN,
                "x5", NOT_SHOWN, "y", NOT_SHOWN), summed);
    }

    /**
     * Where a relation is shown nothing of a way past the figure, the figure is why, and the
     * relation says so: a run allowed more ways would split the way and read each. Five choices on
     * what {@code x1 + x2 + x3 + x4 + x5 == y} reads are thirty-two ways, each of which bears on
     * it. Where every way is looked along and a way leaves a value no row beside it reaches, no
     * figure is why, and none is named.
     */
    @Test
    void aRelationShownNothingOfAWayPastTheFigureSaysTheFigureStoppedIt() {
        String figure = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.counts();
        String inputs = "x1: Int, x2: Int, x3: Int, x4: Int, x5: Int, y: Int";
        String body = "if (x1 >= 0 || x1 <= -5) && (x2 >= 0 || x2 <= -5) && (x3 >= 0 || x3 <= -5)"
                + " && (x4 >= 0 || x4 <= -5) && (x5 >= 0 || x5 <= -5)"
                + " then x1 + x2 + x3 + x4 + x5 == y else false";
        List<String> past = linesAbout(measured(inputs, UNUSED, "Bool", body), "x1");
        assertFalse(past.isEmpty());
        assertTrue(past.stream().allMatch(line -> line.contains(figure)), past::toString);

        String within = "if (x >= 0 && x <= 10 || x >= 20 && x <= 30) then x == y else false";
        List<String> about = linesAbout(measured("x: Int, y: Int", UNUSED, "Bool", within), "y");
        assertFalse(about.isEmpty());
        assertTrue(about.stream().noneMatch(line -> line.contains("stopped at")), about::toString);
    }

    /** The lines of a report about {@code place} that say it was not read. */
    private static List<String> linesAbout(Compilation compilation, String place) {
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(
                        compilation.texts())).lines().map(String::strip)
                .filter(line -> line.startsWith("· not read") && line.endsWith("about `" + place + "`"))
                .toList();
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

    private static final String HOURS =
            "data Hours = Decimal invariant value >= 0.0m && value <= 168.0m";

    /**
     * Weighed by four, hours from nought to 168 reach every standard below four times them and
     * every one from it, and run out at 42: from there on no standard is above four times them.
     * A standard past nought has hours below a quarter of it, which a decimal from nought has, so
     * only the standard of nought settles the comparison. Weighed three to four, the hours run out
     * at 126.
     */
    @Test
    void aWeightOnADecimalDrawsTheLineWhereTheOtherRunsOut() {
        String inputs = "h: Hours, s: Hours";
        for (String body : List.of("h.value * 4.0m >= s.value",
                "h.value * 4.0m >= s.value * 3.0m")) {
            assertEquals(Map.of(), left(inputs, HOURS, body, atThe(">=", HOURS, inputs, body)),
                    body);
            assertEquals(List.of("s/0 <= x <= 0", "s/0 < x <= 168"),
                    classesAt(inputs, HOURS, body, "s"), body);
        }
        assertEquals(List.of("h/0 <= x < 42", "h/42 <= x <= 168"),
                classesAt(inputs, HOURS, "h.value * 4.0m >= s.value", "h"));
        assertEquals(List.of("h/0 <= x < 126", "h/126 <= x <= 168"),
                classesAt(inputs, HOURS, "h.value * 4.0m >= s.value * 3.0m", "h"));
    }

    /**
     * Weighed by two, an amount past half the greatest {@code Int} has no row at all, its double
     * past the type, and every amount before it has an insured amount at its double and one above:
     * the revenue is related and the line is the arithmetic's. The greatest insured amount is
     * above every double a row has, so it settles the comparison on its own, and is a class of
     * its own beside the ones before it. Beside an insured amount not shown to take every value
     * between its ends, nothing is shown of the revenue.
     */
    @Test
    void aWeightOnAWholeNumberLeavesTheValuesPastHalfTheTypeToTheArithmetic() {
        String yen = "data Yen = Int invariant value >= 0";
        String body = "r.value * 2 >= i.value";
        assertEquals(Map.of("r", RELATES),
                left("r: Yen, i: Yen", yen, body, atThe(">=", yen, "r: Yen, i: Yen", body)));
        assertEquals(List.of("i/0 <= x <= 0", "i/0 < x < 9223372036854775807",
                        "i/9223372036854775807 <= x"),
                classesAt("r: Yen, i: Yen", yen, body, "i"));
        String gap = yen + "\ndata Gap = Int invariant value <= 10 || value >= 20";
        assertEquals(NOT_SHOWN, left("r: Yen, i: Gap", gap, body,
                atThe(">=", gap, "r: Yen, i: Gap", body)).get("r"));
    }

    /**
     * Asked where an earlier comparison of the same two left {@code w <= t}, {@code t > w} is about
     * how far apart they are, and the earlier one keeps them nought apart or more. A tax of nought
     * has only a withholding of nought, and fails; every other has one below it and one at it, and
     * every withholding has a tax at it and one above. Held apart by anything but their difference
     * the two are not read so. And along {@code w >= t} with {@code w} held to ten, the way
     * holds {@code t} to ten as well: a tax past it takes the other way, and the one at ten has
     * no withholding above it. The earlier comparison draws its own lines on the tax beside
     * that: at nought, below which no withholding is, and from eleven, where every one is below.
     */
    @Test
    void aComparisonUnderTheArmOfAnEarlierOneOfTheSameTwoIsReadOfTheirDifference() {
        String yen = "data Yen = Int invariant value >= 0";
        String inputs = "t: Yen, w: Yen";
        String body = "if w.value > t.value then false else t.value > w.value";
        assertEquals(Map.of("w", RELATES),
                left(inputs, yen, body, atThe("> w.value", yen, inputs, body)));
        assertEquals(List.of("t/0 <= x <= 0", "t/0 < x"), classesAt(inputs, yen, body, "t"));
        String twice = "if w.value > 2 * t.value then false else t.value > w.value";
        assertEquals(Map.of("t", NOT_SHOWN, "w", NOT_SHOWN),
                left(inputs, yen, twice, atThe("> w.value", yen, inputs, twice)));
        String small = yen + "\ndata Small = Int invariant value >= 0 && value <= 10";
        String kept = "if w.value < t.value then false else w.value > t.value";
        assertEquals(Map.of(), left("t: Yen, w: Small", small, kept,
                atThe("> t.value", small, "t: Yen, w: Small", kept)));
        assertEquals(List.of("t/0 <= x <= 0", "t/0 < x < 10", "t/10 <= x < 11", "t/11 <= x"),
                classesAt("t: Yen, w: Small", small, kept, "t"));
    }

    /**
     * Along the arm where an allowance is above its cap, the cap stands in for it on one side and
     * the allowance on the other, so the two do not cancel: {@code a + c - s - 150000 >= 0} with
     * {@code c} from 150001. Held there, {@code c} leaves {@code a} against {@code s} one apart,
     * and each {@code a} has an {@code s} at one above it and two above it. Where nothing shows the
     * allowance takes a value above its cap, nothing is shown of {@code a} along that arm.
     */
    @Test
    void aTermHeldAboveItsCapAlongAnArmIsHeldWhereItStarts() {
        String capped = """
                module w1
                data Yen = Int invariant value >= 0
                %s
                behavior m : (a: Yen, c: %s, s: Yen) -> Bool
                let m (a, c, s) = {
                    let capped = if c.value > 150000 then 150000 else c.value
                    a.value + c.value >= capped + s.value
                }
                """;
        String written = capped.formatted("data Unused = Int", "Yen");
        String at = "7:" + (written.lines().toList().get(6).indexOf(">=") + 1);
        assertEquals(Set.of(), notReadIn(written, at));
        assertEquals(RELATES, leftIn(written, at).get("a"));
        String unshown = capped.formatted(
                "data Gap = Int invariant value <= 150000 || Int.floorMod(value, 2) == 0", "Gap");
        assertTrue(notReadIn(unshown, at).contains("a"), () -> notReadIn(unshown, at).toString());
    }

    /**
     * A premise nothing proves, over positions none of the sum's are related to, leaves the sum's
     * positions the runs their ends give them: it bounds nothing of them, and some row holds it.
     * The sum is then read as beside a premise that is proved.
     */
    @Test
    void aPremiseNothingProvesOverOtherPositionsLeavesASumItsRun() {
        String declared = HOURS + "\ndata Yen = Int invariant value >= 0"
                + "\ndata Rem = { base: Yen, sched: Yen }";
        String inputs = "h: Hours, s: Hours, r: Rem";
        for (String premise : List.of("h.value * 4.0m >= s.value * 3.0m", "h.value >= 30.0m")) {
            String body = "if " + premise + " then false"
                    + " else r.base.value + r.sched.value < 88000";
            assertEquals(Map.of(), left(inputs, declared, body,
                    atThe("< 88000", declared, inputs, body)), premise);
        }
    }

    /**
     * A way only values past the greatest {@code Int} take leaves no row to the comparison behind
     * it, so the amounts there are not shown to reach each other: {@code a - b >= M} beside
     * {@code b >= 1}, which the box and its differences prove, and {@code a - 2b >= M - 1} beside
     * it, which nothing proves, are each held by an {@code a} past {@code M} alone. A way some
     * pair of {@code Int}s holds leaves the amounts every value they take.
     */
    @Test
    void aWayOnlyValuesPastTheirTypeTakeLeavesNoRowToReachAnything() {
        String yen = "data Yen = Int invariant value >= 0";
        String inputs = "a: Int, b: Int, x: Yen, y: Yen";
        for (String way : List.of("b >= 1 && a - b >= 9223372036854775807",
                "b >= 1 && a - 2 * b >= 9223372036854775806")) {
            String body = "if " + way + " then x.value >= y.value else false";
            assertEquals(NOT_SHOWN, left(inputs, yen, body,
                    atThe(">= y.value", yen, inputs, body)).get("x"), way);
        }
        String some = "if b >= 1 && a - 2 * b >= 9223372036854775805 then x.value >= y.value"
                + " else false";
        assertEquals(RELATES, left(inputs, yen, some, atThe(">= y.value", yen, inputs, some))
                .get("x"));
    }

    /**
     * And of a behavior over such a declaration: no {@code D} is held by two lists further apart
     * than the greatest {@code Int}, so it is refused, and nothing the body compares is said to
     * reach anything. One less apart, a list of the greatest length beside one of one holds it,
     * and the amounts relate.
     */
    @Test
    void aDeclarationOnlyLengthsPastWhereAnIntStopsHoldLeavesABehaviorNoRowToReachAnything() {
        for (String apart : List.of("9223372036854775807", "9223372036854775806")) {
            String declared = """
                    data Yen = Int invariant value >= 0
                    data D = { g: Yen, d: Yen, ys: List<Int>, zs: List<Int> }
                        invariant List.length(zs) >= 1
                            && List.length(ys) - List.length(zs) >= %s""".formatted(apart);
            String body = "v.g.value >= v.d.value";
            boolean none = apart.endsWith("7");
            assertEquals(none ? List.of("E1013") : List.of(), measured("v: D", declared, "Bool",
                    body).diagnostics().values().stream().flatMap(List::stream)
                    .map(each -> each.diagnostic().code().toString()).toList(), apart);
            assertEquals(none ? Map.of() : Map.of("v.g", RELATES), left("v: D", declared, body,
                    atThe(">=", declared, "v: D", body)), apart);
        }
    }

    /**
     * The same of a declaration's rules over lengths, since a length is an {@code Int} and stops
     * where one does: {@code List.length(ys) - List.length(zs) >= M} beside
     * {@code List.length(zs) >= 1} is held by no two lists, so the amounts the rule beside it
     * relates are not shown to reach each other. One less than {@code M} is held by a list of
     * {@code M} beside a list of one.
     */
    @Test
    void aRuleOnlyLengthsPastWhereAnIntStopsHoldLeavesNoRowToReachAnything() {
        for (String apart : List.of("9223372036854775807", "9223372036854775806")) {
            Compilation compilation = Compilation.ofSource("""
                    module w1
                    data Yen = Int invariant value >= 0
                    data D = { g: Yen, d: Yen, ys: List<Int>, zs: List<Int> }
                        invariant g.value >= d.value && List.length(zs) >= 1
                            && List.length(ys) - List.length(zs) >= %s
                    behavior m : (x: D) -> Bool
                    let m (x) = true
                    """.formatted(apart), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String report = AdequacyReport.of(compilation)
                    .human(SourceRendering.namedByIdentity(compilation.texts()));
            String said = apart.endsWith("7") ? "not shown to reach every value here"
                    : "it relates the value here to another value rather than dividing";
            for (String place : List.of("x.g", "x.d")) {
                assertTrue(report.lines().anyMatch(line -> line.contains("invariant D #1")
                        && line.contains(said) && line.endsWith("about `" + place + "`")),
                        apart + "\n" + report);
            }
        }
    }

    /**
     * Over decimals from nought, {@code a >= s + 5}: every {@code s} has an {@code a} at five
     * above it and one below, the {@code a} needed running on without end on an order that has
     * none, and an {@code a} below five holds it for no {@code s}.
     */
    @Test
    void aDecimalRunsOnPastEveryValueAnotherIsNeededAt() {
        String amount = "data Amount = Decimal invariant value >= 0.0m";
        String body = "a.value >= s.value + 5.0m";
        assertEquals(Map.of("s", RELATES), left("a: Amount, s: Amount", amount, body,
                atThe(">=", amount, "a: Amount, s: Amount", body)));
        assertEquals(List.of("a/0 <= x < 5", "a/5 <= x"),
                classesAt("a: Amount, s: Amount", amount, body, "a"));
    }

    /** The places some comparison at {@code at} of a model written out whole is not read about. */
    private static Set<String> notReadIn(String source, String at) {
        Compilation compilation = measured(source);
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Set<String> out = new TreeSet<>();
        for (String line : report.lines().map(String::strip).toList()) {
            if (line.startsWith("· not read") && line.contains("comparison@" + at + " ")
                    && line.contains("about `")) {
                out.add(line.substring(line.lastIndexOf("about `") + 7, line.length() - 1));
            }
        }
        return out;
    }
}
