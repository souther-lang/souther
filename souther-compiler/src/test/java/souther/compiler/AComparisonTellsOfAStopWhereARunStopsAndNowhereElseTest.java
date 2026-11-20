package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.runtime.ConstraintViolation;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison is told to be one a run may stop in where some run that reaches it does stop, and
 * is told nothing where none does.
 *
 * <p>The truth is the program run: each condition is compiled and run on the numbers a run stops
 * at, and a run that stops is a {@code ConstraintViolation}. What the report says is held to that
 * and not to what the readings of the comparison came to, so a stop a reading drops, or one it
 * tells where no run stops, is found by the program and not by whoever reads the output.
 *
 * <p>The numbers are the fewest that decide every form below as the ends of an {@code Int}, the
 * numbers beside them, the number whose square passes them, and lists of those did, as ten
 * numbers and sixteen lists were tried against these.
 *
 * <p>What is not told though a run stops is written down in {@link #NOT_TOLD}, one form each
 * with why: a stop the compiler learns to tell moves the form out of it, and a form that is not
 * there and is not told is a stop dropped. What is told though none of these numbers stops is
 * in {@link #TOLD_THOUGH_NONE_STOPS}, a stop that cannot be ruled out yet.
 *
 * <p>A stop that is not told as one is not left unsaid: where a run stops and no note says so,
 * the report says the comparison is not read to the end. A form where it says neither is a stop
 * dropped without a word. And where no run stops, it does not say that a run evaluating the
 * comparison may stop where nothing says: what each element, each step and each operand comes to
 * shows that none does.
 *
 * <p>This holds the report and the program to one another on these numbers, and not on every
 * input: a stop only some other number reaches is not found by it.
 *
 * <p>Compiling and running every form costs more than a change is worth waiting on, so it is asked
 * at night; the unit tests of each reading ask the forms one at a time.
 */
@Nightly
class AComparisonTellsOfAStopWhereARunStopsAndNowhereElseTest {

    private static final long MAX = Long.MAX_VALUE;
    private static final long MIN = Long.MIN_VALUE;

    private static final List<Long> NUMBERS = List.of(0L, MAX - 1, MAX, MIN, 3_037_000_500L);

    private static final List<List<Long>> LISTS = List.of(List.of(), List.of(MAX),
            List.of(MAX - 1), List.of(MIN), List.of(MAX, 1L), List.of(3_037_000_500L),
            List.of(4_611_686_018_427_387_904L, 4_611_686_018_427_387_904L));

    /** Each condition on {@code ds} and {@code q}, by the name it is told under. */
    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    /** What a run stops in and no note says, each with why. */
    private static final Map<String, String> NOT_TOLD = new LinkedHashMap<>();

    /** What is told though no run of the numbers tried stops: a stop that cannot be ruled out,
     *  each with why it cannot. */
    private static final Map<String, String> TOLD_THOUGH_NONE_STOPS = new LinkedHashMap<>();

    /** What is said to work out what may stop a run where nothing tells, though no run of the
     *  numbers tried stops: a stop that cannot be ruled out, nor told, each with why. */
    private static final Map<String, String> UNTOLD_THOUGH_NONE_STOPS = new LinkedHashMap<>();

    static {
        // an operation of the comparison, and the same without it
        FORMS.put("sumOfANumber", "q + 1 <= 10");
        FORMS.put("cancelled", "q + 1 >= q");
        FORMS.put("shifted", "(q + 2) - 1 >= 0");
        FORMS.put("quotient", "(q + 1) / 3 >= 2");
        FORMS.put("remainder", "Int.floorMod(q + 1, 7) == 0");
        FORMS.put("negated", "(0 - (q + 1)) <= 5");
        FORMS.put("absOfASum", "Int.abs(q + 1) >= 0");
        FORMS.put("absOfANumber", "Int.abs(q) >= 0");
        FORMS.put("maxOfASum", "Int.max(q + 1, q) >= q");
        FORMS.put("maxOfANumber", "Int.max(q, q) >= q");
        FORMS.put("productOfTwoNumbers", "List.length(ds) * q >= 3");
        FORMS.put("absInALetBody", "Int.abs({ let a = 1 \n q + a }) >= 0");
        FORMS.put("absInALetBodyUnchanged", "Int.abs({ let a = 1 \n q }) >= 0");
        FORMS.put("noOperation", "q >= 3");
        // a choice: what decides it on every run, and an arm on the runs that take it
        FORMS.put("conditionOfAChoice", "(if q + 1 > 0 then 1 else 2) >= 1");
        FORMS.put("armOfAChoice", "(if q > 5 then q + 1 else 3) >= q");
        FORMS.put("armNoRunTakes", "(if q > 5 && q < 3 then q + 1 else 3) >= q");
        FORMS.put("rightOfAnAnd", "q > 0 && q + 1 > 3");
        // a guard that keeps what is worked out within the type
        FORMS.put("sumOfANumberGuarded", "q < 100 && q > -100 && q + 1 > 0");
        FORMS.put("absOfASumGuarded", "q < 100 && q > -100 && Int.abs(q + 1) >= 0");
        FORMS.put("totalOfNoElements", "List.length(ds) < 1 && List.sum(ds) >= 10");
        FORMS.put("lengthOfAStepOfNoElements",
                "List.length(ds) < 1 && List.length(List.map(x -> x + 1, ds)) >= 2");
        // a comparison no run reaches: what is worked out in it is worked out by no run
        FORMS.put("sumOfANumberNoRunReaches", "q > 5 && q < 3 && q + 1 > 0");
        FORMS.put("totalNoRunReaches", "q > 5 && q < 3 && List.sum(ds) >= 10");
        FORMS.put("lengthOfAStepNoRunReaches",
                "q > 5 && q < 3 && List.length(List.map(x -> x + 1, ds)) >= 2");
        FORMS.put("absOfASumNoRunReaches", "q > 5 && q < 3 && Int.abs(q + 1) >= 0");
        // a total, which is worked out exactly before its type holds it
        FORMS.put("totalOfTheElements", "List.sum(ds) >= 10");
        FORMS.put("foldOfTheElements", "List.fold((w, l) -> w + l, 0, ds) >= 10");
        FORMS.put("totalOfAStep", "List.sum(List.map(x -> x + 1, ds)) >= 10");
        FORMS.put("foldOfAStep", "List.fold((w, l) -> w + l, 0, List.map(x -> x + 1, ds)) >= 10");
        FORMS.put("totalOfTakenSteps", "List.sum(List.take(2, List.map(x -> x + 1, ds))) >= 10");
        FORMS.put("totalOfWrittenNumbers", "List.sum([1, 2]) >= 2");
        FORMS.put("totalOfWrittenNumbersPastTheType", "List.sum([9223372036854775807, 1]) >= 2");
        // a step over the elements of a list that is only counted, and the same changing nothing
        FORMS.put("lengthOfAStep", "List.length(List.map(x -> x + 1, ds)) >= 2");
        FORMS.put("lengthOfAnUnchangedStep", "List.length(List.map(x -> x, ds)) >= 2");
        FORMS.put("emptyOfAStep", "List.isEmpty(List.map(x -> x + 1, ds))");
        FORMS.put("lengthOfASortedStep", "List.length(List.sort(List.map(x -> x + 1, ds))) >= 2");
        FORMS.put("lengthOfATakenStep",
                "List.length(List.take(2, List.map(x -> x + 1, ds))) >= 2");
        FORMS.put("lengthOfAFlatStep", "List.length(List.flatMap(x -> [x + 1], ds)) >= 2");
        FORMS.put("lengthOfAStepAtAnIndex",
                "List.length(List.mapIndexed((i, x) -> x + 1, ds)) >= 2");
        FORMS.put("lengthOfACancelledStep", "List.length(List.map(x -> (x + 1) - 1, ds)) >= 2");
        FORMS.put("lengthOfAShiftedStep", "List.length(List.map(x -> (x + 2) - 1, ds)) >= 2");
        FORMS.put("lengthOfACancelledConstantStep",
                "List.length(List.map(x -> ((x - x) + 9223372036854775807) + 1, ds)) >= 1");
        FORMS.put("lengthOfACancelledConstantStepWithinTheType",
                "List.length(List.map(x -> ((x - x) + 9223372036854775807) + 0, ds)) >= 1");
        FORMS.put("lengthOfAStepInAWrittenList",
                "List.length(List.map(x -> List.length([x + 1]), ds)) >= 1");
        FORMS.put("lengthOfAnUnusedBinding",
                "List.length(List.map(x -> { let unused = x + 1 \n 0 }, ds)) >= 1");
        FORMS.put("lengthOfAnUnusedBindingWithinTheType",
                "List.length(List.map(x -> { let unused = x + 0 \n 0 }, ds)) >= 1");
        FORMS.put("lengthOfATupleStep", "List.length(List.map(x -> (x + 1, 1), ds)) >= 2");
        FORMS.put("lengthOfATupleStepUnchanged", "List.length(List.map(x -> (x, 1), ds)) >= 2");
        FORMS.put("lengthOfAConditionStep",
                "List.length(List.map(x -> if x + 1 > 0 then 1 else 2, ds)) >= 2");
        FORMS.put("lengthOfAConditionStepUnchanged",
                "List.length(List.map(x -> if x > 0 then 1 else 2, ds)) >= 2");
        FORMS.put("everyOfAStep", "List.all(r -> r <= 10, List.map(x -> x + 1, ds))");
        FORMS.put("everyOfAShiftedStep", "List.all(r -> r <= 10, List.map(x -> (x + 2) - 1, ds))");
        FORMS.put("lengthOfAnArmStepNoStop",
                "List.length(List.map(x -> if x < 0 then x + 1 else 0, ds)) >= 2");
        FORMS.put("stepBeside", "List.fold((w, l) -> if l > w then l else w, 0, ds) <= q + 1");

        TOLD_THOUGH_NONE_STOPS.put("totalOfNoElements", "a total is worked out exactly and its "
                + "range is not derived from the ends of the elements and how many there are "
                + "(FormRange.asWorkedOut says a total is not known), so a way that leaves no "
                + "element does not rule the stop out");
        TOLD_THOUGH_NONE_STOPS.put("lengthOfAStepOfNoElements", "the same, for what a step works "
                + "out at the elements of a list the way leaves none of");
        NOT_TOLD.put("absOfANumber", "a call's own stop, here the least Int having no absolute "
                + "value, is told by no reading as an operation of the call: only what it is "
                + "made of is");
        NOT_TOLD.put("absInALetBodyUnchanged", "the same, in the body of a let");
        NOT_TOLD.put("squareOfANumber", "no product of numbers that share a place is a "
                + "NumericTerm.ProductOf (signed): a line on a product needs factors of their own");
        FORMS.put("squareOfANumber", "q * q >= 3");
        NOT_TOLD.put("totalOfSquares", "the same: the answer x * x is a square, which "
                + "ElementValue holds as no monomial of distinct places");
        FORMS.put("totalOfSquares", "List.sum(List.map(x -> x * x, ds)) >= 10");
        NOT_TOLD.put("totalOfAStepByQ", "the comparison is not read, so there is no range for "
                + "what it works out");
        FORMS.put("totalOfAStepByQ", "List.sum(List.map(x -> x + q, ds)) >= 10");
        NOT_TOLD.put("productOfTheElements", "the comparison is not read: a product of what a "
                + "container holds is no term (FormRange.aTotal asks of a sum)");
        FORMS.put("productOfTheElements", "List.product(ds) >= 10");
        FORMS.put("maxOfAStep", "Option.withDefault(0, List.max(List.map(x -> x + 1, ds))) >= 3");
        NOT_TOLD.put("maxPlusOne", "the operation over what the option holds is told on the arm "
                + "of the match that opens it, the list holding an element; but a comparison over "
                + "that value is stated as no condition, and a stop told on an arm is asked of "
                + "rows only through the condition the comparison is stated as "
                + "(GuardThresholds.aRunTakingAnArmMayStop): said as not read");
        FORMS.put("maxPlusOne", "Option.withDefault(0, List.max(ds)) + 1 <= 10");
        NOT_TOLD.put("maxOfAWrittenListPlusOne", "the same, on an arm every run takes");
        NOT_TOLD.put("defaultPastTheTypePlusOne", "the same, where the default is past the type");
        // what an option holds, from the elements of the list or the default: a stop where one of
        // them is past where the operation keeps within the type, and none where none is
        FORMS.put("maxOfAWrittenListPlusOne", "Option.withDefault(0, List.max([q, 3])) + 1 >= 3");
        FORMS.put("maxOfAWrittenListPlusOneWithinTheType",
                "Option.withDefault(0, List.max([1, 2])) + 1 >= 3");
        FORMS.put("defaultPastTheTypePlusOne",
                "Option.withDefault(9223372036854775807, List.max(ds)) + 1 >= 3");
        FORMS.put("maxPlusOneGuarded",
                "List.all(x -> x < 9223372036854775807, ds) && Option.withDefault(0, List.max(ds))"
                        + " + 1 <= 10");
        FORMS.put("maxOfAStepByQ", "Option.withDefault(0, List.max(List.map(x -> x - q, ds))) >= 3");
        NOT_TOLD.put("foldOfAProduct", "AddedOfEachElement reads only a step that adds to the "
                + "answer so far; an operation over the running value has no operand that is a "
                + "place of the input");
        FORMS.put("foldOfAProduct", "List.fold((w, l) -> w * l, 1, ds) >= 10");
        NOT_TOLD.put("lengthOfAStepOfAFilter", "the elements a filter keeps stand at no place "
                + "(everyElementAt), and an operation told over the elements cannot carry the test "
                + "that keeps them");
        FORMS.put("lengthOfAStepOfAFilter",
                "List.length(List.map(x -> x + 1, List.filter(y -> y > 0, ds))) >= 2");
        // one closure applied to the elements of the list and to q: what is told of the one
        // application is no word of the other
        FORMS.put("oneClosureOnTheElementsAndOnQ", "{ let f = x -> x + 1 \n "
                + "List.sum(List.map(f, ds)) + List.length(List.map(f, [q])) } >= 3");
        NOT_TOLD.put("oneClosureOnTheElementsAndOnQ", "a closure bound to a name is read as no "
                + "step: the comparison is about a value made from the input and is not worked "
                + "out, so no application of it is told");
        FORMS.put("oneClosureBoundOnQAndSummedOnTheElements", "{ let f = x -> x + 1 \n "
                + "let unused = List.map(f, [q]) \n List.sum(List.map(f, ds)) } >= 3");
        NOT_TOLD.put("oneClosureBoundOnQAndSummedOnTheElements", "the same, where the one "
                + "application is bound and never read");
        // a step that answers afresh on one arm of a choice written inside a sum, and takes from
        // the answer so far on the other: the answer so far starts again from that arm's value
        FORMS.put("aStepAnsweringAfreshInsideASum", "List.fold((w, x) -> (if x > 1 then "
                + "(0 - 9223372036854775758) else w - 75) + 0, 9223372036854775807, ds) >= 10");
        NOT_TOLD.put("aStepAnsweringAfreshInsideASum", "a step whose answer so far is taken from "
                + "on one arm is told by no reading step by step, so its stop is said as one "
                + "nothing tells; that no run of it is shown held where one stops is "
                + "WhatAnElementsPartWorksOutIsAskedOperationByOperationTest's");
        // the elements of a list a choice makes, each made only on its arm's runs: one that
        // stops is said though what the other arm makes is not shown to keep within its type
        FORMS.put("elementsOfAChosenListThatAgree",
                "List.all(x -> x >= 3, if q > 0 then [q + 1] else [(q + 2) - 1])");
        FORMS.put("elementsOfAChosenListThatKeepWithin",
                "List.all(x -> x >= 3, if q > 0 then [q - 1] else [q + 1])");
        // an arm held aside beside another, whose operation its condition keeps within its type
        FORMS.put("anArmHeldAsideWhereItsConditionHolds",
                "(if q > 7 then 1 else 2) + (if q > 5 then q - 1 else 3) >= q");
        // the same step, where the filter keeps no element the step stops at
        FORMS.put("lengthOfAStepOfAFilterKeepingNoEnd",
                "List.length(List.map(x -> x + 1, List.filter(y -> y < 0, ds))) >= 2");
        // the same, where the test keeps the elements between two numbers, and where it is
        // written the other way round
        FORMS.put("lengthOfAStepOfAFilterKeepingBetween", "List.length(List.map(x -> x + 1, "
                + "List.filter(y -> y > 0 && y < 100, ds))) >= 2");
        FORMS.put("lengthOfAStepOfAFilterKeepingNoEndTheOtherWayRound",
                "List.length(List.map(x -> x + 1, List.filter(y -> 0 > y, ds))) >= 2");
        NOT_TOLD.put("lengthOfAnArmStep", "what an arm works out is worked out only where the "
                + "arm is taken, which an operation told over the elements cannot say");
        FORMS.put("lengthOfAnArmStep",
                "List.length(List.map(x -> if x > 5 then x + 1 else 0, ds)) >= 2");
        // an operation over what a walk comes to: what that may be shows where no run stops, and
        // never that one does
        String walk = "List.fold((w, l) -> if l > w then l else w, 0, ds)";
        NOT_TOLD.put("walkPlusOne", "what the walk comes to, its seed or an element, may take the "
                + "operation past its type, which shows no run that does: said as not read");
        FORMS.put("walkPlusOne", walk + " + 1 <= 10");
        // the same walk from a seed past where the operation keeps within the type, one that
        // keeps only what is below nought, which no run takes past it, one a test of every element
        // keeps within it, and one over a list written out whose every element and seed keep it
        // within
        NOT_TOLD.put("walkFromTheGreatestSeedPlusOne", "the same, from the seed");
        FORMS.put("walkFromTheGreatestSeedPlusOne",
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) + 1 >= 3");
        UNTOLD_THOUGH_NONE_STOPS.put("walkKeepingWhatIsBelowNoughtPlusOne", "what the walk "
                + "comes to is read as its seed or any element, and not as the elements the arm "
                + "that keeps one is taken for, so nothing shows it keeps the operation within");
        FORMS.put("walkKeepingWhatIsBelowNoughtPlusOne",
                "List.fold((w, l) -> if l < 0 then l else w, 0, ds) + 1 <= 10");
        FORMS.put("walkPlusOneGuarded",
                "List.all(x -> x < 9223372036854775807, ds) && " + walk + " + 1 <= 10");
        FORMS.put("walkOverAWrittenListPlusOneWithinTheType",
                "List.fold((w, l) -> if l > w then l else w, 0, [1, 2]) + 1 >= 3");
        NOT_TOLD.put("walkAgainstAnOption", "the operation over what the option holds, against "
                + "a walk, is told on no arm or application the report asks of: said as not "
                + "read");
        FORMS.put("walkAgainstAnOption", walk + " <= Option.withDefault(0, List.max(ds)) + 1");
        NOT_TOLD.put("armOfAWalkPlusOne", "the same, the operation over the walk in an arm");
        FORMS.put("armOfAWalkPlusOne", "(if q > 3 then " + walk + " + 1 else 0) >= 2");
        NOT_TOLD.put("remainderOfAWalkPlusOne", "what the remainder divides is a part of an "
                + "expression held aside, told beside it only where it is read as a number of the "
                + "input (tellWhatIsWorkedOutIn); an operation over a walk is no such number and "
                + "is passed over, though what the walk comes to is known");
        FORMS.put("remainderOfAWalkPlusOne", "Int.floorMod(" + walk + " + 1, 7) >= 3");
        NOT_TOLD.put("armOfAWalkPlusOneInAClosure", "the same, in an arm of what a closure "
                + "works out on each element");
        FORMS.put("armOfAWalkPlusOneInAClosure",
                "List.all(x -> (if x > 3 then " + walk + " + 1 else 0) >= 2, ds)");
        FORMS.put("remainderOfAWalk", "Int.floorMod(" + walk + ", 7) + 1 >= 3");
        // what each element, each step and each operand comes to, from where it stands
        FORMS.put("countOfAChoiceStep", "List.fold((w, l) -> if l > 0 then w + 1 else w, 0, ds)"
                + " >= 3");
        FORMS.put("sumOfAChoiceStep", "List.fold((w, l) -> if l > 0 then w + l else w, 0, ds)"
                + " >= 3");
        FORMS.put("armKeptWithinTheType", "(if q == " + MAX + " then 0 else q) + 1 >= 3");
        FORMS.put("armPastTheType", "(if q == 0 then 0 else q) + 1 >= 3");
        FORMS.put("takenFromARemainderInAnArm",
                "(if q > 0 then 11 - Int.floorMod(" + walk + ", 11) else 0) >= 3");
        FORMS.put("takenFromAProductInAnArm",
                "(if q > 0 then 11 - List.length(ds) * q else 0) >= 3");
        FORMS.put("totalOfAWrittenStep", "List.sum(List.map(x -> 100, ds)) >= 3");
        FORMS.put("totalOfAnEmptyRange", "List.sum(List.rangeInclusive(3, 1)) >= q");
        FORMS.put("totalOfThePositions", "List.sum(List.mapIndexed((i, x) -> i, ds)) >= 3");
        FORMS.put("totalOfThePositionsTimesTheElements",
                "List.sum(List.mapIndexed((i, x) -> (i + 1) * x, ds)) >= 3");
        // a total of a list written out, each element chosen alike however it is written
        FORMS.put("totalOfWrittenChoices",
                "List.sum([if q > 0 then q else 0, if q > 0 then q else 0]) >= 10");
        FORMS.put("totalOfChoicesAStepMakes",
                "List.sum(List.map(x -> if x > 0 then x else 0, [q, q])) >= 10");
        FORMS.put("totalOfWhatAFilterKeeps", "List.sum(List.filter(x -> x > 0, [q, q])) >= 10");
        // a filter that keeps q only where twice it is within the type, and one whose comparison
        // holds on every row of the way that stops
        FORMS.put("totalOfWhatAFilterKeepsOnlyWithinTheType",
                "List.sum(List.filter(x -> x > 0 && x < 100, [q, q])) >= 10");
        FORMS.put("totalOfWhatAFilterKeepsHeldAgainstWhatItKeeps",
                "List.sum(List.filter(x -> x > 0, [q, 1])) >= q");
        // a step over what a step made, and a walk that starts again from a number written down
        FORMS.put("totalOfAStepOverAStep",
                "List.sum(List.map(p -> 2 * p, List.map(x -> x, ds))) >= 10");
        FORMS.put("foldStartingAgain",
                "List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, ds) >= 3");
        // a walk adding a choice of the element, one arm of which works out an operation, and the
        // same total added up exactly
        FORMS.put("foldAddingAChoice",
                "List.fold((acc, x) -> acc + (if x > 0 then x else 0 - x), 0, ds) >= 3");
        FORMS.put("totalOfTheSameChoice",
                "List.sum(List.map(x -> if x > 0 then x else 0 - x, ds)) >= 3");
        // a part of what a walk carries in a tuple, counted and summed
        FORMS.put("countCarriedInATuple", "{ let (s, _) = List.fold((acc, x) -> { "
                + "let (s, c) = acc \n if x > 0 then (s + 1, c) else acc }, (0, 0), ds) \n s }"
                + " >= 3");
        FORMS.put("sumCarriedInATuple", "{ let (s, _) = List.fold((acc, x) -> { "
                + "let (s, c) = acc \n (s + x, c) }, (0, 0), ds) \n s } >= 3");
        // a field taken off a construction whose other part is refused at some q
        FORMS.put("fieldBesideARefusedPart",
                "Pay { base = Yen(5), other = Yen(0 - q) }.base.value >= q");
        // a part of a tuple beside a construction made only where its invariant holds
        FORMS.put("tuplePartBesideAPartMadeWhereItHolds", "{ let (a, r) = if q <= 5 "
                + "then (q, Yen(0)) else (5, Yen(q - 5)) \n a } >= 3");
    }

    @Test
    void aComparisonIsToldOfAStopWhereARunStopsAndNowhereElse() throws Exception {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder("module demo\n\n"
                + "data In = { ds: List<Int>, q: Int }\ndata Out = Int\n"
                + "data Yen = Int invariant value >= 0\ndata Pay = { base: Yen, other: Yen }\n");
        for (int at = 0; at < names.size(); at++) {
            String condition = FORMS.get(names.get(at)).replaceAll("\\bds\\b", "i.ds")
                    .replaceAll("\\bq\\b", "i.q");
            model.append("\nbehavior b").append(at)
                    .append(" : (i: In) -> Out constructs Out")
                    .append(condition.contains("Yen(") ? ", Yen" : "")
                    .append(condition.contains("Pay {") ? ", Pay" : "")
                    .append("\nlet b").append(at)
                    .append(" (i) = Out { value = if ").append(condition)
                    .append(" then 1 else 2 }\n");
        }
        Map<String, int[]> said = notes(model.toString());
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model.toString()),
                AComparisonTellsOfAStopWhereARunStopsAndNowhereElseTest.class.getClassLoader());
        TreeSet<String> stopsAndNothingTold = new TreeSet<>();
        TreeSet<String> toldAndNoRunStops = new TreeSet<>();
        TreeSet<String> stopsAndNothingSaid = new TreeSet<>();
        TreeSet<String> untoldAndNoRunStops = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                    .getConstructor().newInstance();
            boolean stops = someRunStops(loader, behavior);
            int[] counts = said.getOrDefault("b" + at, new int[3]);
            if (!stops && counts[UNTOLD] > 0) {
                untoldAndNoRunStops.add(names.get(at));
            }
            if (stops && counts[MAY_STOP] == 0) {
                stopsAndNothingTold.add(names.get(at));
                if (counts[NOT_READ] == 0) {
                    stopsAndNothingSaid.add(names.get(at));
                }
            }
            if (!stops && counts[MAY_STOP] > 0) {
                toldAndNoRunStops.add(names.get(at));
            }
        }
        assertEquals(new TreeSet<>(TOLD_THOUGH_NONE_STOPS.keySet()), toldAndNoRunStops,
                "told of a stop, and no run of the numbers tried stops, beside the stops the "
                        + "compiler cannot yet rule out");
        assertEquals(new TreeSet<>(NOT_TOLD.keySet()), stopsAndNothingTold,
                "a run stops and no note says so, beside the forms the compiler cannot yet tell");
        assertEquals(new TreeSet<>(), stopsAndNothingSaid,
                "a run stops and the report says nothing of it, not even that it is not read to "
                        + "the end, beside the forms whose stop no reading knows to ask of");
        assertEquals(new TreeSet<>(UNTOLD_THOUGH_NONE_STOPS.keySet()), untoldAndNoRunStops,
                "the report says a run may stop where nothing says, and no run stops, beside the "
                        + "stops the compiler cannot yet rule out nor tell");
    }

    private static final int MAY_STOP = 0;
    private static final int NOT_READ = 1;
    private static final int UNTOLD = 2;

    private static boolean someRunStops(ClassLoader loader, Object behavior) throws Exception {
        for (List<Long> list : LISTS) {
            for (long number : NUMBERS) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("ds", list, "q", number));
                try {
                    Codecs.apply(behavior, in);
                } catch (ConstraintViolation stopped) {
                    return true;
                }
            }
        }
        return false;
    }

    /** How many {@code may stop a run} notes ({@link #MAY_STOP}) and how many places said not read
     *  ({@link #NOT_READ}) each behavior's report holds. */
    private static Map<String, int[]> notes(String model) {
        Compilation compilation = ACompiledModel.measured(model,
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        Pattern header = Pattern.compile("^(\\w+)\\s+implemented\\b.*");
        Map<String, int[]> out = new LinkedHashMap<>();
        String current = null;
        for (String line : AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList()) {
            Matcher started = header.matcher(line);
            if (started.matches()) {
                current = started.group(1);
                out.put(current, new int[3]);
            } else if (current != null && line.contains("may stop a run")) {
                out.get(current)[MAY_STOP]++;
            } else if (current != null && line.startsWith("· not read:")) {
                out.get(current)[NOT_READ]++;
                if (line.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD)) {
                    out.get(current)[UNTOLD]++;
                }
            }
        }
        return out;
    }
}
