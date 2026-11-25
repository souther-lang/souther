package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison is told to be one a run may stop in where some run that reaches it does stop, and
 * is told nothing where none does, as {@link StopsHeldToTheRuns} holds what is said of each step
 * a run may stop at to the runs of the numbers tried.
 *
 * <p>The numbers are the fewest that decide every form below as the ends of an {@code Int}, the
 * numbers beside them, the number whose square passes them, and lists of those did, as ten
 * numbers and sixteen lists were tried against these.
 *
 * <p>A step a run stops at and no stop is shown at is written down in {@link #NOT_TOLD}, one form
 * each with the reasons the findings give and why: a stop the compiler learns to show moves the
 * form out of it, and a step a run stops at that no finding names is a stop dropped without a
 * word, which none is. A step said not resolved where none of these numbers stops is written down
 * in {@link #UNTOLD_THOUGH_NONE_STOPS}, a stop that cannot be ruled out yet.
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

    /** The input every form takes: the numbers {@code q} takes, and the lists {@code ds} does. */
    private static final StopsHeldToTheRuns.Input INPUT = new StopsHeldToTheRuns.Input("demo", "In",
            Map.of("ds", List.of(List.of(), List.of(MAX), List.of(MAX - 1), List.of(MIN),
                            List.of(MAX, 1L), List.of(3_037_000_500L),
                            List.of(4_611_686_018_427_387_904L, 4_611_686_018_427_387_904L)),
                    "q", List.of(0L, MAX - 1, MAX, MIN, 3_037_000_500L)));

    /** Each condition on {@code ds} and {@code q}, by the name it is told under. */
    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    /**
     * A form a run stops at a step of that the findings say is not resolved and show no stop at.
     *
     * @param because the reasons the findings give, every one of them
     * @param why     why the compiler cannot yet show it
     */
    private record NotTold(Set<Enum<?>> because, String why) {}

    /** The forms a run stops at a step of that is said not resolved: a stop the compiler learns
     *  to show moves the form out of it. */
    private static final Map<String, NotTold> NOT_TOLD = new LinkedHashMap<>();

    /** The forms a step of which is said not resolved though no run of the numbers tried stops
     *  there: a stop that cannot be ruled out yet, each with why. */
    private static final Map<String, String> UNTOLD_THOUGH_NONE_STOPS = new LinkedHashMap<>();

    /** The forms a claim of every run of which no run of the numbers tried is about, each with
     *  why. */
    private static final Map<String, String> NOT_ABOUT = new LinkedHashMap<>();

    /** {@code name} as a form a run stops at a step of that is said not resolved, for
     *  {@code because}, as {@code why} says. */
    private static void notTold(String name, String why, Enum<?>... because) {
        NOT_TOLD.put(name, new NotTold(Set.of(because), why));
    }

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

        notTold("absOfANumber", "a call's own stop, here the least Int having no absolute "
                + "value, is told by no reading as an operation of the call: only what it is "
                + "made of is", WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("absInALetBodyUnchanged", "the same, in the body of a let",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("squareOfANumber", "no product of numbers that share a place is a "
                + "NumericTerm.ProductOf (signed): a line on a product needs factors of their own",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        FORMS.put("squareOfANumber", "q * q >= 3");
        notTold("totalOfSquares", "the same: the answer x * x is a square, which "
                + "ElementValue holds as no monomial of distinct places",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        FORMS.put("totalOfSquares", "List.sum(List.map(x -> x * x, ds)) >= 10");
        FORMS.put("totalOfAStepByQ", "List.sum(List.map(x -> x + q, ds)) >= 10");
        notTold("totalOfAStepByQ", "the total, worked out exactly over a step reading another "
                + "place: no value of the elements is put to it", WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("productOfTheElements", "the comparison is not read: a product of what a "
                + "container holds is no term (FormRange.aTotal asks of a sum)",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        FORMS.put("productOfTheElements", "List.product(ds) >= 10");
        FORMS.put("maxOfAStep", "Option.withDefault(0, List.max(List.map(x -> x + 1, ds))) >= 3");
        FORMS.put("maxPlusOne", "Option.withDefault(0, List.max(ds)) + 1 <= 10");
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
        notTold("foldOfAProduct", "AddedOfEachElement reads only a step that adds to the "
                + "answer so far; an operation over the running value has no operand that is a "
                + "place of the input", WhyAStopIsNotShown.NO_OPERATION_TOLD);
        FORMS.put("foldOfAProduct", "List.fold((w, l) -> w * l, 1, ds) >= 10");
        FORMS.put("lengthOfAStepOfAFilter",
                "List.length(List.map(x -> x + 1, List.filter(y -> y > 0, ds))) >= 2");
        // one closure applied to the elements of the list and to q: what is told of the one
        // application is no word of the other
        FORMS.put("oneClosureOnTheElementsAndOnQ", "{ let f = x -> x + 1 \n "
                + "List.sum(List.map(f, ds)) + List.length(List.map(f, [q])) } >= 3");
        notTold("oneClosureOnTheElementsAndOnQ", "a closure bound to a name is read as no "
                + "step: the comparison is about a value made from the input and is not worked "
                + "out, so no application of it is told", WhyAStopIsNotShown.NO_OPERATION_TOLD);
        FORMS.put("oneClosureBoundOnQAndSummedOnTheElements", "{ let f = x -> x + 1 \n "
                + "let unused = List.map(f, [q]) \n List.sum(List.map(f, ds)) } >= 3");
        notTold("oneClosureBoundOnQAndSummedOnTheElements", "the same, where the one "
                + "application is bound and never read", WhyAStopIsNotShown.NO_OPERATION_TOLD);
        // a step that answers afresh on one arm of a choice written inside a sum, and takes from
        // the answer so far on the other: the answer so far starts again from that arm's value
        FORMS.put("aStepAnsweringAfreshInsideASum", "List.fold((w, x) -> (if x > 1 then "
                + "(0 - 9223372036854775758) else w - 75) + 0, 9223372036854775807, ds) >= 10");
        notTold("aStepAnsweringAfreshInsideASum", "a step whose answer so far is taken from "
                + "on one arm is told by no reading step by step, so its stop is said as one "
                + "nothing tells; that no run of it is shown held where one stops is "
                + "WhatAnElementsPartWorksOutIsAskedOperationByOperationTest's",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
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
        FORMS.put("lengthOfAnArmStep",
                "List.length(List.map(x -> if x > 5 then x + 1 else 0, ds)) >= 2");
        // an operation over what a walk comes to: what that may be shows where no run stops, and
        // never that one does
        String walk = "List.fold((w, l) -> if l > w then l else w, 0, ds)";
        FORMS.put("walkPlusOne", walk + " + 1 <= 10");
        // the same walk from a seed past where the operation keeps within the type, which a walk
        // over none comes to; one that keeps only what is below nought, which no run takes past
        // it, one a test of every element keeps within it, and one over a list written out whose
        // every element and seed keep it within
        FORMS.put("walkFromTheGreatestSeedPlusOne",
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) + 1 >= 3");
        FORMS.put("walkKeepingWhatIsBelowNoughtPlusOne",
                "List.fold((w, l) -> if l < 0 then l else w, 0, ds) + 1 <= 10");
        FORMS.put("walkPlusOneGuarded",
                "List.all(x -> x < 9223372036854775807, ds) && " + walk + " + 1 <= 10");
        // the same test of every element, deciding the arm the walk is worked out on
        FORMS.put("walkPlusOneOnAnArmEveryElementDecides",
                "(if List.all(x -> x < 9223372036854775807, ds) then " + walk + " + 1 else 0)"
                        + " <= 10");
        // a test some element meets, which leaves the others anything, and one over a number the
        // walk does not read
        notTold("walkPlusOneSomeElementGuarded", "what some element meets is a condition no "
                + "reading puts on the way", WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        FORMS.put("walkPlusOneSomeElementGuarded",
                "List.any(x -> x < 9223372036854775807, ds) && " + walk + " + 1 <= 10");
        FORMS.put("walkPlusOneGuardedByQ", "q > 0 && " + walk + " + 1 <= 10");
        FORMS.put("walkOverAWrittenListPlusOneWithinTheType",
                "List.fold((w, l) -> if l > w then l else w, 0, [1, 2]) + 1 >= 3");
        FORMS.put("walkAgainstAnOption", walk + " <= Option.withDefault(0, List.max(ds)) + 1");
        FORMS.put("armOfAWalkPlusOne", "(if q > 3 then " + walk + " + 1 else 0) >= 2");
        FORMS.put("remainderOfAWalkPlusOne", "Int.floorMod(" + walk + " + 1, 7) >= 3");
        notTold("armOfAWalkPlusOneInAClosure", "the walk is worked out inside the closure "
                + "on one application standing for every element, so a value looked for at the "
                + "element is a list of one, and the walk over that list is what the step is over: "
                + "no way of the walk is read in terms of that one element",
                WhyAStopIsNotShown.A_CONDITION_NOT_READ);
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
        UNTOLD_THOUGH_NONE_STOPS.put("countCarriedInATuple", "a step that answers a tuple is "
                + "read by no reading of what a walk comes to over its elements "
                + "(AddedOfEachElement reads a step answering a number), so the count one part "
                + "carries is not shown to keep within the type");
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

        // A stop is shown only where it is worked out wherever the comparison is, over numbers a
        // row of the input holds at a place, every other operation and every condition on the way
        // read whole (StopAssessment). Each of these is a stop a run comes to and none of that is
        // shown of, so it is said as not resolved.
        notTold("takenFromAProductInAnArm", "an operation on an arm of a choice",
                WhyAStopIsNotShown.NO_VALUE_SHOWN);
        notTold("totalOfAStepOverAStep", "an operation over what an application is worked out"
                + " over, which no value of the elements is put to",
                WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        notTold("totalOfThePositionsTimesTheElements", "the same, the product of a position and"
                + " an element worked out before the total", WhyAStopIsNotShown.NO_OPERATION_TOLD,
                WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        notTold("totalOfTheElements", "a total of the elements, worked out exactly: no value of"
                + " the elements is put to it", WhyAStopIsNotShown.NO_VALUE_SHOWN);
        notTold("foldOfTheElements", "the same, added up by a walk",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("sumOfAChoiceStep", "the same, of what a choice of each element answers",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("sumCarriedInATuple", "the same, carried in a part of a tuple",
                WhyAStopIsNotShown.NO_OPERATION_TOLD);
        notTold("productOfTwoNumbers", "a product of two numbers of the input, which is no form"
                + " a value is put to", WhyAStopIsNotShown.NO_VALUE_SHOWN);
        // A step after one a run may stop at first is not shown to be got to: each of these shows
        // a stop at one step and says a step after it not resolved.
        String afterAStep = "what is worked out before the step may stop a run first";
        notTold("fieldBesideARefusedPart", afterAStep,
                WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        notTold("foldOfAStep", afterAStep, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        // The fold's sum is said to stop every run whose elements are at the greatest Int, the
        // rows of the step that adds one to each: every such run stops at that step first, and
        // none gets to the sum.
        NOT_ABOUT.put("foldOfAStep", "the rows of the step before the fold's sum, said at the"
                + " sum, which every run within them stops before");
        notTold("totalOfAStep", afterAStep, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        notTold("totalOfTakenSteps", afterAStep, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        notTold("totalOfTheSameChoice", afterAStep,
                WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        notTold("foldAddingAChoice", "the total a walk adds a choice of each element to, worked"
                + " out exactly", WhyAStopIsNotShown.NO_OPERATION_TOLD);

        // Steps said not resolved where no run of the numbers tried stops: a stop that cannot be
        // ruled out yet.
        for (String name : List.of("oneClosureBoundOnQAndSummedOnTheElements",
                "oneClosureOnTheElementsAndOnQ", "totalOfSquares")) {
            UNTOLD_THOUGH_NONE_STOPS.put(name, "the application to q, or the square, is said"
                    + " not resolved where only the total over the elements stops");
        }
        UNTOLD_THOUGH_NONE_STOPS.put("totalOfAStepOverAStep", "the doubling, said not resolved"
                + " where only the total stops");
        UNTOLD_THOUGH_NONE_STOPS.put("totalOfThePositionsTimesTheElements", "the position plus"
                + " one, said not resolved where only the product and the total stop");
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
        Compilation compilation = ACompiledModel.measured(model.toString(),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        ClassLoader loader = compilation.loaderSayingWhereRunsStop("demo").orElseThrow(
                () -> new AssertionError("the module is generated to say where runs stop"));
        Map<String, Object> wrong = new TreeMap<>();
        Map<String, Set<Enum<?>>> notShown = new TreeMap<>();
        Set<String> notResolvedWhereNoneStops = new TreeSet<>();
        Map<String, List<String>> notAbout = new TreeMap<>();
        for (int at = 0; at < names.size(); at++) {
            List<WhatIsShownOfAStop> said = StopsHeldToTheRuns.saidOf(compilation, "demo", "b" + at);
            StopsHeldToTheRuns.Held held = StopsHeldToTheRuns.heldTo(said,
                    new StopsHeldToTheRuns.Runs(compilation, loader, INPUT, "b" + at, said));
            if (!held.unheld().isEmpty() || !held.notHeldTo().isEmpty()) {
                wrong.put(names.get(at), List.of(held.unheld(), held.notHeldTo()));
            }
            if (!held.notAbout().isEmpty()) {
                notAbout.put(names.get(at), held.notAbout());
            }
            if (!held.notShown().isEmpty()) {
                notShown.put(names.get(at), held.notShownBecause());
            }
            if (!held.notResolvedWhereNoneStops().isEmpty()) {
                notResolvedWhereNoneStops.add(names.get(at));
            }
        }
        assertAll(
                () -> assertEquals(Map.of(), wrong,
                        "what is said of a step is what the runs of the numbers tried do there"),
                () -> {
                    Map<String, Set<Enum<?>>> written = new TreeMap<>();
                    NOT_TOLD.forEach((name, told) -> written.put(name, told.because()));
                    assertEquals(written, notShown,
                            "a run stops at a step said not resolved, for the reasons written down");
                },
                () -> assertEquals(new TreeSet<>(NOT_ABOUT.keySet()), notAbout.keySet(),
                        "a claim of every run no run of the numbers tried is about, beside the"
                                + " forms written down: " + notAbout),
                () -> assertEquals(new TreeSet<>(UNTOLD_THOUGH_NONE_STOPS.keySet()),
                        notResolvedWhereNoneStops,
                        "a step is said not resolved where no run of the numbers tried stops,"
                                + " beside the stops the compiler cannot yet rule out"));
    }
}
