package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where an operation a comparison works out comes to past its type, and every operation a run may
 * work out before it gets past, every run that gets to the comparison there stops in it. That is
 * said beside the rule, as the operation and the rows, and leaves nothing open: no measure waits
 * on it, and no question stands for it.
 *
 * <p>The rows are said over as many numbers as the operation is over, and an operation worked
 * out of another's value comes after it on every run.
 *
 * <p>An operation over a name read off a container is over the values the container hands it:
 * every run stops where the operation is past its type at every one of those values, and a run
 * may stop wherever some value takes it past.
 */
class AnOperationPastItsTypeStopsEveryRunThatGetsToItsComparisonTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo

            data Small = Int
                invariant value <= 1000

            data Yes = { n: Int }
            data No = { n: Int }

            behavior f : (x: %s, y: Int, z: Int) -> Yes | No
            let f (%s, y, z) = {
                %s
                if %s then Yes { n = y } else No { n = z }
            }
            """;

    private static final String GREATEST = "9223372036854775807";

    private static final String LEAST = "-9223372036854775808";

    /** The rows every run stops at, as {@code operation where form least..greatest and ...},
     *  an end the type already holds left blank. */
    private static List<String> everyRunStops(String type, String bound, String before,
                                              String comparison) {
        Compilation compilation = measured(MODEL.formatted(type, bound, before, comparison));
        JsonNode findings = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("findings");
        List<String> out = new ArrayList<>();
        for (JsonNode each : findings) {
            if (each.get("kind").asString().equals("rule_may_stop_a_run")
                    && each.has("everyRunStops")) {
                for (JsonNode stop : each.get("everyRunStops")) {
                    List<String> where = new ArrayList<>();
                    for (JsonNode within : stop.get("where")) {
                        where.add(within.get("form").asString() + " "
                                + (within.has("least") ? within.get("least").asString() : "")
                                + ".."
                                + (within.has("greatest") ? within.get("greatest").asString()
                                        : ""));
                    }
                    out.add(stop.get("operation").asString() + " where "
                            + String.join(" and ", where));
                }
            }
        }
        return out;
    }

    /** The questions left standing for {@code f}. */
    private static List<PartitionEvidence.Unanswered> standing(String type, String bound,
                                                               String before,
                                                               String comparison) {
        Compilation compilation = measured(MODEL.formatted(type, bound, before, comparison));
        return compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0))).value()
                .get("f").unanswered();
    }

    @Test
    void aSumPastTheGreatestIntStopsEveryRunAtTheGreatest() {
        assertEquals(List.of("x + 1 where x " + GREATEST + ".."),
                everyRunStops("Int", "x", "", "x + 1 == y"));
        assertEquals(List.of(), standing("Int", "x", "", "x + 1 == y"),
                "a run shown to stop leaves nothing open");
    }

    /** A line on one number is a relation of that number too, and the sum it is read through
     *  stops every run where it is past the type, as one over two numbers does. */
    @Test
    void aSumOverOneNumberHeldAgainstAConstantStopsEveryRunAtTheGreatest() {
        assertEquals(List.of("x + 10 where x " + plus(GREATEST, -9) + ".."),
                everyRunStops("Int", "x", "", "x + 10 >= 0"));
    }

    /** The constant added a piece at a time is the same relation, and leaves nothing open. */
    @Test
    void aConstantAddedInPiecesLeavesNothingOpen() {
        assertEquals(List.of(), standing("Int", "x", "", "(x + 1) + 1 == y"));
        assertEquals(List.of(), standing("Int", "x", "", "(x - 1) - 1 == y"));
    }

    /** A position held well short of the end of its type never gets there. */
    @Test
    void aPositionHeldShortOfTheEndStopsNoRun() {
        assertEquals(List.of(), everyRunStops("Small", "Small(x)", "", "x + 1 == y"));
    }

    /** The ways before the comparison keep the end away, and no run getting to it is there. */
    @Test
    void aGuardKeepingTheEndAwayLeavesNoRunToStop() {
        assertEquals(List.of(), everyRunStops("Int", "x", "guard x < 10 else No { n = 0 }",
                "x + 1 == y"));
    }

    /** Every value of {@code x} has a {@code z} that brings the sum back within the type, so no
     *  value of either stops a run: the two together do. */
    @Test
    void aSumOverTwoPositionsStopsWhereTheTwoTogetherPassTheType() {
        assertEquals(List.of("x + z where x + z " + plus(GREATEST, 1) + "..",
                        "x + z where x + z .." + plus(LEAST, -1)),
                everyRunStops("Int", "x", "", "x + z == y"));
        assertEquals(List.of(), standing("Int", "x", "", "x + z == y"));
    }

    /** A number taken away is weighed against its own end: one less than nought less the least
     *  two are past the greatest. */
    @Test
    void aNumberTakenAwayStopsAtTheOtherEnd() {
        assertEquals(List.of("-x + 1 where x .." + plus(LEAST, 1)),
                everyRunStops("Int", "x", "", "1 - x == y"));
    }

    /**
     * {@code x + 2} is worked out of {@code x + 1}, so a run stops in it only where
     * {@code x + 1} got past: at the greatest {@code x}, the run stopped in {@code x + 1} and
     * never worked {@code x + 2} out.
     */
    @Test
    void anOperationWorkedOutOfAnotherStopsOnlyWhereThatOneGotPast() {
        assertEquals(List.of("x + 1 where x " + GREATEST + "..",
                        "x + 2 where x " + plus(GREATEST, -1) + ".." + plus(GREATEST, -1)),
                everyRunStops("Int", "x", "", "(x + 1) + 1 == y"));
    }

    /** {@code z + 1} is worked out first and may stop the run at the greatest {@code z}, so the
     *  sum is said to stop it only where {@code z + 1} got past. */
    @Test
    void anOperationOverAnotherNumberWorkedOutFirstIsGotPastBeforeTheSumStops() {
        assertEquals(List.of("z + 1 where z " + GREATEST + "..",
                        "x + z + 1 where x + z " + GREATEST + ".. and z .."
                                + plus(GREATEST, -1)),
                everyRunStops("Int", "x", "guard z >= 0 else No { n = 0 }", "(z + 1) + x == y"));
    }

    /** Neither of {@code x + 1} and {@code z + 1} is worked out of the other, so either may come
     *  first: each is said to stop a run only where the other gets past, and where both pass the
     *  type nothing says which one the run stops in. */
    @Test
    void twoOperationsInEitherOrderEachStopsARunOnlyWhereTheOtherGetsPast() {
        assertEquals(List.of("x + 1 where x " + GREATEST + ".. and z .." + plus(GREATEST, -1),
                        "z + 1 where x .." + plus(GREATEST, -1) + " and z " + GREATEST + "..",
                        "x + z + 2 where x .." + plus(GREATEST, -1) + " and x + z "
                                + plus(GREATEST, -1) + ".. and z .." + plus(GREATEST, -1),
                        "x + z + 2 where x .." + plus(GREATEST, -1) + " and x + z .."
                                + plus(LEAST, -3) + " and z .." + plus(GREATEST, -1)),
                everyRunStops("Int", "x", "", "(x + 1) + (z + 1) == y"));
    }

    /**
     * The sum is worked out on the arm taken where {@code y} is above nought and on no other, so a
     * run that takes the other arm at the greatest {@code x} gets past: no run stops there.
     */
    @Test
    void anOperationOfOneArmStopsNoRunThatTakesAnotherArm() {
        assertEquals(List.of(),
                everyRunStops("Int", "x", "", "(if y > 0 then x + 1 else x) == z"));
        assertTrue(everyRunStops("Int", "x", "",
                        "(if y > 0 then x + 1 else x) + (z + 1) == 0").stream()
                .noneMatch(stop -> stop.startsWith("x + 1 ")),
                "the arm taken where y is above nought is not the only way to the comparison");
    }

    /**
     * The product is worked out too, and a run may stop in it before it works the sum out: the
     * sum is not told to be where every run stops.
     */
    @Test
    void anOperationBesideAnExpressionAnotherAnalysisAnswersForIsNotWhereEveryRunStops() {
        assertEquals(List.of(), everyRunStops("Int", "x", "", "x * z + (y + 1) == 0"));
    }

    /**
     * An element of a list of every whole number between two is no number of the input, and the
     * sum over it is still one a run stops in: every run that gets to the comparison stops where
     * the sum is past the greatest at the first end. Past the least at the last end is only where
     * the last end is below the first, a list holding nothing, which no application is made on.
     */
    @Test
    void aSumOverAnElementOfAListOfWholeNumbersStopsEveryRunPastItAtTheFirstEnd() {
        String comparison = "List.any(n -> x + n >= 10, List.rangeInclusive(3, z))";
        assertEquals(List.of("n + x where x " + plus(GREATEST, -2) + ".."),
                everyRunStops("Int", "x", "", comparison));
        assertEquals(1, mayStop("Int", "x", "", comparison).size());
    }

    /**
     * Where an element stands lies from nought to one below how many the walk's list holds. Below
     * the least at the last place is only where the list holds nothing, and no application is
     * made there: a run may stop in the sum, past the greatest, and no row stops every run.
     */
    @Test
    void aSumOverWhereAnElementStandsStopsNoRowsEveryRunAndSomeRuns() {
        String comparison = "List.any(b -> b, List.mapIndexed((i, _) -> y + i >= 10, x))";
        assertEquals(List.of(), everyRunStops("List<Int>", "x", "", comparison));
        assertEquals(1, mayStop("List<Int>", "x", "", comparison).size());
    }

    /**
     * Each element of a list written out is a number of its own, and the sum over the last is
     * past the greatest where {@code x} is nine below it, and not ten: the run stops in it there,
     * after the sum over the first got past. Read element by element up to a figure, a list of
     * every whole number between two numbers written down is the same.
     */
    @Test
    void aSumOverTheLastElementOfAListWrittenOutStopsEveryRunPastIt() {
        assertEquals(List.of("x + 10 where x " + plus(GREATEST, -9) + ".."),
                everyRunStops("Int", "x", "", "List.all(n -> n + x >= 0, [0, 10])"));
        assertEquals(List.of("x + 10 where x " + plus(GREATEST, -9) + ".." + plus(GREATEST, -9)),
                everyRunStops("Int", "x", "", "List.all(n -> n + x >= 0, List.rangeInclusive(0, 10))"));
    }

    /**
     * An application a walk stopping on an answer never makes works nothing out: where the first
     * element holds, the second is not looked at. Its sum stops the runs that get to it, where the
     * first does not hold.
     */
    @Test
    void aSumOnAnApplicationMadeOnlyPastAnAnswerStopsOnlyTheRunsThatMakeIt() {
        assertEquals(List.of(), everyRunStops("Int", "x", "", "List.any(n -> n + x >= 0, [0, 10])"));
        assertEquals(List.of(), mayStop("Int", "x", "", "List.any(n -> n + x >= 0, [0, 10])"));
        assertEquals(List.of("x + 10 where x " + plus(GREATEST, -9) + ".."),
                everyRunStops("Int", "x", "", "List.any(n -> n + x < 0, [0, 10])"));
    }

    /** A closure applied to a list holding nothing works nothing out on any run. */
    @Test
    void aSumInAClosureAppliedToNothingStopsNoRun() {
        assertEquals(List.of(),
                mayStop("Int", "x", "", "List.all(n -> n + x >= 0, List.take(0, [0, 10]))"));
    }

    /** One past where an element stands is at most how many a list holds, which an {@code Int}
     *  holds: the sum stops no run, and nothing is said of it. */
    @Test
    void oneAddedToWhereAnElementStandsStopsNoRun() {
        String comparison = "List.any(b -> b, List.mapIndexed((i, _) -> i + 1 == y, x))";
        assertEquals(List.of(), everyRunStops("List<Int>", "x", "", comparison));
        assertEquals(List.of(), mayStop("List<Int>", "x", "", comparison));
    }

    /**
     * The sum a remainder is of is worked out before anything is divided, and stops every run
     * where it is past the type, as the sum alone does. And the lines its witness draws stay: a
     * {@code z} keeps {@code x + z} within its type at every remainder, so the remainder takes
     * each of them and the number held against it is parted at the two ends — the sum stopping
     * some runs is no part of that.
     */
    @Test
    void theSumARemainderIsOfStopsEveryRunPastItBesideTheLinesItsWitnessDraws() {
        String comparison = "y == Int.floorMod(x + z, 11)";
        assertEquals(List.of("x + z where x + z " + plus(GREATEST, 1) + "..",
                        "x + z where x + z .." + plus(LEAST, -1)),
                everyRunStops("Int", "x", "", comparison));
        List<String> onY = Adequacy.readingsOf(measured(MODEL.formatted("Int", "x", "",
                comparison)).db(), "demo").get("f").stream()
                .filter(line -> line.left().equals("y")).map(BorderAssessment::value).toList();
        assertTrue(onY.containsAll(List.of("-1", "11")), onY::toString);
    }

    /** A remainder of a difference held against a number stops every run where the difference
     *  is past the type, at either end. */
    @Test
    void theDifferenceARemainderIsOfStopsEveryRunPastIt() {
        assertEquals(List.of("x - z where x - z " + plus(GREATEST, 1) + "..",
                        "x - z where x - z .." + plus(LEAST, -1)),
                everyRunStops("Int", "x", "", "Int.floorMod(x - z, 7) >= 1"));
    }

    /** A remainder of a sum over an element of a list of the input stops a run on the element
     *  that takes the sum past the type, as the sum alone does. */
    @Test
    void theSumARemainderIsOfOverAnElementStopsARun() {
        String over = "List.isEmpty(List.filter(n -> %s, x))";
        List<String> ofTheSum = everyRunStops("List<Int>", "x", "", over.formatted("y + n >= 1"));
        assertFalse(ofTheSum.isEmpty(), "the sum alone stops every run past it");
        assertEquals(ofTheSum, everyRunStops("List<Int>", "x", "",
                over.formatted("Int.floorMod(y + n, 7) >= 1")));
        assertEquals(1, mayStop("List<Int>", "x", "",
                over.formatted("Int.floorMod(y + n, 7) >= 1")).size());
    }

    /** A remainder of a place moved by a number is read as the place's own, and a run works out
     *  the moved value all the same: it stops every run where that is past the type, against a
     *  number or another value. */
    @Test
    void thePlaceARemainderIsOfMovedByANumberStopsEveryRunPastItsType() {
        List<String> past = List.of("x + 1 where x " + GREATEST + "..");
        assertEquals(past, everyRunStops("Int", "x", "", "Int.floorMod(x + 1, 7) == 0"));
        assertEquals(past, everyRunStops("Int", "x", "", "Int.floorMod(x + 1, 7) == y"));
    }

    /** A remainder worked out on one arm only is worked out by no run taking the other: the sum
     *  under it stops no row of every run. */
    @Test
    void theSumARemainderOnOneArmIsOfStopsNoRunThatTakesTheOther() {
        assertEquals(List.of(), everyRunStops("Int", "x", "",
                "(if y > 0 then Int.floorMod(x + z, 7) else 1) >= 1"));
    }

    /** Numbers the ways keep well short of the ends never take the sum past its type, and
     *  nothing is said of it. */
    @Test
    void theSumARemainderIsOfKeptWithinItsTypeStopsNoRun() {
        assertEquals(List.of(), mayStop("Small", "Small(x)",
                "guard x >= 0 && z >= 0 && z <= 10 else No { n = 0 }",
                "Int.floorMod(x - z, 7) >= 1"));
    }

    /**
     * A remainder of a sum over an element of a list of every whole number between two stops a
     * run as the sum alone does. The remainder comes round every seventh element, and what it
     * states is read on the first seven ({@code TheWholeNumbersAListStartsWith}); the sum does not come round, and an element past them takes it past the type where none of
     * them does: {@code x} seven short of the end, and {@code y} seven.
     */
    @Test
    void theSumARemainderIsOfOverAWholeNumberInTurnStopsARunAsTheSumAloneDoes() {
        String over = "List.isEmpty(List.filter(n -> %s, List.rangeInclusive(0, y)))";
        List<JsonNode> ofTheSum = mayStop("Int", "x", "", over.formatted("x + n >= 1"));
        assertEquals(1, ofTheSum.size(), ofTheSum::toString);
        assertEquals(1, mayStop("Int", "x", "",
                over.formatted("Int.floorMod(x + n, 7) == 0")).size());
        assertEquals(everyRunStops("Int", "x", "", over.formatted("x + n >= 1")),
                everyRunStops("Int", "x", "", over.formatted("Int.floorMod(x + n, 7) == 0")));
    }

    /** The sum the remainder is of is worked out in the order it is written: {@code x + n} is
     *  past the type before one is added to it, as it is without the remainder. */
    @Test
    void aSumUnderTheSumARemainderOverAWholeNumberInTurnIsOfStopsARunFirst() {
        String over = "List.isEmpty(List.filter(n -> %s, List.rangeInclusive(0, y)))";
        assertEquals(1, mayStop("Int", "x", "",
                over.formatted("Int.floorMod((x + n) + 1, 7) == 0")).size());
        assertEquals(everyRunStops("Int", "x", "", over.formatted("(x + n) + 1 >= 1")),
                everyRunStops("Int", "x", "",
                        over.formatted("Int.floorMod((x + n) + 1, 7) == 0")));
    }

    /** No element on any row the ways leave, or none written, and the remainder is worked out
     *  on no run; over numbers that keep short of the ends, it stops none, and over numbers that
     *  do not, it may stop one. */
    @Test
    void theSumARemainderOverAWholeNumberInTurnIsOfStopsNoRunThatDoesNotWorkItOutPastItsType() {
        assertEquals(List.of(), mayStop("Int", "x", "guard y < 0 else No { n = 0 }",
                "List.isEmpty(List.filter(n -> Int.floorMod(x + n, 7) == 0,"
                        + " List.rangeInclusive(0, y)))"));
        String between = "List.isEmpty(List.filter(n -> Int.floorMod(x + z + n, 7) == 0,"
                + " List.rangeInclusive(1, %s)))";
        assertEquals(1, mayStop("Int", "x", "", between.formatted("1")).size());
        assertEquals(List.of(), mayStop("Int", "x", "", between.formatted("0")));
        String upTo = "List.isEmpty(List.filter(n -> Int.floorMod(n + %s, 7) == 0,"
                + " List.rangeInclusive(0, List.length(x))))";
        assertEquals(1, mayStop("List<Int>", "x", "", upTo.formatted(GREATEST)).size());
        assertEquals(List.of(), mayStop("List<Int>", "x", "", upTo.formatted("5")));
    }

    /** The findings that a rule of {@code f} is one a run may stop in. */
    private static List<JsonNode> mayStop(String type, String bound, String before,
                                          String comparison) {
        Compilation compilation = measured(MODEL.formatted(type, bound, before, comparison));
        JsonNode findings = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("findings");
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode each : findings) {
            if (each.get("kind").asString().equals("rule_may_stop_a_run")) {
                out.add(each);
            }
        }
        return out;
    }

    private static String plus(String number, int by) {
        return new BigInteger(number).add(BigInteger.valueOf(by)).toString();
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured(String model) {
        return MEASURED.computeIfAbsent(model, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }
}
