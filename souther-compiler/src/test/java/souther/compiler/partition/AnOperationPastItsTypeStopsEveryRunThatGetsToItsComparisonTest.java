package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
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

/**
 * Where an operation a comparison works out comes to past its type, and every operation a run may
 * work out before it gets past, every run that gets to the comparison there stops in it. That is
 * said beside the rule, as the operation and the rows, and leaves nothing open: no measure waits
 * on it, and no question stands for it.
 *
 * <p>The rows are said over as many numbers as the operation is over, and an operation worked
 * out of another's value comes after it on every run.
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
