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
 * Where an operation a comparison works out comes to past its type at a value of a position,
 * whatever else it is over holds, every run that gets to the comparison there stops in it. That is
 * said beside the rule, as the values and the operation, and leaves nothing open: no measure waits
 * on it, and no question stands for it.
 *
 * <p>Said of a position only where the operation alone rules every row there out. Where the other
 * numbers it is over can bring it back within its type, a row there gets past, and nothing is said.
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

    /** Each run every run stops at, as {@code at from..to in operation}. */
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
                    out.add(stop.get("at").asString() + " " + stop.get("from").asString() + ".."
                            + stop.get("to").asString() + " in " + stop.get("operation")
                            .asString());
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
        assertEquals(List.of("x " + GREATEST + ".." + GREATEST + " in x + 1"),
                everyRunStops("Int", "x", "", "x + 1 == y"));
        assertEquals(List.of(), standing("Int", "x", "", "x + 1 == y"),
                "a run shown to stop leaves nothing open");
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

    /** Every value of {@code x} has a {@code z} that brings the sum back within the type. */
    @Test
    void aSumOverTwoPositionsStopsNoValueOfEither() {
        assertEquals(List.of(), everyRunStops("Int", "x", "", "x + z == y"));
    }

    /** A number taken away is weighed against its own end: one less than nought less the least
     *  two are past the greatest. */
    @Test
    void aNumberTakenAwayStopsAtTheOtherEnd() {
        assertEquals(List.of("x " + LEAST + ".." + new BigInteger(LEAST).add(BigInteger.ONE)
                        + " in -x + 1"),
                everyRunStops("Int", "x", "", "1 - x == y"));
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
