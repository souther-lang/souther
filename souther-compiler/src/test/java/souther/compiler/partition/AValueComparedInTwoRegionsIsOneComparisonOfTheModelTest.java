package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison a value states is one comparison of the model, however many regions build the value.
 *
 * <p>What the reading of a body says about a comparison is filed under the construct of the model
 * it is, and a value's comparison is one construct whether one region builds the value or two. Read
 * off a tree that holds a copy of the value for each region, one construct arrives once per copy,
 * each under what stood on the way into that region, and the reading was made to refuse that: there
 * is one account of a construct and two copies would be two.
 *
 * <p>Held both ways. The reading is made without being refused, and it holds the comparison the
 * value writes once — a reading that met no comparison in the value would not be refused either,
 * and would be a body whose rules had gone missing.
 */
class AValueComparedInTwoRegionsIsOneComparisonOfTheModelTest {

    private static final String MODEL = """
            module m exposing (f)

            let big = List.length([1, 2, 3]) > 2

            behavior f : (n: Int) -> Int
            let f (n) =
                (if n > 0 then (if big then 1 else 2) else 0)
                + (if n > 5 then (if big then 3 else 4) else 0)
            """;

    private record Read(AnalysisBody analysis, Core emitted, CoverageSites.Plan plan,
                        InputDomain inputs, RuleReadingSource rules) { }

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return new Read(checked.analysisBodies().get("f"), checked.behaviorBodies().get("f"),
                checked.plan(), inputs.get("f"), rules);
    }

    @Test
    void theReadingIsNotRefusedWhereTwoRegionsBuildTheValue() {
        Read read = read();

        assertDoesNotThrow(() -> GuardThresholds.of("f", read.analysis(), read.emitted(),
                read.plan(), read.inputs(), read.rules()));
    }

    @Test
    void theValuesComparisonIsReadOnce() {
        Read read = read();
        ElementBindings elements = ElementBindings.of(read.analysis(), read.rules().newtypes());

        List<ComparisonReadings.Reading> readings = ComparisonReadings.of("f", read.analysis(),
                read.inputs().reading(read.rules()),
                InputReads.ofParametersWhereCallsStand(read.inputs().parameterReads(), elements),
                InputReads.ofParametersWhereCallsStand(Map.of(), elements)).comparisons();

        long ofTheValue = readings.stream()
                .filter(each -> each.occurrence().origin().owner() instanceof WrittenOwner.Body owner
                        && owner.definition().equals("big"))
                .count();
        assertEquals(1, ofTheValue,
                "`big` writes one comparison, and it is read once for the two regions that build it");
    }
}
