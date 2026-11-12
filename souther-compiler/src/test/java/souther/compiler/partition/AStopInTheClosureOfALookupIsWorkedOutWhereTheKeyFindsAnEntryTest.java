package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operator inside the closure of an option a lookup made is worked out where the lookup finds
 * an entry, which turns on the map and on the key it is made at; one inside the closure of a
 * list is worked out where the list holds something, which turns on the list alone.
 */
class AStopInTheClosureOfALookupIsWorkedOutWhereTheKeyFindsAnEntryTest {

    private static final TermPath KEY = TermPath.of("k");
    private static final TermPath MAP = TermPath.of("m");
    private static final TermPath LIST = TermPath.of("xs");

    @Test
    void aStopInTheClosureOfALookupIsWorkedOutWhereTheMapHoldsTheKey() {
        List<Pullback.WorkedOutWhere> wheres = wheresOfTheStops(
                "Option.withDefault(false, Option.map(r -> 100 / r > d, Map.get(k, m))) || d > 3");
        assertEquals(1, wheres.size(), wheres.toString());
        assertEquals(List.of(Set.of(MAP)), wheres.getFirst().oneHolds());
        assertTrue(wheres.getFirst().decidedBy().containsAll(Set.of(MAP, KEY)),
                wheres.toString());
        assertTrue(wheres.getFirst().known());
    }

    @Test
    void aStopInTheClosureOfAListIsWorkedOutWhereTheListHoldsSomething() {
        assertEquals(List.of(new Pullback.WorkedOutWhere(List.of(Set.of(LIST)), Set.of(), true)),
                wheresOfTheStops("List.any(x -> 100 / x > d, xs) || d > 3"));
    }

    @Test
    void aStopOutsideEveryClosureIsWorkedOutOnEveryRun() {
        List<Pullback.WorkedOutWhere> wheres = wheresOfTheStops("100 / (d * d) > 3 || d > 3");
        assertFalse(wheres.isEmpty());
        assertTrue(wheres.stream().allMatch(Pullback.WorkedOutWhere.ALWAYS::equals),
                wheres.toString());
    }

    /** A division by a number the arithmetic composes into a form is told where its divisor is not
     *  nought, and leaves no tie. */
    @Test
    void aDivisionByAFormIsToldAndLeavesNoStopUnsaid() {
        assertEquals(List.of(), wheresOfTheStops("100 / d > 3 || d > 3"));
    }

    /** An operator owed where its total fits is worked out where the lookup finds an entry,
     *  as a tie is: whether a run gets past it turns on what decides that. */
    @Test
    void anOperatorOwedInTheClosureOfALookupIsWorkedOutWhereTheMapHoldsTheKey() {
        List<Pullback.WorkedOutWhere> wheres = answeredAtTheLast(
                "Option.withDefault(0, Option.map(r -> List.sum(xs), Map.get(k, m))) > d"
                        + " || d > 3").owed().stream().map(Pullback.StopObligation::where)
                .toList();
        assertEquals(1, wheres.size(), wheres.toString());
        assertEquals(List.of(Set.of(MAP)), wheres.getFirst().oneHolds());
        assertTrue(wheres.getFirst().decidedBy().containsAll(Set.of(MAP, KEY)),
                wheres.toString());
    }

    /** Where each tie the run to the last comparison of {@code m} gets past is worked out. */
    private static List<Pullback.WorkedOutWhere> wheresOfTheStops(String body) {
        return answeredAtTheLast(body).tied().stream().map(DemandReading.Tie::where).toList();
    }

    /** What the run to the last comparison of {@code m} gets past. */
    private static DemandReading.Answered answeredAtTheLast(String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (k: String, m: Map<String, Int>, xs: List<Int>, d: Int) -> Bool
                let m (k, m, xs, d) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("m");
        AnalysisBody analysis = checked.analysisBodies().get("m");
        List<ComparisonReadings.Reading> readings = ComparisonReadings.of("m", analysis,
                inputs.reading(rules),
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).comparisons();
        return readings.getLast().getsPast();
    }
}
