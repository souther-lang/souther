package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a run that applies a closure to every element of a list is shown to make a comparison in it
 * on is the place the list's elements stand at: the position's own elements for a list, the
 * entries' values for the values of a map and the keys for the keys of one. A comparison in the
 * closure reads the key through the name the closure gives it, so evidence that every element was
 * walked is told apart by where the elements stand, and a closure over the keys that said it
 * walked the values said nothing a row could be held to.
 */
class AClosureOverTheKeysOfAMapIsMadeOnTheKeysTest {

    private static final String MODEL = """
            module probe
            data Line = { tags: List<String>, rates: Map<String, Int> }

            behavior overList : (l: Line) -> List<Bool>
            let overList (l) = List.map(t -> t == "K", l.tags)
            behavior overKeys : (l: Line) -> List<Bool>
            let overKeys (l) = List.map(k -> k == "K", Map.keys(l.rates))
            behavior overValuesCompared : (l: Line) -> List<Bool>
            let overValuesCompared (l) = List.map(v -> v == 5, Map.values(l.rates))
            behavior overKeysThenValues : (l: Line) -> List<Bool>
            let overKeysThenValues (l) = List.map(k -> k == "K", List.sort(Map.keys(l.rates)))
            """;

    private static final TermPath TAGS = TermPath.of("l").then("tags");

    private static final TermPath RATES = TermPath.of("l").then("rates");

    @Test
    void theElementsAWalkIsMadeOnStandWhereTheListHoldsThem() {
        assertEquals(List.of(TAGS.element()), madeOnEvery("overList"));
        assertEquals(List.of(RATES.key()), madeOnEvery("overKeys"));
        assertEquals(List.of(RATES.element()), madeOnEvery("overValuesCompared"));
    }

    /** A row holding several keys shows all of them only where the place it asks stands in the
     *  keys that were walked, and the elements of the containers around it stand where they
     *  do. */
    @Test
    void theElementsACompositionIsShownOnAreToldApartByWhereThePlaceStands() {
        TermPath groups = TermPath.of("l").then("groups");
        TermPath inner = groups.element().then("rates");
        assertEquals(RATES.key(), ReachWitnesses.Witness.walkedAt(RATES.key(), RATES));
        assertEquals(RATES.element(), ReachWitnesses.Witness.walkedAt(RATES.element(), RATES));
        assertEquals(TAGS.element(), ReachWitnesses.Witness.walkedAt(TAGS.element(), TAGS));
        assertEquals(groups.element(),
                ReachWitnesses.Witness.walkedAt(inner.key(), groups));
        assertEquals(inner.key(), ReachWitnesses.Witness.walkedAt(inner.key(), inner));
    }

    /** What is made of the keys by an operation that puts them in another order is not said. */
    @Test
    void aListMadeOfTheKeysIsNotOneAWalkIsShownMadeOn() {
        assertEquals(Optional.empty(), walked("overKeysThenValues").elements());
    }

    private static List<TermPath> madeOnEvery(String behavior) {
        return walked(behavior).elements().orElseThrow();
    }

    private static ClosureApplications.MadeOnEvery walked(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputReading read = inputs.reading(rules);
        List<ComparisonReadings.Reading> readings = ComparisonReadings.of(behavior, analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).comparisons();
        return readings.getLast().applying().madeOnEvery();
    }
}
