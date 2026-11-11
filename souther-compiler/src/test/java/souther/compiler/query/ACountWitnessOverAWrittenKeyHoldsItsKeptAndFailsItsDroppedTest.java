package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.check.Sig;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.values.Operand;
import souther.compiler.values.Value;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count of the elements whose map holds a key the statement writes is witnessed by a row built
 * from the rows' own values: the element it is kept for holds the key and the one it is dropped
 * for does not, and counting the row's elements by the count itself answers one.
 */
class ACountWitnessOverAWrittenKeyHoldsItsKeptAndFailsItsDroppedTest {

    private static final String SOURCE = """
            module demo

            data Line = { rates: Map<String, Int> }

            behavior forecast : (lines: List<Line>, k: Int) -> Bool
            let forecast (lines, k) =
                List.length(List.filter(l -> Map.containsKey("USD", l.rates), lines)) == k
            """;

    private static final TermPath LINES = TermPath.of("lines");

    private static final TermPath RATES = LINES.element().then("rates");

    private static Quantity.HowManyMeet counting(boolean holds) {
        return new Quantity.HowManyMeet(new DecisionSubject.AnInput(LINES),
                new Proposition.Some(new DecisionSubject.AnInput(RATES),
                        new Proposition.SameValue(new DecisionSubject.AnInput(RATES.key()),
                                new Operand.Written<DecisionSubject>(Value.text("USD")), true),
                        holds));
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }

    private static CountWitnesses.Witness witnessIn(Compilation compilation,
                                                    Quantity.HowManyMeet count) {
        Set<ConditionOutcomeSite> reaching = new HashSet<>();
        compilation.db().ask(new Bodies.Observable("demo")).value().plan().sites().forEach(site -> {
            if (site instanceof CoverageSites.ComparisonSite compared
                    && compared.body().equals("forecast")) {
                reaching.add(compared.index());
            }
        });
        Optional<CountWitnesses.Witness> found = compilation.db()
                .ask(new Adequacy.WitnessOfACount("demo", "forecast", count, reaching))
                .value().found();
        assertTrue(found.isPresent(), "a witness is found");
        return found.get();
    }

    /** The count of a witness's elements by the count itself, where the elements are the given
     *  ones. */
    private static Optional<Integer> countedOn(Compilation compilation,
                                               Quantity.HowManyMeet count,
                                               List<FixtureTemplate> inputs) {
        Db db = compilation.db();
        Sig sig = db.ask(new Bodies.Signatures("demo")).value().get("forecast");
        FixturesAtTheBoundary building = Adequacy.constructing(db, "demo");
        InputReading read = db.ask(new Adequacy.Inputs("demo")).value().get("forecast")
                .reading(RuleReadings.of(compilation, "demo"));
        return CountWitnesses.metOn(count, "forecast", read, inputs,
                (at, fixture) -> building.build(sig.ins().get(at), fixture)
                        instanceof BoundaryValues.Built.Value(ObservedValue value)
                        ? Optional.of(value) : Optional.<ObservedValue>empty());
    }

    @Test
    void theElementKeptHoldsTheWrittenKeyAndTheOneDroppedDoesNot() {
        Compilation compilation = compiled();
        CountWitnesses.Witness witness = witnessIn(compilation, counting(true));
        assertTrue(witness.kept().text().contains("\"USD\""), witness.kept().text());
        assertTrue(!witness.dropped().text().contains("\"USD\""), witness.dropped().text());
        assertEquals(Optional.of(1), countedOn(compilation, counting(true), witness.inputs()));
    }

    @Test
    void theElementsKeptAndDroppedSwapWhereTheMapMustNotHoldTheKey() {
        Compilation compilation = compiled();
        CountWitnesses.Witness witness = witnessIn(compilation, counting(false));
        assertTrue(!witness.kept().text().contains("\"USD\""), witness.kept().text());
        assertTrue(witness.dropped().text().contains("\"USD\""), witness.dropped().text());
        assertEquals(Optional.of(1), countedOn(compilation, counting(false), witness.inputs()));
    }
}
