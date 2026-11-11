package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Sig;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.partition.FixtureTemplate;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The witness of a count of the entries of a map that meet a statement is two entries the boundary
 * builds under two keys, one the statement holds of and one it fails of: whatever the statement
 * says of the key, and whatever the type of the map asks of how many entries it holds.
 *
 * <p>Asked of the witness and not of what a relation made of it: a count not shown at every value
 * says nothing of whether the entries it was told apart by were looked for where the statement
 * says they are.
 */
class ACountWitnessOverAMapIsOfEntriesTheBoundaryKeepsUnderTwoKeysTest {

    private static final String KEY = "a-key-the-type-does-not-offer";

    private static final String SOURCE = """
            module demo

            data Exactly = Map<String, Int>
                invariant Map.size(value) == 2

            behavior named : (m: Map<String, Int>, k: Int) -> Bool
            let named (m, k) =
                Map.size(Map.filterEntries((key, v) -> key == "%s", m)) == k

            behavior held : (m: Exactly, k: Int) -> Bool
            let held (m, k) = Map.size(Map.filterEntries((key, v) -> v > 5, m.value)) == k
            """.formatted(KEY);

    private static final Compilation COMPILED = compiled();

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.db().ask(new Adequacy.Coverage("demo"));
        return compilation;
    }

    /** What the boundary builds of the container of the witness's row, the row being the witness
     *  as it is written. */
    private static ObservedValue builtOfTheTwo(String behavior, CountWitnesses.Witness witness) {
        Db db = COMPILED.db();
        Sig sig = db.ask(new Bodies.Signatures("demo")).value().get(behavior);
        FixtureTemplate row = witness.inputs().get(witness.container());
        ObservedValue built = Adequacy.constructing(db, "demo")
                .build(sig.ins().get(witness.container()), row)
                instanceof BoundaryValues.Built.Value(ObservedValue value) ? value : null;
        // The name the map is worn under is taken off.
        return built instanceof ObservedValue.Constructed(var _, var fields)
                && fields.containsKey("value") ? fields.get("value") : built;
    }

    private static CountWitnesses.Witness witnessOf(String behavior) {
        List<Adequacy.WitnessOfACount> counts = ACountWitnessOverAWrittenValueMakesEveryNumberOfElementsTest
                .askedOf(COMPILED).getOrDefault(behavior, List.of());
        assertTrue(!counts.isEmpty(), behavior + " asked a witness of its count");
        Optional<CountWitnesses.Witness> found = COMPILED.db().ask(counts.getFirst()).value()
                .found();
        assertTrue(found.isPresent(), behavior + " has a witness");
        return found.get();
    }

    private static void holdsTwoEntriesUnderTwoKeys(String behavior,
                                                    CountWitnesses.Witness witness) {
        assertTrue(builtOfTheTwo(behavior, witness) instanceof ObservedValue.Mapping(var entries)
                && entries.size() == 2, behavior + ": two entries: " + witness.inputs());
    }

    /** The key the statement names is the key of the entry it holds of, which no type of the key
     *  offers: the place the statement reads is the key, and not a collection of keys. */
    @Test
    void aKeyTheStatementNamesIsTheKeyOfTheEntryItHoldsOf() {
        CountWitnesses.Witness witness = witnessOf("named");
        holdsTwoEntriesUnderTwoKeys("named", witness);
        assertTrue(witness.one().text().startsWith("(\"" + KEY + "\""), witness.one().text());
    }

    /** A map that must hold two is held to the two the witness names, under two keys. */
    @Test
    void aMapHeldToTwoEntriesIsWitnessedByTheTwo() {
        CountWitnesses.Witness witness = witnessOf("held");
        holdsTwoEntriesUnderTwoKeys("held", witness);
        assertEquals(CountWitnesses.Expansion.INDEPENDENT_KEYS, witness.expansion());
    }
}
