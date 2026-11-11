package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CountWitnesses;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two elements a count is told apart by are a witness only where the container holds the two
 * together, which is what its rules say of the elements it holds and not of each. So each pair is
 * asked of the container, and the witness is a pair it holds, wherever it is among the elements
 * tried: a pair the container refuses is no reason to look at no other.
 */
class ACountWitnessIsAskedOfEveryPairBeforeItIsGivenUpTest {

    private static Optional<CountWitnesses.Witness> witnessOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        compilation.db().ask(new Adequacy.Coverage("demo"));
        Map<String, List<Adequacy.WitnessOfACount>> asked =
                ACountWitnessOverAWrittenValueMakesEveryNumberOfElementsTest.askedOf(compilation);
        List<Adequacy.WitnessOfACount> counts = asked.getOrDefault(behavior, List.of());
        assertFalse(counts.isEmpty(), "the count asked a witness");
        return compilation.db().ask(counts.getFirst()).value().found();
    }

    /** Two that differ: a roster that holds a {@code "a"} alone and anything else beside none of
     *  it holds {@code "b"} and {@code "c"} together and no pair with {@code "a"}. */
    @Test
    void twoThatDifferAreThePairTheContainerHoldsWhereTheFirstElementIsInNoSuchPair() {
        Optional<CountWitnesses.Witness> found = witnessOf("""
                module demo

                data Item = { id: String, qty: Int }

                data Roster = List<Item>
                    invariant List.length(value) <= 1
                            || List.length(List.filter(p -> p.id == "a", value)) == 0

                behavior keptIds : (xs: Roster, k: Int) -> Bool
                let keptIds (xs, k) = Set.size(Set.fromList(List.map(p -> p.id,
                        List.filter(p -> p.id == "a" || p.id == "b" || p.id == "c",
                                xs.value)))) == k
                """, "keptIds");
        assertTrue(found.isPresent(), "a pair the container holds is found");
        assertFalse(found.get().one().text().contains("\"a\""), found.get().one().text());
        assertFalse(found.get().other().text().contains("\"a\""), found.get().other().text());
    }

    /** One the statement holds of and one it fails of: a roster that holds an element of none
     *  alone and anything else beside none of it holds the pair of the others, though the element
     *  of none is the first the statement fails of. */
    @Test
    void oneKeptAndOneDroppedAreThePairTheContainerHoldsWhereTheFirstOfEachIsInNoSuchPair() {
        Optional<CountWitnesses.Witness> found = witnessOf("""
                module demo

                data Item = { id: String, qty: Int }

                data Roster = List<Item>
                    invariant List.length(value) <= 1
                            || List.length(List.filter(p -> p.qty == 0, value)) == 0

                behavior kept : (xs: Roster, k: Int) -> Bool
                let kept (xs, k) = List.length(List.filter(p -> p.qty > 3, xs.value)) == k
                """, "kept");
        assertTrue(found.isPresent(), "a pair the container holds is found");
        assertFalse(found.get().one().text().contains("qty = 0"), found.get().one().text());
        assertFalse(found.get().other().text().contains("qty = 0"), found.get().other().text());
    }
}
