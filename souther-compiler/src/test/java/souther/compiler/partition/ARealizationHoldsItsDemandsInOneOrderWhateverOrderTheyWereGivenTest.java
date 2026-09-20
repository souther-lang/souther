package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a search fixed is held in one order, whichever order the demands came in.
 *
 * <p>A reader that walks the demands meets them in the order the realization keeps them, and a
 * realization that kept the order it was given would hand every reader the order some earlier walk
 * happened to reach them in. The demands of one term are told apart by where they write, and two
 * places can be written alike and not be the same one: an optional's present carrier and a sum's
 * case declared as {@code Some} are both {@code @Some}. An order by how a place is spelled ties
 * those two, and leaves them in the order they were given.
 */
class ARealizationHoldsItsDemandsInOneOrderWhateverOrderTheyWereGivenTest {

    private static final NumericTerm.FromOnePosition TERM =
            new NumericTerm.ValueOf(TermPath.of("amount"));

    @Test
    void twoPlacesWrittenAlikeAreTwoPlacesAndTheSampleSaysSo() {
        TermPath carrier = under(Refinement.of(new Case.Presence(true)));
        TermPath declared = under(Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("g", "Some")), false)));

        assertEquals(carrier.toString(), declared.toString(),
                "the two places are meant to be spelled alike, or the check below is about nothing");
        assertNotEquals(carrier, declared, "the two places are meant to be two");
    }

    @Test
    void theDemandsAreHeldInOneOrderWhateverOrderTheyWereGiven() {
        List<RealizationTarget> targets = List.of(
                target(under(Refinement.of(new Case.Presence(true)))),
                target(under(Refinement.of(new Case.SumCase(
                        TypeSymbols.declared(new TypeKey("g", "Some")), false)))),
                target(under(Refinement.of(new Case.SumCase(
                        TypeSymbols.declared(new TypeKey("h", "Some")), false)))),
                target(under(Refinement.of(new Case.Presence(false)))),
                target(TermPath.of("elsewhere")));

        List<List<RealizationTarget>> heldIn = new ArrayList<>();
        for (List<RealizationTarget> given : permutations(targets)) {
            Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
            for (RealizationTarget each : given) {
                fixing.put(each, Count.of(fixing.size()));
            }
            heldIn.add(List.copyOf(new Realization.Found(fixing).fixing().keySet()));
        }

        for (List<RealizationTarget> each : heldIn) {
            assertEquals(heldIn.get(0), each,
                    "the same demands were held in another order for another order they were given in");
        }
    }

    private static TermPath under(Refinement narrowing) {
        return TermPath.of("some").refine(narrowing);
    }

    private static RealizationTarget target(TermPath writeRoot) {
        return new RealizationTarget.AtOnePositionElsewhere(TERM, writeRoot);
    }

    private static <T> List<List<T>> permutations(List<T> these) {
        if (these.size() <= 1) {
            return List.of(these);
        }
        List<List<T>> out = new ArrayList<>();
        for (int at = 0; at < these.size(); at++) {
            List<T> rest = new ArrayList<>(these);
            T first = rest.remove(at);
            for (List<T> tail : permutations(rest)) {
                List<T> whole = new ArrayList<>();
                whole.add(first);
                whole.addAll(tail);
                out.add(whole);
            }
        }
        return out;
    }
}
