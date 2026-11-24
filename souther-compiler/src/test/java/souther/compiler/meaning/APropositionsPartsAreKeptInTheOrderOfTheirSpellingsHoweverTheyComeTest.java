package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A conjunction and a disjunction hold their parts in the order of their spellings, each spelling
 * once, whatever order the parts are handed over in — in order already, the other way round, with
 * one spelled twice, or inside a conjunction made before.
 *
 * <p>Held against the order a sorted table keeps, over every order of a few parts: a part placed
 * by asking the last one kept first is placed where the table would put it.
 */
class APropositionsPartsAreKeptInTheOrderOfTheirSpellingsHoweverTheyComeTest {

    private static Proposition truth(String at, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), holds);
    }

    /** What a sorted table keeps of {@code parts}, nested conjunctions taken apart. */
    private static List<Proposition> asATableKeeps(List<Proposition> parts, boolean every) {
        SortedMap<Spelling, Proposition> kept = new TreeMap<>();
        for (Proposition part : parts) {
            List<Proposition> flat = switch (part) {
                case Proposition.All all when every -> all.parts();
                case Proposition.Any any when !every -> any.parts();
                default -> List.of(part);
            };
            flat.forEach(one -> kept.putIfAbsent(one.spelling(), one));
        }
        return List.copyOf(kept.values());
    }

    private static List<Proposition> partsOf(Proposition joined) {
        return switch (joined) {
            case Proposition.All all -> all.parts();
            case Proposition.Any any -> any.parts();
            default -> List.of(joined);
        };
    }

    private static void permutations(List<Proposition> left, List<Proposition> so,
                                     List<List<Proposition>> out) {
        if (left.isEmpty()) {
            out.add(List.copyOf(so));
            return;
        }
        for (int at = 0; at < left.size(); at++) {
            List<Proposition> rest = new ArrayList<>(left);
            Proposition one = rest.remove(at);
            so.add(one);
            permutations(rest, so, out);
            so.removeLast();
        }
    }

    @Test
    void everyOrderOfThePartsComesToTheOrderOfTheirSpellings() {
        Proposition a = truth("a", true);
        Proposition b = truth("b", false);
        Proposition c = truth("c", true);
        Proposition d = truth("d", true);
        Proposition twiceA = truth("a", true);
        Proposition madeBefore = Proposition.all(List.of(b, d));
        Proposition anyMadeBefore = Proposition.any(List.of(a, c));
        List<List<Proposition>> orders = new ArrayList<>();
        permutations(List.of(a, b, c, d, twiceA), new ArrayList<>(), orders);
        permutations(List.of(madeBefore, a, c, twiceA), new ArrayList<>(), orders);
        permutations(List.of(anyMadeBefore, b, d), new ArrayList<>(), orders);
        int asked = 0;
        for (List<Proposition> order : orders) {
            for (boolean every : new boolean[]{true, false}) {
                Proposition joined = every ? Proposition.all(order) : Proposition.any(order);
                List<Proposition> expected = asATableKeeps(order, every);
                assertEquals(expected, partsOf(joined), order + (every ? " all" : " any"));
                asked++;
            }
        }
        assertEquals(2 * (120 + 24 + 6), asked);
    }
}
