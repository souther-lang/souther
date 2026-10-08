package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Joining, disjoining and denying a proposition state what the connective says of the parts, on
 * every way the parts can come out.
 *
 * <p>The rules of a derivation conclude through these, and a step that changed what was stated on
 * the way would be a step no rule took. So they are held to what they mean: every proposition over
 * three truths up to one join deep, joined in pairs and denied, evaluated on every assignment of the
 * three, against what the connective computes of its parts' values.
 */
class NormalisingAPropositionKeepsWhatItStatesTest {

    private static final List<TermPath> ATOMS =
            List.of(TermPath.of("a"), TermPath.of("b"), TermPath.of("c"));

    @Test
    void joiningDisjoiningAndDenyingStateWhatTheConnectiveSays() {
        List<Proposition> pool = pool();
        int checked = 0;
        for (Map<TermPath, Boolean> values : assignments()) {
            for (Proposition one : pool) {
                assertEquals(!value(one, values), value(one.denied(), values),
                        () -> "the denial of " + one.key() + " under " + values);
                for (Proposition other : pool) {
                    List<Proposition> parts = List.of(one, other);
                    assertEquals(value(one, values) && value(other, values),
                            value(Proposition.all(parts), values),
                            () -> "both of " + parts.stream().map(Proposition::key).toList()
                                    + " under " + values);
                    assertEquals(value(one, values) || value(other, values),
                            value(Proposition.any(parts), values),
                            () -> "either of " + parts.stream().map(Proposition::key).toList()
                                    + " under " + values);
                    checked++;
                }
            }
        }
        assertFalse(checked == 0, "something was checked");
    }

    /** Both truth values, each atom both ways round, and every pair of those joined either way. */
    private static List<Proposition> pool() {
        List<Proposition> leaves = new ArrayList<>(List.of(new Proposition.Always(true),
                new Proposition.Always(false)));
        for (TermPath atom : ATOMS) {
            leaves.add(new Proposition.Truth(new DecisionSubject.AnInput(atom), true));
            leaves.add(new Proposition.Truth(new DecisionSubject.AnInput(atom), false));
        }
        List<Proposition> out = new ArrayList<>(leaves);
        for (Proposition one : leaves) {
            for (Proposition other : leaves) {
                out.add(Proposition.all(List.of(one, other)));
                out.add(Proposition.any(List.of(one, other)));
            }
        }
        return out;
    }

    private static List<Map<TermPath, Boolean>> assignments() {
        List<Map<TermPath, Boolean>> out = new ArrayList<>();
        for (int bits = 0; bits < 1 << ATOMS.size(); bits++) {
            int at = bits;
            out.add(Map.of(ATOMS.get(0), (at & 1) != 0, ATOMS.get(1), (at & 2) != 0,
                    ATOMS.get(2), (at & 4) != 0));
        }
        return out;
    }

    private static boolean value(Proposition stated, Map<TermPath, Boolean> values) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds;
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds) ->
                    values.get(at) == holds;
            case Proposition.All all -> all.parts().stream().allMatch(part -> value(part, values));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> value(part, values));
            default -> throw new IllegalArgumentException("no atom of this test: " + stated);
        };
    }
}
