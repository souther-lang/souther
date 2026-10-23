package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /**
     * The two cases of a condition, each with its own arm, are denied as the same two cases with
     * each arm denied, and so they are beside a third part of the same "or", as two statements
     * joined by one are: {@code (a ∧ b) ∨ (¬a ∧ c) ∨ c} fails where {@code ((¬a ∧ ¬c) ∨ (a ∧ ¬b))
     * ∧ ¬c} holds, one choice of the cases of {@code a} where every part failing apart would be
     * two.
     */
    @Test
    void theCasesOfAConditionBesideAThirdPartAreDeniedCaseByCase() {
        Proposition a = truth(0, true);
        Proposition b = truth(1, true);
        Proposition c = truth(2, true);
        Proposition stated = Proposition.any(List.of(Proposition.all(List.of(a, b)),
                Proposition.all(List.of(a.denied(), c)), c));

        assertEquals(Proposition.all(List.of(
                        Proposition.any(List.of(Proposition.all(List.of(a.denied(), c.denied())),
                                Proposition.all(List.of(a, b.denied())))),
                        c.denied())),
                stated.denied());
    }

    private static Proposition truth(int atom, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(ATOMS.get(atom)), holds);
    }

    /**
     * What a denial by cases states on every assignment is the denial's, beside a third part or
     * not, and the denial of two cases is a disjunction each part of which holds one condition or
     * its denial — which is what lets the choices of several such denials close where they take
     * the condition both ways.
     */
    @Test
    void theCasesOfAConditionAreDeniedCaseByCase() {
        List<Proposition> pool = pool();
        Proposition condition = truth(0, true);
        List<Proposition> beside = new ArrayList<>();
        beside.add(null);
        for (int atom = 1; atom < ATOMS.size(); atom++) {
            beside.add(truth(atom, true));
            beside.add(truth(atom, false));
        }
        int kept = 0;
        for (Proposition third : beside) {
            for (Proposition one : pool) {
                for (Proposition other : pool) {
                    List<Proposition> parts = new ArrayList<>(List.of(
                            Proposition.all(List.of(condition, one)),
                            Proposition.all(List.of(condition.denied(), other))));
                    if (third != null) {
                        parts.add(third);
                    }
                    Proposition cases = Proposition.any(parts);
                    Proposition denied = cases.denied();
                    for (Map<TermPath, Boolean> values : assignments()) {
                        assertEquals(!value(cases, values), value(denied, values),
                                () -> "the denial of " + cases.key() + " under " + values);
                    }
                    if (third == null && casesOfOneCondition(denied)) {
                        kept++;
                    }
                }
            }
        }
        assertTrue(kept > 0, "some denial of two cases is kept as two cases");
    }

    /** Whether {@code stated} is a disjunction each part of which holds one condition or its
     *  denial. */
    private static boolean casesOfOneCondition(Proposition stated) {
        if (!(stated instanceof Proposition.Any any)) {
            return false;
        }
        List<Proposition> disjuncts = any.parts();
        return conjunctsOf(disjuncts.getFirst()).stream().anyMatch(each -> disjuncts.stream()
                .allMatch(part -> conjunctsOf(part).contains(each)
                        || conjunctsOf(part).contains(each.denied())));
    }

    private static List<Proposition> conjunctsOf(Proposition stated) {
        return stated instanceof Proposition.All all ? all.parts() : List.of(stated);
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
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    values.get(at) == holds;
            case Proposition.All all -> all.parts().stream().allMatch(part -> value(part, values));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> value(part, values));
            default -> throw new IllegalArgumentException("no atom of this test: " + stated);
        };
    }
}
