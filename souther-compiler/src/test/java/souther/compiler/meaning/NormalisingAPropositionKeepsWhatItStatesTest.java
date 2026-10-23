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

    /**
     * A disjunction is denied by the cases of a condition only where the condition's denial holds
     * on every row it fails: denied that way or part by part, it states the same on every
     * assignment, whatever the condition is. A condition that may answer nothing fails where its
     * denial fails too, and one read on two applications may hold on one and fail on the other, so
     * neither is two cases, and each is denied part by part.
     */
    @Test
    void aDisjunctionIsDeniedByTheCasesOnlyOfAConditionItsDenialFailsBeside() {
        Proposition a = truth(0, true);
        Proposition b = truth(1, true);
        List<Proposition> conditions = List.of(a, Proposition.all(List.of(a, b)),
                Proposition.whereItAnswers(b, a), Proposition.onAnApplication(List.of(a, b)));
        int checked = 0;
        for (Proposition condition : conditions) {
            for (Proposition one : leaves()) {
                for (Proposition other : leaves()) {
                    Proposition cases = Proposition.any(List.of(
                            Proposition.all(List.of(condition, one)),
                            Proposition.all(List.of(condition.denied(), other))));
                    Proposition partByPart = cases instanceof Proposition.Any any
                            ? Proposition.all(any.parts().stream().map(Proposition::denied)
                            .toList())
                            : cases.denied();
                    Proposition denied = cases.denied();
                    for (Map<TermPath, Boolean> values : assignments()) {
                        assertEquals(value(partByPart, values), value(denied, values),
                                () -> "the denial of " + cases.key() + " under " + values);
                        checked++;
                    }
                }
            }
        }
        assertTrue(checked > 0, "something was checked");
    }

    /**
     * A statement said to be denied wherever it fails is: on every assignment its denial holds
     * exactly where it does not, joined into others or not. One that may answer nothing, or that is
     * read on two applications, is not said to be, and there is an assignment where it and its
     * denial are not the two cases of one statement.
     */
    @Test
    void aStatementSaidToBeDeniedWhereverItFailsIs() {
        List<Proposition> partial = List.of(Proposition.whereItAnswers(truth(1, true),
                        truth(0, true)),
                Proposition.onAnApplication(List.of(truth(0, true), truth(1, true))));
        List<Proposition> parts = new ArrayList<>(leaves());
        parts.addAll(partial);
        List<Proposition> stated = new ArrayList<>(parts);
        for (Proposition one : parts) {
            for (Proposition other : parts) {
                stated.add(Proposition.all(List.of(one, other)));
                stated.add(Proposition.any(List.of(one, other)));
            }
        }
        int said = 0;
        for (Proposition each : stated) {
            boolean complement = assignments().stream()
                    .allMatch(values -> value(each.denied(), values) != value(each, values));
            if (Proposition.deniedWhereverItFails(each)) {
                said++;
                assertTrue(complement, () -> "the denial of " + each.key() + " is its complement");
            }
        }
        for (Proposition each : partial) {
            assertFalse(Proposition.deniedWhereverItFails(each), each.key());
            assertFalse(assignments().stream()
                            .allMatch(values -> value(each.denied(), values) != value(each, values)),
                    () -> "some assignment where " + each.key() + " and its denial are not cases");
        }
        assertTrue(said > 0, "some statement is said to be denied wherever it fails");
    }

    /**
     * A statement read on two applications holds on one and fails on the other at once, so it
     * beside its denial is no statement that fails whatever its parts are.
     */
    @Test
    void aStatementOnTwoApplicationsBesideItsDenialMayHold() {
        Proposition onBoth = Proposition.onAnApplication(List.of(truth(0, true), truth(1, true)));

        assertFalse(TruthTable.failsWhateverItsPartsAre(
                Proposition.all(List.of(onBoth, onBoth.denied()))));
    }

    private static Proposition truth(int atom, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(ATOMS.get(atom)), holds);
    }

    /**
     * What a denial by cases states on every assignment is the denial's, beside a third part or
     * not, and the denial of two cases is a disjunction each part of which holds one condition or
     * its denial — which is what lets the choices of several such denials close where they take
     * the condition both ways. Beside a third part the arms are the leaves: what the third part
     * changes is which parts are cases, and an arm joined deeper is denied as it is without one.
     */
    @Test
    void theCasesOfAConditionAreDeniedCaseByCase() {
        Proposition condition = truth(0, true);
        List<Proposition> beside = new ArrayList<>();
        beside.add(null);
        for (int atom = 1; atom < ATOMS.size(); atom++) {
            beside.add(truth(atom, true));
            beside.add(truth(atom, false));
        }
        int kept = 0;
        for (Proposition third : beside) {
            List<Proposition> arms = third == null ? pool() : leaves();
            for (Proposition one : arms) {
                for (Proposition other : arms) {
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

    /** Both truth values and each atom both ways round. */
    private static List<Proposition> leaves() {
        List<Proposition> out = new ArrayList<>(List.of(new Proposition.Always(true),
                new Proposition.Always(false)));
        for (TermPath atom : ATOMS) {
            out.add(new Proposition.Truth(new DecisionSubject.AnInput(atom), true));
            out.add(new Proposition.Truth(new DecisionSubject.AnInput(atom), false));
        }
        return out;
    }

    /** The leaves, and every pair of those joined either way. */
    private static List<Proposition> pool() {
        List<Proposition> leaves = leaves();
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
            // Holds where it answers and states it; its denial answers there as well, so neither
            // holds where it does not.
            case Proposition.WhereItAnswers where -> value(where.answers(), values)
                    && value(where.states(), values);
            // Holds where some application's statement does, and its denial where some
            // application's denial does: one of each on two applications that differ.
            case Proposition.OnAnApplication applications -> applications.each().stream()
                    .anyMatch(each -> value(each, values));
            default -> throw new IllegalArgumentException("no atom of this test: " + stated);
        };
    }
}
