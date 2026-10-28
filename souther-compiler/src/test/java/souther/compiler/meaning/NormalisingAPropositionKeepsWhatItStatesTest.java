package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

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
     * What follows from a condition and what follows from its denial, joined, are the cases of the
     * condition only where its denial holds on every row it fails: joined that way or kept as the
     * two implications, they state the same on every assignment, whatever the condition and the
     * rest are. A condition that may answer nothing fails where its denial fails too, and one read
     * on two applications may hold on one and fail on the other, so neither is two cases, and the
     * implications are kept as they were written.
     */
    @Test
    void aConjunctionIsTheCasesOnlyOfAConditionItsDenialFailsBeside() {
        Proposition a = truth(0, true);
        Proposition b = truth(1, true);
        Proposition partial = Proposition.whereItAnswers(b, a);
        Proposition onBoth = Proposition.onAnApplication(List.of(a, b));
        List<Proposition> arms = new ArrayList<>(leaves());
        arms.add(Proposition.whereItAnswers(truth(2, true), b));
        int checked = 0;
        for (Proposition condition : List.of(a, Proposition.all(List.of(a, b)), partial,
                onBoth)) {
            for (Proposition one : arms) {
                for (Proposition other : arms) {
                    List<Proposition> implications = List.of(
                            Proposition.any(List.of(condition.denied(), one)),
                            Proposition.any(List.of(condition, other)));
                    Proposition joined = Proposition.all(implications);
                    for (Map<TermPath, Boolean> values : assignments()) {
                        assertEquals(implications.stream().allMatch(each -> value(each, values)),
                                value(joined, values),
                                () -> "the conjunction of " + implications.stream()
                                        .map(Proposition::key).toList() + " under " + values);
                        checked++;
                    }
                    // Two arms that are an atom and its denial are the cases of that atom, which
                    // hold the condition in each, and so are arms over the condition's own atoms;
                    // other arms are cases of nothing here.
                    if ((condition == partial || condition == onBoth)
                            && overTheThirdAtom(one) && overTheThirdAtom(other)
                            && !one.equals(other.denied())) {
                        assertFalse(casesOf(joined, condition), joined.key());
                    }
                }
            }
        }
        assertTrue(checked > 0, "something was checked");
        assertTrue(casesOf(Proposition.all(List.of(
                        Proposition.any(List.of(a.denied(), b)),
                        Proposition.any(List.of(a, truth(2, true))))), a),
                "two implications of a condition and its denial are its cases");
    }

    /** Whether {@code stated} names no atom but the third, or none. */
    private static boolean overTheThirdAtom(Proposition stated) {
        return !stated.key().contains("a") && !stated.key().contains("b");
    }

    /** Whether {@code stated} is a disjunction each part of which holds {@code condition} or its
     *  denial. */
    private static boolean casesOf(Proposition stated, Proposition condition) {
        return stated instanceof Proposition.Any any && any.parts().stream()
                .allMatch(part -> conjunctsOf(part).contains(condition)
                        || conjunctsOf(part).contains(condition.denied()));
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

    /**
     * The cases of two conditions in one "or", as the reasons a list is empty of are: denied, it
     * states what every part failing does, and is one choice of the cases of each condition — two
     * by two, where every part failing apart is a choice of two for each part.
     */
    @Test
    void theCasesOfTwoConditionsInOneDisjunctionAreTwoChoicesOfTwo() {
        Proposition a = truth(0, true);
        Proposition b = truth(1, true);
        Proposition c = truth(2, true);
        List<Proposition> parts = List.of(Proposition.all(List.of(a, c)),
                Proposition.all(List.of(a.denied(), c.denied())),
                Proposition.all(List.of(b, c.denied())), Proposition.all(List.of(b.denied(), c)));
        Proposition stated = Proposition.any(parts);

        for (Map<TermPath, Boolean> values : assignments()) {
            assertEquals(parts.stream().allMatch(each -> value(each.denied(), values)),
                    value(stated.denied(), values),
                    () -> "the denial of " + stated.key() + " under " + values);
        }
        assertEquals(16, parts.stream().mapToLong(each -> waysOf(each.denied()))
                .reduce(1, (one, other) -> one * other));
        assertEquals(4, waysOf(stated.denied()), stated.denied().key());
    }

    /** How many ways a row may take through {@code stated}: one of each disjunction's parts, and
     *  every part of each conjunction. */
    private static long waysOf(Proposition stated) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream()
                    .mapToLong(NormalisingAPropositionKeepsWhatItStatesTest::waysOf)
                    .reduce(1, (one, other) -> one * other);
            case Proposition.Any any -> any.parts().stream()
                    .mapToLong(NormalisingAPropositionKeepsWhatItStatesTest::waysOf).sum();
            default -> 1;
        };
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
    @Test
    void theSpellingOfADenialIsTheSpellingOfTheDenialOfEveryProposition() {
        List<Proposition> all = new ArrayList<>(pool());
        for (boolean holds : new boolean[] {true, false}) {
            all.add(new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                    ExactRatio.of(-3), Map.of(new DecisionAtom.OfTheInput(
                            new NumericTerm.ValueOf(ATOMS.get(0))), ExactRatio.ONE)), Rel.GT),
                    holds));
        }
        for (Proposition each : all) {
            assertEquals(each.denied().key(), each.deniedKey(), each.key());
            assertEquals(each.key(), each.denied().deniedKey(), each.key());
        }
    }

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
