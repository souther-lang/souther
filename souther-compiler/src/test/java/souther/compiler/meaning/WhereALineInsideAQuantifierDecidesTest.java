package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation inside a quantifier is a line where the element the quantifier chose crosses it, and
 * where it decides is said of that element and of every other quantifier whole.
 *
 * <p>Two quantifiers over one container choose an element each, and the two may be different
 * elements. Where a line inside one of them decides is where the other holds of an element of its
 * own; said of the line's element, it would ask one element to be what two are.
 */
class WhereALineInsideAQuantifierDecidesTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(XS);
    private static final TermPath N = XS.element().then("n");
    private static final TermPath A = TermPath.of("a");

    /**
     * Some element above nought and some element below it: the line at nought on the first
     * decides where some element is below nought, which is the other quantifier and not the
     * element at the line.
     */
    @Test
    void besideAnotherQuantifierOverTheSameContainerTheOtherStaysAQuantifier() {
        Proposition above = new Proposition.Some(CONTAINER, compared(N, 0, Rel.GT), true);
        Proposition below = new Proposition.Some(CONTAINER, compared(N, 0, Rel.GE).denied(),
                true);
        List<Proposition> cases = casesOf(Proposition.all(List.of(above, below)),
                compared(N, 0, Rel.GT));
        assertFalse(cases.isEmpty(), "the line decides somewhere");
        for (Proposition each : cases) {
            assertTrue(unquantified(each).stream().noneMatch(atom -> atom.equals(
                            compared(N, 0, Rel.GE).key())),
                    () -> "the element below nought is the other quantifier's: " + each);
        }
    }

    /**
     * A relation about the row inside a quantifier is the same relation wherever the quantifier
     * looks: it decides where some element meets the rest, and asks nothing of one element.
     */
    @Test
    void aRelationOfTheRowInsideAQuantifierDecidesWhereSomeElementMeetsTheRest() {
        Proposition some = new Proposition.Some(CONTAINER,
                Proposition.all(List.of(compared(N, 0, Rel.GT), compared(A, 5, Rel.GT))), true);
        List<Proposition> cases = casesOf(some, compared(A, 5, Rel.GT));
        assertFalse(cases.isEmpty() || cases.equals(List.of(new Proposition.Always(false))),
                () -> "the line on a decides somewhere: " + cases);
        for (Proposition each : cases) {
            assertTrue(unquantified(each).stream().noneMatch(atom -> atom.contains("xs")),
                    () -> "nothing of an element is asked outside the quantifier: " + each);
        }
    }

    /**
     * A relation about the row decides in the same cases whether it is written inside a quantifier
     * or beside it: some element above nought with {@code a} above five is {@code a} above five
     * and some element above nought. Each case a case of its own, as written beside it — and
     * taken apart the same where the relation stands outside the quantifier as well.
     */
    @Test
    void aRelationOfTheRowDecidesTheSameInsideAQuantifierAsBesideIt() {
        Proposition.Compared row = compared(A, 5, Rel.GT);
        Proposition element = compared(N, 0, Rel.GT);
        Proposition inside = new Proposition.Some(CONTAINER,
                Proposition.all(List.of(element, row)), true);
        Proposition beside = Proposition.all(List.of(row,
                new Proposition.Some(CONTAINER, element, true)));
        Proposition t0 = truth("t0");
        Proposition t1 = truth("t1");
        Proposition t2 = truth("t2");
        // Inside alone, and inside as well as outside it.
        for (List<Proposition> rest : List.of(
                List.of(Proposition.all(List.of(t0, t1))),
                List.of(Proposition.all(List.of(row, t0)), Proposition.all(List.of(t1, t2))))) {
            List<Proposition> written = new ArrayList<>(rest);
            written.add(inside);
            List<Proposition> read = new ArrayList<>(rest);
            read.add(beside);
            List<DecidingCase> cases = decidingCasesOf(Proposition.any(written), row);
            assertTrue(cases.size() > 1 && cases.stream().allMatch(DecidingCase::saidAlone),
                    () -> "taken apart, each said for itself: " + cases);
            assertEquals(Set.copyOf(casesOf(Proposition.any(read), row)),
                    Set.copyOf(cases.stream().map(DecidingCase::condition).toList()),
                    () -> "the same cases as written beside the quantifier, of " + written);
        }
    }

    /**
     * A truth of the row inside a quantifier and beside it is one part: {@code x} above nought
     * decides where {@code t} and {@code u} hold, or where {@code t} fails and some element is
     * above nought — and not where some element is above nought with {@code t} failing whatever
     * {@code t} is beside it, which a quantifier read as a part of its own would say.
     */
    @Test
    void aTruthOfTheRowInsideAQuantifierAndBesideItIsOnePart() {
        Proposition.Compared line = compared(A, 0, Rel.GT);
        Proposition t = truth("t");
        Proposition element = compared(N, 0, Rel.GT);
        Proposition written = Proposition.all(List.of(line, Proposition.any(List.of(
                Proposition.all(List.of(t, truth("u"))),
                new Proposition.Some(CONTAINER, Proposition.all(List.of(element, t.denied())),
                        true)))));
        Proposition read = Proposition.all(List.of(line, Proposition.any(List.of(
                Proposition.all(List.of(t, truth("u"))),
                Proposition.all(List.of(t.denied(),
                        new Proposition.Some(CONTAINER, element, true)))))));

        assertEquals(Set.copyOf(casesOf(read, line)), Set.copyOf(casesOf(written, line)));
    }

    /**
     * A quantifier holding eighteen relations about the row, each with one about its element and
     * any of them enough, is said outside the quantifier once for every way the eighteen come
     * out, which is more than a statement is read in. Nothing is taken apart then, and every line
     * says so, naming the figure.
     */
    @Test
    void aQuantifierPastTheStepsLeavesEveryLineNotTakenApart() {
        List<Proposition> each = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            each.add(Proposition.all(List.of(compared(TermPath.of("r" + i), 0, Rel.GT),
                    compared(XS.element().then("n" + i), 0, Rel.GT))));
        }
        Proposition stated = new Proposition.Some(CONTAINER, Proposition.any(each), true);
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);

        assertEquals(36, lines.size(), lines::toString);
        for (WhereEachLineDecides.Decides line : lines) {
            assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                    stoppedAt(line.cases()), () -> "nothing taken apart: " + line);
        }
    }

    /** Every figure the cases were stopped at, and none where a case was taken apart. */
    private static Set<CompositionBudget> stoppedAt(List<DecidingCase> cases) {
        Set<CompositionBudget> out = new HashSet<>();
        for (DecidingCase each : cases) {
            stoppedAt(each.standsFor(), out);
        }
        return out;
    }

    private static void stoppedAt(DecidingCase.Cases cases, Set<CompositionBudget> into) {
        switch (cases) {
            case DecidingCase.Cases.One one -> throw new AssertionError("a case taken: " + one);
            case DecidingCase.Cases.EachOf(var alternatives) ->
                    alternatives.forEach(one -> stoppedAt(one, into));
            case DecidingCase.Cases.Together(var factors) ->
                    factors.forEach(one -> stoppedAt(one, into));
            case DecidingCase.Cases.NotTakenApart(var figure) -> into.add(figure);
        }
    }

    private static Proposition truth(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    /** The relation {@code at} against {@code value} as {@code rel}, held. */
    private static Proposition.Compared compared(TermPath at, long value, Rel rel) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(at)), ExactRatio.ONE)), rel), true);
    }

    /** Where {@code line} decides in {@code stated}. */
    private static List<Proposition> casesOf(Proposition stated, Proposition.Compared line) {
        return decidingCasesOf(stated, line).stream().map(DecidingCase::condition).toList();
    }

    private static List<DecidingCase> decidingCasesOf(Proposition stated,
                                                      Proposition.Compared line) {
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);
        for (WhereEachLineDecides.Decides each : lines) {
            if (each.line().key().equals(line.key())) {
                return each.cases();
            }
        }
        throw new AssertionError(line + " is a line of " + stated + ": " + lines);
    }

    /** The spellings of the parts of {@code stated} no quantifier holds, held. */
    private static List<String> unquantified(Proposition stated) {
        List<String> out = new ArrayList<>();
        switch (stated) {
            case Proposition.All all -> all.parts().forEach(part -> out.addAll(unquantified(part)));
            case Proposition.Any any -> any.parts().forEach(part -> out.addAll(unquantified(part)));
            case Proposition.Some _ -> { }
            default -> out.add(stated instanceof Proposition.Compared compared && !compared.holds()
                    ? compared.denied().key() : stated.key());
        }
        return out;
    }
}
