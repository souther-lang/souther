package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

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
     * A quantifier holding eighteen relations about the row, each or one about its element and
     * every one of those choices together, is said outside the quantifier once for every way the
     * eighteen come out, which is more than a statement is read in. Nothing is taken apart then,
     * and every line says so, naming the figure.
     */
    @Test
    void aQuantifierPastTheStepsLeavesEveryLineNotTakenApart() {
        List<Proposition> each = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            each.add(Proposition.any(List.of(compared(TermPath.of("r" + i), 0, Rel.GT),
                    compared(XS.element().then("n" + i), 0, Rel.GT))));
        }
        Proposition stated = new Proposition.Some(CONTAINER, Proposition.all(each), true);
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);

        assertEquals(36, lines.size(), lines::toString);
        for (WhereEachLineDecides.Decides line : lines) {
            assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                    stoppedAt(line.cases()), () -> "nothing taken apart: " + line);
        }
    }

    /**
     * Eighteen relations about the row, each with one about the element, any of them enough: some
     * element meeting one of them is one of them with some element meeting its other half, so
     * nothing is said once for each way the eighteen come out, and the statement is read. Where a
     * line decides is then more cases than are taken apart, which is the figure said, and not how
     * many steps a statement is read in.
     */
    @Test
    void aQuantifierOverChoicesIsSaidChoiceByChoice() {
        List<Proposition> each = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            each.add(Proposition.all(List.of(compared(TermPath.of("r" + i), 0, Rel.GT),
                    compared(XS.element().then("n" + i), 0, Rel.GT))));
        }
        Proposition stated = new Proposition.Some(CONTAINER, Proposition.any(each), true);

        for (WhereEachLineDecides.Decides line : WhereEachLineDecides.in(stated)) {
            assertFalse(notTakenApartAt(line.cases())
                            .contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                    () -> "read: " + line.line());
        }
    }

    /**
     * Some element meeting a truth of the row or a relation of its own: with the truth held, the
     * element meets what holds wherever it is, which is no part to say once held and once failing.
     * Read, and where the line on the element decides is taken apart; and the same of a quantifier
     * written over what holds everywhere beside a line of the row.
     */
    @Test
    void aQuantifierOverWhatHoldsEverywhereIsReadAsItIs() {
        Proposition.Compared element = compared(N, 0, Rel.GT);
        List<DecidingCase> ofTheElement = decidingCasesOf(new Proposition.Some(CONTAINER,
                Proposition.any(List.of(truth("flag"), element)), true), element);
        assertFalse(ofTheElement.isEmpty(), "the line on the element decides somewhere");
        assertEquals(Set.of(), notTakenApartAt(ofTheElement), ofTheElement::toString);

        Proposition.Compared row = compared(A, 5, Rel.GT);
        List<DecidingCase> ofTheRow = decidingCasesOf(Proposition.all(List.of(row,
                new Proposition.Some(CONTAINER, new Proposition.Always(true), true))), row);
        assertFalse(ofTheRow.isEmpty(), "the line on the row decides somewhere");
        assertEquals(Set.of(), notTakenApartAt(ofTheRow), ofTheRow::toString);
    }

    /**
     * Some element meeting {@code k} and the line, or no element meeting {@code k} and {@code d}:
     * a lookup with a default. The first quantifier holds only where the second does, so with
     * the second failing the first cannot hold, and {@code d} turns nothing of whether the line is
     * read. The line decides in one case, where some element meets {@code k}; and {@code d}
     * decides where none does, with nothing asked of the first quantifier. The same where the
     * second asks nothing of its element, which is the container holding one.
     */
    @Test
    void aQuantifierHoldingOnlyWhereAnotherDoesIsNotSplitByWhatStandsBesideTheOther() {
        Proposition.Compared line = compared(N, 0, Rel.GT);
        Proposition.Compared d = compared(A, 0, Rel.GT);
        for (Proposition k : List.of(compared(XS.element().then("k"), 0, Rel.GT),
                new Proposition.Always(true))) {
            Proposition entry = new Proposition.Some(CONTAINER,
                    Proposition.all(List.of(k, line)), true);
            Proposition.Some filed = new Proposition.Some(CONTAINER, k, true);
            Proposition stated = Proposition.any(List.of(entry,
                    Proposition.all(List.of(filed.denied(), d))));

            assertEquals(List.of(Proposition.all(List.of(filed, k))), casesOf(stated, line),
                    () -> "where some element meets k, and of the element at the line, k: "
                            + stated);
            assertEquals(List.of(filed.denied()), casesOf(stated, d),
                    () -> "the default's line decides where nothing meets k, of " + stated);
        }
    }

    /**
     * The same lookup beside five pairs of truths, any of which is enough: the entry's line
     * decides where none of the pairs holds, which is more cases than are said one by one, and is
     * said in one condition. That condition is where some element meets {@code k} as well, as the
     * cases it stands for are: said without it, it would hold where no element does, which is
     * no row's.
     */
    @Test
    void aLineSaidInOneConditionIsSaidWhereTheQuantifierItImpliesHolds() {
        Proposition.Compared line = compared(N, 0, Rel.GT);
        Proposition k = compared(XS.element().then("k"), 0, Rel.GT);
        Proposition.Some filed = new Proposition.Some(CONTAINER, k, true);
        List<Proposition> parts = new ArrayList<>(List.of(
                new Proposition.Some(CONTAINER, Proposition.all(List.of(k, line)), true),
                Proposition.all(List.of(filed.denied(), compared(A, 0, Rel.GT)))));
        for (int i = 0; i < 5; i++) {
            parts.add(Proposition.all(List.of(truth("t" + i), truth("u" + i))));
        }
        List<DecidingCase> cases = decidingCasesOf(Proposition.any(parts), line);

        assertFalse(cases.isEmpty() || cases.stream().allMatch(DecidingCase::saidAlone),
                () -> "said in one condition: " + cases);
        for (DecidingCase each : cases) {
            assertTrue(each.condition() instanceof Proposition.All all
                            && all.parts().contains(filed),
                    () -> "said where some element meets k: " + each.condition());
        }
    }

    /**
     * The control: where the second quantifier asks of its element something the first does not,
     * an element meeting the first need not meet it, and {@code d} beside it turns whether the
     * line is read.
     */
    @Test
    void aQuantifierAskingWhatAnotherDoesNotIsSplitByWhatStandsBesideIt() {
        Proposition.Compared line = compared(N, 0, Rel.GT);
        Proposition.Compared d = compared(A, 0, Rel.GT);
        Proposition entry = new Proposition.Some(CONTAINER, Proposition.all(List.of(
                compared(XS.element().then("k"), 0, Rel.GT), line)), true);
        Proposition other = new Proposition.Some(CONTAINER,
                compared(XS.element().then("j"), 0, Rel.GT), false);
        Proposition stated = Proposition.any(List.of(entry, Proposition.all(List.of(other, d))));

        List<Proposition> ofTheLine = casesOf(stated, line);
        assertTrue(ofTheLine.stream().anyMatch(each -> each.key().contains(d.key())),
                () -> "the default's line tells the cases apart: " + ofTheLine);
    }

    /**
     * Three quantifiers each holding only where the next does: some element meeting {@code k},
     * {@code j} and the line, or none meeting {@code k} and {@code j} and {@code d}, or none
     * meeting {@code k} and {@code e}. The line decides in one case, where some element meets
     * {@code k} and {@code j}, which is where the first can hold at all; neither {@code d} nor
     * {@code e} is any part of it. Each quantifier holding only where the next does leaves no
     * way that two parts have to cross at once.
     */
    @Test
    void aChainOfQuantifiersIsNotSplitByWhatStandsBesideAnyOfThem() {
        Proposition.Compared line = compared(N, 0, Rel.GT);
        Proposition k = compared(XS.element().then("k"), 0, Rel.GT);
        Proposition j = compared(XS.element().then("j"), 0, Rel.GT);
        Proposition.Some both = new Proposition.Some(CONTAINER, Proposition.all(List.of(k, j)),
                true);
        Proposition stated = Proposition.any(List.of(
                new Proposition.Some(CONTAINER, Proposition.all(List.of(k, j, line)), true),
                Proposition.all(List.of(both.denied(), truth("d"))),
                Proposition.all(List.of(new Proposition.Some(CONTAINER, k, false), truth("e")))));

        assertEquals(List.of(Proposition.all(List.of(both, k, j))), casesOf(stated, line),
                stated::toString);
    }

    /**
     * A quantifier holding only where another does, in a statement that also asks one value's
     * case twice: the value is one case and the quantifiers leave out one way, and both are kept
     * out together. The line decides where some element meets {@code k} and the other case with
     * {@code d} does not hold, which the default's case is no part of.
     */
    @Test
    void aQuantifierBesideAValueAskedTwiceIsReadWithBoth() {
        Proposition.Compared line = compared(N, 0, Rel.GT);
        Proposition k = compared(XS.element().then("k"), 0, Rel.GT);
        Proposition.Some filed = new Proposition.Some(CONTAINER, k, true);
        Proposition other = inCases("Other");
        Proposition d = truth("d");
        Proposition stated = Proposition.any(List.of(
                new Proposition.Some(CONTAINER, Proposition.all(List.of(k, line)), true),
                Proposition.all(List.of(filed.denied(), inCases("One"))),
                Proposition.all(List.of(other, d))));

        assertEquals(Set.of(Proposition.all(List.of(filed, d.denied(), k)),
                        Proposition.all(List.of(filed, d, other.denied(), k))),
                Set.copyOf(casesOf(stated, line)), stated::toString);
    }

    /**
     * Two quantifiers asking the same parts of their elements, written in two orders and so
     * spelled apart: neither is said to hold only where the other does, which would leave every
     * way out where the two come out apart, and the two could be told apart by no one part.
     */
    @Test
    void twoQuantifiersAskingTheSamePartsHoldNeitherOnlyWhereTheOtherDoes() {
        Proposition k = compared(XS.element().then("k"), 0, Rel.GT);
        Proposition n = compared(N, 0, Rel.GT);
        Proposition.Some one = new Proposition.Some(CONTAINER,
                new Proposition.All(List.of(k, n)), true);
        Proposition.Some other = new Proposition.Some(CONTAINER,
                new Proposition.All(List.of(n, k)), true);

        assertFalse(one.key().equals(other.key()), "spelled apart");
        assertFalse(one.elementAsked().holdsOnlyWhere(other.elementAsked()));
        assertFalse(other.elementAsked().holdsOnlyWhere(one.elementAsked()));
    }

    /** The value at {@code term} being the case {@code leaf}. */
    private static Proposition inCases(String leaf) {
        TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
        return new Proposition.InCases(new DecisionSubject.AnInput(TermPath.of("term")),
                CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(symbol, true)))), true);
    }

    /** Every figure some case nobody took apart was stopped at. */
    private static Set<CompositionBudget> notTakenApartAt(List<DecidingCase> cases) {
        Set<CompositionBudget> out = new HashSet<>();
        cases.forEach(each -> notTakenApartAt(each.standsFor(), out));
        return out;
    }

    private static void notTakenApartAt(DecidingCase.Cases cases, Set<CompositionBudget> into) {
        switch (cases) {
            case DecidingCase.Cases.One _ -> { }
            case DecidingCase.Cases.EachOf(var alternatives) ->
                    alternatives.forEach(one -> notTakenApartAt(one, into));
            case DecidingCase.Cases.Together(var factors) ->
                    factors.forEach(one -> notTakenApartAt(one, into));
            case DecidingCase.Cases.NotTakenApart(var figure) -> into.add(figure);
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
