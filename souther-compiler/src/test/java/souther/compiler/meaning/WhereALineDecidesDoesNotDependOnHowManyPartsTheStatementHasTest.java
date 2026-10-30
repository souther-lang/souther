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
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line decides is taken apart into cases however many parts the statement holds, and comes
 * to the same cases for the same statement however it is written.
 *
 * <p>The cases are what a reader asks one at a time whether rows stand on each side of the line
 * in, and said as one condition for several, a row on one side and a row on the other may each be
 * in a case of its own, which the line never turns between. So a statement too large to read one
 * way is not one whose cases may be said as one: it is read another way, or it is said not to have
 * been read.
 */
class WhereALineDecidesDoesNotDependOnHowManyPartsTheStatementHasTest {

    private static final Proposition.Compared LINE = compared("x");

    /**
     * {@code x} above nought with one truth, or every one of {@code truths} others: the line
     * decides where the one holds and some of the others fails, which is a case for each of the
     * others failing with those before it held — the same rule at twelve parts and at fifteen.
     */
    @Test
    void theCasesComeOutByTheSameRuleWhateverHowManyParts() {
        for (int truths : new int[] {10, 14}) {
            List<Proposition> others = truths(1, truths);
            Proposition stated = Proposition.any(List.of(
                    Proposition.all(List.of(LINE, truth("t00"))), Proposition.all(others)));

            List<Proposition> expected = new ArrayList<>();
            for (int failing = 0; failing < others.size(); failing++) {
                List<Proposition> each = new ArrayList<>(others.subList(0, failing));
                each.add(others.get(failing).denied());
                each.add(truth("t00"));
                expected.add(Proposition.all(each));
            }
            List<DecidingCase> cases = casesOf(stated);
            int of = truths;
            assertEquals(Set.copyOf(expected), Set.copyOf(conditions(cases)),
                    () -> "each of the others failing, of " + of + ": " + cases);
            assertTrue(cases.stream().allMatch(DecidingCase::saidAlone),
                    () -> "each said for itself: " + cases);
        }
    }

    /**
     * The same statement with parts that hold nowhere joined to it, as many as take it past a
     * dozen: what it comes to is the same, and so is every case of where the line decides.
     */
    @Test
    void partsThatChangeNothingChangeNoCase() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(LINE, truth("t00"))),
                Proposition.all(truths(1, 4))));
        List<Proposition> nowhere = new ArrayList<>(List.of(stated));
        for (Proposition each : truths(20, 34)) {
            nowhere.add(Proposition.all(List.of(each, each.denied())));
        }

        assertEquals(casesOf(stated), casesOf(Proposition.any(nowhere)));
    }

    /**
     * The line held with {@code q} or with {@code q} failing is the line held: {@code q} turns
     * nothing, and a case taken apart on it would be two, each of which a row could be on one side
     * of alone. Past a dozen parts, as below.
     */
    @Test
    void aPartWhereTheLineDecidesDoesNotTurnOnIsNoCase() {
        Proposition q = truth("q");
        List<Proposition> others = truths(1, 13);
        Proposition stated = Proposition.any(List.of(Proposition.all(List.of(LINE, q)),
                Proposition.all(List.of(LINE, q.denied())), Proposition.all(others)));

        List<DecidingCase> cases = casesOf(stated);
        assertEquals(others.size(), cases.size(), cases::toString);
        assertTrue(conditions(cases).stream().noneMatch(each -> each.spelledOut().contains("q")),
                () -> "no case asks q: " + cases);
    }

    /**
     * {@code x} above nought, the term the first case, and not the second case with every truth
     * holding. The term is one case, so where it is the first it is not the second, and the line
     * decides wherever the term is the first: one case, at four truths and at thirteen — and not
     * the term the first and a truth failing, which asks of ways the term is both.
     */
    @Test
    void waysNoRowIsAreLeftOutPastADozenParts() {
        for (int truths : new int[] {4, 13}) {
            List<Proposition> notBoth = new ArrayList<>(List.of(inCases("B").denied()));
            truths(1, truths).forEach(each -> notBoth.add(each.denied()));
            Proposition stated = Proposition.all(List.of(LINE, inCases("A"),
                    Proposition.any(notBoth)));

            int of = truths;
            assertEquals(List.of(inCases("A")), conditions(casesOf(stated)),
                    () -> "the term the first case, of " + of + " truths");
        }
    }

    /**
     * Eighteen pairs, any of them both holding, beside a choice that holds nowhere and names the
     * first of every pair before any second: read in the order the parts first stand, the
     * statement is left as a different statement every way the first eighteen come out, which is
     * more steps than a statement is read in. The line is where the statement turns, said for
     * cases nobody took apart, and the figure that stopped it is the one said.
     */
    @Test
    void aStatementPastTheStepsIsSaidNotToHaveBeenTakenApart() {
        List<Proposition> pairs = new ArrayList<>();
        List<Proposition> firsts = new ArrayList<>(List.of(truth("a00").denied()));
        for (int i = 0; i < 18; i++) {
            pairs.add(Proposition.all(List.of(truth("a%02d".formatted(i)),
                    truth("b%02d".formatted(i)))));
            firsts.add(truth("a%02d".formatted(i)));
        }
        pairs.add(Proposition.all(firsts));
        List<DecidingCase> cases = casesOf(Proposition.all(List.of(LINE,
                Proposition.any(pairs))));

        assertEquals(1, cases.size(), cases::toString);
        assertEquals(List.of(new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)),
                notTakenApart(cases.getFirst().standsFor()), cases::toString);
    }

    /** What {@code cases} stands for that nobody took apart, failing on any case taken. */
    private static List<DecidingCase.Cases> notTakenApart(DecidingCase.Cases cases) {
        return switch (cases) {
            case DecidingCase.Cases.One one -> throw new AssertionError("a case taken: " + one);
            case DecidingCase.Cases.EachOf(var alternatives) -> alternatives.stream()
                    .flatMap(one -> notTakenApart(one).stream()).toList();
            case DecidingCase.Cases.Together(var factors) -> factors.stream()
                    .flatMap(one -> notTakenApart(one).stream()).toList();
            case DecidingCase.Cases.NotTakenApart notTaken -> List.of(notTaken);
        };
    }

    /** Where {@link #LINE} decides in {@code stated}. */
    static List<DecidingCase> casesOf(Proposition stated) {
        for (WhereEachLineDecides.Decides each : WhereEachLineDecides.in(stated)) {
            if (each.line().spelledOut().equals(LINE.spelledOut())) {
                return each.cases();
            }
        }
        throw new AssertionError(LINE + " is a line of " + stated);
    }

    private static List<Proposition> conditions(List<DecidingCase> cases) {
        return cases.stream().map(DecidingCase::condition).toList();
    }

    /** The truths {@code t<from>} up to {@code t<to>}, not counting the last. */
    private static List<Proposition> truths(int from, int to) {
        List<Proposition> out = new ArrayList<>();
        for (int i = from; i < to; i++) {
            out.add(truth("t%02d".formatted(i)));
        }
        return out;
    }

    private static Proposition truth(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    /** {@code name} above nought, held. */
    private static Proposition.Compared compared(String name) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(name))),
                        ExactRatio.ONE)), Rel.GT), true);
    }

    /** The term being {@code leaf}. */
    private static Proposition inCases(String leaf) {
        return new Proposition.InCases(new DecisionSubject.AnInput(TermPath.of("term")),
                CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(
                        TypeSymbols.declared(new TypeKey("probe", leaf)), true)))),
                true);
    }
}
