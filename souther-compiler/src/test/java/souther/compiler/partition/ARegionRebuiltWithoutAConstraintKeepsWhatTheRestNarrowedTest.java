package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.OnAWay;
import souther.compiler.partition.UndividedByARelation.Rebuilding;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A region made again without some of the constraints it was narrowed by is the declarations with
 * the rest of them taken in: what the ones taken away narrowed is given back, and what the others
 * narrowed stays, the hole a case or a value leaves as much as a relation between values.
 *
 * <p>Held here by what the region leaves the places, with a sum held to a line and a value held
 * off nought: without the sum the first place runs as far as the declarations let it, and the
 * second still runs from one.
 */
class ARegionRebuiltWithoutAConstraintKeepsWhatTheRestNarrowedTest {

    private static final String MODEL = """
            module example.sum

            data P = { a: Int, b: Int }
                invariant aWithin = a >= 0 && a <= 50
                invariant bWithin = b >= 0 && b <= 12

            data Taken

            behavior take : (p: P) -> Taken
            """;

    private static final NumericTerm.ValueOf A = value("a");
    private static final NumericTerm.ValueOf B = value("b");

    /** {@code a + b <= 50}. */
    private static final TakenConstraint.Affine SUM_WITHIN_THE_LINE = new TakenConstraint.Affine(
            sum(ExactRatio.of(-50)), Rel.LE);

    /** {@code b >= 1}. */
    private static final TakenConstraint.Affine B_AT_LEAST_ONE = new TakenConstraint.Affine(
            LinearForm.atomMinusConstant(B, ExactRatio.ONE), Rel.GE);

    /** {@code b} is not nought, as the else of {@code b == 0} holds it. */
    private static final TakenConstraint B_IS_NOT_NOUGHT =
            new TakenConstraint.AwayFrom(B, Count.of(0));

    private static NumericTerm.ValueOf value(String field) {
        return new NumericTerm.ValueOf(TermPath.of("p").then(field));
    }

    private static LinearForm<NumericTerm> sum(ExactRatio constant) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(A, ExactRatio.ONE);
        coefs.put(B, ExactRatio.ONE);
        return new LinearForm<>(constant, coefs);
    }

    /** What the declarations leave, read once: every test narrows it and none changes it. */
    private static final SearchRegion DECLARATIONS = declarationsOfTheModel();

    private static SearchRegion declarations() {
        return DECLARATIONS;
    }

    private static SearchRegion declarationsOfTheModel() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("take"), reading,
                        TypeCardinality.Counts.workedOutIn(reading),
                        Membership.none())
                .quantities(rules).region();
    }

    /** The ends of the run {@code place} has in {@code within}, as numbers. */
    private static List<BigDecimal> runOf(SearchRegion within, NumericTerm place) {
        NumericDomain.Bounds runs = switch (within.projectionOf(LinearForm.atom(place))) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds) -> bounds;
            case NumericDomain.FormProjection.NothingIsLeft _ ->
                    throw new AssertionError("these rules leave a value: " + place);
            case null -> throw new AssertionError("the region does not project " + place);
        };
        return List.of(((Count) runs.min().at()).at(), ((Count) runs.max().at()).at());
    }

    private static List<BigDecimal> run(int least, int greatest) {
        return List.of(BigDecimal.valueOf(least), BigDecimal.valueOf(greatest));
    }

    private static void assertRuns(SearchRegion within, List<BigDecimal> first,
                                   List<BigDecimal> second, String why) {
        assertEquals(first, runOf(within, A), why + ": a");
        assertEquals(second, runOf(within, B), why + ": b");
    }

    private static final List<TakenConstraint> BOTH = List.of(B_AT_LEAST_ONE,
            SUM_WITHIN_THE_LINE);

    @Test
    void takingNothingAwayIsTheRegionTheConstraintsMake() {
        SearchRegion within = TakenConstraint.narrowedByAllBut(BOTH, List.of(), List.of(),
                declarations());

        assertRuns(within, run(0, 49), run(1, 12), "the floor of b and the sum both narrow");
    }

    /** With the sum out, a runs as far as the declarations let it, and b keeps its floor. */
    @Test
    void theSumTakenAwayGivesBackWhatItNarrowedAndKeepsTheFloor() {
        SearchRegion within = TakenConstraint.narrowedByAllBut(BOTH,
                List.of(SUM_WITHIN_THE_LINE), List.of(), declarations());

        assertRuns(within, run(0, 50), run(1, 12), "the sum is out and the floor stays");
    }

    @Test
    void theFloorTakenAwayKeepsTheSum() {
        SearchRegion within = TakenConstraint.narrowedByAllBut(BOTH,
                List.of(B_AT_LEAST_ONE), List.of(), declarations());

        assertRuns(within, run(0, 50), run(0, 12), "the floor is out, and the sum with b at"
                + " nought leaves a its greatest");
    }

    /** A value held apart is no end of a run, and is kept when another constraint is taken away. */
    @Test
    void aHoleStaysWhateverElseIsTakenAway() {
        List<TakenConstraint> held = List.of(B_IS_NOT_NOUGHT, SUM_WITHIN_THE_LINE);

        assertTrue(TakenConstraint.narrowedByAllBut(held, List.of(), List.of(), declarations())
                .apartAt(B).has(Count.of(0)), "the hole is in the region the two make");
        assertTrue(TakenConstraint.narrowedByAllBut(held, List.of(SUM_WITHIN_THE_LINE),
                List.of(), declarations()).apartAt(B).has(Count.of(0)),
                "and stays with the sum taken away");
        assertFalse(TakenConstraint.narrowedByAllBut(held, List.of(B_IS_NOT_NOUGHT), List.of(),
                declarations()).apartAt(B).has(Count.of(0)),
                "and goes with the hole taken away");
    }

    /** One taken away of two alike leaves one; every one of them taken away leaves none. */
    @Test
    void aConstraintTakenInTwiceIsTakenAwayOnceOrEverywhereAsAskedFor() {
        List<TakenConstraint> twice = List.of(SUM_WITHIN_THE_LINE, B_AT_LEAST_ONE,
                SUM_WITHIN_THE_LINE);

        assertRuns(TakenConstraint.narrowedByAllBut(twice, List.of(SUM_WITHIN_THE_LINE),
                List.of(), declarations()), run(0, 49), run(1, 12), "one of the two is left");
        assertRuns(TakenConstraint.narrowedByAllBut(twice, List.of(),
                List.of(SUM_WITHIN_THE_LINE), declarations()), run(0, 50), run(1, 12),
                "every one of them is out");
    }

    private static OnAWay statingThat(TakenConstraint relation) {
        return new OnAWay(Set.of(TermPath.of("p").then("a")), false, relation, null);
    }

    /** A case an arm opens: what stands at a value, with no relation. */
    private static final OnAWay THE_CASE = new OnAWay(Set.of(TermPath.of("p")), true, null, null);

    /** What some element of a container meets: nothing a region carries as a relation. */
    private static final OnAWay SOME_ELEMENT = new OnAWay(Set.of(TermPath.of("p").then("items")),
            false, null, TermPath.of("p").then("items"));

    private static final OnAWay THE_SUM = statingThat(SUM_WITHIN_THE_LINE);
    private static final OnAWay THE_FLOOR = statingThat(B_AT_LEAST_ONE);

    private static Rebuilding rebuilding(List<TakenConstraint> applied, List<OnAWay> written,
                                         List<TakenConstraint.Affine> met) {
        return new Rebuilding(applied, written, met);
    }

    /**
     * The case an arm opens stays among the statements and the sum is taken away: the region is
     * the declarations less the sum, and the floor of {@code b} stays.
     */
    @Test
    void aCaseLeftAmongTheStatementsDoesNotKeepTheSumTakenAwayInTheRegion() {
        SearchRegion within = rebuilding(BOTH, List.of(THE_CASE, THE_FLOOR, THE_SUM), List.of())
                .without(List.of(THE_CASE, THE_FLOOR), declarations());

        assertRuns(within, run(0, 50), run(1, 12), "the sum is out, the case and the floor stay");
    }

    @Test
    void statementsTakenAwayOfNothingLeaveTheRegionTheListMakes() {
        List<OnAWay> written = List.of(THE_CASE, THE_FLOOR, THE_SUM);

        assertRuns(rebuilding(BOTH, written, List.of()).without(written, declarations()),
                run(0, 49), run(1, 12), "nothing is taken away");
    }

    /** A statement a row at the line meets stays among the statements and leaves the list. */
    @Test
    void aStatementMetByARowAtTheLineComesOutOfTheListWhereverItIs() {
        List<OnAWay> written = List.of(THE_FLOOR, THE_SUM);

        assertRuns(rebuilding(BOTH, written, List.of(SUM_WITHIN_THE_LINE))
                .without(written, declarations()), run(0, 50), run(1, 12), "the sum is met");
    }

    /** Of two statements alike one is taken away, and the other keeps its place in the list. */
    @Test
    void ofTwoStatementsAlikeOneTakenAwayLeavesTheOther() {
        SearchRegion within = rebuilding(List.of(B_AT_LEAST_ONE, SUM_WITHIN_THE_LINE,
                SUM_WITHIN_THE_LINE), List.of(THE_SUM, THE_SUM), List.of())
                .without(List.of(THE_SUM), declarations());

        assertRuns(within, run(0, 49), run(1, 12), "the sum is still in the list once");
    }

    /**
     * A case or an element asked of a container narrowed the region by what a statement does not
     * carry, so taking it away is refused; a statement that narrows nothing is taken away and
     * the region is the one the list makes.
     */
    @Test
    void aStatementTheRegionTookInBySomethingItDoesNotCarryCannotBeTakenAway() {
        List<OnAWay> written = List.of(THE_CASE, SOME_ELEMENT, THE_SUM);

        assertThrows(IllegalStateException.class, () -> rebuilding(BOTH, written, List.of())
                .without(List.of(SOME_ELEMENT, THE_SUM), declarations()), "the case");
        assertThrows(IllegalStateException.class, () -> rebuilding(BOTH, written, List.of())
                .without(List.of(THE_CASE, THE_SUM), declarations()), "the element");
        OnAWay saysNothing = new OnAWay(Set.of(), false, null, null);
        assertRuns(rebuilding(BOTH, List.of(saysNothing, THE_SUM), List.of())
                .without(List.of(THE_SUM), declarations()), run(0, 49), run(1, 12),
                "a statement of nothing the region took in");
    }
}
