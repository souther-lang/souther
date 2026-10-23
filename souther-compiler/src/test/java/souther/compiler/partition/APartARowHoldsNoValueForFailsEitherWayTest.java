package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A part of a statement about a position a row put nothing at is on neither side at that row: the
 * part fails there, and so does its denial.
 *
 * <p>A row holding no value at a position — under a case it is not, past the end of a container —
 * is no row whose value there is anything, so it is not one where the part is false either. Read as
 * failing and the denial read off that, a denied truth, a denied case and a denied relation all held
 * at every row that left the position empty, and a line deciding where one of them is denied was
 * said to decide at rows that never reach it. Asked of every kind of part a row is asked, since the
 * way round is applied to what each says in one place.
 */
class APartARowHoldsNoValueForFailsEitherWayTest {

    private static final RuleReadingSource RULES =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final TermPath A = TermPath.of("a");
    private static final TermPath B = TermPath.of("b");

    private static final NumericTerm.ValueOf A_NUMBER = new NumericTerm.ValueOf(A);
    private static final NumericTerm.ValueOf B_NUMBER = new NumericTerm.ValueOf(B);

    @Test
    void aTruthOfAPositionNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.Truth(new DecisionSubject.AnInput(A), true));
    }

    @Test
    void aValueBeingThereAtAPositionNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.Present(new DecisionSubject.AnInput(A), true));
    }

    @Test
    void aCaseOfAPositionNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.InCases(new DecisionSubject.AnInput(A),
                CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(
                        TypeSymbols.declared(new TypeKey("probe", "Hot")), true)))), true));
    }

    @Test
    void oneValueAtTwoPositionsNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.SameValue(new DecisionSubject.AnInput(A),
                new DecisionSubject.AnInput(B), true));
    }

    @Test
    void aRelationOverAPositionNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-3), Map.of(new DecisionAtom.OfTheInput(A_NUMBER), ExactRatio.ONE)),
                Rel.GT), true));
    }

    @Test
    void aRelationOnAProductOfAFactorNothingWasWrittenAtFailsEitherWay() {
        assertFailsEitherWay(new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-3), Map.of(new Quantity.ProductOfTwo(A_NUMBER, B_NUMBER),
                        ExactRatio.ONE)), Rel.GT), true));
    }

    private static void assertFailsEitherWay(Proposition stated) {
        assertEquals(AStatementAtARow.Answer.FAILS, atARowWritingNothing(stated),
                () -> "held: " + stated);
        assertEquals(AStatementAtARow.Answer.FAILS, atARowWritingNothing(stated.denied()),
                () -> "denied: " + stated);
    }

    private static AStatementAtARow.Answer atARowWritingNothing(Proposition stated) {
        return AStatementAtARow.of(stated, "f", quantities()).at(new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(ObservationAtPoint.WROTE_NOTHING);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a part about one position is not read over a run");
            }
        });
    }

    /** A reading of an input taking two whole numbers, {@code a} and {@code b}. */
    private static Quantities quantities() {
        RuleReadingContext reading =
                RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(
                List.of(new InputDomain.Parameter("a", null, Type.INT),
                        new InputDomain.Parameter("b", null, Type.INT)),
                reading, TypeCardinality.Counts.workedOutIn(reading),
                Membership.none()).quantities(RULES);
    }
}
